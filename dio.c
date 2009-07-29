/* See LICENSE file for copyright and license details. 
Most of this code is taken from dio

TODO:
	- Allow tagging and group of items
	- Allow output of single items, groups of items or the whole list
	- Allow adding stuff to the list from the command line
	- Allow output of stuff from the commandline
	
*/
#define _BSD_SOURCE
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <locale.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>
#include <sys/wait.h>
#include <X11/keysym.h>
#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>

/* macros */
#define CLEANMASK(mask)	(mask & ~(numlockmask | LockMask))
#define VSEND				((multicol && tw > maxw ? tw / maxw : 1) * th / lh)

/* enums */
enum { ColFG, ColBG, ColLast };
enum { NoColour, Red, Blue, Green, Purple};

/* typedefs */
typedef struct {
	int x, y, w, h;
	unsigned long filter[ColLast];
	unsigned long norm[ColLast];
	unsigned long sel[ColLast];
	unsigned long other[ColLast];
	GC gc;
	struct {
		XFontStruct *xfont;
		XFontSet set;
		int ascent;
		int descent;
		int height;
	} font;
	Window win;
} DC; /* draw context */

typedef struct Item Item;

struct Item {
	Bool played;
	char *text;
	int group;
	Item *next;		/* traverses all items */
	Item *up, *down;	/* traverses items matching current search pattern */
};

/* forward declarations */

/*list*/
static void additem(char *p);
static void delitem(Item *it);
static void clearlist(void);

static void bpress(XButtonEvent * e);
static void cleanup(void);
static void drawline(const char *text, unsigned long bgcol[ColLast], unsigned long fgcol[ColLast]);
static void drawlist(void);
static void drawout(void);
static void drawtext(const char *text, unsigned int l, unsigned int xoffset);

static unsigned long getcolor(const char *colstr);
static Item *getitem(int l);
static unsigned char * getsel(unsigned long offset, unsigned long *len, unsigned long *remain);
static void initfont(const char *fontstr);
static void kpress(XKeyEvent * e);
static void match(void);
static void pointerdown(int x, int y);
static void pointerup(int x, int y);
static void procev(XEvent ev);
static void readstdin(void);
static void run(void);
static void scroll(int nhs, int nvs);
static void scrollto(Item *it);

static void setup(void);
static int textnw(const char *text, unsigned int len);
static int textw(const char *text);

static void sendout(const char *output);
static void eprint(const char *errstr, ...);
#include "config.h"

/* variables */
static char *intxt;
static char outtxt[4096];
static char *p = NULL;
static char searchtxt[4096];
static int common = 0;
static int hscroll, vscroll;
static int maxw = 0;
static int naitems = 0;
static int nitems;
static int screen;
static int wx, wy, ww, wh = 0;
static int lh, tw, th = 0;
static unsigned int numlockmask = 0;
static Bool chording = False;
static Bool doing = False;
static Bool follow = False;
static Bool multicol = False;
static Bool over = False;
static Bool readin = True;
static Bool readonly = False;
static Bool running = False;
static Bool scrolling = False;
static Bool urgent = False;
static Display *dpy;
static DC dc;
static Item *allitems = NULL;	/* first of all items */
static Item *item = NULL;	/* first of pattern matching items */
static Item *first = NULL;
static Item *last = NULL;
static Item *lastview = NULL;
static Item *nextsel = NULL;
static Item *nextpage = NULL;
static Item *sel = NULL;
static Window outwin, root, txtwin, win;
static pid_t chldpid = -1;
Atom wmdeletemsg;

void
additem(char *p) {
	Item *new;
	XWMHints hints;

	if(!strcmp(p, "\e[2J")) {
		clearlist();
		return;
	}
	if((new = (Item *)malloc(sizeof(Item))) == NULL)
		eprint("fatal: could not malloc() %u bytes\n", sizeof(Item));
	new->next = new->up = new->down = NULL;
	new->played = False;
	new->text = p;
	new->group = NoColour;
	if(!last || !allitems)
		allitems = new;
	else 
		last->next = new;
	last = new;
	naitems++;
	if(urgent && win) {
		hints.flags = XUrgencyHint;
		XSetWMHints(dpy, win, &hints);
	}
}

void
bpress(XButtonEvent * e) {
	int l;

	l = (multicol && tw > maxw ? (e->x / maxw) * (th / lh) : 0) + e->y / lh;
	drawlist();
	switch(e->button) {
	default:
		return;
		break;
	case Button1:
		if(e->window == win) {
			/*if(playcmd && CLEANMASK(e->state) & Button3Mask) {
				chording = True;
				drawlist();
				break;
			}*/
			scrolling = True;
			scroll(hscroll, (e->y - 1) * nitems / (wh - 2));
		}
		else if(CLEANMASK(e->state) & Button3Mask) {
			chording = True;
			if(readonly)
				break;
			delitem(getitem(l));
			drawlist();
		}
		break;
	case Button2:
		if(e->window == outwin) {
			/*pastesel();*/
			break;
		}
		if(e->window == win) {
			scrollto(nextsel);
			break;
		}
		nextsel = getitem(l);
		drawlist();
		break;
	case Button3:
		chording = False;
		break;
	case Button4:
		l = (l == 0) ? 1 : l;
		scroll(hscroll, vscroll - l);
		break;
	case Button5:
		l = (l == 0) ? 1 : l;
		scroll(hscroll, vscroll + l);
		break;
	case 6:
		scroll(hscroll - 1, vscroll);
		break;
	case 7:
		scroll(hscroll + 1, vscroll);
		break;
	}
}

void
cleanup(void) {
	Item *itm;

	signal(SIGCHLD, SIG_IGN);
	if(chldpid != -1)
		kill(chldpid, SIGTERM);
	while(allitems) {
		itm = allitems->next;
		free(allitems->text);
		free(allitems);
		allitems = itm;
	}
	if(dc.font.set)
		XFreeFontSet(dpy, dc.font.set);
	else
		XFreeFont(dpy, dc.font.xfont);
	XFreeGC(dpy, dc.gc);
	XDestroyWindow(dpy, win);
	XUngrabKeyboard(dpy, CurrentTime);
}

void
clearlist(void) {
	while(allitems) {
		delitem(allitems);
	}
}

void
configwin(int width, int height) {
	ww = width;
	wh = height;
	tw = ww - lh;
	th = (intxt == outtxt && wh > lh + 1) ? wh - lh - 1 : wh;
	XResizeWindow(dpy, txtwin, tw, th);
	if(follow && nextpage == NULL)
		scroll(hscroll, nitems);
	if(intxt == outtxt) {
		XMoveResizeWindow(dpy, outwin, 0, wh > lh + 1 ? th + 1 : 0, ww, lh);
		XMapRaised(dpy, outwin);
	}
	else {
		XUnmapWindow(dpy, outwin);
	}
	scroll(hscroll, vscroll);
}

void
delitem(Item *it) {
	Item *i;

	if(!it)
		return;
	for(i = allitems; i && i->next != it; i = i->next);
	if(i)
		i->next = it->next;
	if(it == last)
		i = last;
	if(it == item)
		item = it->down;
	if(it->down)
		it->down->up = it->up;
	if(it->up)
		it->up->down = it->down;
	if(it == first)
		first = (it->down) ? it->down : it->up;
	if(first == it->up)
		vscroll--;
	if(it == allitems)
		allitems = it->next;
	nitems--;
	naitems--;
	match();
	free(it->text);
	free(it);
}

void
drawline(const char *text, unsigned long bgcol[ColLast], unsigned long fgcol[ColLast]) {
	int i, i0, len, x;
	XRectangle r = { dc.x, dc.y, dc.w, dc.h };

	XSetForeground(dpy, dc.gc, bgcol[ColBG]);
	XFillRectangles(dpy, dc.win, dc.gc, &r, 1);
	if(!text)
		return;
	len = strlen(text);
	XSetForeground(dpy, dc.gc, fgcol[ColFG]);
	for(i = i0 = x = 0; i < len; i++)
		if(text[i] == '\t') {
			drawtext(text + i0, i - i0, x);
			x += (textnw(text + i0, i - i0) / TABWIDTH + 1) * TABWIDTH;
			i0 = i + 1;
		}
	drawtext(text + i0, i - i0, x);
}

void
drawlist(void) {
	int height;
	unsigned long *bg, *fg;
	unsigned long *groupfg, *groupbg;
	Item *i;

	/* set window name */
	if(sel)
		XStoreName(dpy, win, &sel->text[common]);
	else
		XStoreName(dpy, win, wtitle);

	dc.h = lh;
	dc.x = 0 - hscroll * lh;
	dc.y = 0;
	dc.w = tw - dc.x;
	dc.win = txtwin;
	i = first;
	bg = vscroll % 2 == 1 && normaltbgcolor ? dc.other : dc.norm;
	fg = (!urgent) || lastview ? dc.norm : dc.other;

	do {
		groupfg = fg;
		groupbg = bg;
		if(i){
			if(i->group == Red){
				groupbg = dc.sel;
				groupfg = dc.other;
			}
		}
		drawline(i ? &i->text[common] : NULL, (i && nextsel == i) ? dc.sel : groupbg, (sel == i) ? dc.sel : groupfg);
		bg = normaltbgcolor && bg == dc.norm ? dc.other : dc.norm;
		if(i) {
			if(urgent && i == lastview && i->next)
				fg = dc.other;
			i = i->down;
		}
		dc.y += lh;
		/*if(multicol && i && dc.y + dc.h >= th && 2 * maxw < tw - dc.x) {
			drawline(NULL, dc.norm, dc.norm);
			dc.x += maxw;
			dc.y = 0;
		}*/
	}
	while(dc.y + lh <= th);
	nextpage = i;
	drawline(NULL, dc.norm, dc.norm);

	/* print filter */
	/*dc.w = dc.font.height + textw(searchtxt);
	dc.x = tw - dc.w;
	dc.y = 0;
	if(searchtxt[0])
		drawline(searchtxt[0] ? searchtxt : NULL, dc.filter, dc.filter);*/

	/* vertical scrollbar */
	XSetForeground(dpy, dc.gc, dc.sel[ColBG]);
	XFillRectangle(dpy, win, dc.gc, 0, 0, lh, th);
	if(nitems != 0) {
		height = VSEND * (th - 2) / nitems > 0 ? VSEND * (th - 2) / nitems : 1;
		XFillRectangle(dpy, win, dc.gc, 1, vscroll * (th - 2) / nitems, lh - 2, height);
	}
	else
		XFillRectangle(dpy, win, dc.gc, 1, 1, lh - 2, th - 2);

	drawout();
	XFlush(dpy);
}

void
drawout(void) {
	if(intxt != outtxt)
		return;
	XSetForeground(dpy, dc.gc, dc.sel[ColBG]);
	XFillRectangle(dpy, win, dc.gc, 0, th, ww, 1);
	XSetForeground(dpy, dc.gc, dc.norm[ColBG]);
	XFillRectangle(dpy, outwin, dc.gc, 0, 0, ww, lh);
	dc.h = lh;
	dc.w = dc.font.height / 2 + textnw(outtxt, strlen(outtxt));
	dc.x = dc.w < ww ? 0 : ww - dc.w;
	dc.y = 0;
	dc.win = outwin;
	drawline(outtxt[0] ? outtxt : NULL, dc.norm, dc.sel);
	XSetForeground(dpy, dc.gc, dc.sel[ColFG]);
	XFillRectangle(dpy, outwin, dc.gc, dc.font.height / 2 + textnw(outtxt, strlen(outtxt)), 0, lh / 2, lh);
}

void
drawtext(const char *text, unsigned int l, unsigned int xoffset) {
	int h, y, x;

	h = dc.font.ascent + dc.font.descent;
	y = dc.y + (dc.h / 2) - (h / 2) + dc.font.ascent;
	x = dc.x + (h / 2) + xoffset;
	if(dc.font.set)
		XmbDrawString(dpy, dc.win, dc.font.set, dc.gc, x, y, text, l);
	else
		XDrawString(dpy, dc.win, dc.gc, x, y,  text, l);
}

void
eprint(const char *errstr, ...) {
	va_list ap;

	va_start(ap, errstr);
	vfprintf(stderr, errstr, ap);
	va_end(ap);
	exit(EXIT_FAILURE);
}

unsigned long
getcolor(const char *colstr) {
	Colormap cmap = DefaultColormap(dpy, screen);
	XColor color;

	if(!XAllocNamedColor(dpy, cmap, colstr, &color, &color))
		eprint("error, cannot allocate color '%s'\n", colstr);
	return color.pixel;
}

Item*
getitem(int l) {
	int i;
	Item *it;

	it = first;
	for(i = 0; i < l && it; i++)
		it = it->next;
	return it;
}

static unsigned char *
getsel(unsigned long offset, unsigned long *len, unsigned long *remain) {
	Atom utf8_string;
	Atom xa_clip_string;
	XEvent ev;
	Atom typeret;
	int format;
	unsigned char *data;
	unsigned char *result = NULL;

	utf8_string = XInternAtom(dpy, "UTF8_STRING", False);
	xa_clip_string = XInternAtom(dpy, "_SSELP_STRING", False);
	XConvertSelection(dpy, XA_PRIMARY, utf8_string, xa_clip_string,
			win, CurrentTime);
	XFlush(dpy);
	XNextEvent(dpy, &ev);
	if(ev.type == SelectionNotify && ev.xselection.property != None) {
		XGetWindowProperty(dpy, win, ev.xselection.property, offset, 4096L, False,
				AnyPropertyType, &typeret, &format, len, remain, &data);
		if(*len) {
			result = malloc(sizeof(unsigned char) * *len);
			memcpy(result, data, *len);
		}
		XDeleteProperty(dpy, win, ev.xselection.property);
	}
	return result;
}

void
initfont(const char *fontstr) {
	char *def, **missing;
	int i, n;

	if(!fontstr || fontstr[0] == '\0')
		eprint("error, cannot load font: '%s'\n", fontstr);
	missing = NULL;
	dc.font.set = XCreateFontSet(dpy, fontstr, &missing, &n, &def);
	if(missing)
		XFreeStringList(missing);
	if(dc.font.set) {
		XFontSetExtents *font_extents;
		XFontStruct **xfonts;
		char **font_names;
		dc.font.ascent = dc.font.descent = 0;
		font_extents = XExtentsOfFontSet(dc.font.set);
		n = XFontsOfFontSet(dc.font.set, &xfonts, &font_names);
		for(i = 0, dc.font.ascent = 0, dc.font.descent = 0; i < n; i++) {
			if(dc.font.ascent < (*xfonts)->ascent)
				dc.font.ascent = (*xfonts)->ascent;
			if(dc.font.descent < (*xfonts)->descent)
				dc.font.descent = (*xfonts)->descent;
			xfonts++;
		}
	}
	else {
		if(!(dc.font.xfont = XLoadQueryFont(dpy, fontstr))
		&& !(dc.font.xfont = XLoadQueryFont(dpy, "fixed")))
			eprint("error, cannot load font: '%s'\n", fontstr);
		dc.font.ascent = dc.font.xfont->ascent;
		dc.font.descent = dc.font.xfont->descent;
	}
	dc.font.height = dc.font.ascent + dc.font.descent;
}

void
kpress(XKeyEvent * e) {
	char buf[32];
	int i, l, num;
	unsigned int len;
	KeySym ksym;

	l = e->y / lh;
	len = strlen(intxt);
	buf[0] = 0;
	num = XLookupString(e, buf, sizeof buf, &ksym, 0);
	if(IsKeypadKey(ksym)) {
		if(ksym == XK_KP_Enter)
			ksym = XK_Return;
		else if(ksym >= XK_KP_0 && ksym <= XK_KP_9)
			ksym = (ksym - XK_KP_0) + XK_0;
	}
	if(ksym == XK_Insert) {
		intxt = outtxt;
		configwin(ww, wh);
		return;
	}
	if(IsFunctionKey(ksym) || IsKeypadKey(ksym)
	   || IsMiscFunctionKey(ksym) || IsPFKey(ksym)
	   || IsPrivateKeypadKey(ksym))
		return;
	if(e->state & ControlMask) {
		switch (ksym) {
		default:	
			return;
		case XK_bracketleft:
			ksym = XK_Escape;
			break;
		case XK_h:
		case XK_H:
			ksym = XK_BackSpace;
			break;
		case XK_R:
		case XK_r:
			nextsel->group = Red;
		case XK_i:
		case XK_I:
			ksym = XK_Tab;
			break;
		case XK_j:
		case XK_J:
			ksym = XK_Return;
			break;
		case XK_l:
		case XK_L:
			clearlist();
			break;
		case XK_u:
		case XK_U:
			intxt[0] = 0;
			/*updatetxt();*/
			return;
		case XK_v:
		case XK_V:
			/*pastesel();*/
			return;
		case XK_w:
		case XK_W:
			if(len) {
				i = len - 1;
				while(i >= 0 && intxt[i] == ' ')
					intxt[i--] = 0;
				while(i >= 0 && intxt[i] != ' ')
					intxt[i--] = 0;
				/*updatetxt();*/
			}
			return;
		}
	}
	
	switch(ksym) {
	default:
		if(num && !iscntrl((int) buf[0])) {
			buf[num] = 0;
			if(len > 0)
				strncat(intxt, buf, sizeof intxt);
			else
				strncpy(intxt, buf, sizeof intxt);
			drawout();
		}
		break;
	case XK_BackSpace:
		if(len) {
			intxt[--len] = 0;
			drawout();
		}
		break;
	case XK_End:
		scroll(hscroll, nitems);
		break;
	case XK_Down:
		pointerdown(e->x, e->y);
		if(nextsel->down){
			nextsel = nextsel->down;
		}
		drawlist();
		break;
	case XK_Home:
		scroll(hscroll, 0);
		break;
	case XK_Left:
		scroll(hscroll - 1, vscroll);
		break;
	case XK_Next:
		scroll(hscroll, vscroll + wh / lh - 1);
		break;
	case XK_Prior:
		scroll(hscroll, vscroll + 1 - wh / lh);
		break;
	case XK_Return:
		/*sendout(outtxt);
		outtxt[0] = 0;*/
		sel = nextsel;
		sendout(sel->text);
		drawlist();
		break;
	case XK_Right:
		scroll(hscroll + 1, vscroll);
		break;
	case XK_Up:
		pointerup(e->x, e->y);
		if(nextsel->up){
			nextsel = nextsel->up;
		}
		drawlist();
		break;
	}
	
}

void
match(void) {
	int w;
	Item *i, *itemend;

	item = itemend = NULL;
	maxw = 0;
	nitems = 0;
	for(i = allitems; i; i = i->next)
		/*if(fstrstr(i->text, searchtxt)) {*/
		if(i != NULL){
			if(!itemend)
				item = i;
			else
				itemend->down = i;
			i->down = NULL;
			i->up = itemend;
			itemend = i;
			w = textw(&i->text[common]);
			maxw = (w > maxw) ? w : maxw;
			nitems++;
		}
	if(i == first || !first) {
		first = item;
		hscroll = 0;
		vscroll = 0;
	}
}

void
pointerdown(int x, int y) {
	int nx, ny;

	nx = (x < 0 || x > tw) ? 1 : x;
	ny= (y < 0 || y > th) ? 1 : y + lh;
	if(ny > th) {
		scroll(hscroll, vscroll + 1);
		ny = y;
	}
	/*XWarpPointer(dpy, None, txtwin, 0, 0, 0, 0, nx, ny);*/
}

void
pointerup(int x, int y) {
	int nx, ny;

	nx = (x < 0 || x > tw) ? 1 : x;
	ny= (y < 0 || y > wh) ? 1 : y - lh;
	if(ny < 0) {
		scroll(hscroll, vscroll - 1);
		ny = y;
	}
	XWarpPointer(dpy, None, txtwin, 0, 0, 0, 0, nx, ny);
}

void
procev(XEvent ev) {
	int hs = hscroll, vs = vscroll;

	/* main event loop */
	switch (ev.type) {
	default:	/* ignore all crap */
		break;
	case ButtonPress:
		bpress(&ev.xbutton);
		break;
	case ButtonRelease:
		if(ev.xbutton.button == Button1)
			scrolling = False;
		if(!chording && ev.xbutton.button == Button3) {
			if(ev.xbutton.window == win)
				scrollto(sel);
		}
		break;
	case ClientMessage:		/* window closed */
		if(ev.xclient.data.l[0] == wmdeletemsg) {
			doing = False;
			running = False;
		}
		break;
	case ConfigureNotify:
		if(ev.xconfigure.window == win)
			configwin(ev.xconfigure.width, ev.xconfigure.height);
		break;
	case Expose:
		if(ev.xexpose.count == 0)
			drawlist();
		break;
	case KeyPress:
		if(lastview != last) {
			lastview = last;
			drawlist();
		}
		kpress(&ev.xkey);
		break;
	case MotionNotify:
		if(lastview != last) {
			lastview = last;
			drawlist();
		}
		if(scrolling) {
			if(maxw > tw && ev.xmotion.x > lh)
				hs = (ev.xmotion.x - lh) * (maxw + lh - tw) / (tw -lh) / lh;
			else
				vs = (ev.xmotion.y - 1) * nitems / (th - 2);
			scroll(hs, vs);
		}
		break;
	}
}

void
readstdin(void) {
	char *p2, buf[1024];
	unsigned int len = 0;

	fcntl(STDIN_FILENO, F_SETFL, O_NONBLOCK);
	while(fgets(buf, sizeof buf, stdin) > 0) {
		len = strlen(buf);
		if (buf[len - 1] == '\n')
			buf[len - 1] = 0;
		else
			len = 0;
		if(p != NULL) {
			p2 = malloc(strlen(buf) + strlen(p));
			strncpy(p2, p, strlen(p));
			strncpy(p2, buf, strlen(buf));
		}
		if(!(p = strdup(buf)))
			eprint("fatal: could not strdup() %u bytes\n", strlen(buf));
		if(len > 0) {
			additem(p);
			drawlist();
			p = NULL;
		}
	}
//	fcntl(STDIN_FILENO, F_SETFL, !O_NONBLOCK);
	if(running && len == 0)
		readin = False;
}

void
run(void) {
	fd_set rd;
	int xfd;
	XEvent ev;

	/* main event loop, also reads from stdin */
	xfd = ConnectionNumber(dpy);
	FD_ZERO(&rd);
	FD_SET(xfd, &rd);
	setup();
	if(follow){
		scroll(hscroll, nitems);
	}
	drawlist();
	while(running) {
		if(readin)
			FD_SET(STDIN_FILENO, &rd);
		/*if(chlddied) {
			if(sel) {
				if(playdelete)
					delitem(sel);
				else
					sel->played = played;
			}
			doing = False;
			XStoreName(dpy, win, wtitle);
			sel = NULL;
			drawlist();
			chlddied = False;
		}*/
		if(select(xfd + 1, &rd, NULL, NULL, NULL) == -1) {
			if(errno == EINTR)
				continue;
			fprintf(stderr, "select failed\n");
			running = False;
			return;
		}
		if(FD_ISSET(STDIN_FILENO, &rd)) {
			readstdin();
			/*setcommon();*/
			match();
			if(follow && nextpage != first)
				scroll(hscroll, nitems);
			drawlist();
		}
		while(XPending(dpy)) {
			XNextEvent(dpy, &ev);
			procev(ev);
		}
		FD_ZERO(&rd);
		FD_SET(xfd, &rd);
	}
}

void
scroll(int nhs, int nvs) {
	int i, hs, vs;

	hs = nhs > (maxw + lh - tw) / lh ? (maxw + lh - tw) / lh : nhs;
	hs = hs < 0 ? 0 : hs;
	vs = (nvs > (nitems - ((multicol && maxw > 0 && tw > maxw) ? tw / maxw : 1) * th / lh)) ? (nitems - ((multicol && maxw > 0 && tw > maxw) ? tw / maxw : 1) * th / lh) : nvs;
	vs = vs < 0 ? 0 : vs;
	if(!first)
		first = item;
	if(hs != hscroll || vs != vscroll) {
		hscroll = hs;
		for(i = 0; first && i < abs(vs - vscroll); i++)
			first = (vs - vscroll > 0) ? first->down : first->up;
		vscroll = vs;
		drawlist();
	}
}

void
scrollto(Item* it) {
	int vs = 0;
	Item *f;

	if(!item || !it)
		return;
	for(f = item; f && f != it; f = f->down)
		vs++;
	if(it == f)
		scroll(hscroll, vs);
}

/*sends a string to stdout and clears the out buffer*/
void
sendout(const char *output){
	/*char *p;

	if(!(p = strdup(outtxt))){
		eprint("fatal: could not strdup() %u bytes\n", strlen(outtxt));
	} else {
		additem(p);
		nextsel = last;
	}*/
	fprintf(stdout, "%s\n", output);
	fflush(stdout);
}


/* sets up colours and sizes and draws windows*/
void
setup(void) {
	int i, j;
	XClassHint classhint;
	XModifierKeymap *modmap;
	XSetWindowAttributes wa;

	/* init modifier map */
	modmap = XGetModifierMapping(dpy);
	for(i = 0; i < 8; i++)
		for(j = 0; j < modmap->max_keypermod; j++) {
			if(modmap->modifiermap[i * modmap->max_keypermod + j]
			== XKeysymToKeycode(dpy, XK_Num_Lock))
				numlockmask = (1 << i);
		}
	XFreeModifiermap(modmap);

	/* style */
	dc.norm[ColBG] = getcolor(normbgcolor);
	dc.norm[ColFG] = getcolor(normfgcolor);
	dc.filter[ColBG] = getcolor(filterbgcolor);
	dc.filter[ColFG] = getcolor(filterfgcolor);
	dc.sel[ColBG] = getcolor(selbgcolor);
	dc.sel[ColFG] = getcolor(selfgcolor);
	if(normaltbgcolor)
		dc.other[ColBG] = getcolor(normaltbgcolor);
	dc.other[ColFG] = getcolor(urgentfgcolor);
	initfont(font);

	/* window */
	wa.override_redirect = over;
	wa.background_pixmap = ParentRelative;
	wa.event_mask = ButtonMotionMask | PointerMotionMask | ButtonPressMask |
	ButtonReleaseMask | ExposureMask | KeyPressMask | StructureNotifyMask;
	classhint.res_name = classhint.res_class = (char *)wclass;

	/* window geometry */
	match();
	lh = dc.font.height + 2;
	ww = (ww == 0) ? lh + maxw : ww;
	wh = (wh == 0) ? (lh * nitems > DisplayHeight(dpy, screen) ? DisplayHeight(dpy, screen) : lh * nitems) : wh;
	wh = (wh == 0) ? lh : wh;	// TODO: FIX THIS!
	ww = (ww > lh) ? ww : 2 * lh;

	win = XCreateWindow(dpy, root, wx, wy, ww, wh, 0,
			DefaultDepth(dpy, screen), CopyFromParent,
			DefaultVisual(dpy, screen),
			CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
	XSetClassHint(dpy, win, &classhint);

	/* text window */
	txtwin =  XCreateWindow(dpy, win, lh, 0, ww - lh, wh > lh ? wh - lh : lh, 0,
			DefaultDepth(dpy, screen), CopyFromParent,
			DefaultVisual(dpy, screen),
			CWBackPixmap | CWEventMask, &wa);

	/* out window */
	outwin =  XCreateWindow(dpy, win, 0, wh > lh ? wh - lh : 0, ww, lh, 0,
				DefaultDepth(dpy, screen), CopyFromParent,
				DefaultVisual(dpy, screen),
				CWBackPixmap | CWEventMask, &wa);

	/* catch delete window events */
	wmdeletemsg = XInternAtom(dpy, "WM_DELETE_WINDOW", False);
	(void) XSetWMProtocols(dpy, win, &wmdeletemsg, 1);

	dc.gc = XCreateGC(dpy, win, 0, 0);
	XSetLineAttributes(dpy, dc.gc, 1, LineSolid, CapButt, JoinMiter);
	if(!dc.font.set)
		XSetFont(dpy, dc.gc, dc.font.xfont->fid);
	intxt = outtxt;
	outtxt[0] = searchtxt[0] = 0;
	XMapRaised(dpy, win);
	XMapRaised(dpy, txtwin);
	XMapRaised(dpy, outwin);
	XSync(dpy, False);
}

/* gets the width of a string in the current font*/
int
textnw(const char *text, unsigned int len) {
	XRectangle r;

	if(dc.font.set) {
		XmbTextExtents(dc.font.set, text, len, NULL, &r);
		return r.width;
	}
	return XTextWidth(dc.font.xfont, text, len);
}

/* gets the width of a string in the current font*/
int
textw(const char *text) {
	int i, i0, len, x;

	if(!text)
		return 0;
	len = strlen(text);
	for(i = i0 = x = 0; i < len; i++)
		if(text[i] == '\t') {
			x += (textnw(text + i0, i - i0) / TABWIDTH + 1) * TABWIDTH;
			i0 = i + 1;
		}
	x += textnw(text + i0, i - i0);
	return x + dc.font.height;
}


int
main(int argc, char *argv[]) {
	unsigned int i;
	follow = True;
	urgent = True;
	
	if(!setlocale(LC_CTYPE, "") || !XSupportsLocale())
		fprintf(stderr, "warning: no locale support\n");
	if(!(dpy = XOpenDisplay(0)))
		eprint("dio: cannot open display\n");
	screen = DefaultScreen(dpy);
	root = RootWindow(dpy, screen);
	readstdin();
	running = True;
	char *string = malloc(10);
	strcpy(string,"pizza");
	char *string2 = malloc(10);
	strcpy(string2,"pizza2");
	char *string3 = malloc(10);
	strcpy(string3,"pizza3");
	additem(string);
	additem(string2);
	additem(string3);
	nextsel = allitems;
	run();

	cleanup();
	XCloseDisplay(dpy);
	return 0;
}
