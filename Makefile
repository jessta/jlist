# dio - dynamic i/o
# See LICENSE file for copyright and license details.

include config.mk

SRC = dio.c
OBJ = ${SRC:.c=.o}

all: options dio

bin: all
	@echo installing executable files to ${DESTDIR}${PREFIX}/bin
	@chmod 755 bin/*
	@cp -f bin/* ${DESTDIR}${PREFIX}/bin

options:
	@echo dio build options:
	@echo "CFLAGS   = ${CFLAGS}"
	@echo "LDFLAGS  = ${LDFLAGS}"
	@echo "CC       = ${CC}"

.c.o:
	@echo CC $<
	@${CC} -c ${CFLAGS} $<

${OBJ}: config.h config.mk

config.h:
	@echo creating $@ from config.def.h
	@cp config.def.h $@

dio: ${OBJ}
	@echo CC -o $@
	@${CC} -g -o $@ ${OBJ} ${LDFLAGS}

clean:
	@echo cleaning
	@rm -f dio ${OBJ} dio-${VERSION}.tar.gz

dist: clean
	@echo creating dist tarball
	@mkdir -p dio-${VERSION}
	@cp -R LICENSE Makefile README config.mk dio.1 config.def.h bin ${SRC} dio-${VERSION}
	@tar -cf dio-${VERSION}.tar dio-${VERSION}
	@gzip dio-${VERSION}.tar
	@rm -rf dio-${VERSION}

install: all
	@echo installing executable files to ${DESTDIR}${PREFIX}/bin
	@mkdir -p ${DESTDIR}${PREFIX}/bin
	@cp -f dio ${DESTDIR}${PREFIX}/bin
	@chmod 755 ${DESTDIR}${PREFIX}/bin/dio
	@echo installing manual page to ${DESTDIR}${MANPREFIX}/man1
	@mkdir -p ${DESTDIR}${MANPREFIX}/man1
	@sed "s/VERSION/${VERSION}/g" < dio.1 > ${DESTDIR}${MANPREFIX}/man1/dio.1
	@chmod 644 ${DESTDIR}${MANPREFIX}/man1/dio.1

uninstall:
	@echo removing executable file from ${DESTDIR}${PREFIX}/bin
	@rm -f ${DESTDIR}${PREFIX}/bin/dio
	@echo removing manual page from ${DESTDIR}${MANPREFIX}/man1
	@rm -f ${DESTDIR}${MANPREFIX}/man1/dio.1

.PHONY: all bin options clean dio install uninstall
