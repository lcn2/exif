#!/usr/bin/make
#
# exif - print EXIF information that may be in a file
#
# @(#) $Revision: 1.2 $
# @(#) $Id: Makefile,v 1.2 2005/07/13 04:23:00 chongo Exp root $
# @(#) $Source: /usr/local/src/cmd/exif/RCS/Makefile,v $
#
# Copyright (c) 2001 by Landon Curt Noll.  All Rights Reserved.
#
# Permission to use, copy, modify, and distribute this software and
# its documentation for any purpose and without fee is hereby granted,
# provided that the above copyright, this permission notice and text
# this comment, and the disclaimer below appear in all of the following:
#
#       supporting documentation
#       source copies
#       source works derived from this source
#       binaries derived from this source or from derived source
#
# LANDON CURT NOLL DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE,
# INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO
# EVENT SHALL LANDON CURT NOLL BE LIABLE FOR ANY SPECIAL, INDIRECT OR
# CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF
# USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
#
# chongo <was here> /\oo/\
#
# Share and enjoy!

SHELL=/bin/sh
INSTALL= install
BINMODE=0555

DESTBIN=/usr/local/bin

TARGETS= exif exifrename exifforceorder

all: ${TARGETS}

exif: exif.pl
	-rm -f $@
	cp $@.pl $@
	chmod +x $@

exifrename: exifrename.pl
	-rm -f $@
	cp $@.pl $@
	chmod +x $@

exifforceorder: exifforceorder.sh
	-rm -f $@
	cp $@.sh $@
	chmod +x $@

install: all
	${INSTALL} -c -m ${BINMODE} ${TARGETS} ${DESTBIN}

clean:

clobber: clean
	-rm -f ${TARGETS}
