#!/usr/bin/env make
#
# exif - print EXIF information that may be in a file
#
# Copyright (c) 2001,2023 by Landon Curt Noll.  All Rights Reserved.
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

SHELL= bash
INSTALL= install
BINMODE= 0555
RM= rm
CP= cp
CHMOD= chmod

DESTBIN= /usr/local/bin

TARGETS= exif exifrename exifforceorder

all: ${TARGETS}

exif: exif.pl
	${RM} -f $@
	${CP} $@.pl $@
	${CHMOD} +x $@

exifrename: exifrename.pl
	${RM} -f $@
	${CP} $@.pl $@
	${CHMOD} +x $@

exifforceorder: exifforceorder.sh
	${RM} -f $@
	${CP} $@.sh $@
	${CHMOD} +x $@

install: all
	${INSTALL} -c -m ${BINMODE} ${TARGETS} ${DESTBIN}

clean:

clobber: clean
	${RM} -f ${TARGETS}
