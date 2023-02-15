#!/bin/bash -
#
# exifforceorder - force DateTimeOriginal order in a directory for iPad
#
# The iPod dislays images in a directory by order of the DateTimeOriginal
# value.  This tool will change the DateTimeOriginal values so that they
# will match the file order of images in a given directory.
#
# If the next file (in filename order) has a DateTimeOriginal that is
# less than the previous file we will change its DateTimeOriginal to
# be 1 second later.
#
# When we advance the DateTimeOriginal 1 second later, we need simply
# add 1 to the second.  This is because a time such as "0:46:60" is
# converted into "0:47:00" and "0:46:61" into "0:47:01".
#
# @(#) $Revision: 1.1 $
# @(#) $Id: exifforceorder.sh,v 1.1 2013/03/03 19:39:33 root Exp $
# @(#) $Source: /usr/local/src/bin/exif/RCS/exifforceorder.sh,v $
#
# Copyright (c) 2013 by Landon Curt Noll.  All Rights Reserved.
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
# chongo (Landon Curt Noll, http://www.isthe.com/chongo/index.html) /\oo/\
#
# Share and enjoy! :-)

# parse args
#
USAGE="usage: $0 [-n] [-v] dir

    -n	    do nothing (def: do)
    -v	    verbose output (def: not verbose)"
N_FLAG=
V_FLAG=
args=$(getopt nv $*)
if [ $? != 0 ]; then
    echo "$0: unknown or invalid -flag" 1>&2
    echo $USAGE 1>&2
    exit 1
fi
set -- $args
for i in $*; do
    case "$i" in
    -o) O_FLAG="$2"; ;;
    -d) D_FLAG="true"; ;;
    -f) F_FLAG="true" ;;
    -n) N_FLAG="true" ;;
    -v) V_FLAG="true" ;;
    --) shift; break ;;
    esac
    shift
done
if [ $# -lt 1 ]; then
    echo "$0: must have at least one arg" 1>&2
    echo $USAGE 1>&2
    exit 2
fi
IMG_DIR="$@"
if [[ ! -d "$IMG_DIR" ]]; then
    echo "$0: ERROR: not a directory: $IMG_DIR" 1>&2
    exit 3
fi

# process each image
#
#	cr2 raw tif tiff jpg jpeg png gif psd eps
#
cd "$IMG_DIR"
PREV_DateTimeOriginal=
PREV_TIMESTAMP=
export PREV_DateTimeOriginal PREV_TIMESTAMP
DateTimeOriginal=
TIMESTAMP=
export DateTimeOriginal TIMESTAMP
NEXT_DateTimeOriginal=
NEXT_TIMESTAMP=
export NEXT_DateTimeOriginal NEXT_TIMESTAMP
find . \( -iname '*.cr2' -o \
	  -iname '*.raw' -o \
	  -iname '*.tiff' -o \
	  -iname '*.jpg' -o \
	  -iname '*.jpeg' -o \
	  -iname '*.png' -o \
	  -iname '*.gif' -o \
	  -iname '*.psd' -o \
	  -iname '*.eps' \) -mindepth 1 -maxdepth 1 \
	  -print | while read file; do

    # if this is our first file, just note its DateTimeOriginal
    #
    if [[ -z "$PREV_DateTimeOriginal" ]]; then
	PREV_DateTimeOriginal=$(exif -t DateTimeOriginal "$file")
	PREV_TIMESTAMP=$(echo "$PREV_DateTimeOriginal" | sed -e 's/[ :-]//g')
	if [[ -n "$V_FLAG" ]]; then
	    echo "1st file: $file DateTimeOriginal: $PREV_DateTimeOriginal timestamp: $PREV_TIMESTAMP" 1>&2
	fi
	continue
    else
	DateTimeOriginal=$(exif -t DateTimeOriginal "$file")
	TIMESTAMP=$(echo "$DateTimeOriginal" | sed -e 's/[ :-]//g')
	if [[ -n "$V_FLAG" ]]; then
	    echo "nxt file: $file DateTimeOriginal: $DateTimeOriginal timestamp: $TIMESTAMP" 1>&2
	fi
    fi

    # if this timestamp is later than the previous, remember it and move on
    #
    if [[ "$PREV_TIMESTAMP" -lt "$TIMESTAMP" ]]; then
	if [[ -n "$V_FLAG" ]]; then
	    echo "prev DateTimeOriginal: $PREV_DateTimeOriginal < this DateTimeOriginal: $DateTimeOriginal" 1>&2
	    echo "prev PREV_TIMESTAMP: $PREV_TIMESTAMP < this TIMESTAMP: $TIMESTAMP" 1>&2
	fi
	PREV_DateTimeOriginal="$DateTimeOriginal"
	PREV_TIMESTAMP="$TIMESTAMP"
	if [[ -n "$V_FLAG" ]]; then
	    echo "" 1>&2
	fi
	continue
    fi
    if [[ -n "$V_FLAG" ]]; then
	echo "prev DateTimeOriginal: $PREV_DateTimeOriginal >= this DateTimeOriginal: $DateTimeOriginal" 1>&2
	echo "prev PREV_TIMESTAMP: $PREV_TIMESTAMP >= this TIMESTAMP: $TIMESTAMP" 1>&2
    fi

    # form a DateTimeOriginal that is one second later
    #
    ((NEXT_TIMESTAMP=PREV_TIMESTAMP+1))
    NEXT_DateTimeOriginal=$(echo "$NEXT_TIMESTAMP" | sed -e 's/\(....\)\(..\)\(..\)\(..\)\(..\)\(..\)/\1-\2-\3 \4:\5:\6/')
    if [[ -n "$V_FLAG" ]]; then
	echo "next DateTimeOriginal: $NEXT_DateTimeOriginal next timestamp: $NEXT_TIMESTAMP" 1>&2
    fi

    # change the DateTimeOriginal of the current file
    #
    if [[ -n "$V_FLAG" ]]; then
	echo "exiftool -quiet -overwrite_original -DateTimeOriginal='"$NEXT_DateTimeOriginal"' $file" 1>&2
    fi
    if [[ -z "$N_FLAG" ]]; then
	exiftool -quiet -overwrite_original -DateTimeOriginal="$NEXT_DateTimeOriginal" "$file"
	status="$?"
	if [[ "$status" -ne 0 ]]; then
	    echo "$0: Warning: exiftool exit code: $status" 1>&2
	fi
    fi

    # save the new DateTimeOriginal as the
    #
    PREV_DateTimeOriginal="$NEXT_DateTimeOriginal"
    PREV_TIMESTAMP="$NEXT_TIMESTAMP"
done

# All Done!! - Jessica Noll, Age 2
#
exit 0
