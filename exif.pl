#!/usr/bin/perl -wT
#
# exif - print EXIF information that may be in a file
#
# @(#) $Revision$
# @(#) $Id$
# @(#) $Source$
#
# Copyright (c) 2005 by Landon Curt Noll.  All Rights Reserved.
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

# requirements
#
use strict;
use bytes;
use vars qw($opt_n $opt_m $opt_g $opt_u $opt_b $opt_p
	    $opt_d $opt_e $opt_f $opt_h $opt_v);
use Getopt::Long;
use Image::ExifTool qw(ImageInfo);

# version - RCS style *and* usable by MakeMaker
#
my $VERSION = substr q$Revision: 1.1 $, 10;
$VERSION =~ s/\s+$//;

# my vars
#
my %expand;	# $expand{$i} is either $i or %xx hex expansion

# usage and help
#
my $usage =
    "$0 [-n][-m][-g] [-u][-b][-p] [-d][-e] [-f fmt] [-h][-v lvl] imgfile";
my $help = qq{$usage

	-n	output EXIF tag name before value (default: don't)
	-m	output EXIF tag name instead of value (default: don't)
	-g	output EXIF tag group before EXIF tag value (default: don't)

	-u	output unknown EXIF tags (default: don't)
	-b	output binary values (implies -p) (default: print binary len)
	-p	disable conversion (default: printable data, shorter lists)

	-d	output duplicate EXIF tag names (default: don't)
	-e	output ExitTool tag names (defailt: output canonical names)

	-f fmt	format for date related strings (default: \%F \%T)
		\%a short weekday name	\%A full weekday name
		\%b short month name	\%B full month name
		\%c default format	\%C 2 digit century
		\%d day [01-31]		\%D \%m/\%d/\%y
		\%e dat [ 1-31]		\%E locale modifier for cCxXyY
					\%F \%Y-\%m-\%d (ISO 8601)
		\%g XXX			\%G XXX
		\%h == \%b		\%H hour [00-23]
					\%I hour [01-12]
		\%j day of year [001-366]
		\%k hour [0-23]
		\%l hour [ 1-12]
		\%m month [01-12]	\%M minute [00-59]
		\%n \\n
					\%O modifier for deHImMSuUVwWy
		\%p AM or PM		\%P am or pm
		\%r \%I:\%M:\%S \%p\t	\%R \%H:\%M
		\%s seconds since Epoch	\%S seconds [00-61]
		\%t \\t			\%T \%H:\%M:\%S
		\%u day of week [1-7]	\%U week num [00-53] 1st Sun week 01
					\%V week num [01-53] ISO 8601:1988
		\%w day of week [0-6]	\%W week num [00-53] 1st Mon week 01
		\%x locate date		\%X locate time
		\%y year [00-99]	\%Y 4 digit year
		\%z UTC timezone offset	\%Z time zone or name or abbreviation
		\%+ date(1) format	\%\% \%

	-h	print this help message
	-v 	verbose / debug level

	exit 0	all is OK
	exit 1	problems were encountered while extracting EXIF info
	exit 2	fatal error during EXIF processing
	exit >2 some other fatal error
};
my %optctl = (
    "n" => \$opt_n,
    "m" => \$opt_m,
    "g" => \$opt_g,

    "u" => \$opt_u,
    "b" => \$opt_b,
    "p" => \$opt_p,

    "d" => \$opt_d,
    "e" => \$opt_e,

    "f=s" => \$opt_f,

    "h" => \$opt_h,
    "v=i" => \$opt_v,
);


# function prototypes
#
sub canonical_str($);
sub error($$);


# setup
#
MAIN: {
    my $imgname;	# image filename containing EXIF data
    my $exiftool;	# Image::ExifTool object
    my %exifoptions;	# EXIF extraction options (see Image::ExifTool doc)
    my $info;		# exiftool extracted EXIF information
    my @tag_list;	# list of extracted EXIF field tag names
    my %canon_tag;	# map of canonical EFIF tag names to extracted names
    my $tag;		# an EXIF extracted field tag name
    my $canon;		# canonical value of tag name
    my $value;		# the value an EXIF extracted tag field
    my $description;	# description of an EXIF field

    # setup
    #
    select(STDOUT);
    $| = 1;

    # set the defaults
    #
    $opt_v = 0;

    # parse args
    #
    if (!GetOptions(%optctl)) {
	error(3, "invalid command line\nusage: $help");
    }
    if (defined $opt_h) {
	error(0, "usage: $help");
    }
    if (! defined $ARGV[0]) {
	error(4, "missing filename\nusage: $help");
    }
    $imgname = $ARGV[0];
    if (! -r $imgname) {
	error(5, "cannot read: $imgname");
    }
    # -b determines if we extract large binary EXIF tags and implies -p
    $exifoptions{Binary} = (defined $opt_b ? 1 : 0);
    $opt_p = 1 if defined $opt_b;
    # -p disables print conversion and list shortening
    $exifoptions{PrintConv} = (defined $opt_p ? 0 : 1);
    # -u determines if we extract unknown EXIF tags
    $exifoptions{Unknown} = (defined $opt_u ? (defined $opt_b ? 2 : 1) : 0);
    # -f fmt changes the date format
    $exifoptions{DateFormat} = (defined $opt_f ? $opt_f : '%F %T');
    # -d allows for the output of duplicate field tags
    $exifoptions{Duplicates} = (defined $opt_d ? 1 : 0);

    # create a new Image::ExifTool object
    #
    $exiftool = new Image::ExifTool;

    # set the ExifTool options
    #
    $exiftool->Options(%exifoptions);

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($imgname);
    if (! defined $info) {
	error(6, "failed to extract EXIF data from $imgname");
    }
    if (defined $$info{Error}) {
	# NOTE: exit(2) on ExifTool errors
	error(2, "FATAL: $$info{Error}");
    }

    # get list of tags in the order that tags were found in the file
    #
    @tag_list = $exiftool->GetFoundTags('File');
    if (scalar @tag_list <= 0) {
	error(6, "no EXIF tags found in $imgname");
    }

    # Determine the canonical EXIF tag name of each EXIF tag found
    #
    # Because of a bug(?) / mis-feature in Image::ExifTool (at least as of
    # version 5.05) a tag such as Compression might show up 3 times as:
    #
    #		Compression
    #		Compression (1)
    #		Compression (2)
    #
    # In each case the canonical EXIF tag name should be just Compression.
    #
    foreach $tag (@tag_list) {
	($canon_tag{$tag} = $tag) =~ s/\s+(\(\d+\))?\s*$//;
    }

    # dump all EXIF information
    #
    print "EXIF data for $imgname\n" if $opt_v >= 2;
    foreach $tag (@tag_list) {

    	# determine canonical name of this tag
	#
	$canon = $canon_tag{$tag};

	# binary EXIF field firewall
	#
	$value = $$info{$tag};
	if (ref $value eq 'SCALAR') {
	    if (defined $opt_b) {
		$value = $$value;
	    } else {
		if ($$value =~ /^Binary data/) {
		    $value = "($$value)";
		} else {
		    $value = "(Binary data " . length($$value) . " bytes)";
		}
	    }
	} elsif (ref $value eq 'ARRAY') {
	    if (defined $opt_b) {
		$value = $$value;
	    } else {
		$value = "(List data " . length($$value) . " bytes)";
	    }
	}

	# output the canonical EXIF field tag name if -n
	#
	if (defined $opt_n || defined $opt_m) {
	    printf("%-28s", (defined $opt_e ? $tag : $canon));
	}

	# output the EXIF field group if -g
	#
	if (defined $opt_g) {
	    printf("%-16s", $exiftool->GetGroup($tag));
	}

	# output EXIF tag value
	#
	if (defined $opt_m) {
	    # -m disables printing of EXIT tag values
	    print "\n";
	} elsif (defined $opt_p) {
	    # -p (or -b which implies -p) prints values raw
	    print "$value\n";
	} else {
	    # ensure that the value we print is printable
	    #
	    # NOTE: In some cases, unknown EXIF tags contain non-printable
	    #	    characters even though the PrintConv is set.
	    #
	    print canonical_str($value), "\n";
	}

	# output field description if -v is high enough
	#
	if ($opt_v > 0) {
	    $description = $exiftool->GetDescription($tag);
	    if (defined $description) {
		print "    $description\n";
	    } else {
		print "    Unknown EXIF field: $tag\n";
	    }
	}
    }

    # All done! -- Jessica Noll, Age 2
    #
    if (defined $$info{Warning}) {
	# NOTE: exit(1) on ExifTool warnings after processing
	error(1, "warning: $$info{Warning}");
    }
    exit(0);
}


# canonical_str - canonicalize the string
#
# given:
#	$str	the strign to canonicalize
#
# returns:
#	$str with % as %25, [^\w\s] as %xx
#
sub canonical_str($)
{
    my ($str) = @_;	# get arg
    my @chars;		# string chars as an array
    my $char;		# current char from chars array

    # strip leading and trailing blanks
    #
    $str =~ s/^\s+//;
    $str =~ s/\s+$//;

    # convert %'s to %25's
    #
    $str =~ s/%/%25/g;

    # if we have chars outside of [\w\s], convert then to hex as well
    #
    if ($str =~ /[^[:graph:] \t]/) {

    	# setup %expand once
	#
	# NOTE: We already did the % ==> %25 so our expand
	#	hash must have $expand{'%'} == '%'.
	#
	if (! defined $expand{'%'}) {
	    my $i;
	    for ($i = 0; $i < 256; ++$i) {
	    	if (chr($i) =~ /[^[:graph:] \t]/) {
		    $expand{chr($i)} = "%" . sprintf("%02x", $i);
		} else {
		    $expand{chr($i)} = chr($i);
		}
	    }
	}

	# convert string character by character
	#
	@chars = split(//, $str);
	$str = "";
	foreach $char (@chars) {
	    $str .= $expand{$char};
	}
    }
    return $str;
}


# error - report an error and exit
#
# given:
#       $exitval	exit code value
#       $msg		the message to print
#
sub error($$)
{
    my ($exitval, $msg) = @_;    # get args

    # parse args
    #
    if (!defined $exitval) {
	$exitval = 254;
    }
    if (!defined $msg) {
	$msg = "<<< no message supplied >>>";
    }
    if ($exitval =~ /\D/) {
	$msg .= "<<< non-numeric exit code: $exitval >>>";
	$exitval = 253;
    }

    # issue the error message
    #
    print STDERR "$0: $msg\n";

    # issue an error message
    #
    exit($exitval);
}
