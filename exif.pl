#!/usr/bin/env perl -w
#
# exif - print EXIF information that may be in a file
#
# Copyright (c) 2005,2023 by Landon Curt Noll.  All Rights Reserved.
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
use vars qw($opt_n $opt_m $opt_g $opt_i $opt_u $opt_b $opt_p @opt_t
	    $opt_d $opt_e $opt_f $opt_h $opt_v);
use Getopt::Long;
use Image::ExifTool qw(ImageInfo);

# version - RCS style *and* usable by MakeMaker
#
my $VERSION = substr q$Revision: 1.8 $, 10;
$VERSION =~ s/\s+$//;

# my vars
#
my %expand;	# $expand{$i} is either $i or %xx hex expansion

# usage and help
#
my $usage =
    "$0 [-n][-m][-g][-i] [-u][-b][-p] [-d][-e] [-t tag] ...\n" .
    "\t\t[-f fmt] [-h][-v lvl] imgfile ...";
my $help = qq{$usage

	-n	output EXIF tag name before value (default: don't)
	-m	output EXIF tag name instead of value (default: don't)
	-g	output EXIF tag group before EXIF tag value (default: don't)
	-i	output imgfile filename at start of line (default: don't)

	-u	output unknown EXIF tags (default: don't)
	-b	output binary values (implies -p) (default: print binary len)
	-p	disable conversion (default: printable data, shorter lists)

	-d	output duplicate EXIF tag names (default: don't)
	-e	output ExitTool tag names (defailt: output canonical names)

	-t tag	only just EXIF tag (default: output any tag (see also -u))
		    (NOTE: multiple -t tags are allowed)

	-f fmt	format for date related strings (default: \%F \%T)
		\%a short weekday name	\%A full weekday name
		\%b short month name	\%B full month name
		\%c default format	\%C 2 digit century
		\%d day [01-31]		\%D \%m/\%d/\%y
		\%e dat [ 1-31]		\%E locale modifier for cCxXyY
					\%F \%Y-\%m-\%d (ISO 8601)
		\%g 2 digit year of \%V\t\%G 4 digit year of \%V
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

	imgfile ...	files to look for EXIF data

    NOTE:
	exit 0	all is OK
	exit 1	problems were encountered while extracting EXIF info
	exit 2	cannot open or read filename
	exit 3	fatal error during EXIF processing
	exit >3 some other fatal error
};
my %optctl = (
    "n" => \$opt_n,
    "m" => \$opt_m,
    "g" => \$opt_g,
    "i" => \$opt_i,

    "u" => \$opt_u,
    "b" => \$opt_b,
    "p" => \$opt_p,

    "d" => \$opt_d,
    "e" => \$opt_e,

    "t=s" => \@opt_t,

    "f=s" => \$opt_f,

    "h" => \$opt_h,
    "v=i" => \$opt_v,
);


# function prototypes
#
sub exif($$);
sub printable_str($);


# setup
#
MAIN: {
    my $filename;	# image filename containing EXIF data
    my $exiftool;	# Image::ExifTool object
    my %exifoptions;	# EXIF extraction options (see Image::ExifTool doc)
    my $exifcode;	# exif() return code, 0 ==> OK, >0 ==> error
    my $exitcode;	# what to exit with, 0 ==> all files OK, >0 ==> errors
    my $error_msg;	# fatal error message, or undef ==> no error

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
	print STDERR "$0: invalid command line\nusage:\n\t$help\n";
	exit(4);
    }
    if (defined $opt_h) {
	# just print help, no error
	print STDERR "$0: usage: $help\n";
	exit(0);
    }
    if (! defined $ARGV[0]) {
	print STDERR "$0: missing filename\nusage:\n\t$help\n";
	exit(5);
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

    # process each file
    #
    $exitcode = 0;
    while (defined($filename = shift @ARGV)) {
	($exifcode, $error_msg) = exif($exiftool, $filename);
	# report errors as they happen but don't exit
	if (defined $error_msg) {
	    if ($exifcode > 1) {
		print STDERR "$0: Error: $filename: $error_msg\n";
	    } else {
		print STDERR "$0: warning: $filename: $error_msg\n";
	    }
	}
	# track the highest exit code
	$exitcode = $exifcode if ($exifcode > $exitcode);
    }

    # All done! -- Jessica Noll, Age 2
    #
    exit($exitcode);
}


# exif - process EXIF data in an imgfile
#
# given:
#	$exiftool	Image::ExifTool object
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, =! 0 ==> exit code
#	    $message:	error message or undef if no error
#
sub exif($$)
{
    my ($exiftool, $filename) = @_;	# get arg
    my $info;		# exiftool extracted EXIF information
    my @tag_list;	# list of extracted EXIF field tag names
    my %canon_tag;	# map of canonical EFIF tag names to extracted names
    my $tag;		# an EXIF extracted field tag name
    my $canon;		# canonical value of tag name
    my $value;		# the value an EXIF extracted tag field
    my $description;	# description of an EXIF field
    my $need_pr_name;	# if -i, 1 ==> need to print filename, 0 ==> printed

    # firewall - image file must be readable
    #
    if (! -e $filename) {
	# NOTE: exit(2) for unable to open filename
	return(2, "cannot open");
    }
    if (! -r $filename) {
	# NOTE: exit(2) for unable to read filename
	return(2, "cannot read");
    }

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($filename, @opt_t);
    if (! defined $info) {
	return(7, "failed to extract EXIF data from $filename");
    }
    if (defined $$info{Error}) {
	# NOTE: exit(3) on ExifTool errors
	return(3, $$info{Error});
    }

    # get list of tags in the order that tags were found in the file
    #
    @tag_list = $exiftool->GetFoundTags('File');
    if (scalar @tag_list <= 0) {
	return(8, "no EXIF tags found in $filename");
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
    if (! -r $filename) {
	# NOTE: exit(2) for unable to read filename
	return(2, "cannot read");
    }

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($filename, @opt_t);
    if (! defined $info) {
	return(7, "failed to extract EXIF data from $filename");
    }
    if (defined $$info{Error}) {
	# NOTE: exit(3) on ExifTool errors
	return(3, $$info{Error});
    }

    # get list of tags in the order that tags were found in the file
    #
    @tag_list = $exiftool->GetFoundTags('File');
    if (scalar @tag_list <= 0) {
	return(8, "no EXIF tags found in $filename");
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
    print "EXIF data for $filename\n" if $opt_v >= 2;
    foreach $tag (@tag_list) {

    	# determine canonical name of this tag
	#
	$canon = $canon_tag{$tag};

	# binary EXIF tag value firewall
	#
	$value = $$info{$tag};
	if (! defined $value) {
	    # no such value, skip
	    next;
	} elsif (ref $value eq 'SCALAR') {
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
	$need_pr_name = 1;	# no filename printed yet
	if (defined $opt_n || defined $opt_m) {
	    print "$filename\t" if (defined $opt_i && $need_pr_name);
	    $need_pr_name = 0;
	    printf("%-31s\t", (defined $opt_e ? $tag : $canon));
	}

	# output the EXIF field group if -g
	#
	if (defined $opt_g) {
	    print "$filename\t" if (defined $opt_i && $need_pr_name);
	    $need_pr_name = 0;
	    printf("%-15s\t", $exiftool->GetGroup($tag));
	}

	# output EXIF tag value
	#
	print "$filename\t" if (defined $opt_i && $need_pr_name);
	$need_pr_name = 0;
	if (defined $opt_m) {
	    # -m disables printing of EXIT tag values
	    print "\n";
	} elsif (defined $opt_u && ! defined $opt_p) {
	    # ensure that the value we print is printable
	    #
	    # NOTE: Sometimes unknown EXIF tags (-u) contain non-printable
	    #	    characters even though the PrintConv option was set.
	    #	    This printable string processing is not done if
	    #	    we have turned off PrintConv (due to -p or -b).
	    #
	    print printable_str($value), "\n";
	} else {
	    print "$value\n";
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

    # check for warnings
    #
    if (defined $$info{Warning}) {
	# NOTE: exit(1) on ExifTool warnings
	return(1, $$info{Warning});
    }

    # all if ok
    #
    return(0, undef);
}


# printable_str - make a string printable
#
# given:
#	$str	the strign to canonicalize
#
# returns:
#	$str with % as %25, [^\w\s] as %xx
#
sub printable_str($)
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
