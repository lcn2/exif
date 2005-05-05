#!/usr/bin/perl -wT
#
# exifrename - copy files based on EXIF or file time data
#
# @(#) $Revision: 1.8 $
# @(#) $Id: exif.pl,v 1.8 2005/05/04 16:15:23 chongo Exp chongo $
# @(#) $Source: /usr/local/src/cmd/exif/RCS/exif.pl,v $
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
use vars qw($opt_h $opt_v);
use Getopt::Long;
use Image::ExifTool qw(ImageInfo);
no warnings 'File::Find';
use File::Find;

# version - RCS style *and* usable by MakeMaker
#
my $VERSION = substr q$Revision: 1.8 $, 10;
$VERSION =~ s/\s+$//;

# my vars
#
# EXIF timestamp related tag names to look for
my @tag_list = qw( ModifyDate DateTimeOriginal CreateDate );
# timestamps prior to Thu Oct  7 13:20:00 1993 UTC are too old for an image
my $mintime = 750000000;
my $srcdir;	# source of image files
my $destdir;	# where the renamed files will be copied
my $setdir;	# $destdir/set where set symlinks go
my $exiftool;	# Image::ExifTool object

# usage and help
#
my $usage = "$0 [-h][-v lvl] srcdir destdir"
my $help = qq{\n$usage

	-h	    print this help message
	-v 	    verbose / debug level

	srcdir	    source directory
	destdir	    destination directory

    NOTE:
	exit 0	all is OK
	exit >0 some other fatal error
};
my %optctl = (
    "h" => \$opt_h,
    "v=i" => \$opt_v,
);


# function prototypes
#
sub dir_setup();
sub exif_setup();
sub exif_date($$);
sub file_date($);


# setup
#
MAIN: {

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
    if (! defined $ARGV[0] || ! defined $ARGV[1]) {
	print STDERR "$0: missing args\nusage:\n\t$help\n";
	exit(5);
    }
    if (defined $ARGV[2]) {
	print STDERR "$0: too many args\nusage:\n\t$help\n";
	exit(3);
    }
    $srcdir = $ARGV[0];
    $destdir = $ARGV[1];
    $setdir = "$destdir/set";

    # setup directories
    #
    setup_dir();

    # setup ExifTool
    #
    $exiftool = exif_setup();

    # process all files and directories under $srcdir
    #
    # XXX - move these comments to the find wanted function
    #
    # We we process files under $srcdir, we copy them to $destdir and
    # we build up the symlink tree under $setdir.
    #
    # Consider the a file under srcdir:
    #
    #	/srcdir/DCIM/101EOS1D/LS1F5627.CR2
    #
    # Assume that the EXIF timestamp (or file timestamp if if lacks
    # EXIF timestamp tags) is:
    #
    #	2005-05-15
    #
    # Then we will create the file:
    #
    #	/destdir/200505/20050515-ls1f5627.cr2
    #
    # The created file path is:
    #
    #	/destdir
    #	4 digit Year of the timestamp
    #	Month [01-12] of the timestamp
    #	/
    #	4 digit Year of the timestamp
    #	Month [01-12] of the timestamp
    #   Day [01-31] of the timestamp
    #	- (dash)
    #	basename of srcfile mapped to lower case
    #
    # In addition, a symlink is setup under setdir as follows:
    #
    #	/destdir/set/set0031/101eos1d/20050515-ls1f5627.cr2 ->
    #	    ../../20050515-ls1f5627.cr2
    #
    # Note that the symlink filename basename is the same as the destination 
    # filename.  The symlink path is:
    #
    #	/destdir
    #	/set
    #	/setWXYZ	(WXYZ is a 4 digit number)
    #	/101eos1d	(the directory path under /srcdir/DCIM lowercased)
    #	/
    #	4 digit Year of the timestamp
    #	Month [01-12] of the timestamp
    #   Day [01-31] of the timestamp
    #	- (dash)
    #	basename of srcfile mapped to lower case
    #
    #
    # The WXYZ is a 4 digit serial number from the file:
    #
    #	~/.exifnum
    #
    # It if initialized to 0000 if that file does not exist.  The current
    # value is used to form the setWXYZ path component and then is incremented
    # by 1.  If incrementing reaches 10000, it is reset to 0000.  Note that
    # the WXYZ used in the path is the value prior to incrementing.
    #
    # NOTE: The EOS 1D Canon Image filesystem, without any images looks like:
    #
    #	/DCIM/			# all image directories go under DCIM
    #	/DCIM/100EOS1D/		# 1st image directory (2nd is 101EOS1D, ...)
    #	/.Trashes/		# directory where deleted images go?
    #	/.Trashes/501/		# ??? directory (other 5xx dirs have been seen)
    #	/.Trashes/._501		# ??? file (other (._5xx files have beens seen)
    #
    # Once the camera deletes an image, this file is created:
    #
    #	/constate.tof
    #
    # In addition, other files such as .DS_Store may be created by OS X.
    # These .DS_Store files should be ignored by the tool.
    #
    # So we need to ignore the following:
    #
    #	/.Trashes		# entire directory tree directly under srcdir
    #	/.comstate.tof		# this file directly under srcdir
    #	.DS_Store		# this fiile anywhere
    #
    # In addition, for path purposes, we do not create DCIM as a path component
    # when forming files and symlinks in destdir.
}


# dir_setup - setup and/or check on srcdir and destdir
#
# uses these globals:
#	$srcdir		where images are from
#	$desdir		where copied and renamed files go
#	$setdir		$destdir/set where symlinks are formed
#
# NOTE: Does not return on error.
#
sub dir_setup()
{
    # firewall - sanity check, srcdir cannot be a substring of destdir
    #
    if ($srcdir eq substr($destdir, 0, length $srcdir)) {
	print STDERR "$0: destdir: $destdir cannot be under srcdir: $srcdir\n";
	exit(6);
    }

    # firewall - check for a sane srcdir
    #
    if (! -e $srcdir) {
	print STDERR "$0: srcdir does not exist: $srcdir\n";
	exit(7);
    }
    if (! -d $srcdir) {
	print STDERR "$0: srcdir is not a directory: $srcdir\n";
	exit(8);
    }
    if (! -r $srcdir) {
	print STDERR "$0: srcdir is not readable: $srcdir\n";
	exit(9);
    }
    if (! -x $srcdir) {
	print STDERR "$0: srcdir is not searchable: $srcdir\n";
	exit(10);
    }

    # setup the destination directory if needed
    #
    if (-e $destdir && ! -d $destdir) {
	print STDERR "$0: destdir is a non-directory: $destdir\n";
	exit(11);
    } elsif (! -d $destdir && ! mkdir($destdir, 0775) {
	print STDERR "$0: cannot make destdir: $destdir: $!\n";
	exit(12);
    } elsif (! -w $destdir) {
	print STDERR "$0: destdir is not writable: $destdir\n";
	exit(13);
    }

    # setup the set symlink dir if needed
    #
    if (-e $setdir && ! -d $setdir) {
	print STDERR "$0: destdir/set is a non-directory: $setdir\n";
	exit(14);
    } elsif (! -d $setdir && ! mkdir($setdir, 0775) {
	print STDERR "$0: cannot make destdir/set: $setdir: $!\n";
	exit(15);
    } elsif (! -w $setdir) {
	print STDERR "$0: destdir/set is not writable: $setdir\n";
	exit(16);
    }
    return;
}


# exif_setup - setup for ExifTool processing
#
# returns:
#	Image::ExifTool object
#
sub exif_setup()
{
    my %exitoptions;			# ExifTool options
    my $exif_tool;			# Image::ExifTool object

    # setup ExifTool options
    #
    $exifoptions{Binary} = 0;		# no timestamp is a binary field
    $exifoptions{PrintConv} = 0;	# no need to waste time converting
    $exifoptions{Unknown} = 0;		# all timestamps are in known fields
    $exifoptions{DateFormat} = "\%s"	# timestamps as seconds since the Epoch
    $exifoptions{Duplicates} = 0;	# use the last timestamp if we have dups

    # create a new Image::ExifTool object
    #
    $exif_tool = new Image::ExifTool;

    # set the ExifTool options
    #
    $exif_tool->Options(%exifoptions);
    return $exif_tool;
}


# exif_date - determine a file date string using EXIF and file timestamps
#
# given:
#	$exiftool	Image::ExifTool object
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, =! 0 ==> exit code
#	    $message:	date string of $exitcode, else error message
#
sub exif_date($$)
{
    my ($exiftool, $filename) = @_;	# get arg
    my $info;		# exiftool extracted EXIF information
    my $tag;		# EXIF tag name
    my $timestamp = -1;	# seconds since the epoch of early tstamp or -1

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
    $info = $exiftool->ImageInfo($filename, @tag_list);
    if (! defined $info || defined $$info{Error}) {
	# failure to get a EXIF data, use file dates instead
	return file_date($filename);
    }

    # look at each EXIF tag value we found
    #
    # We are looking for the earliest timestamp that is not before
    # $mintime.  A < 0 timestamp means nothing found so far.
    #
    foreach $tag (@tag_list) {

	# ignore if no EXIF value or non-numeric
	#
	if (defined $$info{$tag} && $$info{$tag} =~ /^\d+$/ &&
	    $$info{$tag} > $mintime &&
	    ($timestamp < 0 || $$info{$tag} < $timestamp)) {
	    $timestamp = $$info{$tag};
        }
    }

    # If we did not find any reasonable EXIF timestamp data, then we
    # must use the file name
    #
    if ($timestamp < 0) {
	return file_date($filename);
    }

    # return the EXIF timestamp
    #
    return(0, $timestamp);
}


# file_date - return the earlist reasonable create/modify timestamp
#
#
# given:
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, =! 0 ==> exit code
#	    $message:	date string of $exitcode, else error message
#
sub file_date($)
{
    my ($filename) = @_;	# get arg
    my $mtime;			# modify timestamp
    my $ctime;			# create timestamp

    # firewall - file must be readable
    #
    if (! -e $filename) {
	# NOTE: exit(2) for unable to open filename
	return(2, "cannot open");
    }
    if (! -r $filename) {
	# NOTE: exit(2) for unable to read filename
	return(2, "cannot read");
    }

    # stat the file
    #
    (undef, undef, undef, undef, undef, undef, undef, undef,
     undef, $mtime, $ctime) = stat($filename);

    # first try the create timestamp
    #
    if (defined $ctime && $ctime >= $mintime) {
	# use create time
	return(0, $ctime);

    # next try the modify timestamp
    #
    } elsif (defined $mtime && $mtime >= $mintime) {
	# use modify time
	return(0, $mtime);
    }

    # we cannot find a useful file timestamp
    #
    return(1, "file is too old");
}
