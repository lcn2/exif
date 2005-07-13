#!/usr/bin/perl -wT
#
# exifrename - copy files based on EXIF or file time data
#
# @(#) $Revision: 1.16 $
# @(#) $Id: exifrename.pl,v 1.16 2005/07/13 06:00:29 chongo Exp chongo $
# @(#) $Source: /usr/local/src/cmd/exif/RCS/exifrename.pl,v $
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
use vars qw($opt_h $opt_v $opt_o $opt_m $opt_t $opt_c $opt_e $opt_r $opt_s);
use Getopt::Long;
use Image::ExifTool qw(ImageInfo);
use POSIX qw(strftime);
use File::Find;
no warnings 'File::Find';
use File::Copy;
use File::Compare;
use File::Basename;
use Time::Local qw(timegm_nocheck timegm);

# version - RCS style *and* usable by MakeMaker
#
my $VERSION = substr q$Revision: 1.16 $, 10;
$VERSION =~ s/\s+$//;

# my vars
#
my $srcdir;	# source of image files
my $destdir;	# where the renamed files will be copied
my $destdev;	# device of $destdir
my $destino;	# inode numner of $destdir
my $rollnum;	# EXIF roll number
my $exiftool;	# Image::ExifTool object
# NOTE: We will only cd into dirs whose name is only [-+\w\s./] chars
my $untaint = qr|^([-+\w\s./]+)$|; 	# untainting path pattern
my $datelines = 16;	# date: must be in the 1st datelines of a file
my %mname = (
    "Jan" => 0, "Feb" => 1, "Mar" => 2, "Apr" => 3, "May" => 4, "Jun" => 5,
    "Jul" => 6, "Aug" => 7, "Sep" => 8, "Oct" => 9, "Nov" => 10, "Dec" => 11,
);
my $subdirchars = 3;	# number of initial chars of subdir to use in path
my $rollfile;		# file that keeps track of next roll number


# EXIF timestamp related tag names to look for
#
my @tag_list = qw( ModifyDate DateTimeOriginal CreateDate );

# file extensions, in priority order, that are likely to
# contain EXIF data
#
my @exif_ext = qw(
    cr2 CR2
    raw RAW
    tif TIF tiff TIFF
    jpg JPG jpeg JPEG
    png PNG
    gif GIF
    psd PSD
    eps EPS
);

# timestamps prior to:
#	Tue Nov  5 00:53:20 1985 UTC
# are too old for an image with EXIF data.   See:
#	perl -e 'my $x=500000000; print scalar gmtime($x), "\n";'
#
my $mintime = 500000000;

# usage and help
#
my $usage = "$0 [-c][-e][-m][-o][-r rollfile][-s sdirlen][-t] \n" .
	"\t[-h][-v lvl] srcdir destdir";
my $help = qq{\n$usage

	-c	     don't verify/compare files after they are copied (def: do)
	-e	     don't abort/exit after a fatal error (def: do)
	-m	     move, do not copy files from srcdir to destdir (def: copy)
	-o	     overwrite, don't add _# after time on duplicates (def: add)
	-r rollfile  read EXIF rull number of rollfile (def: ~/.exifroll)
	-s sdirlen   initial top sub-dir chars to use (def: 3, 0 ==> use all)
	-t	     don't touch modtime to match EXIF/file image (def: do)

	-h	     print this help message
	-v 	     verbose / debug level

	srcdir	     source directory
	destdir	     destination directory

    NOTE:
	exit 0	all is OK
	exit >0 some fatal error

    Version: $VERSION};
my %optctl = (
    "c" => \$opt_c,
    "e" => \$opt_e,
    "h" => \$opt_h,
    "m" => \$opt_m,
    "o" => \$opt_o,
    "r=s" => \$opt_r,
    "t" => \$opt_t,
    "s=i" => \$opt_s,
    "v=i" => \$opt_v,
);


# function prototypes
#
sub wanted();
sub dir_setup();
sub timestamp($);
sub exif_date($);
sub file_date($);
sub text_date($);
sub form_dir($);
sub roll_setup();


# setup
#
MAIN: {
    my %find_opt;	# File::Find directory tree walk options
    my %exifoptions;	# Image::ExifTool options

    # setup
    #
    select(STDOUT);
    $| = 1;

    # set the defaults
    #
    $opt_v = 0;
    $ENV{HOME} = "/" unless defined $ENV{HOME};
    $rollfile = "$ENV{HOME}/.exifroll";

    # parse args
    #
    if (!GetOptions(%optctl)) {
	print STDERR "$0: invalid command line\nusage:\n\t$help\n";
	exit(1);
    }
    if (defined $opt_h) {
	# just print help, no error
	print STDERR "$0: usage: $help\n";
	exit(0);
    }
    if (defined $opt_m && defined $opt_c) {
	# cannot compare if we are moving
	print STDERR "$0: -c (compare) conflicts with -m (move)\n";
	exit(2);
    }
    if (! defined $ARGV[0] || ! defined $ARGV[1]) {
	print STDERR "$0: missing args\nusage:\n\t$help\n";
	exit(3);
    }
    if (defined $ARGV[2]) {
	print STDERR "$0: too many args\nusage:\n\t$help\n";
	exit(4);
    }
    $subdirchars = $opt_s if defined $opt_s;
    $rollfile = $opt_r if defined $opt_r;
    $srcdir = $ARGV[0];
    $destdir = $ARGV[1];
    if ($opt_v > 0) {
	print "DEBUG:";
	print " -c" if defined $opt_c;
	print " -e" if defined $opt_e;
	print " -m" if defined $opt_m;
	print " -o" if defined $opt_o;
	print " -r $opt_r" if defined $opt_r;
	print " -s $opt_s" if defined $opt_s;
	print " -t" if defined $opt_t;
	print " -v $opt_v" if $opt_v > 0;
	print " $srcdir $destdir\n";
    }
    if ($opt_v > 1) {
	print "DEBUG: won't verify/compare files afterwards\n" if $opt_c;
	print "DEBUG: won't abort/exit after a fatal error\n" if $opt_e;
	print "DEBUG: ", ($opt_m ? "move" : "copy"), " files\n";
	print "DEBUG: ",
		($opt_o ? "override" : "add _# on"),
		" duplicate files\n";
	print "DEBUG: ~/exifroll file: $rollfile\n";
	print "DEBUG: use ",
		($subdirchars > 0 ? $subdirchars : "all"),
		" chars from highest subdir to form path\n";
	print "DEBUG: ", ($opt_t ? "don't" : "do"), " touch file modtimes\n";
	print "DEBUG: srcdir: $srcdir\n";
	print "DEBUG: destdir: $destdir\n";
    }

    # setup to walk the srcdir
    #
    $find_opt{wanted} = \&wanted; # call this on each non-pruned node
    $find_opt{bydepth} = 0;	# walk from top down, not from bottom up
    $find_opt{follow} = 0;	# do not follow symlinks
    $find_opt{no_chdir} = 0;	# OK to chdir as we walk the tree
    $find_opt{untaint} = 1;	# untaint dirs we chdir to
    $find_opt{untaint_pattern} = $untaint; # untaint pattern
    $find_opt{untaint_skip} = 1; # we will skip any dir that is tainted

    # untaint $srcdir, $destdir, and $rollfile
    #
    if ($srcdir =~ /$untaint/o) {
    	$srcdir = $1;
    } else {
	print STDERR "$0: bogus chars in srcdir\n";
	exit(5);
    }
    if ($destdir =~ /$untaint/o) {
    	$destdir = $1;
    } else {
	print STDERR "$0: bogus chars in destdir\n";
	exit(6);
    }
    if ($rollfile =~ /$untaint/o) {
    	$rollfile = $1;
    } else {
	print STDERR "$0: bogus chars in -r filename\n";
	exit(7);
    }

    # setup directories
    #
    dir_setup();

    # initialize roll serial number $rollnum
    #
    roll_setup();

    # setup ExifTool options
    #
    $exifoptions{Binary} = 0;		# no timestamp is a binary field
    $exifoptions{PrintConv} = 1;	# we will need to convert timestamps
    $exifoptions{Unknown} = 0;		# ignore unknown fields
    $exifoptions{DateFormat} = '%s';	# timestamps as seconds since the Epoch
    $exifoptions{Duplicates} = 0;	# use the last timestamp if we have dups
    $exiftool = new Image::ExifTool;
    $exiftool->Options(%exifoptions);

    # walk the srcdir, making renamed copies and symlinks
    #
    find(\%find_opt, $srcdir);

    # all done
    #
    exit(0);
}


# dir_setup - setup and/or check on srcdir and destdir
#
# uses these globals:
#
#	$srcdir		where images are from
#	$destdir	where copied and renamed files go
#
# sets these global values:
#
#	$destdev	device of $destdir
#	$destino	inode number of $destdir
#
# NOTE: Does not return on error.
#
sub dir_setup()
{
    my ($errcode, $errmsg);	# form_dir return values

    # firewall - check for a sane srcdir
    #
    if (! -e $srcdir) {
	print STDERR "$0: srcdir does not exist: $srcdir\n";
	exit(8);
    }
    if (! -d $srcdir) {
	print STDERR "$0: srcdir is not a directory: $srcdir\n";
	exit(9);
    }
    if (! -r $srcdir) {
	print STDERR "$0: srcdir is not readable: $srcdir\n";
	exit(10);
    }
    if (! -x $srcdir) {
	print STDERR "$0: srcdir is not searchable: $srcdir\n";
	exit(11);
    }

    # setup the destination directory if needed
    #
    ($errcode, $errmsg) = form_dir($destdir);
    if ($errcode != 0) {
	print STDERR "$0: mkdir error: $errmsg for $destdir\n";
	exit(12);
    }

    # record the device and inode number of $destdir
    #
    ($destdev, $destino,) = stat($destdir);
    return;
}


# wanted - File::Find tree walking function called at each non-pruned node
#
# This function is a callback from the File::Find directory tree walker.
# It will walk the $srcdir and copy/rename files as needed.
#
# We we process files under $srcdir, we copy them to $destdir.
#
# uses these globals:
#
#	$opt_c		see -c in program usage at top
#	$opt_e		see -e in program usage at top
#	$opt_f		see -f in program usage at top
#	$opt_o		see -o in program usage at top
#	$opt_t		see -t in program usage at top
#	$srcdir		where images are from
#	$destdir	where copied and renamed files go
#	$rollnum	EXIF roll number
#	$untaint	untainting path pattern
#
# Consider the a file under srcdir:
#
#	/srcdir/DCIM/101EOS1D/LS1F5627.CR2
#
# Assume that the EXIF timestamp (or file timestamp if if lacks
# EXIF timestamp tags) is:
#
#	2005-05-12 15:25:45 UTC
#
# Then we will create the file:
#
#    /destdir/200505/043-101/043-101-20050512-152545-ls1f5627.cr2
#
# The created file path is:
#
#	/destdir			# destdir path of image library
#	/200505				# image year & month
#	/043-101			# roll-subdir
#	/043-101-20050512-152545-ls1f5627.cr2	# image filename (see below)
#
# The filename itself:
#
#	043-101-20050512-152545-ls1f5627.cr2
#
# If another image was taken during the same second, its name becomes:
#
#	043-101-20050512-152545_1-ls1f5628.cr2
#
# is constructed out of the following:
#
#	043			# roll number, 3 digits, 0 padded
#	-			# (dash) separator
#	101			# top subdir initial chars w/o -'s & lowercase
#	-			# (dash) separator
#	2005			# image 4 digit Year
#	05			# image month, 2 digits [01-12]
#	12			# image day of month, 2 digits [01-31]
#	-			# (dash) separator
#	15			# image hour (UTC), 2 digits [00-23]
#	25			# image minute of hour, 2 digits [00-59]
#	45			# image seconf of minites, 2 digits [00-60]
#	     _			# (underscore) optional for dups in same sec
#	     1			# optional digits for dups in same sec
#	-			# (dash) separator
#	ls1f5627.cr2		# image basename, in lower case w/o -'s
#
# The 3 digit roll serial number from the file:
#
#	~/.exifroll
#
# The roll is initialized to 000 if that file does not exist.  The current
# value in the file is used to form the roll number component.  The value
# in the roll number file is incremented by one in preparation for next use.
#
####
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
# These .DS_Store files should be ignored by the tool.  The Titanium
# Toast CD/DVD burner creates "desktop db" and "desktop df" which
# are also ignored by this shell.
#
# So we need to ignore the following:
#
#	/.Trashes		# entire directory tree directly under srcdir
#	/.comstate.tof		# this file directly under srcdir
#	.DS_Store		# this fiile anywhere
#	desktop db		# Titanium Toast CD/DVD burner file
#	desktop df		# Titanium Toast CD/DVD burner file
#
# In addition, for path purposes, we do not create DCIM as a path component
# when forming files and symlinks in destdir.
#
####
#
# NOTE: The File::Find calls this function with this argument:
#
#	$_			current filename within $File::Find::dir
#
# and these global vaules set:
#
#	$File::Find::dir	current directory name
#	$File::Find::name 	complete pathname to the file
#	$File::Find::prune	set 1 one to prune current node out of path
#	$File::Find::topdir	top directory path ($srcdir)
#	$File::Find::topdev	device of the top directory
#	$File::Find::topino	inode number of the top directory
#
sub wanted()
{
    my $filename = $_;		# current filename within $File::Find::dir
    my $pathname;		# complete path $File::Find::name
    my $nodedev;		# device of the current file
    my $nodeino;		# inode number of the current file
    my $roll_sub;		# roll-subdir
    my ($errcode, $errmsg);	# form_dir return values
    my $lowerfilename;	# lower case filename
    my $levels;	# directoy levels under $srcdir/DCIM or $srcdir
    my $datecode;	# exif_date error code or 0 ==> OK
    my $datestamp;	# EXIF or filename timestamp of OK, or error msg
    my $yyyymm;	# EXIF or filename timestamp year and month
    my $dd;		# EXIF or filename timestamp day
    my $hhmmss;	# EXIF or filename timestamp time
    my $hhmmss_d;	# EXIF or filename timestamp time and optional _#
    my $dupnum;	# -# de-duplication number
    my $destname;	# the destination filename to form
    my $destpath;	# the full path of the destination file

    # canonicalize the path by removing leading ./ and multiple //'s
    #
    print "DEBUG: in wanted arg: $filename\n" if $opt_v > 3;
    print "DEBUG: in wanted with: $File::Find::name\n" if $opt_v > 2;
    ($pathname = $File::Find::name) =~ s|^(\./+)+||;
    $pathname =~ s|//+|/|g;
    print "DEBUG: ready to process $pathname\n" if $opt_v > 1;

    # prune out anything that is directory or file
    #
    if (! -d $filename && ! -f $filename) {
	# skip non-dir/non-files
	print "DEBUG: non-dir/non-file prune #0 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out certain top level paths
    #
    # As notied in detail above, we will prune off any .Trashes,
    # .comstate.tof that are directly under $srcdir
    #
    if ($pathname eq "$srcdir/.Trashes") {
	# skip this useless camera node
	print "DEBUG: .Trashes prune #1 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }
    if ($pathname eq "$srcdir/.comstate.tof") {
	# skip this useless camera node
	print "DEBUG: .comstate.tof prune #2 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out .DS_Store files
    #
    if ($filename eq ".DS_Store") {
	# skip OS X .DS_Store files
	print "DEBUG: .DS_Store prune #3 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out Titanium Toast files
    #
    if ($filename =~ /^desktop d[bf]$/i) {
	# skip Titanium Toast files
	print "DEBUG: desktop prune #4 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # ignore names that match common directories
    #
    if ($filename eq ".") {
	# ignore but do not prune directories
	print "DEBUG: . ignore #6 $pathname\n" if $opt_v > 3;
    	return;
    }
    if ($filename eq "..") {
	# ignore but do not prune directories
	print "DEBUG: .. ignore #7 $pathname\n" if $opt_v > 3;
    	return;
    }
    if ($filename eq "DCIM") {
	# ignore but do not prune directories
	print "DEBUG: DCIM ignore #8 $pathname\n" if $opt_v > 3;
    	return;
    }

    # ignore non-files
    #
    if (! -f $filename) {
	# ignore but do not prune directories
	print "DEBUG: dir ignore #9 $pathname\n" if $opt_v > 3;
    	return;
    }

    # Determine the leading chars of the top level directory under $srcdir,
    # in lowercase, with -'s (dashes) replaced with _'s (underscores)
    #
    if ($pathname =~ m|^$srcdir/[^/]+/|o) {
	$roll_sub = basename(dirname($pathname));
	print "DEBUG: orig roll_sub is: $roll_sub\n" if $opt_v > 4;
    } elsif ($pathname =~ m|^$srcdir/[^/]+$|o) {
	$roll_sub = "";
	print "DEBUG: no top dir, using empty roll_sub\n" if $opt_v > 4;
    } else {
	print STDERR "$0: Fatal $pathname not under $srcdir\n";
	print "DEBUG: non-srcdir prune #13 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(13) unless defined $opt_e;
	return;
    }
    $roll_sub =~ tr/[A-Z]/[a-z]/;	# conver to lower case
    $roll_sub = "" if ($roll_sub eq "dcim");
    $roll_sub =~ s/-/_/g;	# -'s (dash) become _'s (underscore)
    $roll_sub = substr($roll_sub, 0, $subdirchars) if $subdirchars > 0;
    $roll_sub = "$rollnum-$roll_sub";
    print "DEBUG: roll_sub name: $roll_sub\n" if $opt_v > 2;

    # untaint roll_sub
    #
    if ($roll_sub =~ /$untaint/o) {
    	$roll_sub = $1;
    } else {
	print STDERR "$0: Fatal: strange chars in roll_sub \n";
	print "DEBUG: tainted roll_sub prune #14 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(14) unless defined $opt_e;
	return;
    }

    # determine the date of the image by EXIF or filename date
    #
    ($datecode, $datestamp) = timestamp($pathname);
    if ($datecode != 0) {
	print STDERR "$0: Fatal: EXIF image timestamp error $datecode: ",
		     "$datestamp\n";
	print "DEBUG: bad timestamp prune #15 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(15) unless defined $opt_e;
	return;
    }
    print "DEBUG: EXIF image / file timestamp: $datestamp\n" if $opt_v > 3;

    # untaint datestamp
    #
    if ($datestamp =~ /$untaint/o) {
	$datestamp = $1;
    } else {
	print STDERR "$0: Fatal: strange chars in datestamp \n";
	print "DEBUG: tainted datestamp prune #16 $pathname\n"
	    if $opt_v > 0;
	$File::Find::prune = 1;
	exit(16) unless defined $opt_e;
	return;
    }

    # canonicalize the filename
    #
    ($lowerfilename = $filename) =~ tr /[A-Z]/[a-z]/;	# lower case

    # If the lowercase name is already of the form:
    #
    #	043-101-20050512-152545-ls1f5628.cr2
    #	043-101-20050512-152545_1-ls1f5628.cr2
    #
    # convert it to just ls1f5628.cr2 so that we won't keep adding
    # date strings to the filename.
    #
    if ($lowerfilename =~ /^\d{3}-[^-]+-\d{8}-\d{6}(_\d+)?-(.*)$/) {
	$lowerfilename = $2;
    }
    $lowerfilename =~ s/-/_/g;	# -'s (dash) become _'s (underscore)

    # convert the timestamp into date strings
    #
    $yyyymm = strftime("%Y%m", gmtime($datestamp));
    $dd = strftime("%d", gmtime($datestamp));

    # untaint yyyymm
    #
    if ($yyyymm =~ /$untaint/o) {
	$yyyymm = $1;
    } else {
	print STDERR "$0: Fatal: strange chars in yyyymm \n";
	print "DEBUG: tainted yyyymm prune #17 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(17) unless defined $opt_e;
	return;
    }

    # ensure the $destdir/yyyymm/rol-sub direct path exists
    #
    ($errcode, $errmsg) = form_dir("$destdir/$yyyymm");
    if ($errcode != 0) {
	print STDERR "$0: Fatal: mkdir error: $errmsg for ",
		     "$destdir/$yyyymm\n";
	print "DEBUG: mkdir err prune #18 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(18) unless defined $opt_e;
	return;
    }
    ($errcode, $errmsg) = form_dir("$destdir/$yyyymm/$roll_sub");
    if ($errcode != 0) {
	print STDERR "$0: Fatal: mkdir error: $errmsg for ",
		     "$destdir/$yyyymm/$roll_sub\n";
	print "DEBUG: mkdir err prune #19 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(19) unless defined $opt_e;
	return;
    }

    # deal with the case of when the destination file already exists
    #
    # If the filename exists, start adding _X for X 0 to 99
    # after the seconds.
    #
    $hhmmss = strftime("%H%M%S", gmtime($datestamp));
    $hhmmss_d = $hhmmss;	# assume no de-dup is needed
    $dupnum = 0;
    do {
	# determine destination filename and full path
	#
	$destname = "$roll_sub-$yyyymm$dd-$hhmmss_d-$lowerfilename";
	$destpath = "$destdir/$yyyymm/$roll_sub/$destname";

	# prep for next cycle if destination already exists
	#
	if (-e $destpath) {
	    print "DEBUG: dest file exists: $destpath\n" if $opt_v > 4;
	    $hhmmss_d = $hhmmss . "_" . ++$dupnum;

	    # if -o, then try to remove the old desitnation
	    #
	    if (defined $opt_o) {
		if (-f $destpath) {
		    print "DEBUG: -o pre-remove: $destpath\n" if $opt_v > 4;
		    unlink $destpath;
		    if ($opt_v > 4 && -f $destpath) {
			print "DEBUG: cannot pre-remove: $destpath: $!\n";
		    }
		} else {
		    print "DEBUG: will not -o pre-remove ",
			  "a non-file: $destpath\n" if $opt_v > 4;
		}
		if ($opt_v > 4 && -e $destpath) {
		    print "DEBUG: we must try another filename\n";
		}
	    }
	}

	# firewall - do not allow more than 99 duplicates
	#
	if ($dupnum > 99) {
	    print STDERR "$0: Fatal: more than 99 duplicates for ",
			 "$yyyymm-$roll_sub-$dd-$hhmmss-$lowerfilename\n";
	    print "DEBUG: 100 dups prune #20 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(20) unless defined $opt_e;
	    return;
	}
    } while (-e "$destpath");
    print "DEBUG: destination: $destname\n" if $opt_v > 1;
    print "DEBUG: destination path: $destpath\n" if $opt_v > 2;

    # untaint destpath
    #
    if ($destpath =~ /$untaint/o) {
	$destpath = $1;
    } else {
	print STDERR "$0: Fatal: strange chars in destpath \n";
	print "DEBUG: tainted destpath prune #21 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(21) unless defined $opt_e;
	return;
    }

    # copy (or move of -m) the image file
    #
    if (defined $opt_m) {
	if (move($pathname, $destpath) == 0) {
	    print STDERR "$0: Fatal: in ", $File::Find::dir, ": ",
			 "mv $filename $destpath failed: $!\n";
	    print "DEBUG: mv err prune #22 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(22) unless defined $opt_e;
	    return;
	}
	print "DEBUG: success: mv $filename $destpath\n" if $opt_v > 2;
    } else {
	if (copy($pathname, $destpath) == 0) {
	    print STDERR "$0: Fatal: in ", $File::Find::dir, ": ",
			 "cp $filename $destpath failed: $!\n";
	    print "DEBUG: cp err prune #23 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(23) unless defined $opt_e;
	    return;
	}
	print "DEBUG: success: cp $filename $destpath\n" if $opt_v > 2;
    }

    # compare unless -t
    #
    if (! defined $opt_c && compare($pathname, $destpath) != 0) {
	print STDERR "$0: Fatal: in ", $File::Find::dir, ": ",
		     "compare of $filename and $destpath failed\n";
	print "DEBUG: cmp err prune #24 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(24) unless defined $opt_e;
	return;
    }
    print "DEBUG: success: cmp $filename $destpath\n" if $opt_v > 2;

    # set the access and modification time unless -t
    #
    if (! defined $opt_t) {
	utime $datestamp, $datestamp, $destpath;
    }
    print "DEBUG: processed: $destpath\n" if $opt_v > 0;
    return;
}


# timestamp - determine a file date string using EXIF and file timestamps
#
# We will first look at EXIF data for a timestamp.  If none is found
# we will look for a readable related filename that is likely to have
# EXIF data.  If none is found, we will try to use the file's creation
# or modification timestamps.
#
# A common reason for lack of EXIF data is that the file in question
# is not a file that the type of file that has EXIF data.  Cameras
# that allow one to record sound will create audio files.  Such audio
# files do not contain any EXIF data.
#
# It is frequently the case that non-EXIF files created by cameras
# have a filename that is similar to an image file.  For example on
# the Canon EOS 1D Mark II, one may have an image file "ls1f5627.cr2"
# and a related sound file "ls1f5627.wav".  It would be useful to
# associate the wav file with the image file.  Therefore an attempt
# will be made to look for a corresponding EXIF image file when
# a non-EXIF file is found.
#
# When we are called, we will look for a readable file that has the same
# basename as our $filename arg, but with an extension that implies
# it is an image file.  For example, if we are called with a filename of
# "/.../ls1f5627.wav", we will look for readable files such as
# "/.../ls1f5627.cr2", "/.../ls1f5627.jpg", etc.
#
# The order of extensions is defined by the @exif_ext array.  We will
# search for readable files in order of that array.  If we find a
# readable file that has a valid EXIF timestamp, we will use that
# timestamp.  Otherwise we will keep looking through the rest of the
# @exif_ext array.  If and only if we reach the end of the @exif_ext
# array without a valid EXIF timestamp, then we will look at the
# create/modify timestamp.
#
# NOTE: The non-EXIF and related EXIF files must be in the same directory.
#
# given:
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, else ==> exit code
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub timestamp($)
{
    my ($filename) = @_;	# get args
    my $noext;			# filename without any extension
    my $exif_file;		# a potential EXIF related filename
    my $extension;		# a potential EXIF related file extension
    my $errcode;		# 0 ==> OK
    my $timestamp = -1;	# seconds since the epoch of early tstamp or -1
    my $filename_dev;		# device of the $filename arg
    my $filename_ino;		# inode number of the $filename arg

    # try to get an EXIF based timestamp
    #
    print "DEBUG: looking for EXIF timestamp in $filename\n" if $opt_v > 4;
    ($errcode, $timestamp) = exif_date($filename);
    if ($errcode == 0) {
	print "DEBUG: EXIF timestamp for $filename: $timestamp\n" if $opt_v > 4;
	return (0, $timestamp);
    }
    print "DEBUG: EXIF timestamp $filename: return code: $errcode: ",
    	  "$timestamp\n" if $opt_v > 4;

    # We did not find a valif EXIF in gthe filename, so we will
    # look for related files that might have EXIF data
    #
    ($filename_dev, $filename_ino, ) = stat($filename);
    ($noext = $filename) =~ s|\.[^./]*$||;
    foreach $extension ( @exif_ext ) {

	# Look for a related readable file that is likely to have
	# EXIF data in it ... and only if that related filename
	# is not exactly the same as our filename argument.
	#
	$exif_file = "$noext.$extension";
	if ($exif_file ne $filename && -r $exif_file) {
	    my $errcode;	# 0 ==> OK
	    my $timestamp;	# timestamp or error msg
	    my $exif_dev;	# device of the related EXIF filename
	    my $exif_ino;	# inode number of the related EXIF filename

	    # ignore if same dev/inode
	    #
	    # We cannot depend on a filename match to determine
	    # if our EXIF candidate is the same file.  Some OS'
	    # have case insensitive filenames.  Some OS' allow
	    # for hard links or symlinks.  We match on the
	    # device and inode number in addition to the filename.
	    #
	    ($exif_dev, $exif_ino, ) = stat($exif_file);
	    if (defined $filename_dev && defined $exif_dev &&
	    	$filename_dev == $exif_dev &&
	        defined $filename_ino && defined $exif_ino &&
	    	$filename_ino == $exif_ino) {
		print "DEBUG: ignoring EXIF file: $exif_file, same as ",
		      "filename: $filename\n" if $opt_v > 5;
		next;
	    }

	    # try to get an EXIF based timestamp
	    #
	    print "DEBUG: looking at related filename: $exif_file\n"
	    	if $opt_v > 4;
	    ($errcode, $timestamp) = exif_date($exif_file);

	    # return EXIF data if we were able to find a good timestamp
	    #
	    if ($errcode == 0) {
		print "DEBUG: found related EXIF timestamp in $exif_file: ",
			"$timestamp\n" if $opt_v > 4;
		return (0, $timestamp);
	    }
	    print "DEBUG: EXIF timestamp $filename: EXIF code: $errcode: ",
		  "$timestamp\n" if $opt_v > 5;
	}
    }
    print "DEBUG: found no related EXIF file for: $filename\n" if $opt_v > 4;

    # If the file is a txt file or a file without an extension,
    # then look for a Date: string in the early lines of the file.
    #
    if ($filename =~ /\.txt$/i || basename($filename) !~ /\./) {
	print "DEBUG: looking for text date in $filename\n" if $opt_v > 4;
	($errcode, $timestamp) = text_date($filename);
	if ($errcode == 0) {
	    print "DEBUG: text timestamp for file: $filename: $timestamp\n"
	        if $opt_v > 4;
	    return (0, $timestamp);
	}
	print "DEBUG: no valid text date found in $filename\n" if $opt_v > 4;
    }

    # No valid EXIF timestamps in the file or related readable files.
    # Try the file's creation / modification timestamp and return
    # whatever it says ... a timestamp or error.
    #
    print "DEBUG: forced to use file timestamp for $filename\n" if $opt_v > 4;
    ($errcode, $timestamp) = file_date($filename);
    if ($opt_v > 4) {
	if ($errcode == 0) {
	    print "DEBUG: timestamp for file: $filename: $timestamp\n";
	} else {
	    print "DEBUG: file timestamp: $filename: error: $errcode: ",
	    	  "$timestamp\n";
	}
    }
    return ($errcode, $timestamp);
}


# exif_date - determine a file date string using EXIF data
#
# given:
#	$filename	image filename to process
#
# uses these globals:
#
#	$exiftool	Image::ExifTool object
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, else ==> could not get an EXIF timestamp
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub exif_date($)
{
    my ($filename) = @_;	# get args
    my $info;		# exiftool extracted EXIF information
    my $tag;		# EXIF tag name
    my $timestamp;	# seconds since the epoch of early tstamp or -1

    # firewall - image file must be readable
    #
    if (! -e $filename) {
	return (25, "cannot open");	# exit(25)
    }
    if (! -r $filename) {
	return (26, "cannot read");	# exit(26)
    }

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($filename, @tag_list);
    if (! defined $info || defined $$info{Error}) {
	# failure to get a EXIF data
	if (defined $$info{Error}) {
	    return (27, "EXIF data error: $$info{Error}");	# exit(27)
        } else {
	    return (28, "no EXIF data");	# exit(28)
	}
    }

    # look at each EXIF tag value we found
    #
    # We are looking for the earliest timestamp that is not before
    # $mintime.  A < 0 timestamp means nothing found so far.
    #
    $timestamp = -1;	# no timestamp yet
    foreach $tag (@tag_list) {

	# ignore if no EXIF value or non-numeric
	#
	if (! defined $$info{$tag}) {
	    print "DEBUG: ignoring undef EXIF tag value: $tag\n" if $opt_v > 5;
	} elsif ($$info{$tag} !~ /^\d+$/) {
	    print "DEBUG: ignoring non-numeric tag: $tag: ",
	    	"$$info{$tag}\n" if $opt_v > 5;
	} elsif ($$info{$tag} <= $mintime) {
	    print "DEBUG: ignoring pre-mintime: $tag: ",
	    	  "$$info{$tag} <= $mintime\n" if $opt_v > 5;
	} elsif ($timestamp > 0 && $$info{$tag} == $timestamp) {
	    print "DEBUG: ignoring timestamp tag: $tag: ",
	    	  "$$info{$tag} same value\n"
		  if $opt_v > 5;
	} elsif ($timestamp > 0 && $$info{$tag} > $timestamp) {
	    print "DEBUG: ignoring timestamp tag: $tag: ",
	    	  "$$info{$tag} that is not earlist > $timestamp\n"
		  if $opt_v > 5;
	} else {
	    print "DEBUG: found useful numeric timestamp tag: $tag ",
	    	  "$$info{$tag}\n" if $opt_v > 5;
	    $timestamp = $$info{$tag};
        }
    }
    if ($timestamp < 0) {
	return (29, "no timestamp in EXIF data");	# exit(29)
    }

    # Avoid very old EXIF timestamps
    #
    if ($timestamp < $mintime) {
	return (30, "timestamp: $timestamp < min: $mintime");	# exit(30)
    }

    # return the EXIF timestamp
    #
    return (0, $timestamp);
}


# file_date - return the earlist reasonable create/modify timestamp
#
# given:
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, =! 0 ==> exit code
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub file_date($)
{
    my ($filename) = @_;	# get arg
    my $mtime;			# modify timestamp
    my $ctime;			# create timestamp

    # firewall - file must exist
    #
    if (! -e $filename) {
	return (31, "cannot open");	# exit(31)
    }

    # stat the file
    #
    (undef, undef, undef, undef, undef, undef, undef, undef,
     undef, $mtime, $ctime) = stat($filename);

    # first try the create timestamp
    #
    if (defined $ctime && $ctime >= $mintime) {
	# use create time
	print "DEBUG: using: $filename: create timestamp: $ctime\n"
	    if $opt_v > 4;
	return (0, $ctime);

    # next try the modify timestamp
    #
    } elsif (defined $mtime && $mtime >= $mintime) {
	# use modify time
	print "DEBUG: using: $filename: modify timestamp: $ctime\n"
	    if $opt_v > 4;
	return (0, $mtime);
    }

    # we cannot find a useful file timestamp
    #
    print "DEBUG: no valid file timestamps: $filename\n" if $opt_v > 4;
    return (32, "file is too old");	# exit(32)
}


# text_date - find a date: timestamp in the first few lines of a txt file
#
# We look in the first $datelines of a text file for a string of
# the form:
#
#	# date: Xyz Oct dd HH:MM:SS ABC YYYY
#	xx    xxxxx 		xxxxxxxx    xxx... <== x's mark optional fields
#
# NOTE: SS (seconds of minute) default to 0 if it is not given.
#
# or of these forms:
#
#	# date: YYYY/MM/dd hh:mm:ss
#	xx    x           xxxxxxxxxxxx            <== x's mark optional fields
#	# date: YYYY-MM-dd hh:mm:ss
#	xx    x            xxxxxxxxxxxx            <== x's mark optional fields
#	# date: YYYY.MM.dd hh:mm:ss
#	xx    x           xxxxxxxxxxxx            <== x's mark optional fields
#
# NOTE: hh:mm:ss default to 12:00:00 if it is not given
#
# The match is case insensitve.  The leading #(whitespace) is optional.
# The Xyz (day of week) is optional.  The ABC timezone field is optional.
#
# given:
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, =! 0 ==> exit code
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub text_date($)
{
    my ($filename) = @_;	# get arg
    my $line;			# line from the text file
    my $i;

    # firewall - image file must be readable
    #
    if (! -e $filename) {
	return (33, "cannot open");	# exit(33)
    }
    if (! -r $filename) {
	return (34, "cannot read");	# exit(34)
    }

    # open the text file
    #
    print "DEBUG: looking for date in text file: $filename\n" if $opt_v > 4;
    if (! open TEXT, '<', $filename) {
	return (35, "cannot open: $!");	# exit(35)
    }

    # read the 1st $datelines of a file looking for a timestamp
    #
    for ($i=0; $i < $datelines; ++$i) {

	# read a line
	#
	if (! defined($line = <TEXT>)) {
	    return (36, "EOF or text read error");	# exit(36)
	}
	chomp $line;
	print "DEBUG: read text line $i in $filename: $line\n" if $opt_v > 6;

	# look for a date string of the form:
	#
	#	# date: Xyz Oct dd HH:MM:SS ABC YYYY
	#	xx    xxxxx 		xxxxxxxx    xxx... <== optional fields
	#
	# NOTE: SS (seconds of minute) default to 0 if it is not given.
	#
	if ($line =~  m{
		      ^
		      (\#\s*)?	# 1: optional # space (ignored)
		      date(:)?	# 2: date with optional : (ignored)
		      (\s*\S+)?	# 3: day of week (ignored)
		      \s+
		      (\S+)	# 4: short name of month
		      \s+
		      (\d+)	# 5: day of month
		      \s+
		      (\d+)	# 6: hour of day
		      :
		      (\d+)	# 7: minute of hour
		      (:\d+)?	# 8: optional :seconds (defaults to "00")
		      (\s+\S+)?	# 9: optional timezone (ignored)
		      \s+
		      (\d{4})	# 10: 4 digit year
		      }ix) {

	    my $sec = $8;	# seconds or 0 if not given
	    my $min = $7;	# minite of hour
	    my $hour = $6;	# hour of day
	    my $mday = $5;	# day of month
	    my $monname = $4;	# short name of month
	    my $mon = -1;	# month of year [0..11]
	    my $year = $10;	# year
	    my $timestamp;	# date string coverted into a timestamp
	    print "DEBUG: #1 parsed $year-$monname-$mday $hour:$min",
	    	  (defined $sec ? $sec : ""), "\n" if $opt_v > 6;

	    # convert short name of month to month number [0..11]
	    #
	    print "DEBUG: line $i, found possible date string in $filename: ",
	    	   "$line\n" if $opt_v > 5;
	    foreach ( keys %mname ) {
		$mon = $mname{$_} if $monname =~ /^$_$/i;
	    }
	    if ($mon < 0) {
		print "DEBUG: ignoring bad month name $monname on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }

	    # fix seconds, the above regexp prepends a : or undefs it
	    #
	    if (defined $sec) {
		$sec =~ s/\D//g;
	    } else {
		$sec = 0;
	    }

	    # convert fields to a timestamp
	    #
	    printf("DEBUG: #1 using timestamp for %04d-%02d-%02d %02d:%02d:%02d\n",
	    	   $year, $mon, $mday, $hour, $min, $sec) if $opt_v > 6;
	    $timestamp = timegm_nocheck($sec, $min, $hour, $mday, $mon, $year);
	    if (! defined $timestamp) {
		print "DEBUG: #1 ignoring malformed date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }
	    if ($timestamp < $mintime) {
		print "DEBUG: #1 ignoring very early date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }

	    # return the timestamp according to this date line we read
	    #
	    return (0, $timestamp);

	# look for a date string of the form:
	#
	#	# date: YYYY/MM/dd hh:mm:ss
	#	xx    x           xxxxxxxxxxxx     <== x's mark optional fields
	#
	#	# date: YYYY-MM-dd hh:mm:ss
	#	xx    x           xxxxxxxxxxxx     <== x's mark optional fields
	#
	#	# date: YYYY.MM.dd hh:mm:ss
	#	xx    x           xxxxxxxxxxxx     <== x's mark optional fields
	#
	# NOTE: hh:mm:ss default to 12:00:00 if it is not given
	#
	} elsif ($line =~  m{
		      ^
		      (\#\s*)?	# 1: optional # space (ignored)
		      date(:)?	# 2: date with optional : (ignored)
		      \s+
		      (\d{4})	# 3: 4 digit year
		      [/.-]
		      (\d{2})	# 4: 2 digit month of year [01-12]
		      [/.-]
		      (\d{2})	# 5: 2  2 digit day of month [01-31]
		      (\s+\d{2}:\d{2}:\d{2})?	# 6: optional hh:mm:ss timestamp
		      }ix) {

	    my $sec;		# seconds of minute
	    my $min;		# minite of hour
	    my $hour;		# hour of day
	    my $timeofday = $6;	# optional hh:mm:ss timestamp
	    my $mday = $5;	# day of month
	    my $mon = $4;	# month of year [01-12]
	    my $year = $3;	# year
	    my $timestamp;	# date string coverted into a timestamp
	    print "DEBUG: #2 parsed $year-$mon-$mday",
	    	  (defined $timeofday ? $timeofday : ""), "\n" if $opt_v > 6;

	    # parse timeofday, if given
	    #
	    if (defined $timeofday && 
	    	$timeofday =~ m{\s+(\d{2}):(\d{2}):(\d{2})$}) {
		$hour = $1;
		$min = $2;
		$sec = $3;
	    } else {
		# no time of day, use noon
		$hour = 12;
		$min = 0;
		$sec = 0;
	    }

	    # convert fields to a timestamp
	    #
	    printf("DEBUG: #2 using timestamp for %04d-%02d-%02d %02d:%02d:%02d\n",
	    	   $year, $mon, $mday, $hour, $min, $sec) if $opt_v > 6;
	    $timestamp = timegm_nocheck($sec, $min, $hour, $mday, $mon, $year);
	    if (! defined $timestamp) {
		print "DEBUG: #2 ignoring malformed date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }
	    if ($timestamp < $mintime) {
		print "DEBUG: #2 ignoring very early date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }

	    # return the timestamp according to this date line we read
	    #
	    return (0, $timestamp);
	}
    }

    # no date stamp found
    #
    return (37, "no date stamp found in initial lines");
}


# form_dir - ensure that a directory exists and is writable
#
# given:
#	$dirname	directory to name
#
# returns:
#	($code, $errmsg)
#	$code:	0 ==> error, >0 ==> error
#	$errmsg: error code or undef ==> OK
#
sub form_dir($)
{
    my ($dir_name) = @_;	# get args

    # setup the destination directory if needed
    #
    if (-e $dir_name && ! -d $dir_name) {
	print STDERR "$0: is a non-directory: $dir_name\n";
	return (35, "is a non-directory");	# exit(35)
    }
    if (! -d $dir_name) {
	print "DEBUG: will try to mkdir: $dir_name\n" if $opt_v > 1;
        if (! mkdir($dir_name, 0775)) {
	    print STDERR "$0: cannot mkdir: $dir_name: $!\n";
	    return (36, "cannot mkdir");	# exit(36)
	} elsif (! -w $dir_name) {
	    print STDERR "$0: directory is not writable: $dir_name\n";
	    return (37, "directory is not writable");	# exit(37)
	}
    }
    # all is OK
    return (0, undef);
}


# roll_setup - setup and/or increment the .exifroll EXIF roll number file
#
# uses these globals:
#
#	$rollfile	see -r in program usage at top
#	$rollnum	EXIF roll number
#
sub roll_setup()
{
    # process an existing ~/.exifroll file
    #
    $rollnum = "000";	# default initial roll number
    if (-e $rollfile) {

	# firewall - must be readable
	#
	if (! -r $rollfile) {
	    print STDERR "$0: cannot read exifroll file: $rollfile\n";
	    exit(31);
	} elsif (! -w $rollfile) {
	    print STDERR "$0: cannot write exifroll file: $rollfile\n";
	    exit(32);
	}

	# open ~/.exifroll file
	#
	if (! open EXIFROLL, '<', $rollfile) {
	    print STDERR "$0: cannot open for reading exifroll: ",
	    		 "$rollfile: $!\n";
	    exit(33);
	}

	# read only the first line
	#
	$rollnum = <EXIFROLL>;
	chomp $rollnum;
	close EXIFROLL;

	# assume roll number of 000 if bad line or no line
	#
	if ($rollnum !~ /^\d{3}$/) {
	    print STDERR "$0: Warning: invalid roll number in $rollfile\n";
	    print STDERR "$0: will use roll number 000 instead\n";
	    $rollnum = "000";
	}
    }

    # write the next roll numner into ~/.exifroll
    #
    print "DEBUG: will use roll number: $rollnum\n" if $opt_v > 0;
    if (! open EXIFROLL, '>', $rollfile) {
	print STDERR "$0: cannot open for writing exifroll: $rollfile: $!\n";
	exit(34);
    }
    if ($rollnum > 999) {
	if (! print EXIFROLL "000\n") {
	    print "DEBUG: nexr roll number will be 000\n" if $opt_v > 1;
	} else {
	    print STDERR "$0: cannot write 000 rollnum ",
	    		 "to exifroll: $rollfile: $!\n";
	    exit(35);
	}
    } else {
	if (printf EXIFROLL "%03d\n", $rollnum+1) {
	    print "DEBUG: next roll number will be ",
	    	sprintf("%03d", $rollnum+1), "\n" if $opt_v > 1;
	} else {
	    print STDERR "$0: cannot write next rollnum ",
	    		 "to exifroll: $rollfile: $!\n";
	    exit(36);
	}
    }
    close EXIFROLL;
    return;
}
