#!/usr/bin/perl -wT
#
# exifrename - copy files based on EXIF or file time data
#
# @(#) $Revision: 1.8 $
# @(#) $Id: exifrename.pl,v 1.8 2005/06/14 17:56:34 chongo Exp chongo $
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
use vars qw($opt_h $opt_v $opt_o $opt_m $opt_t $opt_c $opt_e $opt_r);
use Getopt::Long;
use Image::ExifTool qw(ImageInfo);
use POSIX qw(strftime);
use File::Find;
no warnings 'File::Find';
use File::Copy;
use File::Compare;

# version - RCS style *and* usable by MakeMaker
#
my $VERSION = substr q$Revision: 1.8 $, 10;
$VERSION =~ s/\s+$//;

# my vars
#
my $srcdir;	# source of image files
my $destdir;	# where the renamed files will be copied
my $destdev;	# device of $destdir
my $destino;	# inode numner of $destdir
my $rollnum;	# EXIF roll number
my $exiftool;	# Image::ExifTool object

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
my $usage = "$0 [-c][-e][-m][-o][-r rollfile][-t] [-h][-v lvl] srcdir destdir";
my $help = qq{\n$usage

	-c	     don't verify/compare files after they are copied (def: do)
	-e	     don't abort on fatal errors (def: exit)
	-m	     move, do not copy files from srcdir to destdir (def: copy)
	-o	     overwrite, don't add _# after time on duplicates (def: add)
	-r rollfile  read EXIF rull number of rollfile (def: ~/.exifroll)
	-t	     don't touch modtime to match EXIF/file image (def: do)

	-h	     print this help message
	-v 	     verbose / debug level

	srcdir	     source directory
	destdir	     destination directory

    NOTE:
	exit 0	all is OK
	exit >0 some fatal error
};
my %optctl = (
    "c" => \$opt_c,
    "e" => \$opt_e,
    "h" => \$opt_h,
    "m" => \$opt_m,
    "o" => \$opt_o,
    "r=s" => \$opt_r,
    "t" => \$opt_t,
    "v=i" => \$opt_v,
);


# function prototypes
#
sub wanted();
sub dir_setup();
sub exif_setup();
sub timestamp($$);
sub exif_date($$);
sub file_date($);
sub form_dir($);
sub roll_setup();


# setup
#
MAIN: {
    my %find_opt;		# File::Find directory tree walk options

    # setup
    #
    select(STDOUT);
    $| = 1;

    # set the defaults
    #
    $opt_v = 0;
    $ENV{HOME} = "/" unless defined $ENV{HOME};
    $opt_r = "$ENV{HOME}/.exifroll";

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
    $srcdir = $ARGV[0];
    $destdir = $ARGV[1];
    print "DEBUG: srcdir: $srcdir\n" if $opt_v > 0;
    print "DEBUG: destdir: $destdir\n" if $opt_v > 0;
    print "DEBUG: ~/exifroll: $opt_r\n" if $opt_v > 0;

    # setup to walk the srcdir
    #
    $find_opt{wanted} = \&wanted; # call this on each non-pruned node
    $find_opt{bydepth} = 0;	# walk from top down, not from bottom up
    $find_opt{follow} = 0;	# do not follow symlinks
    $find_opt{no_chdir} = 0;	# OK to chdir as we walk the tree
    $find_opt{untaint} = 1;	# untaint dirs we chdir to
    # NOTE: We will only cd into dirs whose name is only [-+@\w./] chars
    $find_opt{untaint_pattern} = qr|^([-+@\w./]+)$|; # untaint pattern
    $find_opt{untaint_skip} = 1; # we will skip any dir that is tainted

    # untaint $srcdir and $destdir
    #
    if ($srcdir =~ /$find_opt{untaint_pattern}/) {
    	$srcdir = $1;
    } else {
	print STDERR "$0: bogus chars in srcdir\n";
	exit(5);
    }
    if ($destdir =~ /$find_opt{untaint_pattern}/) {
    	$destdir = $1;
    } else {
	print STDERR "$0: bogus chars in destdir\n";
	exit(6);
    }

    # setup directories
    #
    dir_setup();

    # initialize roll serial number $rollnum
    #
    roll_setup();

    # setup ExifTool
    #
    $exiftool = exif_setup();

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
#	$desdir		where copied and renamed files go
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
    ($errcode, $errmsg) = form_dir($destdir);
    if ($errcode != 0) {
	print STDERR "$0: mkdir error: $errmsg for $destdir\n";
	exit(11);
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
#	$desdir		where copied and renamed files go
#	$rollnum	EXIF roll number
#	$exiftool	Image::ExifTool object
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
#    /destdir/200505/043-101/200505-043-101-12-152545-ls1f5627.cr2
#
# The created file path is:
#
#	/destdir			# destdir path of image library
#	/200505				# image year & month
#	/043-101			# roll-subdir
#	/200505-043-101-12-152545-ls1f5627.cr2	# image filename (see below)
#
# The filename itself:
#
#	200505-043-101-12-152545-ls1f5627.cr2
#
# If another image was taken during the same second, its name becomes:
#
#	200505-043-101-12-152545_1-ls1f5628.cr2
#
# is constructed out of the following:
#
#	2005			# image 4 digit Year
#	05			# image month, 2 digits [01-12]
#	-			# (dash) 1st separator
#	043			# roll number, 3 digits, 0 padded
#	-			# (dash) 2nd separator
#	101			# lowercase top subdir w/o -'s, or empty
#				# and eos\w+ suffix removed
#	-			# (dash) 3rd separator
#	12			# image day of month, 2 digits [01-31]
#	-			# (dash) 4th separator
#	15			# image hour (UTC), 2 digits [00-23]
#	25			# image minute of hour, 2 digits [00-59]
#	45			# image seconf of minites, 2 digits [00-60]
#	     _			# (underscore) optional for dups in same sec
#	     9			# optional digits for dups in same sec
#	-			# (dash) 5th separator
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
# XXX - tie non image files to their image parent dates?
#
sub wanted()
{
    my $filename = $_;		# current filename within $File::Find::dir
    my $pathname;		# complete path $File::Find::name
    my $nodedev;		# device of the current file
    my $nodeino;		# inode number of the current file
    my $roll_sub;		# roll-subdir
    my ($errcode, $errmsg);	# form_dir return values

    # canonicalize the path by removing leading ./ and multiple //'s
    #
    print "DEBUG: wanted filename: $filename\n" if $opt_v > 3;
    print "DEBUG: wanted given $File::Find::name\n" if $opt_v > 2;
    ($pathname = $File::Find::name) =~ s|^(\./)+||;
    $pathname =~ s|//+|/|g;
    print "DEBUG: ready to process $pathname\n" if $opt_v > 1;

    # prune out anything that is not a directory or file
    #
    if (! -d $filename && ! -f $filename) {
	# skip non-dir/non-files
	print "DEBUG: prune #0 $pathname\n" if $opt_v > 2;
	$File::Find::prune = 1;
	return;
    }

    # prune out certain top level paths
    #
    # As notied in detail above, we will prune off any .Trashes,
    # .comstate.tof that are directly under $srcdir
    #
    if ($pathname eq "$srcdir/.Trashes" ||
        $pathname eq "$srcdir/.comstate.tof") {
	# skip this useless camera node
	print "DEBUG: prune #2 $pathname\n" if $opt_v > 2;
	$File::Find::prune = 1;
	return;
    }

    # prune out .DS_Store files
    #
    if ($filename eq ".DS_Store") {
	# skip OS X .DS_Store files
	print "DEBUG: ignore #3 $pathname\n" if $opt_v > 2;
	$File::Find::prune = 1;
	return;
    }

    # ignore (but not prune) . and ..
    #
    if ($filename eq "." || $filename eq "..") {
	# ignore but do not prune . and ..
	print "DEBUG: ignore #4 $pathname\n" if $opt_v > 2;
    	return;
    }

    # If we are at /$srcdir/DCIM, then just return (don't prune)
    # because we want to look at images below DCIM
    #
    if ($pathname eq "$srcdir/DCIM") {
	# ignore but do not prune /DCIM
	print "DEBUG: ignore #5 $pathname\n" if $opt_v > 2;
    	return;
    }

    # Determine the top level directory under $srcdir/DCIM or $srcdir,
    # in lowercase without -'s
    #
    if ($pathname =~ m|^$srcdir/DCIM/(.+)/$|o) {
	$roll_sub = $1;
    } elsif ($pathname =~ m|^$srcdir/(.+)/$|o) {
	$roll_sub = $1;
    } elsif ($pathname =~ m|^$srcdir/(.+)$|o) {
	$roll_sub = "";
    } else {
	print STDERR "$0: Fatal $pathname not under $srcdir\n";
	print "DEBUG: prune #13 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(13) unless defined $opt_e;
	return;
    }
    $roll_sub = tr/[A-Z]/[a-z]/;	# conver to lower case
    $roll_sub =~ s/eos\w+$//;	# remove common EOS trailing chars
    $roll_sub =~ s/-//g;	# no extra -'s
    $roll_sub = "$rollnum-$roll_sub";
    print "DEBUG: top level subdir: $roll_sub\n" if $opt_v > 2;

    # file processing
    #
    if (-f $filename) {
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

	# determine the date of the image by EXIF or filename date
	#
	($datecode, $datestamp) = timestamp($exiftool, $filename);
	if ($datecode != 0) {
	    print STDERR "$0: Fatal: EXIF image timestamp error $datecode: ",
	    		 "$datestamp\n";
	    print "DEBUG: prune #15 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(15) unless defined $opt_e;
	    return;
	}
	print "DEBUG: EXIF image / file timestamp: $datestamp\n" if $opt_v > 3;

	# canonicalize the filename
	#
	($lowerfilename = $filename) =~ tr /[A-Z]/[a-z]/;	# lower case

	# If the lowercase name is already of the form:
	#
	#	200505-043-101-12-152545_1-ls1f5628.cr2
	#
	# convert it to just ls1f5628.cr2 so that we won't keep adding
	# date strings to the filename.
	#
	if ($lowerfilename =~ /^\d{6}-\d{3}-[^-]+-\d{2}-\d{6}(_\d+)?-(.*)$/) {
	    $lowerfilename = $2;
	}

	# Remove any -'s in the lowercase name so as to not confuse
	# a filename field parser.
	#
	$lowerfilename =~ s/-//g;

	# convert the timestamp into date strings
	#
	$yyyymm = strftime("%Y%m", gmtime($datestamp));
	$dd = strftime("%d", gmtime($datestamp));

	# ensure the $destdir/yyyymm/rol-sub direct path exists
	#
	($errcode, $errmsg) = form_dir("$destdir/$yyyymm");
	if ($errcode != 0) {
	    print STDERR "$0: Fatal: mkdir error: $errmsg for ",
	    		 "$destdir/$yyyymm\n";
	    print "DEBUG: prune #16 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(16) unless defined $opt_e;
	    return;
	}
	($errcode, $errmsg) = form_dir("$destdir/$yyyymm/$roll_sub");
	if ($errcode != 0) {
	    print STDERR "$0: Fatal: mkdir error: $errmsg for ",
	    		 "$destdir/$yyyymm/$roll_sub\n";
	    print "DEBUG: prune #17 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(17) unless defined $opt_e;
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
	    $destname = "$yyyymm-$roll_sub-$dd-$hhmmss_d-$lowerfilename";
	    $destpath = "$destdir/$yyyymm/$roll_sub/$destname";

	    # prep for next cycle if destination already exits
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
		print "DEBUG: prune #18 $pathname\n" if $opt_v > 0;
		$File::Find::prune = 1;
		exit(18) unless defined $opt_e;
		return;
	    }
	} while (-e "$destpath");
	print "DEBUG: destination: $destname\n" if $opt_v > 1;
	print "DEBUG: destination path: $destpath\n" if $opt_v > 2;

	# copy (or move of -m) the image file
	#
	if (defined $opt_m) {
	    if (move($pathname, $destpath) == 0) {
		print STDERR "$0: Fatal: in ", $File::Find::dir, ": ",
			     "mv $filename $destpath failed: $!\n";
		print "DEBUG: prune #20 $pathname\n" if $opt_v > 0;
		$File::Find::prune = 1;
		exit(20) unless defined $opt_e;
		return;
	    }
	} else {
	    if (copy($pathname, $destpath) == 0) {
		print STDERR "$0: Fatal: in ", $File::Find::dir, ": ",
			     "cp $filename $destpath failed: $!\n";
		print "DEBUG: prune #21 $pathname\n" if $opt_v > 0;
		$File::Find::prune = 1;
		exit(21) unless defined $opt_e;
		return;
	    }
	}

	# compare unless -t
	#
	if (! defined $opt_c && compare($pathname, $destpath) != 0) {
	    print STDERR "$0: Fatal: in ", $File::Find::dir, ": ",
			 "compare of $filename and $destpath failed\n";
	    print "DEBUG: prune #22 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(22) unless defined $opt_e;
	    return;
	}

	# set the access and modification time unless -t
	#
	if (! defined $opt_t) {
	    utime $datestamp, $datestamp, $destpath;
	}
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
    my %exifoptions;			# ExifTool options
    my $exif_tool;			# Image::ExifTool object

    # setup ExifTool options
    #
    $exifoptions{Binary} = 0;		# no timestamp is a binary field
    $exifoptions{PrintConv} = 0;	# no need to waste time converting
    $exifoptions{Unknown} = 0;		# all timestamps are in known fields
    $exifoptions{DateFormat} = "\%s";	# timestamps as seconds since the Epoch
    $exifoptions{Duplicates} = 0;	# use the last timestamp if we have dups

    # create a new Image::ExifTool object
    #
    $exif_tool = new Image::ExifTool;

    # set the ExifTool options
    #
    $exif_tool->Options(%exifoptions);
    return $exif_tool;
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
# given:
#	$exiftool	Image::ExifTool object
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, else ==> exit code
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub timestamp($$)
{
    my ($exiftool, $filename) = @_;	# get args
    my $noext;			# filename without any extension
    my $exif_file;		# a potential EXIF related filename
    my $extension;		# a potential EXIF related file extension
    my $errcode;		# 0 ==> OK
    my $timestamp = -1;	# seconds since the epoch of early tstamp or -1

    # try to get an EXIF based timestamp
    #
    ($errcode, $timestamp) = exif_date($exiftool, $filename);
    if ($errcode == 0) {
	print "DEBUG: EXIF timestamp for $filename: $timestamp\n" if $opt_v > 4;
	return (0, $timestamp);
    }
    print "DEBUG: EXIF timestamp $filename: error: $errcode: ",
    	  "$timestamp\n" if $opt_v > 4;

    # look for related files that might have EXIF data
    #
    ($noext = $filename) =~ s|\.[^./]*$||;
    foreach $extension ( @exif_ext ) {

	# Look for a related readable file that is likely to have
	# EXIF data in it ... and only if that related filename
	# is not exactly the same as our filename argument.
	$exif_file = "$noext.$extension";
	if ($exif_file ne $filename && -r $exif_file) {
	    my $errcode;		# 0 ==> OK
	    my $timestamp;		# timestamp or error msg

	    # try to get an EXIF based timestamp
	    #
	    print "DEBUG: looking at related filename: $exif_file\n"
	    	if $opt_v > 4;
	    ($errcode, $timestamp) = exif_date($exiftool, $exif_file);

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

    # use the file method and return whatever it says
    #
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
#	$exiftool	Image::ExifTool object
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, else ==> could not get an EXIF timestamp
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub exif_date($$)
{
    my ($exiftool, $filename) = @_;	# get args
    my $info;		# exiftool extracted EXIF information
    my $tag;		# EXIF tag name
    my $timestamp = -1;	# seconds since the epoch of early tstamp or -1

    # firewall - image file must be readable
    #
    if (! -e $filename) {
	# NOTE: exit(24) for unable to open filename
	return (24, "cannot open");
    }
    if (! -r $filename) {
	# NOTE: exit(25) for unable to read filename
	return (25, "cannot read");
    }

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($filename, @tag_list);
    if (! defined $info || defined $$info{Error}) {
	# failure to get a EXIF data
	if (defined $$info{Error}) {
	    return (26, "EXIF data error: $$info{Error}");
        } else {
	    return (27, "no EXIF data");
	}
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
    if ($timestamp < 0) {
	return (28, "no timestamp in EXIF data");
    }

    # Avoid very old EXIF timestamps
    #
    if ($timestamp < $mintime) {
	return (29, "timestamp: $timestamp < min: $mintime");
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
	# NOTE: exit(26) for unable to open filename
	return (26, "cannot open");
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
    return (30, "file is too old");
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
    my ($dir_name) = $_;	# get args

    # setup the destination directory if needed
    #
    if (-e $dir_name && ! -d $dir_name) {
	print STDERR "$0: is a non-directory: $dir_name\n";
	# NOTE: exit(28): non-directory
	return (31, "is a non-directory");
    }
    if (! -d $dir_name) {
	print "DEBUG: will try to mkdir: $dir_name\n" if $opt_v > 1;
        if (! mkdir($dir_name, 0775)) {
	    print STDERR "$0: cannot mkdir: $dir_name: $!\n";
	    # NOTE: exit(29): mkdir error
	    return (32, "cannot mkdir");
	} elsif (! -w $dir_name) {
	    print STDERR "$0: directory is not writable: $dir_name\n";
	    # NOTE: exit(30): dir not writbale
	    return (33, "directory is not writable");
	}
    }
    # all is OK
    return (0, undef);
}


# roll_setup - setup and/or increment the .exifroll EXIF roll number file
#
# uses these globals:
#
#	$opt_r		see -r in program usage at top
#	$rollnum	EXIF roll number
#
sub roll_setup()
{
    # process an existing ~/.exifroll file
    #
    $rollnum = "000";	# default initial roll number
    if (-e $opt_r) {

	# firewall - must be readable
	#
	if (! -r $opt_r) {
	    print STDERR "$0: cannot read exifroll file: $opt_r\n";
	    exit(31);
	} elsif (! -w $opt_r) {
	    print STDERR "$0: cannot write exifroll file: $opt_r\n";
	    exit(32);
	}

	# open ~/.exifroll file
	#
	if (! open EXIFROLL, 'r', $opt_r) {
	    print STDERR "$0: cannot open for reading exifroll: $opt_r: $!\n";
	    exit(33);
	}

	# read only the first line
	#
	$rollnum = <EXIFROLL>;
	close EXIFROLL;

	# assume roll number of 000 if bad line or no line
	#
	if ($rollnum !~ /^\d{3}$/) {
	    print STDERR "$0: Warning: invalid roll number in $opt_r\n";
	    print STDERR "$0: will use roll number 000 instead\n";
	    $rollnum = "000";
	}
    }

    # write the next roll numner into ~/.exifroll
    #
    if (! open EXIFROLL, 'w', $opt_r) {
	print STDERR "$0: cannot open for writing exifroll: $opt_r: $!\n";
	exit(34);
    }
    if ($rollnum > 999) {
	if (! print EXIFROLL "000", "\n") {
	    print STDERR "$0: cannot write 000 rollnum ",
	    		 "to exifroll: $opt_r: $!\n";
	    exit(35);
	}
    } else {
	if (! print EXIFROLL $rollnum+1, "\n") {
	    print STDERR "$0: cannot write next rollnum ",
	    		 "to exifroll: $opt_r: $!\n";
	    exit(36);
	}
    }
    close EXIFROLL;
    print "DEBUG: roll number: $rollnum\n" if $opt_v > 0;
    return;
}
