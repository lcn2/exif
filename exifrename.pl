#!/usr/bin/perl -wT
#
# exifrename - copy files based on EXIF or file time data
#
# @(#) $Revision: 2.7 $
# @(#) $Id: exifrename.pl,v 2.7 2006/07/16 19:32:07 chongo Exp chongo $
# @(#) $Source: /usr/local/src/cmd/exif/RCS/exifrename.pl,v $
#
# Copyright (c) 2005-2006 by Landon Curt Noll.  All Rights Reserved.
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
use vars qw($opt_h $opt_v $opt_o $opt_m $opt_t $opt_c $opt_a $opt_e
            $opt_s $opt_r $opt_n $opt_y $opt_z $opt_k);
use Getopt::Long;
use Image::ExifTool qw(ImageInfo);
use POSIX qw(strftime);
use File::Find;
no warnings 'File::Find';
use File::Copy;
use File::Compare;
use File::Basename;
use Time::Local qw(timegm_nocheck timegm);
use Cwd qw(abs_path);

# version - RCS style *and* usable by MakeMaker
#
my $VERSION = substr q$Revision: 2.7 $, 10;
$VERSION =~ s/\s+$//;

# my vars
#
my $srcdir;	# source of image files
my $destdir;	# where the renamed files will be copied
my $destdev;	# device of $destdir
my $destino;	# inode number of $destdir
my $rollnum;	# EXIF roll number
my $exiftool;	# Image::ExifTool object
# NOTE: We will only cd into paths whose name is not tainted
my $untaint = qr|^([-+\w\s./]+)$|; 	# untainting path pattern
my $untaint_file = qr|^([-+\w\s.]+)$|; 	# untainting pattern w/o the /
my $datelines = 16;	# date: must be in the 1st datelines of a file
my %mname = (
    "Jan" => 0, "Feb" => 1, "Mar" => 2, "Apr" => 3, "May" => 4, "Jun" => 5,
    "Jul" => 6, "Aug" => 7, "Sep" => 8, "Oct" => 9, "Nov" => 10, "Dec" => 11,
);
my $roll_sub_maxlen = 3;	# max length of a roll_sub (0 ==> unlimited)
my $roll_sub_skip = 0;	# ignore this many leading chars when forming a roll_sub
my $rollfile;		# file that keeps track of next roll number
my $mv_fwd_chars = 4;	# chars after initial -z skchars put near filename front
my $mv_end_chars = 4;	# initial -z skchars put near end of filename
my $readme_path = undef;	# if -r readme, this is the absolute src path
my $readme_dev = undef;		# if -r readme, this is the device number
my $readme_ino = undef;		# if -r readme, this is the inode number
my $readme_timestamp = undef;	# if -r readme, this is its special timestamp


# EXIF timestamp related tag names to look for
#
my @tag_list = qw( ModifyDate DateTimeOriginal CreateDate );

# file extensions, in priority order, that are likely to
# contain EXIF data
#
my @exif_ext = qw(
    cr2 raw tif tiff jpg jpeg png gif psd eps
);

# hash of potential files found walking $srcdir giving basename
#
# $path_basenoext{$path}
#	key: source path
#	value: basename of $path w/o .ext
#
# $path_roll_sub{$path}
#	key: source path
#	value: roll number subdirectory (roll_sub) or undef
#	NOTE: undef ==> put file under 2nd level directory, not 3rd
#
# $devino_path{"file_dev/file_inum"}
#	key: file device number + / (slash) + file inode number
#	value: path
#	NOTE: Use to detect hard links / duplicate files
#
# $path_filetime{$path}
#	key: source path
#	value: file non-EXIF timestamp
#	NOTE: This is not the EXIF data derived timestamp.
#
# $need_plus{$path}
#	key: source path
#	value: 0 ==> use -, 1 ==> multiple found, use +
#	NOTE: destination files use a - or + as a separator between the 1st
#	      and 3nd fields in the filename.  A + indicates that the file
#	      is part of a set of files that share the same basename but
#	      with different .extensions.
#
# $basenoext_pathset{$basenoext}
#	key: basename of $path w/o .ext
#	value: array of paths with dup base w/o .ext
#
# $pathset_timestamp{$basenoext}
#	key: basename of $path w/o .ext
#	value: timestamp basename of $path w/o .ext
#
# $path_destdir{$path}
#	key: source path
#	value: full path of where to place destination file
#
# $path_destfile{$path}
#	key: source path
#	value: complete basename of the destination filename
#	NOTE: final destination is "$path_destdir{$path}/$path_destfile{$path}"
#
#
my %path_basenoext;
my %path_roll_sub;
my %devino_path;
my %path_filetime;
my %need_plus;
my %basenoext_pathset;
my %pathset_timestamp;
my %path_destdir;
my %path_destfile;

# timestamps prior to:
#	Tue Nov  5 00:53:20 1985 UTC
# are too old for an image with EXIF data.   See:
#	perl -e 'my $x=500000000; print scalar gmtime($x), "\n";'
#
my $mintime = 500000000;

# usage and help
#
my $usage = "$0 [-a] [-c] [-e exifroll] [-k roll_subskip] [-m] [-n rollnum]\n" .
    "    [-o] [-r readme] [-s roll_sublen] [-t] [-y seqlen] [-z skchars]\n" .
    "    [-h] [-v lvl] srcdir destdir";
my $help = qq{\n$usage

    -a           don't abort/exit after post-setup fatal errors (def: do)
    -c           don't verify/compare files after they are copied (def: do)
    -e exifroll  read roll number from exifroll (def: ~/.exifroll)
    -k roll_subskip	 skip the leading roll_subskip chars (def: 0)
    -m           move, do not copy files from srcdir to destdir (def: copy)
    -n rollnum   roll is rollnum, don't update exifroll (def: use ~/exifroll)
    -o           overwrite, don't add _# after time on duplicates (def: add)
    -r readme    add readme as if it was srcdir/readme.txt (def: don't)
    -s roll_sublen	max length of roll_sub (def: 3, 0 ==> unlimited)
    -t           don't touch modtime to match EXIF/file image (def: do)
    -y seqlen    sequence length, image filename chars after skchars (def: 4)
    -z skchars    initial image-name chars not part of sequence number (def: 4)

    -h           print this help message
    -v lvl       set verbose / debug level to lvl (def: 0)

    srcdir       source directory
    destdir      destination directory

    NOTE: exit 0 means all is OK, exit >0 means some fatal error

    Version: $VERSION};
my %optctl = (
    "a" => \$opt_a,
    "e=s" => \$opt_e,
    "c" => \$opt_c,
    "h" => \$opt_h,
    "k=i" => \$opt_k,
    "m" => \$opt_m,
    "n=s" => \$opt_n,
    "o" => \$opt_o,
    "r=s" => \$opt_r,
    "t" => \$opt_t,
    "s=i" => \$opt_s,
    "v=i" => \$opt_v,
    "y=i" => \$opt_y,
    "z=i" => \$opt_z,
);


# function prototypes
#
sub parse_args();
sub destdir_path($$$);
sub dir_setup();
sub wanted();
sub determine_destname();
sub get_timestamp($);
sub exif_date($);
sub text_date($);
sub form_dir($);
sub roll_setup();
sub readme_check($);

sub old_file_date($);	# XXX - remove when code complete
sub old_timestamp($);	# XXX - remove when code complete
sub old_wanted();	# XXX - remove when code complete


# setup
#
MAIN:
{
    my %find_opt;	# File::Find directory tree walk options
    my %exifoptions;	# Image::ExifTool options
    my $basename_noext;	# pathset basename without .extension
    my $err;		# >0 ==> fatal error number, 0 ==> OK

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
    parse_args();

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
	print STDERR "$0: FATAL: bogus chars in srcdir\n";
	exit(9);
    }
    if ($destdir =~ /$untaint/o) {
    	$destdir = $1;
    } else {
	print STDERR "$0: FATAL: bogus chars in destdir\n";
	exit(10);
    }
    if ($rollfile =~ /$untaint/o) {
    	$rollfile = $1;
    } else {
	print STDERR "$0: FATAL: bogus chars in -e filename\n";
	exit(11);
    }

    # initialize roll serial number $rollnum
    #
    roll_setup();

    # setup ExifTool options
    #
    $exifoptions{Binary} = 0;		# no timestamp is a binary field
    $exifoptions{PrintConv} = 1;	# we will need to convert timestamps
    $exifoptions{Unknown} = 0;		# ignore unknown fields
    $exifoptions{DateFormat} = '%s';	# timestamps as seconds since the Epoch
    $exifoptions{Duplicates} = 0;	# use last tag if we have dup tags
    $exiftool = new Image::ExifTool;
    $exiftool->Options(%exifoptions);

    # walk the srcdir collecting information about useful paths of files
    #
    # NOTE: See the wanted() function for details.
    #
    find(\%find_opt, $srcdir);

    # determine the timestamp for each pathset
    #
    # We will try to process all files and exit after if we had any errors
    #
    $err = 0;
    foreach $basename_noext ( keys %basenoext_pathset ) {
	$pathset_timestamp{$basename_noext} =
	  get_timestamp($basenoext_pathset{$basename_noext});
	if (! defined $pathset_timestamp{$basename_noext}) {
	    print STDERR "$0: FATAL: no valid EXIF timestamp and file ",
	       "timestamp(s) too old for pathset: ",
	       "$basename_noext\n" if $opt_v > 0;
	    err = 12;
	}
    }
    exit($err) if ($err > 0);

    # add in readme.txt if -r readme was given
    #
    if (defined $readme_path && defined $readme_timestamp &&
        defined $readme_dev && defined $readme_ino) {
	$readme_path{$readme_path} = "readme.txt";
	$path_basenoext{$readme_path} = "readme";
	$path_rollsub{$readme_path} = undef;
	$devino_path{"$readme_dev/$readme_ino"} = $readme_path;
	$path_filetime{$readme_path} = $readme_timestamp;
	$need_plus{$readme_path} = 0;
	push(@{$basenoext_pathset{"readme"}, $readme_path);
	$pathset_timestamp{"readme"} = $readme_timestamp;
	# NOTE: $path_destdir{$readme_path} will be filled in by dir_setup();
	print "Debug: added -r readme file: $readme_path\n" if $opt_v > 2;
    }

    # setup directories
    #
    # Fill in %path_destdir and create all destination directories.
    #
    dir_setup();

    # determine desitnation filenames
    #
    determine_destname();

    XXX - more code here

    # all done
    #
    exit(0);
}


# parse_args - parse the command line, set flags and sanity check options
#
sub parse_args()
{
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
	print STDERR "$0: FATAL: -c (compare) conflicts with -m (move)\n";
	exit(2);
    }
    if (! defined $ARGV[0] || ! defined $ARGV[1]) {
	print STDERR "$0: FATAL: missing args\nusage:\n\t$help\n";
	exit(3);
    }
    if (defined $ARGV[2]) {
	print STDERR "$0: FATAL: too many args\nusage:\n\t$help\n";
	exit(4);
    }
    if (defined $opt_e && defined $opt_n) {
	print STDERR "$0: FATAL: -e exifroll conflicts with -n rollnum\n";
	exit(5);
    }
    if (defined $opt_k && $opt_k < 0) {
	print STDERR "$0: FATAL: -k roll_subskip must be >= 0\n";
	exit(6);
    }
    if (defined $opt_s && $opt_s < 0) {
	print STDERR "$0: FATAL: -s roll_sublen must be >= 0\n";
	exit(7);
    }
    if (defined $opt_y && $opt_y < 0) {
	print STDERR "$0: FATAL: -y seqlen must be >= 0\n";
	exit(8);
    }
    if (defined $opt_z && $opt_z < 0) {
	print STDERR "$0: FATAL: -z skchars must be >= 0\n";
	exit(9);
    }
    $roll_sub_maxlen = $opt_s if defined $opt_s;
    $roll_sub_skip = $opt_k if defined $opt_k;
    $rollfile = $opt_e if defined $opt_e;
    # canonicalize srcdir removing leading ./'s, multiple //'s, trailing /'s
    $srcdir = $ARGV[0];
    $srcdir = abs_path($srcdir);
    $srcdir =~ s|^(\./+)+||;
    $srcdir =~ s|//+|/|g;
    $srcdir =~ s|(.)/+$|$1|;
    # canonicalize destdir removing leading ./'s, multiple //'s, trailing /'s
    $destdir = $ARGV[1];
    $destdir = abs_path($destdir);
    $destdir =~ s|^(\./+)+||;
    $destdir =~ s|//+|/|g;
    $destdir =~ s|(.)/+$|$1|;
    $mv_fwd_chars = $opt_y if defined $opt_y;
    $mv_end_chars = $opt_z if defined $opt_z;
    if ($opt_v > 0) {
	print "Debug:";
	print " -a" if defined $opt_a;
	print " -c" if defined $opt_c;
	print " -e $opt_e" if defined $opt_e;
	print " -k $opt_k" if defined $opt_k;
	print " -m" if defined $opt_m;
	print " -n $opt_n" if defined $opt_n;
	print " -o" if defined $opt_o;
	print " -r $opt_r" if defined $opt_r;
	print " -s $opt_s" if defined $opt_s;
	print " -t" if defined $opt_t;
	print " -v $opt_v" if $opt_v > 0;
	print " -y $opt_y" if defined $opt_y;
	print " -z $opt_z" if defined $opt_z;
	print " $srcdir $destdir\n";
    }
    if ($opt_v > 1) {
	print "Debug: won't verify/compare files afterwords\n" if $opt_c;
	print "Debug: won't abort/exit after a fatal error\n" if $opt_a;
	print "Debug: ", ($opt_m ? "move" : "copy"), " files\n";
	print "Debug: ",
		($opt_o ? "override" : "add _# on"),
		" duplicate files\n";
	print "Debug: ~/exifroll file: $rollfile\n";
	print "Debug: roll_sub max length is ",
		($roll_sub_maxlen > 0 ? $roll_sub_maxlen : "unlimited"), "\n";
	print "Debug: ignore the leading $roll_sub_skip chars when forming ",
		"a roll_sub\n";
	print "Debug: ", ($opt_t ? "don't" : "do"), " touch file modtimes\n";
	print "Debug: treating $opt_r as if it was $srcdir/readme.txt\n"
		if $opt_r;
	print "Debug: srcdir: $srcdir\n";
	print "Debug: destdir: $destdir\n";
    }
    # sanity check readme if -r readme was given
    if (defined $opt_r) {
	$readme_path = readme_check($opt_r);
	print "Debug: -r readme file is sane: $opt_r\n" if $opt_v > 1;
	($readme_dev, $readme_ino,) = stat($readme_path);
	if (! defined $readme_dev || ! defined $readme_ino) {
	    print STDERR "$0: FATAL: stat error on $readme_path: $!\n";
	    exit(10);
	}
    }
}


# destdir_path - return the components of the subdirs for a given srcdir path
#
# given:
#	$timestamp	the EXIF or file timestamp of a given path
#	$roll		roll number
#	$roll_sub	part of sub-dir name of lowest directory in src path
#			   or undef
#
# NOTE: In the case of the -r readme.txt file, we the roll_sub will
#	be undef and $dir3 will be undef because that file will
#	do under just $destdir/$dir1/$dir2.
#
# returns:
#	($dir1, $dir2, $dir3) == the 3 directory names for a given path
#	The destination directory will be $destdir/$dir1/$dir2/$dir3.
#
# NOTE: Does not return on error.
#
sub destdir_path($$$)
{
    my ($timestamp, $roll, $roll_sub) = @_;
    my $yyyymm;		# EXIF or filename timestamp UTC year and UTC month

    # convert timestamp into a yyyymm date in UTC
    #
    $yyyymm = strftime("%Y%m", gmtime($timestamp));
    if (defined $yyyymm && $yyyymm =~ /$untaint/o) {
	$yyyymm = $1;
    } else {
	print STDERR "$0: FATAL: strange chars in yyyymm ",
	    "for timestamp: $timestamp\n";
	exit(34);
    }

    # firewall - untaint and sanity check roll number
    #
    if ($roll =~ /$untaint_file/o) {
    	$roll = $1;
    } else {
	print STDERR "$0: FATAL: bogus chars in roll\n";
	exit(45);
    }
    if ($roll =~ /^\s*$/) {
	print STDERR "$0: FATAL: roll is empty or only has whitespace\n";
	exit(45);
    } elsif ($roll =~ /^\./) {
	print STDERR "$0: FATAL: roll start with a .\n";
	exit(45);
    }

    # firewall - untaint and sanity check roll_sub
    #
    if (defined $roll_sub) {
	if ($roll_sub =~ /$untaint_file/o) {
	    $roll_sub = $1;
	} else {
	    print STDERR "$0: FATAL: bogus chars in roll_sub\n";
	    exit(45);
	}
	if ($roll_sub =~ /^\s*$/) {
	    print STDERR "$0: FATAL: roll_sub is empty or ",
	      "only has whitespace\n";
	    exit(45);
	} elsif ($roll_sub =~ /^\./) {
	    print STDERR "$0: FATAL: roll_sub start with a .\n";
	    exit(45);
	}
    } else {
	$roll_sub = undef;
    }

    # return the 3 levels
    #
    return ($yyyymm, $roll, $roll_sub);
}


# dir_setup - setup and/or check on srcdir, destdir and needed destdir subdirs
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
    my @need_subdir;		# directories under $destdir that are needed
    my $path;			# a srcdir path to process
    my $dir1;			# 1st level subdir under destdir
    my $dir2;			# 2nd level subdir under destdir
    my $dir3;			# 3rd level subdir under destdir
    my $err;			# >0 ==> fatal error number, 0 ==> OK

    # firewall - check for a sane srcdir
    #
    if (! -e $srcdir) {
	print STDERR "$0: FATAL: srcdir does not exist: $srcdir\n";
	exit(20);
    }
    if (! -d $srcdir) {
	print STDERR "$0: FATAL: srcdir is not a directory: $srcdir\n";
	exit(21);
    }
    if (! -r $srcdir) {
	print STDERR "$0: FATAL: srcdir is not readable: $srcdir\n";
	exit(22);
    }
    if (! -x $srcdir) {
	print STDERR "$0: FATAL: srcdir is not searchable: $srcdir\n";
	exit(23);
    }

    # setup the destination directory if needed
    #
    ($errcode, $errmsg) = form_dir($destdir);
    if ($errcode != 0) {
	print STDERR "$0: FATAL: destdir mkdir error: $errmsg for $destdir\n";
	exit(24);
    }

    # record the device and inode number of $destdir
    #
    ($destdev, $destino,) = stat($destdir);

    # create, if needed, all the required sub-directories under destdir
    #
    for $path ( keys %path_basenoext ) {

	# get the 3 subdir levels
	#
	# NOTE: In the case of the -r readme.txt file, we the roll_sub will
	#	be undef and $dir3 will be undef because that file will
	#	do under just $destdir/$dir1/$dir2.
	#
	($dir1, $dir2, $dir3) = destdir_path(
	    $pathset_timestamp{$path_basenoext{$path}},
	    $rollnum,
	    $path_roll_sub{$path});

	# add the 3 paths to the set of directories to check
	#
	push($need_subdir, $dir1, "$dir1/$dir2");
	if (defined $dir3) {
	    push($need_subdir, "$dir1/$dir2/$dir3");
	    $path_destdir{$path} = "$dir1/$dir2/$dir3";
	} else {
	    $path_destdir{$path} = "$dir1/$dir2";
	}
	print "Debug: destination of $path is $path_destdir{$path}\n"
	  if $opt_v > 2;
    }

    # now form all of the required destdir subdirs
    #
    $err = 0;
    foreach $path ( sort @need_subdir ) {
    	($errcode, $errmsg) = form_dir("$desitdir/$path");
	if ($errcode != 0) {
	    print STDERR "$0: FATAL: subdir mkdir error: $errmsg ",
	        "for $destdir/path\n";
	    $err = 25;	# delayed exit
	}
    }
    if ($err != 0) {
	exit($err);
    }
    return;
}


# wanted - Find::File calls this to walk the tree collecting filenames
#
# We walk the tree looking for directories.  For those directories
# that are not obvious non-image directories, we collect filenames
# of potential image and meta-image files.
#
# We setup %devino_path for mapping device/inum pairs to paths.
# The %devino_path allows us to determine if we processed the
# same file twice.
#
# We setup the %path_basenoext for mapping paths to basenames w/o .ext.
# For example: $path_basenoext{"/tmp/foo.bar} == "foo".
#
# We fill in %need_plus to mark with paths will need +'s in their
# destination name and with need just -'s.
#
# For each basename of a path w/o .ext, we maintain an array of
# paths for that basename w/o .ext.  If $need_plus{$path} == 1, then
# $basenoext_pathset{$path} will be an array with 2 or more elements.
# If $need_plus{$path} == 0, then $basenoext_pathset{$path} will be
# an array with just 1 element.
#
# We maintain a file timestamp for each path to a file.  This
# timestamp is usually the file create time or file modification time,
# which ever is older.  When selecting the older of create and mod times,
# we ignore those that are older than the minimum timestamp (which is
# Tue Nov  5 00:53:20 1985 UTC).  If both are older than the minimum
# timestamp, we use the older non-zero timestamp.  If both the create
# and modify times are 0, we give up and use 0 as the file timestamp.
# Note that later on elsewhere, files with valid EXIF timestamps will
# override their file timestamps.
#
# We maintain a roll number sub-directory string in %path_roll_sub.  The
# roll_sub # is the basename of the directory in which the file was found.
# It will be used to form destination directories and filenames.
#
####
#
# Regarding directories and files to ignore:
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
# Sometimes after a crash, this file will be created:
#
#	._.Trashes
#
# To be safe, we ignore any file that has .Trashes on the end if its name.
#
# In addition, other files such as .DS_Store may be created by OS X.
# These .DS_Store files should be ignored by the tool.  The Titanium
# Toast CD/DVD burner creates "desktop db" and "desktop df" which
# are also ignored by this shell.
#
# So we need to ignore the following:
#
#	/.Trashes		# entire directory tree directly under srcdir
#	/comstate.tof		# this file directly under srcdir
#	.DS_Store		# this file anywhere
#	desktop\ db		# Titanium Toast CD/DVD burner file
#	desktop\ df		# Titanium Toast CD/DVD burner file
#	*.Trashes		# a file that ends in .Trashes
#	.Spotlight-*		# Spotlight index files
#	.((anything))		# files and dirs that start with .
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
# and these global values set:
#
#	$srcdir			top of where images are from
#	$destdir		top of where copied and renamed files go
#	$File::Find::dir	current directory name
#	$File::Find::name 	complete pathname to the file
#	$File::Find::prune	set 1 one to prune current node out of path
#	$File::Find::top dir	top directory path ($srcdir)
#	$File::Find::topdev	device of the top directory
#	$File::Find::topino	inode number of the top directory
#
# NOTE: While $File::Find will set various values under $File::Find,
#	do not not nor need not use them.
#
sub wanted($)
{
    my $file = $_;		# current filename within $File::Find::dir
    my $pathname;		# complete path $File::Find::name
    my $path;			# path formed from file entries found in a dir
    my $basenoext;		# basename of with w/o .ext
    my $entry;			# entry read from an open directory
    my $dev;			# device number
    my $ino;			# inode number
    my $mtime;			# modify timestamp
    my $ctime;			# create timestamp
    my $roll_sub;		# roll_subdir

    # canonicalize the path by removing leading ./'s, multiple //'s
    # and trailing /'s
    #
    print "Debug: in wanted arg: $file\n" if $opt_v > 4;
    print "Debug: File::Find::name: $File::Find::name\n" if $opt_v > 4;
    ($pathname = $File::Find::name) =~ s|^(\./+)+||;
    $pathname =~ s|//+|/|g;
    $pathname =~ s|(.)/+$|$1|;
    if ($pathname =~ /$untaint/o) {
    	$pathname = $1;
    } else {
	print "Debug: tainted filename prune #1 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	return;
    }
    print "Debug: pathname: $pathname\n" if $opt_v > 4;

    # prune out anything that is not a directory
    #
    if (! -d $file) {
	# skip non-dir/non-files
	print "Debug: non-directory prune #2 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # prune out certain top level paths
    #
    # As noted in detail above, we will prune off any .Trashes,
    # .comstate.tof that are directly under $srcdir
    #
    if ($pathname eq "$srcdir/.Trashes") {
	# skip this useless camera node
	print "Debug: .Trashes prune #2 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }
    if ($pathname eq "$srcdir/comstate.tof") {
	# skip this useless camera node
	print "Debug: comstate.tof prune #4 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # prune out .DS_Store files
    #
    if ($file eq ".DS_Store") {
	# skip OS X .DS_Store files
	print "Debug: .DS_Store prune #5 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # prune out files that end in .Trashes
    #
    if ($file =~ /.Trashes$/) {
	# skip OS X .DS_Store files
	print "Debug: *.Trashes prune #6 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # prune out Titanium Toast files
    #
    if ($file =~ /^desktop d[bf]$/i) {
	# skip Titanium Toast files
	print "Debug: desktop prune #7 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # prune out Spotlight index directories
    #
    if ($file =~ /^\.Spotlight-/i) {
	# skip Spotlight index directories
	print "Debug: Spotlight prune #8 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # prune out anything that start with . except for . itself
    #
    if ($file =~ /^\../) {
	# skip . files and dirs
	print "Debug: dot-file/dir prune #12 $pathname\n" if $opt_v > 4;
	$File::Find::prune = 1;
	return;
    }

    # ignore non-readable directories
    #
    if (! -r $file) {
	print STDERR "$0: FATAL: skipping non-readable directory: $pathname\n";
	print "Debug: Warn: non-readable dir prune #13 $pathname\n" if $opt_v > 1;
	$File::Find::prune = 1;
	exit(31) unless defined $opt_a;
	return;
    }

    # open this directory for filename collection
    #
    if (! opendir DIR,$file) {
	print STDERR "$0: FATAL: opendir failed on: $pathname: $!\n";
	print "Debug: opendir error prune #14 $pathname\n" if $opt_v > 1;
	$File::Find::prune = 1;
	exit(32) unless defined $opt_a;
	return;
    }
    print "Debug: scanning directory for filenames: $pathname\n" if $opt_v > 2;

    # collect useful filenames from this open directory
    #
    while (defined($entry = readdir(DIR))) {

	# ignore these names (listed as file globs, not reg expressions):
	#
	#	*.tof
	#	desktop*
	#	*.Trashes
	#	.*
	#
	if ($entry =~ /\.tof$/i || $entry =~ /^desktop/i ||
	    $entry =~ /\.Trashes$/i || $entry =~ /^\./) {
	    print "Debug: in $pathname ignoring name of: $entry\n"
	      if $opt_v > 6;
	    next;
	}
	$path = "$pathname/$entry";
	print "Debug: found: $path\n" if $opt_v > 4;

	# ignore any entry that is not a file
	#
	if (! -f $path) {
	    print "Debug: in $pathname ignoring non-file: $entry\n"
	      if $opt_v > 6;
	    next;
	}

	# ignore any non-readable file
	#
	if (! -r $path) {
	    print "Debug: in $pathname ignoring non-readable: $entry\n"
	      if $opt_v > 5;
	    next;
	}

	# stat the file
	#
	# NOTE: We stat here because perl will have cached the stat data
	#	due to the above -f and -r tests.  Doing the stat now
	#	rather than later saves on system calls.
	#
	($dev, $ino, undef, undef, undef, undef, undef, undef,
	 undef, $mtime, $ctime) = stat($filename);
	if (! defined $dev || ! defined $ino ||
	    ! defined $mtime || ! defined $ctime) {
	    print STDERR "$0: FATAL: stat failed for: $path: $!\n";
	    print "Debug: stat error prune #15 $path\n" if $opt_v > 1;
	    $File::Find::prune = 1;
	    exit(33) unless defined $opt_a;
	    closedir DIR;
	    return;
	}

	# ignore if we happen to find the -r readme.txt file
	#
	# This is to avoid duplicate processing and to ensure that
	# readme file is processed in a special way.
	#
	if (defined $readme_dev && $dev == $readme_dev &&
	    defined $readme_ino && $ino == $readme_ino) {
	    print "Debug: in $pathname -r readme file, will later ",
	      "add: $entry\n" if $opt_v > 6;
	    next;
	}

	# firewall - must not have seen this device/inode number combo before
	#
	if (defined $devino_path{"$dev/$ino"}) {
	    print STDERR "$0: FATAL: dup dev/ino found: dev: $dev inum: $ino\n";
	    print "Debug: duplicate prune #17 $path same file as ",
	        "$devino_path{"$dev/$ino"}\n" if $opt_v > 1;
	    $File::Find::prune = 1;
	    exit(35) unless defined $opt_a;
	    closedir DIR;
	    return;
	}
	print "Debug: recording information about $path\n" if $opt_v > 3;

	# save the found basename w/o .ext
	#
	($basenoext = $entry) =~ s/\.[^.]*$//;
	if ($basenoext eq "readme" && defined $opt_r) {
	    print STDERR "$0: FATAL: -r was given found file with a basename ",
	      " of readme (before any .extension)\n";
	    print "Debug: duplicate prune #18 $path readme basename w/o ",
	      ".extension: $path\n" if $opt_v > 1;
	    $File::Find::prune = 1;
	    exit(36) unless defined $opt_a;
	    closedir DIR;
	    return;
	}
	$path_basenoext{$path} = $basenoext;

	# save the found device/inum for duplicate detection
	#
	$devino_path{"$dev/$ino"} = $path;

	# track which paths have the same basename w/o .ext
	#
	if (defined $basenoext_pathset{$basenoext}) {
	    # dup basename w/o .ext found, mark both paths
	    $need_plus{$path} = 1;
	    $need_plus{@{$basenoext_pathset{$basenoext}}[0]} = 1;
	    # save this base w/o .ext in the pathset
	    push(@{$basenoext_pathset{$basenoext}}, $path);
	} else {
	    # not a dup (yet)
	    $need_plus{$path} = 0;
	    # save this base w/o .ext in the pathset
	    push(@{$basenoext_pathset{$basenoext}}, $path);
	}

	# save the file timestamp
	#
	# We favor first the older create or modify times that is after
	# mintime (Tue Nov  5 00:53:20 1985 UTC).  Failing that we will
	# take the older non-zero create or modify times.  Failing that
	# we will use a 0 timestamp
	#
	if ($ctime >= $mintime) {
	    if ($mtime >= $mintime) {
		$path_filetime{$path} = ($ctime <= $mtime ? $ctime : $mtime);
    	    } else {
		$path_filetime{$path} = $ctime;
	    }
        } elsif ($mtime >= $mintime) {
	    $path_filetime{$path} = $mtime;
	} elsif ($ctime > 0) {
	    if ($mtime > 0) {
		$path_filetime{$path} = ($ctime <= $mtime ? $ctime : $mtime);
    	    } else {
		$path_filetime{$path} = $ctime;
	    }
	} else {
	    $path_filetime{$path} = 0;
	}
	print "Debug: file timestamp: $path_filetime{$path} for $path\n"
	  if $opt_v > 4;

	# calculate the roll_sub
	#
	# The roll_sub is the directory name, converted to lower case,
	# under which we found this file.
	#
	# If the directory name is not usable, then the roll_sub will be "0".
	# These are directory names that are not usable
	#
	#	is dcim in any case
	#	an empty string
	#	contains only whitespace
	#	contain a /
	#	starts with a .
	#	is the same as the top level directory (srcdir)
	#
	$roll_sub = lc(basename($pathname));
	print "Debug: original lowercase roll_sub: $roll_sub\n" if $opt_v > 5;
	if ($roll_sub =~ /^dcim$/) {
	    print "Debug: converting DCIM roll_sub to 0\n" if $opt_v > 5;
	    $roll_sub = "0";
	} elsif ($roll_sub =~ /^\s*$/) {
	    print "Debug: converting empty/blank roll_sub to 0\n" if $opt_v > 5;
	    $roll_sub = "0";
	} elsif ($roll_sub =~ /\//) {
	    print "Debug: converting roll_sub with / to 0\n" if $opt_v > 5;
	    $roll_sub = "0";
	} elsif ($roll_sub =~ /^\./) {
	    print "Debug: converting .-based roll_sub to 0\n" if $opt_v > 5;
	    $roll_sub = "0";
	} elsif ($dev == $File::Find::topdev && $ino == $File::Find::topino) {
	    print "Debug: converting srcdir roll_sub to 0\n" if $opt_v > 5;
	    $roll_sub = "0";
	}

	# We convert all -'s (dashed) in the roll_sub to _'s (underscores)
	#
	if ($roll_sub =~ /-/) {
	    $roll_sub = s/-/_/g;
	    print "Debug: changed all - to _ in roll_sub\n" if $opt_v > 5;
	}

	# We truncate the roll_sub to the first roll_sub_maxlen (which can be
	# changed from the default by -s roll_sublen) if subdurchars is > 0.
	# A 0 roll_sub_maxlen means we use the full roll_sub.
	#
	# We will skip the first roll_sub_skip chars (which can be changed from
	# the default by -k roll_subskip).
	#
	$roll_sub = substr($roll_sub, $roll_sub_skip, $roll_sub_maxlen);

	# save the final roll_sub
	#
	print "Debug: using roll_sub: $roll_sub\n" if $opt_v > 4;
	$path_roll_sub{$path} = $roll_sub;
    }

    # cleanup
    #
    closedir DIR;
    print "Debug: finished scanning dir: $pathname\n" if $opt_v > 3;
    return;
}


# determine_destname - determine the destination basenames
#
# Consider the a file under srcdir:
#
#	/srcdir/DCIM/101EOS1D/PV5V5627.CR2
#
# Assume that the EXIF timestamp (or file timestamp if if lacks
# EXIF timestamp tags) is:
#
#	2005-05-12 15:25:45 UTC
#
# Then we will create the file:
#
#    /destdir/200505/2005005-043/200505-043-101/
#		121525+5627-45-200505-043-101-pg5v.cr2
#
# The created file path is:
#
#	/destdir			# destdir path of image library
#	/200505				# image year & month
#	/200505-043			# image year & month, - (dash), roll
#	/200505-043-010			# year & month, -, roll, -, roll-subdir
#	/121525+5627-45-200505-043-101-pg5v.cr2	# image filename (see below)
#
# NOTE: The property of directory names under /destdir that they are
#	unuqie  and standalone.  One can look at one of these sub-directories
#	and know where it belongs.  That is why the yyyymm and yyyymm-roll
#	are repeated in the lower level directories.
#
# NOTE: The property of a filename is that they completely define the
#	directory path under whey they belong.  One can look at a filename
#	and know where it belongs.
#
# NOTE: Another important property of a filename is that the original
#	image filename can be re-constructed.  Consider these filenames:
#
#		121525+5627-45-200505-043-101-pg5v.cr2
#		121525+5627-45_1-200505-043-101-pg5v_stuff.cr2
#
#	the original image filenames were:
#
#		PGV55627.CR2
#		PGV55627STUFF.CR2
#
# Consider this filename:
#
#	121525+5627-45-200505-043-101-pg5v.cr2
#
# If another image was taken during the same second, that 2nd image becomes:
#
#	121525+5627-45_1-200505-043-101-pg5v.cr2
#
# is constructed out of the following:
#
#	12			# image day of month (UTC), 2 digits [01-31]
#	15			# image hour (UTC), 2 digits [00-23]
#	25			# image minute of hour (UTC), 2 digits [00-59]
#	- or +			# - ==> has no sound file, + has sound file
#	5627			# image sequence number (see NOTE below)
#	-			# (dash) separator
#	45			# image second of minites, 2 digits [00-60]
#	     _			# (underscore) optional for dups in same sec
#	     1			# optional digits for dups in same sec
#	-			# (dash) separator
#	2005			# image 4 digit Year (UTC)
#	05			# image month (UTC), 2 digits [01-12]
#	-			# (dash) separator
#	043			# roll number, 3 digits, 0 padded
#	-			# (dash) separator
#	101			# optional subdir lead chars, w/o -'s lowercase
#	-			# (dash) separator
#	pg5v			# imagename w/o 5th-8th chars, lowercase no -'s
#	    _			# (underscore) optional if trailing chars
#	    rest		# optional trailing image filename chars
#	.cr2			# .extension
#
# NOTE: The number of leading image filename chars between the UTC ddhhmm- and
#	the -ss, defaults to 4 characters.  The default length can be changed
#	by the -y seqlen option.  These chars come from the image filename
#	after it has been lower cased and had -'s removed AND the initial
#	image filename chars (which also defaults to 4 and may be changed
#	by the -z skchars option) have been skipped.
#
#	By default, the 1st 4 chars of the image filename are not used as part
#	of the image sequence number.  These initial image filename characters
#	are usually fixed for a given camera and are left on the end of
#	the filename.  This default not-used length can be changed by
#	the -z skchars option.
#
#	If there are any remainng image filename chars beyond the sequence
#	number and before the .file extension, we put them after an _
#	(underscore) character.
#
#	A typical Canon EOS 1D Mark II N image filename:
#
#		pg5v5627.cr2
#
#	would, by default, have its chars moved into a filename of this form:
#
#		dddhhmm-5627-...-pg5v.cr2
#
#	The image filename:
#
#		LLLLnnnnXyzzy.ext
#
#	would, by default, have its chars moved into a filename of this form:
#
#		ddhhmm-nnnn-....-LLLL_Xyzzy.ext
#
#	The image filename:
#
#		LLLnnnnnWh-ey.ext
#
#	with -y 5 -z 3 would produce a filename of this form:
#
#		ddhhmm-nnnnn-....-LLL_Whey.ext
#
####
#
# If we encounter a srcfile that is already in destination filename
# form, we convert it back to the original form before forming a
# destination filename again.  This prevents our destination filenames
# from growing very long if we were run the command over the
# same tree.  In fact, by doing this we can rerun this tool over
# the same tree without any ill effects.
#
# In addition to being able to process already renamed files, this
# tool can deal with filenames that have been named with the previous
# genreation of this tool.  These older filenames are of the form:
#
#	999-999-99999999-999999-zzzz9999.xyz
#
# Example: If the lowercase name is already of the form:
#
#	121525+5627-45-200505-043-101-pg5v.cr2
#	121526+5628-45_1-200505-043-101-pg5v.cr2
#	043-101-20050512-152745-ls1f5629.cr2
#	043-101-20050512-152845_1-ls1f5630.cr2
#
# we convert it back to:
#
#	pg5v5627.cr2
#	pg5v5628.cr2
#	ls1f5629.cr2
#	ls1f5630.cr2
#
# This is so that we won't keep adding date strings, roll numbers, etc
# to files that already have them.
#
# Also filenames of the form:
#
#	121525+5631-45-200505-043-101-pg5v_stuff.cr2
#	121525+5632-45_1-200505-043-101-pg5v_stuff.cr2
#
# are converted into:
#
#	pg5v5631stuff.cr2
#	pg5v5632stuff.cr2
#
# as well.
#
sub determine_destname()
{
    my $path;		# a path in the pathset
    my $srcbase;	# basename of the source path
    my $destbase;	# basename of the destination path

    # process all paths
    #
    foreach $path ( keys %path_basenoext ) {

	# get the basename of the source path in lowercase
	#
	$srcbase = lc(basename($path));

	# deal with filenames in old style destination form
	#
	# If the lowercase name is already of the form:
	#
	#	043-101-20050512-152545-ls1f5629.cr2
	#	043-101-20050512-152545_1-ls1f5630.cr2
	#
	# convert it to just ls1f5629.cr2 and ls1f5630.cr2 so we can
	# reprocess the destination tree if we want to later on.
	#
	if ($srcbase =~ /^\d{3}-[^-]*-\d{8}-\d{6}(_\d+)?-(.*)$/) {
	    print "Debug: found old style filename: $srcbase\n" if $opt_v > 2;
	    $srcbase = $2;
	    $srcbase =~ s/-/_/g;	# -'s (dash) become _'s (underscore)
	    print "Debug: preconverted old style to: $srcbase\n" if $opt_v > 2;

	# deal with filenames in the new style destination form
	#
	# If the lowercase name is already of the form:
	#
	#	121525+5627-45-200505-043-101-pg5v.cr2
	#	121526+5628-45_1-200505-043-101-pg5v.cr2
	#
	# convert it to just pg5v5627.cr2 and pg5v5628.cr2 so we can
	# reprocess the destination tree if we want to later on.
	#
	} elsif ($srcbase =~
			m{
    			  \d{6}		# ddmmhh
			  [-+]		# - (dash) or + (plus) separator
			  ([^-]*)	# $1: sequence number
			  -		# - (dash) separator
			  \d{2}		# ss
			  (_\d+)?	# $2: opt digits for dups in same sec
			  \d{6}		# yyyymm
			  -		# - (dash) separator
			  [^-]*		# roll number
			  -		# - (dash) separator
			  [^-]*		# sub-roll number
			  -		# - (dash) separator
			  ([^_.]*)	# $3: image filename chars before seqnum
			  (_[^.]*)?	# $4: optiinal imagename chars after seq
			  (\..*)?$	# $5: optional .extension
    			 }ix) {
	    print "Debug: found new style filename: $srcbase\n" if $opt_v > 2;
	    $srcbase = $3 . $1 . substr($4, 1) . $5;
	    $srcbase =~ s/-/_/g;	# -'s (dash) become _'s (underscore)
	    print "Debug: preconverted new style to: $srcbase\n" if $opt_v > 2;

	# -'s (dash) become _'s (underscore) to avoid filename field confusion
	#
	} else {
	    $srcbase =~ s/-/_/g;
	}

	# form the new destination filename
	#
	$path_destfile = XXX
    }
}


# get_timestamp - determine the timestamp of EXIF or file dates
#
# given:
#	\@pathset	array of paths to to check
#
# returns:
#	timestamp or
#	undef ==> no valid EXIF timestamp and file timestamp(s) too old
#
sub get_timestamp($)
{
    my ($pathset) = $_;		# get arg
    my $path;		# a path in the pathset
    my $exitcode;	# 0 ==> OK, else ==> could not get an EXIF timestamp
    my $message;	# $exitcode==0 ==> timestamp, else error message
    my $oldest;		# oldest timestamp found
    my $oldest_exif;	# path of oldest EXIF timestamp
    my %has_exif_ext;	# $has_exif_ext{$path} == 1 ==> $path's as EXIF .ext
    my $i;

    # see which paths in the pathset have .extensions that might have EXIF data
    #
    foreach $path ( @{$pathset} ) {
	my $path_exit;	# the .ext of the path
	my $has_exif_ext;  # 1 ==> an .ext that might have EXIF data, 0 ==> no

	# canonicalize the .ext of this path (lower case, chars after final .)
	#
	($path_ext = lc($path)) =~ s/^.*\.//;

	# see if this .ext has a like EXIF data holder
	#
	$has_exif_ext = 0;
	foreach $i ( @exif_ext ) {
	    # see if path's .ext is an EXIF type extension
	    if ($i eq $path_ext) {
		$has_exif_ext = 1;
		break;
	    }
	}
	$has_exif_ext{$path} = $has_exif_ext;
    }

    # look for files in the pathset that might contain EXIF data
    #
    $oldest = 0;
    foreach $path ( @{$pathset} ) {

	# look for the oldest EXIF timestamps in EXIF based .extensions
	#
	if ($has_exif_ext{$path}) {

	    # try to get EXIT timestamp
	    ($exitcode, $message) = exif_date($path);

	    # it is OK to fail, but if we have a good time, track oldest
	    if ($exitcode == 0 && $oldest == 0 || $message < $oldest)) {
		print "Debug: get_timestamp EXIF type: $path " .
		    "EXIF time: $message\n" if $opt_v > 3;
		$oldest = $message;
		$oldest_exif = $path;
	    } elsif ($exitcode == 0 && $oldest > 0 || $message < $oldest)) {
		print "Debug: get_timestamp EXIF type: $path " .
		    "older EXIF time: $message\n" if $opt_v > 3;
	    } elsif ($exitcode != 0) {
	        print "Debug: exif_date error code $exifcode: $message\n"
		  if $opt_v > 4;
	    }
	}
    }

    # If we found EXIF timestamps, return the oldest timestamp
    #
    if ($oldest > 0) {
	print "Debug: EXIF type EXIF timestamp: $oldest for $oldest_exif\n"
	  if $opv_v > 2;
	return $oldest;
    }

    # We did not find an EXIF .extension that had a EXIF timestamp, so
    # look for a non-EXIF .extension with an EXIF timestamp in case we
    # have a EXIF image with a unknown extension or in case we have
    # an EXIF image without a .extension
    #
    foreach $path ( @{$pathset} ) {

	# look for the oldest EXIF timestamps in non-EXIF based .extensions
	#
	if (! $has_exif_ext{$path}) {

	    # try to get EXIT timestamp
	    ($exitcode, $message) = exif_date($path);

	    # it is OK to fail, but if we have a good time, track oldest
	    if ($exitcode == 0 && $oldest == 0 || $message < $oldest)) {
		print "Debug: get_timestamp non-EXIF type: $path " .
		    "EXIF time: $message\n" if $opt_v > 3;
		$oldest = $message;
		$oldest_exif = $path;
	    } elsif ($exitcode == 0 && $oldest > 0 || $message < $oldest)) {
		print "Debug: get_timestamp non-EXIF type: $path " .
		    "older EXIF time: $message\n" if $opt_v > 3;
	    }
	}
    }

    # If we found EXIF timestamps, return the oldest timestamp
    #
    if ($oldest > 0) {
	print "Debug: non-EXIF type EXIF timestamp: $oldest for $oldest_exif\n"
	  if $opv_v > 2;
	return $oldest;
    }

    # no EXIF timestamps in set, look for the oldest file timestamp that
    # is not too old
    #
    foreach $path ( @{$pathset} ) {

	# if the file timestamp is not too old
	#
	if ($path_filetime{$path} >= $mintime &&
	    $path_filetime{$path} < $oldest) {
	    $oldest = $path_filetime{$path};
	    $oldest_exif = $path;
	}
    }

    # If we found a file timestamp that is not too old, use the oldest
    #
    if ($oldest > 0) {
	print "Debug: file timestamp: $oldest for $oldest_exif\n"
	  if $opv_v > 2;
	return $oldest;
    }

    # We have no EXIF timestamp and no file timestamp we can use
    #
    return undef;
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
    my $timestamp;	# seconds since the epoch of early timestamp or -1

    # firewall - image file must be readable
    #
    if (! -e $filename) {
	return (50, "cannot open");	# exit(50)
    }
    if (! -r $filename) {
	return (51, "cannot read");	# exit(51)
    }

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($filename, @tag_list);
    if (! defined $info || defined $$info{Error}) {
	# failure to get a EXIF data
	if (defined $$info{Error}) {
	    return (52, "EXIF data error: $$info{Error}");	# exit(52)
        } else {
	    return (53, "no EXIF data");	# exit(53)
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
	    print "Debug: ignoring undef EXIF tag value: $tag\n" if $opt_v > 5;
	} elsif ($$info{$tag} !~ /^\d+$/) {
	    print "Debug: ignoring non-numeric tag: $tag: ",
	    	"$$info{$tag}\n" if $opt_v > 5;
	} elsif ($$info{$tag} <= $mintime) {
	    print "Debug: ignoring pre-mintime: $tag: ",
	    	  "$$info{$tag} <= $mintime\n" if $opt_v > 5;
	} elsif ($timestamp > 0 && $$info{$tag} == $timestamp) {
	    print "Debug: ignoring timestamp tag: $tag: ",
	    	  "$$info{$tag} same value\n"
		  if $opt_v > 5;
	} elsif ($timestamp > 0 && $$info{$tag} > $timestamp) {
	    print "Debug: ignoring timestamp tag: $tag: ",
	    	  "$$info{$tag} that is not earliest > $timestamp\n"
		  if $opt_v > 5;
	} else {
	    print "Debug: found useful numeric timestamp tag: $tag ",
	    	  "$$info{$tag}\n" if $opt_v > 5;
	    $timestamp = $$info{$tag};
        }
    }
    if ($timestamp < 0) {
	return (54, "no timestamp in EXIF data");	# exit(54)
    }

    # Avoid very old EXIF timestamps
    #
    if ($timestamp < $mintime) {
	return (55, "timestamp: $timestamp < min: $mintime");	# exit(55)
    }

    # return the EXIF timestamp
    #
    return (0, $timestamp);
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
# The match is case insensitive.  The leading #(whitespace) is optional.
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
	return (70, "cannot open");	# exit(70)
    }
    if (! -r $filename) {
	return (71, "cannot read");	# exit(71)
    }

    # open the text file
    #
    print "Debug: looking for date in text file: $filename\n" if $opt_v > 4;
    if (! open TEXT, '<', $filename) {
	return (72, "cannot open: $!");	# exit(72)
    }

    # read the 1st $datelines of a file looking for a timestamp
    #
    for ($i=0; $i < $datelines; ++$i) {

	# read a line
	#
	if (! defined($line = <TEXT>)) {
	    return (73, "EOF or text read error");	# exit(73)
	}
	chomp $line;
	print "Debug: read text line $i in $filename: $line\n" if $opt_v > 6;

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
	    my $min = $7;	# minute of hour
	    my $hour = $6;	# hour of day
	    my $mday = $5;	# day of month
	    my $monname = $4;	# short name of month
	    my $mon = -1;	# month of year [0..11]
	    my $year = $10;	# year
	    my $timestamp;	# date string converted into a timestamp
	    print "Debug: #1 parsed $year-$monname-$mday $hour:$min",
	    	  (defined $sec ? $sec : ""), "\n" if $opt_v > 6;

	    # convert short name of month to month number [0..11]
	    #
	    print "Debug: line $i, found possible date string in $filename: ",
	    	   "$line\n" if $opt_v > 5;
	    foreach ( keys %mname ) {
		$mon = $mname{$_} if $monname =~ /^$_$/i;
	    }
	    if ($mon < 0) {
		print "Debug: ignoring bad month name $monname on line $i ",
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
	    printf("Debug: #1 will parse date: " .
		   "%04d-%02d-%02d %02d:%02d:%02d\n",
	    	   $year, $mon, $mday, $hour, $min, $sec) if $opt_v > 6;
	    $timestamp = timegm_nocheck($sec, $min, $hour, $mday, $mon, $year);
	    if (! defined $timestamp) {
		print "Debug: #1 ignoring malformed date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }
	    if ($timestamp < $mintime) {
		print "Debug: #1 ignoring very early date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }
	    print "Debug: #1 $filename timestamp: $timestamp\n" if $opt_v > 2;

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
	    my $min;		# minute of hour
	    my $hour;		# hour of day
	    my $timeofday = $6;	# optional hh:mm:ss timestamp
	    my $mday = $5;	# day of month
	    my $mon = $4;	# month of year [01-12]
	    my $year = $3;	# year
	    my $timestamp;	# date string converted into a timestamp
	    print "Debug: #2 parsed $year-$mon-$mday",
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
	    printf("Debug: #2 will parse date: " .
	    	   "%04d-%02d-%02d %02d:%02d:%02d\n",
	    	   $year, $mon, $mday, $hour, $min, $sec) if $opt_v > 6;
	    $timestamp = timegm_nocheck($sec, $min, $hour,
	    				$mday, $mon-1, $year);
	    if (! defined $timestamp) {
		print "Debug: #2 ignoring malformed date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }
	    if ($timestamp < $mintime) {
		print "Debug: #2 ignoring very early date on line $i ",
		    " in $filename\n" if $opt_v > 4;
	    	next;	# bad month name
	    }
	    print "Debug: #2 $filename timestamp: $timestamp\n" if $opt_v > 2;

	    # return the timestamp according to this date line we read
	    #
	    return (0, $timestamp);
	}
    }

    # no date stamp found
    #
    return (74, "no date stamp found in initial lines");	# exit(74)
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
	return (80, "is a non-directory");	# exit(80)
    }
    if (! -d $dir_name) {
	print "Debug: will try to mkdir: $dir_name\n" if $opt_v > 1;
        if (! mkdir($dir_name, 0775)) {
	    print STDERR "$0: cannot mkdir: $dir_name: $!\n";
	    return (81, "cannot mkdir");	# exit(81)
	}
    }
    if (! -w $dir_name) {
	print STDERR "$0: directory is not writable: $dir_name\n";
	return (82, "directory is not writable");	# exit(82)
    }

    # all is OK
    #
    return (0, undef);
}


# roll_setup - setup and/or increment the .exifroll EXIF roll number file
#
# uses these globals:
#
#	$rollfile	see -e in program usage at top
#	$rollnum	EXIF roll number
#
sub roll_setup()
{
    # if -n rollnum was given, force that value to be used
    # and do not read or update the ~/.exifroll file
    #
    if (defined $opt_n) {

	# firewall - roll number must be 3 digits
	#
	if ($opt_n !~ /^\d{3}$/) {
	    print STDERR "$0: roll number must be 3 digits\n";
	    exit(90);
	}
	$rollnum = $opt_n;
	return;
    }

    # process an existing ~/.exifroll file
    #
    $rollnum = "000";	# default initial roll number
    if (-e $rollfile) {

	# firewall - must be readable
	#
	if (! -r $rollfile) {
	    print STDERR "$0: cannot read exifroll file: $rollfile\n";
	    exit(91);
	} elsif (! -w $rollfile) {
	    print STDERR "$0: cannot write exifroll file: $rollfile\n";
	    exit(92);
	}

	# open ~/.exifroll file
	#
	if (! open EXIFROLL, '<', $rollfile) {
	    print STDERR "$0: cannot open for reading exifroll: ",
	    		 "$rollfile: $!\n";
	    exit(93);
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

    # write the next roll number into ~/.exifroll
    #
    print "Debug: will use roll number: $rollnum\n" if $opt_v > 0;
    if (! open EXIFROLL, '>', $rollfile) {
	print STDERR "$0: cannot open for writing exifroll: $rollfile: $!\n";
	exit(94);
    }
    if ($rollnum > 999) {
	if (! print EXIFROLL "000\n") {
	    print "Debug: next roll number will be 000\n" if $opt_v > 1;
	} else {
	    print STDERR "$0: FATAL: cannot write 000 rollnum ",
	    		 "to exifroll: $rollfile: $!\n";
	    exit(95);
	}
    } else {
	if (printf EXIFROLL "%03d\n", $rollnum+1) {
	    print "Debug: next roll number will be ",
	    	sprintf("%03d", $rollnum+1), "\n" if $opt_v > 1;
	} else {
	    print STDERR "$0: FATAL: cannot write next rollnum ",
	    		 "to exifroll: $rollfile: $!\n";
	    exit(96);
	}
    }
    close EXIFROLL;
    return;
}


# readme_check - check the -r readme filename given
#
# given:
#	$readme		# -r readme file to check
#
# returns:
#	absolute path of the readme file
#
# NOTE: This function also sets the global $readme_timestamp value.
#
# NOTE: This function exits if there are any problems.
#
# NOTE: This function is expected to be called from main
#	soon after arg parsing.
#
sub readme_check($)
{
    my ($readme) = @_;		# get args
    my $exitcode;		# return code from text_date
    my $message;		# timestamp or error message
    my $ret;			# absolute path of readme file

    # -r $readme file must be a readable file
    #
    if (! -e $readme) {
	print STDERR "$0: -r $readme does not exist\n";
	exit(100);
    }
    if (! -f $readme) {
	print STDERR "$0: -r $readme is not a file\n";
	exit(101);
    }
    if (! -r $readme) {
	print STDERR "$0: -r $readme is not readable\n";
	exit(102);
    }

    # must have a text date
    #
    ($exitcode, $message) = text_date($readme);
    if ($exitcode != 0) {
	print STDERR "$0: -r $readme does not have a date timestamp line\n";
	print STDERR "$0: try adding '# date: yyyy-mm-dd' line to $readme\n";
	exit(103);
    }

    # same the timestamp for later
    #
    $readme_timestamp = $message;

    # return the absolute path of readme
    #
    $ret = abs_path($readme);
    if (! defined $ret) {
	print STDERR "$0: cannot determine absolute path of $readme\n";
	exit(104);
    }
    return $ret;
}


# old_file_date - return the earliest reasonable create/modify timestamp
#
# given:
#	$filename	image filename to process
#
# returns:
#	($exitcode, $message)
#	    $exitcode:	0 ==> OK, =! 0 ==> exit code
#	    $message:	$exitcode==0 ==> timestamp, else error message
#
sub old_file_date($)	# XXX - remove when code complete
{
    my ($filename) = @_;	# get arg
    my $mtime;			# modify timestamp
    my $ctime;			# create timestamp

    # firewall - file must exist
    #
    if (! -e $filename) {
	return (60, "cannot open");	# exit(60)
    }

    # stat the file
    #
    (undef, undef, undef, undef, undef, undef, undef, undef,
     undef, $mtime, $ctime) = stat($filename);

    # first try the create timestamp
    #
    if (defined $ctime && $ctime >= $mintime) {
	# use create time
	print "Debug: using: $filename: create timestamp: $ctime\n"
	    if $opt_v > 4;
	return (0, $ctime);

    # next try the modify timestamp
    #
    } elsif (defined $mtime && $mtime >= $mintime) {
	# use modify time
	print "Debug: using: $filename: modify timestamp: $ctime\n"
	    if $opt_v > 4;
	return (0, $mtime);
    }

    # we cannot find a useful file timestamp
    #
    print "Debug: no valid file timestamps: $filename\n" if $opt_v > 4;
    return (61, "file is too old");	# exit(61)
}


# old_wanted - File::Find tree walking function called at each non-pruned node
#
# This function is a callback from the File::Find directory tree walker.
# It will walk the $srcdir and copy/rename files as needed.
#
# uses these globals:
#
#	$opt_c		see -c in program usage at top
#	$opt_a		see -e in program usage at top
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
#	/043-101			# roll_subdir
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
#	101			# optional subdir lead chars, w/o -'s, lowercase
#	-			# (dash) separator
#	2005			# image 4 digit Year
#	05			# image month, 2 digits [01-12]
#	12			# image day of month, 2 digits [01-31]
#	-			# (dash) separator
#	15			# image hour (UTC), 2 digits [00-23]
#	25			# image minute of hour, 2 digits [00-59]
#	45			# image second of minutes, 2 digits [00-60]
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
# Sometimes after a crash, this file will be created:
#
#	._.Trashes
#
# To be safe, we ignore any file that has .Trashes on the end if its name.
#
# In addition, other files such as .DS_Store may be created by OS X.
# These .DS_Store files should be ignored by the tool.  The Titanium
# Toast CD/DVD burner creates "desktop db" and "desktop df" which
# are also ignored by this shell.
#
# So we need to ignore the following:
#
#	/.Trashes		# entire directory tree directly under srcdir
#	/comstate.tof		# this file directly under srcdir
#	.DS_Store		# this file anywhere
#	desktop db		# Titanium Toast CD/DVD burner file
#	desktop df		# Titanium Toast CD/DVD burner file
#	*.Trashes		# a file that ends in .Trashes
#	.Spotlight-*		# Spotlight index files
#	.((anything))		# files and dirs that start with .
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
# and these global values set:
#
#	$srcdir			where images are from
#	$destdir		where copied and renamed files go
#	$File::Find::dir	current directory name
#	$File::Find::name 	complete pathname to the file
#	$File::Find::prune	set 1 one to prune current node out of path
#	$File::Find::topdir	top directory path ($srcdir)
#	$File::Find::topdev	device of the top directory
#	$File::Find::topino	inode number of the top directory
#	$adding_readme		0 ==> function being called by find()
#				!= 0  ==> function being called by add_readme()
#
sub old_wanted($)	# XXX - remove when code complete
{
    my $filename = $_;		# current filename within $File::Find::dir or
				# absolute path of readme if $adding_readme!=0
    my $pathname;		# complete path $File::Find::name
    my $roll_sub;		# roll_subdir
    my ($errcode, $errmsg);	# form_dir return values
    my $lowerfilename;		# lower case filename
    my $levels;		# directory levels under $srcdir/DCIM or $srcdir
    my $datecode;	# exif_date error code or 0 ==> OK
    my $datestamp;	# EXIF or filename timestamp of OK, or error msg
    my $yyyymm;		# EXIF or filename timestamp year and month
    my $dd;		# EXIF or filename timestamp day
    my $hhmmss;		# EXIF or filename timestamp time
    my $hhmmss_d;	# EXIF or filename timestamp time and optional _#
    my $dupnum;		# _number de-duplication number
    my $destname;	# the destination filename to form
    my $destpath;	# the full path of the destination file
    my $exiffound;	# 1 ==> valid EXIF time data found, 0 ==> no EXIF time

    # If we are being called from add_readme() instead of find(),
    # then we have to simulate a File::Find call by setting the
    # $File::Find externals.
    #
    if ($adding_readme != 0) {
	print "Debug: wanted() adding special readme file: ",
	      "$opt_r\n" if $opt_v > 1;
	print "Debug: simulating find() call\n" if $opt_v > 2;
	$filename = basename($opt_r);
	$File::Find::dir = dirname($opt_r);
	$File::Find::name = abs_path($opt_r);
	if (! defined $filename || ! defined $File::Find::dir ||
	    ! defined $File::Find::name) {
	    # skip missing files
	    print STDERR "$0: FATAL: cannot determine basename and/or ",
	    		 "dirname and/or absolute path of $_\n";
	    print "Debug: missing file prune #0 $pathname\n" if $opt_v > 1;
	    $File::Find::prune = 1;
	    exit(30) unless defined $opt_a;
	    return;
	}
	$File::Find::prune = 0;
	$File::Find::topdir = $File::Find::dir;
	# we use a dev/ino that does not match any valid file because we
	# do not care if the readme is already under the srcdir or destdir
	$File::Find::topdev = 0;
	$File::Find::topino = 0;
    }

    # canonicalize the path by removing leading ./'s, multiple //'s
    # and trailing /'s
    #
    print "Debug: in wanted arg: $filename\n" if $opt_v > 3;
    print "Debug: File::Find::name: $File::Find::name\n" if $opt_v > 2;
    ($pathname = $File::Find::name) =~ s|^(\./+)+||;
    $pathname =~ s|//+|/|g;
    $pathname =~ s|(.)/+$|$1|;
    print "Debug: pathname: $pathname\n" if $opt_v > 1;

    # prune out anything that is neither a directory and nor a file
    #
    if (($adding_readme == 0 &&
         ! -d $filename && ! -f $filename) ||
	($adding_readme != 0 &&
	 ! -d $File::Find::name && ! -f $File::Find::name)) {
	# skip non-dir/non-files
	print "Debug: non-dir/non-file prune #1 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out certain top level paths
    #
    # As noted in detail above, we will prune off any .Trashes,
    # .comstate.tof that are directly under $srcdir
    #
    if ($pathname eq "$srcdir/.Trashes") {
	# skip this useless camera node
	print "Debug: .Trashes prune #2 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }
    if ($pathname eq "$srcdir/comstate.tof") {
	# skip this useless camera node
	print "Debug: comstate.tof prune #3 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out .DS_Store files
    #
    if ($filename eq ".DS_Store") {
	# skip OS X .DS_Store files
	print "Debug: .DS_Store prune #4 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out files that end in .Trashes
    #
    if ($filename =~ /.Trashes$/) {
	# skip OS X .DS_Store files
	print "Debug: *.Trashes prune #5 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out Titanium Toast files
    #
    if ($filename =~ /^desktop d[bf]$/i) {
	# skip Titanium Toast files
	print "Debug: desktop prune #6 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # prune out Spotlight index directories
    #
    if ($filename =~ /^\.Spotlight-/i) {
	# skip Spotlight index directories
	print "Debug: Spotlight prune #7 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # ignore names that match common directories
    #
    if ($filename eq ".") {
	# ignore but do not prune directories
	print "Debug: . ignore #7 $pathname\n" if $opt_v > 3;
    	return;
    }
    if ($filename eq "..") {
	# ignore but do not prune directories
	print "Debug: .. ignore #8 $pathname\n" if $opt_v > 3;
    	return;
    }
    if ($filename eq "DCIM") {
	# ignore but do not prune directories
	print "Debug: DCIM ignore #9 $pathname\n" if $opt_v > 3;
    	return;
    }

    # prune out anything that start with . (we already processed . and ..)
    #
    if ($filename =~ /^\../) {
	# skip . files and dirs
	print "Debug: dot-file/dir prune #8 $pathname\n" if $opt_v > 3;
	$File::Find::prune = 1;
	return;
    }

    # ignore missing files
    #
    # NOTE: The add_readme() function simulates find() calling this
    #	    function.  While readme_check() does a sanity check
    #	    on the readme file, this final check is here as an
    #	    extra sanity check.
    #
    if (($adding_readme == 0 && ! -e $filename) ||
	($adding_readme != 0 && ! -e $File::Find::name)) {
	# skip missing files
	print STDERR "$0: FATAL: skipping missing file: $filename\n";
	print "Debug: missing file prune #10 $pathname\n" if $opt_v > 1;
	$File::Find::prune = 1;
	exit(31) unless defined $opt_a;
	return;
    }

    # ignore non-files
    #
    if (($adding_readme == 0 && ! -f $filename) ||
	($adding_readme != 0 && ! -f $File::Find::name)) {
	# ignore but do not prune directories
	print "Debug: dir ignore #11 $pathname\n" if $opt_v > 3;
    	return;
    }

    # ignore non-readable files
    #
    if (($adding_readme == 0 && ! -r $filename) ||
	($adding_readme != 0 && ! -r $File::Find::name)) {
	# skip non-readable files
	print STDERR "$0: FATAL: non-readable file: $filename\n";
	print "Debug: non-readable file prune #12 $pathname\n" if $opt_v > 1;
	$File::Find::prune = 1;
	exit(32) unless defined $opt_a;
	return;
    }

    # Determine 2nd part of the directory we will place the new file in.
    #
    # The directory we will place the new file in comes from the
    # roll number, always followed by - (dash), followed by an
    # optional roll_sub.  This code determines the roll_sub as follows:
    #
    #	If we are adding a readme file (-r readme), then we will act as if
    #	the original file was directly under $srcdir.
    #
    #   Else if we are adding a file that is directly under $srcdir,
    #	then our roll_sub will be empty.
    #
    #	Else use the directory that contains the source file to form roll_sub.
    #	When that directory starts with 978- (3 digits and - (dash)), then we
    #	remove heading 987-.
    #
    #	Next we canonicalize the roll_sub by converting to lower case,
    #	replace -'s (dashes) with _'s (underscores), and by truncating
    #	to the first "-s roll_sublen" chars.
    #
    #   Finally we prepend the roll number follow by a - (dash).
    #
    # This means that the file:
    #
    #	$srcdir/200505/001-/001--20050515-103055-readme.txt
    #	$srcdir/200505/001-100/001-100-20050515-103055-ls1f1234.cr2
    #	$srcdir/DCIM/101EOS1D/LS1F9876.CR2
    #
    # will end up with a roll_sub of:
    #
    #	001
    #	001-100
    #	001-101
    #
    # and will to be placed in:
    #
    #	$destdir/200505/001-/001--20050515-103055-readme.txt
    #	$destdir/200505/001-100/001-100-20050515-103055-ls1f1234.cr2
    #	$destdir/200505/001-101/001-101-20050515-103055-ls1f9876.cr2
    #
    if ($adding_readme != 0) {
	$roll_sub = "";
	print "Debug: adding readme, using empty roll_sub\n" if $opt_v > 4;
    } elsif ($pathname =~ m|^$srcdir/[^/]+/|o) {
	$roll_sub = basename(dirname($pathname));
	if ($roll_sub =~ /^\d{3}-(.*)$/) {
	    $roll_sub = $1;
	}
	print "Debug: orig roll_sub is: $roll_sub\n" if $opt_v > 4;
    } elsif ($pathname =~ m|^$srcdir/[^/]+$|o) {
	$roll_sub = "";
	print "Debug: no top dir, using empty roll_sub\n" if $opt_v > 4;
    } else {
	print STDERR "$0: FATAL: $pathname not under $srcdir\n";
	print "Debug: non-srcdir prune #13 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(33) unless defined $opt_a;
	return;
    }
    $roll_sub =~ tr/[A-Z]/[a-z]/;	# convert to lower case
    $roll_sub = "" if ($roll_sub eq "dcim");
    $roll_sub =~ s/-/_/g;	# -'s (dash) become _'s (underscore)
    $roll_sub = substr($roll_sub, 0, $roll_sub_maxlen) if $roll_sub_maxlen > 0;
    $roll_sub = "$rollnum-$roll_sub";
    print "Debug: roll_sub name: $roll_sub\n" if $opt_v > 2;

    # untaint roll_sub
    #
    if ($roll_sub =~ /$untaint/o) {
    	$roll_sub = $1;
    } else {
	print STDERR "$0: FATAL: strange chars in roll_sub \n";
	print "Debug: tainted roll_sub prune #14 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(34) unless defined $opt_a;
	return;
    }

    # determine the date of the image by EXIF or filename date
    #
    ($datecode, $datestamp, $exiffound) = old_timestamp($pathname);
    if ($datecode != 0) {
	print STDERR "$0: FATAL: EXIF image timestamp error $datecode: ",
		     "$datestamp\n";
	print "Debug: bad timestamp prune #15 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(35) unless defined $opt_a;
	return;
    }
    print "Debug: EXIF image / file timestamp: $datestamp\n" if $opt_v > 3;

    # If we are moving and we are only moving non-EXIF files, then
    # ignore bug to not prune EXIF data was found
    #
    # We must move non-EXIF files first because we need the EXIF data
    # from the related EXIF file.   To see why, consider the case where
    # we have:
    #
    #	.../inputdir/foo.cr2
    #	.../inputdir/foo.wav
    #
    # The timestamp on the destination filename for foo.wav (which
    # does not have EXIF data) depends on foo.cr2 (which has EXIF data).
    #
    # When we copy, there is file ordering problem.  When it comes time to
    # copy foo.wav, we have the original foo.cr2 to consult.  However in
    # the case of moving, if we move foo.cr2 first, then foo.wav no longer
    # has an associated EXIF file under the ../inputdir/ directory.
    #
    # To solve this problem, when moving, we move files without EXIF data
    # first, then on a 2nd pass we move everything else.
    #
    if (defined $opt_m && $premv_nonexif == 1 && $exiffound == 1) {
	# ignore but do not prune file with EXIF data when moving non-EXIF files
	print "Debug: EXIF 1st move pass ignore #10 $pathname\n" if $opt_v > 2;
    	return;
    }

    # untaint datestamp
    #
    if ($datestamp =~ /$untaint/o) {
	$datestamp = $1;
    } else {
	print STDERR "$0: FATAL: strange chars in datestamp \n";
	print "Debug: tainted datestamp prune #16 $pathname\n"
	    if $opt_v > 0;
	$File::Find::prune = 1;
	exit(36) unless defined $opt_a;
	return;
    }

    # canonicalize the filename
    #
    if ($adding_readme == 0) {
	($lowerfilename = $filename) =~ tr /[A-Z]/[a-z]/;	# lower case
    } else {
	# we always add the -r readme file as readme.txt
	$lowerfilename = "readme.txt";
    }
    print "Debug: canonical lowerfilename: $lowerfilename\n" if $opt_v > 4;

    # If the lowercase name is already of the form:
    #
    #	043-101-20050512-152545-ls1f5628.cr2
    #	043-101-20050512-152545_1-ls1f5628.cr2
    #
    # convert it to just ls1f5628.cr2 so that we won't keep adding
    # date strings to the filename.
    #
    if ($lowerfilename =~ /^\d{3}-[^-]*-\d{8}-\d{6}(_\d+)?-(.*)$/) {
	$lowerfilename = $2;
    }
    $lowerfilename =~ s/-/_/g;	# -'s (dash) become _'s (underscore)
    print "Debug: final lowerfilename: $lowerfilename\n" if $opt_v > 3;

    # convert the timestamp into date strings
    #
    $yyyymm = strftime("%Y%m", localtime($datestamp));
    $dd = strftime("%d", localtime($datestamp));

    # untaint yyyymm
    #
    if ($yyyymm =~ /$untaint/o) {
	$yyyymm = $1;
    } else {
	print STDERR "$0: FATAL: strange chars in yyyymm \n";
	print "Debug: tainted yyyymm prune #17 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(37) unless defined $opt_a;
	return;
    }

    # ensure the $destdir/yyyymm/roll_sub direct path exists
    #
    ($errcode, $errmsg) = form_dir("$destdir/$yyyymm");
    if ($errcode != 0) {
	print STDERR "$0: FATAL: mkdir error: $errmsg for ",
		     "$destdir/$yyyymm\n";
	print "Debug: mkdir err prune #18 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(38) unless defined $opt_a;
	return;
    }
    ($errcode, $errmsg) = form_dir("$destdir/$yyyymm/$roll_sub");
    if ($errcode != 0) {
	print STDERR "$0: FATAL: mkdir error: $errmsg for ",
		     "$destdir/$yyyymm/$roll_sub\n";
	print "Debug: mkdir err prune #19 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(39) unless defined $opt_a;
	return;
    }

    # deal with the case of when the destination file already exists
    #
    # If the filename exists, start adding _X for X 0 to 99
    # after the seconds.
    #
    $hhmmss = strftime("%H%M%S", localtime($datestamp));
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
	    print "Debug: dest file exists: $destpath\n" if $opt_v > 4;
	    $hhmmss_d = $hhmmss . "_" . ++$dupnum;

	    # if -o, then try to remove the old destination
	    #
	    if (defined $opt_o) {
		if (-f $destpath) {
		    print "Debug: -o pre-remove: $destpath\n" if $opt_v > 4;
		    unlink $destpath;
		    if ($opt_v > 4 && -f $destpath) {
			print "Debug: cannot pre-remove: $destpath: $!\n";
		    }
		} else {
		    print "Debug: will not -o pre-remove ",
			  "a non-file: $destpath\n" if $opt_v > 4;
		}
		if ($opt_v > 4 && -e $destpath) {
		    print "Debug: we must try another filename\n";
		}
	    }
	}

	# firewall - do not allow more than 99 duplicates
	#
	if ($dupnum > 99) {
	    print STDERR "$0: FATAL: more than 99 duplicates for ",
			 "$yyyymm-$roll_sub-$dd-$hhmmss-$lowerfilename\n";
	    print "Debug: 100 dups prune #20 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(40) unless defined $opt_a;
	    return;
	}
    } while (-e "$destpath");
    print "Debug: destination: $destname\n" if $opt_v > 1;
    print "Debug: destination path: $destpath\n" if $opt_v > 2;

    # untaint pathname
    #
    if ($pathname =~ /$untaint/o) {
	$pathname = $1;
    } else {
	print STDERR "$0: FATAL: strange chars in pathname \n";
	print "Debug: tainted pathname prune #21 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(41) unless defined $opt_a;
	return;
    }

    # untaint destpath
    #
    if ($destpath =~ /$untaint/o) {
	$destpath = $1;
    } else {
	print STDERR "$0: FATAL: strange chars in destpath \n";
	print "Debug: tainted destpath prune #22 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(42) unless defined $opt_a;
	return;
    }

    # copy (or move of -m) the image file
    #
    if (defined $opt_m) {
	if (move($pathname, $destpath) == 0) {
	    print STDERR "$0: FATAL: in ", $File::Find::dir, ": ",
			 "mv $filename $destpath failed: $!\n";
	    print "Debug: mv err prune #23 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(43) unless defined $opt_a;
	    return;
	}
	print "Debug: success: mv $filename $destpath\n" if $opt_v > 2;
    } else {
	if (copy($pathname, $destpath) == 0) {
	    print STDERR "$0: FATAL: in ", $File::Find::dir, ": ",
			 "cp $filename $destpath failed: $!\n";
	    print "Debug: cp err prune #24 $pathname\n" if $opt_v > 0;
	    $File::Find::prune = 1;
	    exit(44) unless defined $opt_a;
	    return;
	}
	print "Debug: success: cp $filename $destpath\n" if $opt_v > 2;
    }

    # compare unless -m
    #
    if (! defined $opt_m && compare($pathname, $destpath) != 0) {
	print STDERR "$0: FATAL: in ", $File::Find::dir, ": ",
		     "compare of $filename and $destpath failed\n";
	print "Debug: cmp err prune #25 $pathname\n" if $opt_v > 0;
	$File::Find::prune = 1;
	exit(45) unless defined $opt_a;
	return;
    }
    if ($opt_v > 2 && ! defined $opt_m) {
	print "Debug: success: cmp $filename $destpath\n";
    }

    # set the access and modification time unless -t
    #
    if (! defined $opt_t) {
	utime $datestamp, $datestamp, $destpath;
    }
    print "Debug: processed: $destpath\n" if $opt_v > 0;
    return;
}


# old_timestamp - determine a file date string using EXIF and file timestamps
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
#	($exitcode, $message, $exiffound)
#	    $exitcode:	0 ==> OK, else ==> exit code
#	    $message:	$exitcode==0 ==> timestamp, else error message
#	    $exiffound:	1 ==> valid EXIF time data found, 0 ==> no EXIF time
#
sub old_timestamp($)	# XXX - remove when code complete
{
    my ($filename) = @_;	# get args
    my $noext;			# filename without any extension
    my $exif_file;		# a potential EXIF related filename
    my $extension;		# a potential EXIF related file extension
    my $errcode;		# 0 ==> OK
    my $timestamp = -1;	# seconds since the epoch of early timestamp or -1
    my $filename_dev;		# device of the $filename arg
    my $filename_ino;		# inode number of the $filename arg

    # try to get an EXIF based timestamp
    #
    print "Debug: looking for EXIF timestamp in $filename\n" if $opt_v > 4;
    ($errcode, $timestamp) = exif_date($filename);
    if ($errcode == 0) {
	print "Debug: EXIF timestamp for $filename: $timestamp\n" if $opt_v > 4;
	return (0, $timestamp, 1);
    }
    print "Debug: EXIF timestamp $filename: return code: $errcode: ",
    	  "$timestamp\n" if $opt_v > 4;

    # We did not find a valid EXIF in the filename, so we will
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
		print "Debug: ignoring EXIF file: $exif_file, same as ",
		      "filename: $filename\n" if $opt_v > 5;
		next;
	    }

	    # try to get an EXIF based timestamp
	    #
	    print "Debug: looking at related filename: $exif_file\n"
	    	if $opt_v > 4;
	    ($errcode, $timestamp) = exif_date($exif_file);

	    # return EXIF data if we were able to find a good timestamp
	    #
	    if ($errcode == 0) {
		print "Debug: found related EXIF timestamp in $exif_file: ",
			"$timestamp\n" if $opt_v > 4;
		return (0, $timestamp, 0);
	    }
	    print "Debug: EXIF timestamp $filename: EXIF code: $errcode: ",
		  "$timestamp\n" if $opt_v > 5;
	}
    }
    print "Debug: found no related EXIF file for: $filename\n" if $opt_v > 4;

    # If the file is a txt file or a file without an extension,
    # then look for a Date: string in the early lines of the file.
    #
    if ($filename =~ /\.txt$/i || basename($filename) !~ /\./) {
	print "Debug: looking for text date in $filename\n" if $opt_v > 4;
	($errcode, $timestamp) = text_date($filename);
	if ($errcode == 0) {
	    print "Debug: text timestamp for file: $filename: $timestamp\n"
	        if $opt_v > 4;
	    return (0, $timestamp, 0);
	}
	print "Debug: no valid text date found in $filename\n" if $opt_v > 4;
    }

    # No valid EXIF timestamps in the file or related readable files.
    # Try the file's creation / modification timestamp and return
    # whatever it says ... a timestamp or error.
    #
    print "Debug: forced to use file timestamp for $filename\n" if $opt_v > 4;
    ($errcode, $timestamp) = file_date($filename);
    if ($opt_v > 4) {
	if ($errcode == 0) {
	    print "Debug: timestamp for file: $filename: $timestamp\n";
	} else {
	    print "Debug: file timestamp: $filename: error: $errcode: ",
	    	  "$timestamp\n";
	}
    }
    return ($errcode, $timestamp, 0);
}
