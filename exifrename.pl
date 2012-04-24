#!/usr/bin/perl -wT
#
# exifrename - copy files based on EXIF or file time data
#
# @(#) $Revision: 4.6 $
# @(#) $Id: exifrename.pl,v 4.6 2009/08/01 23:12:11 chongo Exp root $
# @(#) $Source: /usr/local/src/cmd/exif/RCS/exifrename.pl,v $
#
# Copyright (c) 2005-2006 by Landon Curt Noll.	All Rights Reserved.
#
# Permission to use, copy, modify, and distribute this software and
# its documentation for any purpose and without fee is hereby granted,
# provided that the above copyright, this permission notice and text
# this comment, and the disclaimer below appear in all of the following:
#
#	supporting documentation
#	source copies
#	source works derived from this source
#	binaries derived from this source or from derived source
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
	    $opt_s $opt_r $opt_n $opt_y $opt_z $opt_k $opt_d $opt_u);
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
my $VERSION = substr q$Revision: 4.6 $, 10;
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
my $untaint = qr|^([-+\w\s./][-+\w\s./~]*)$|;	# untainting path pattern
my $untaint_file = qr|^([-+\w\s.][-+\w\s./~]*)$|; # untainting pattern w/o /'s
my $datelines = 16;	# date: must be in the 1st datelines of a file
my %mname = (
    "Jan" => 0, "Feb" => 1, "Mar" => 2, "Apr" => 3, "May" => 4, "Jun" => 5,
    "Jul" => 6, "Aug" => 7, "Sep" => 8, "Oct" => 9, "Nov" => 10, "Dec" => 11,
);
my $roll_sub_maxlen = 3;	# max length of a roll_sub (0 ==> unlimited)
my $roll_sub_skip = 0;	# ignore this many leading chars when forming roll_sub
my $rollfile;		# file that keeps track of next roll number
my $mv_fwd_chars = 4;	# chars after 1st -z skchars put near filename front
my $mv_end_chars = 4;	# initial -z skchars put near end of filename
my $readme_path = undef;	# if -r readme, this is the absolute src path
my $readme_dev = undef;		# if -r readme, this is the device number
my $readme_ino = undef;		# if -r readme, this is the inode number
my $readme_timestamp = undef;	# if -r readme, this is its special timestamp
my $max_dup = 100;	# optional 2 de-dup digits allow for up to 100 dups


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
#	value: array of paths with the same base w/o .ext
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
# $have_mkdir{$dir}
#	key: directory to be made
#	value: 1 ==> created, 0 ==> already exists
#	NOTE: Useful in conjunction with -d to note when we might have
#	      already created a directory.
#
# $destpath_path{"$path_destdir{$path}/$path_destfile{$path}"}
#	key: destination directory/filename
#	value: source path
#	NOTE: This is used to detect when multiple source files are be targeted
#	      to the same destination file.  This can happen when we are
#	      converting old or new filename formats.
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
my %have_mkdir;
my %destpath_path;

# timestamps prior to:
#	Tue Nov	 5 00:53:20 1985 UTC
# are too old for an image with EXIF data.   See:
#	perl -e 'my $x=500000000; print scalar gmtime($x), "\n";'
#
my $mintime = 500000000;

# usage and help
#
my $usage = "$0 [-a] [-c] [-e exifroll] [-k roll_subskip] [-m] [-n rollnum]\n".
    "  [-o] [-r readme] [-s roll_sublen] [-t] [-u] [-y seqlen] [-z skchars]\n" .
    "  [-h] [-d] [-v lvl] srcdir destdir";
my $help = qq{\n$usage

    -a		 don't abort/exit after post-setup fatal errors (def: do)
    -c		 don't verify/compare files after they are copied (def: do)
    -e exifroll	 use/update roll num in exifroll (def: use/update ~/.exifroll)
    -k roll_subskip	 skip the leading roll_subskip chars (def: 0)
    -m		 move, do not copy files from srcdir to destdir (def: copy)
    -n rollnum	 roll is rollnum, don't update exifroll (def: use ~/exifroll)
    -o		 overwrite, don't add _# after mmss on duplicates (def: add)
    -r readme	 add readme as if it was srcdir/readme.txt (def: don't)
    -s roll_sublen	max length of roll_sub (def: 3, 0 ==> unlimited)
    -t		 don't touch modtime to match EXIF/file image (def: do)
    -u		 update only, ignore src if dest has same length (def: don't)
    -y seqlen	 sequence length, image filename chars after skchars (def: 4)
    -z skchars	 initial image-name chars not part of sequence number (def: 4)

    -h		 print this help message
    -d		 do nothing / "dry run", do not create/alter any file (def: do)
    -v lvl	 set verbose / debug level to lvl (def: 0)

    srcdir	 source directory (must exist)
    destdir	 destination directory (must exist)

    NOTE: exit 0 means all is OK, exit !=0 means some fatal error

    Version: $VERSION};
my %optctl = (
    "a" => \$opt_a,
    "c" => \$opt_c,
    "d" => \$opt_d,
    "e=s" => \$opt_e,
    "h" => \$opt_h,
    "k=i" => \$opt_k,
    "m" => \$opt_m,
    "n=s" => \$opt_n,
    "o" => \$opt_o,
    "r=s" => \$opt_r,
    "t" => \$opt_t,
    "s=i" => \$opt_s,
    "u" => \$opt_u,
    "v=i" => \$opt_v,
    "y=i" => \$opt_y,
    "z=i" => \$opt_z,
);


# function prototypes
#
sub parse_args();
sub destdir_path($$$);
sub dir_setup();
sub wanted($);
sub set_destname();
sub get_timestamp($$);
sub exif_date($);
sub text_date($);
sub form_dir($);
sub roll_setup();
sub create_destination();
sub readme_check($);
sub create_readme_link();
sub set_timestamps();
sub forget_path($);
sub warning($);
sub error($$);
sub dbg($$);


# setup
#
MAIN:
{
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
    # must be in UTC timezone so that filename timestamps work correctly!
    $ENV{TZ} = "UTC";
    $rollfile = "$ENV{HOME}/.exifroll";

    # parse args
    #
    parse_args();

    # initialize roll serial number $rollnum
    #
    roll_setup();

    # setup to walk the srcdir
    #
    $find_opt{wanted} = \&wanted; # call this on each non-pruned node
    $find_opt{bydepth} = 0;	# walk from top down, not from bottom up
    $find_opt{follow} = 0;	# do not follow symlinks
    $find_opt{no_chdir} = 0;	# OK to chdir as we walk the tree
    $find_opt{untaint} = 1;	# untaint dirs we chdir to
    $find_opt{untaint_pattern} = $untaint; # untaint pattern
    $find_opt{untaint_skip} = 1; # we will skip any dir that is tainted

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
    set_timestamps();

    # add in readme.txt if -r readme was given
    #
    if ($opt_r) {
	$path_basenoext{$readme_path} = "readinfome";
	$path_roll_sub{$readme_path} = undef;
	$devino_path{"$readme_dev/$readme_ino"} = $readme_path;
	$path_filetime{$readme_path} = $readme_timestamp;
	$need_plus{$readme_path} = 0;
	push(@{$basenoext_pathset{$path_basenoext{$readme_path}}},
	     $readme_path);
	$pathset_timestamp{$path_basenoext{$readme_path}} = $readme_timestamp;
	dbg(1, "readme timestamp: " . gmtime($readme_timestamp) . " UTC");
	# $path_destdir{$readme_path} will be filled in by dir_setup()
	# $path_destfile{$readme_path} will be filled in by set_destname()
	dbg(2, "added -r readme file: $readme_path");
    }

    # setup directories
    #
    # Fill in %path_destdir and create all destination directories.
    #
    dir_setup();

    # determine destination filenames
    #
    set_destname();

    # copy or more src files to destination files
    #
    create_destination();

    # create readme.txt link if -r readme was given
    #
    if ($opt_r) {
	create_readme_link();
    }

    # all done
    #
    exit(0);
}


# parse_args - parse the command line, set flags and sanity check options
#
sub parse_args()
{
    # process command line options
    #
    if (!GetOptions(%optctl)) {
	print STDERR "$0: usage: $help\n";
	error(1, "invalid command line");
    }
    if (defined $opt_h) {
	# just print help, no error
	print STDERR "$0: usage: $help\n";
	exit(0);
    }

    # sanity checks on options
    #
    if (defined $opt_m && defined $opt_c) {
	# cannot compare if we are moving
	error(2, "-c (compare) conflicts with -m (move)");
    }
    if (! defined $ARGV[0] || ! defined $ARGV[1]) {
	error(3, "missing args, usage:\n$help");
    }
    if (defined $ARGV[2]) {
	error(4, "too many args, usage:\n$help");
    }
    if (defined $opt_e && defined $opt_n) {
	error(5, "-e exifroll conflicts with -n rollnum");
    }
    if (defined $opt_k && $opt_k < 0) {
	error(6, "-k roll_subskip must be >= 0");
    }
    if (defined $opt_s && $opt_s < 0) {
	error(7, "-s roll_sublen must be >= 0");
    }
    if (defined $opt_y && $opt_y < 0) {
	error(8, "-y seqlen must be >= 0");
    }
    if (defined $opt_z && $opt_z < 0) {
	error(9, "-z skchars must be >= 0");
    }
    if (defined $opt_u && defined $opt_o) {
	error(10, "-o conflicts with -u");
    }

    # set values based on options
    #
    $roll_sub_maxlen = $opt_s if defined $opt_s;
    $roll_sub_skip = $opt_k if defined $opt_k;
    $rollfile = $opt_e if defined $opt_e;
    # canonicalize srcdir removing leading ./'s, multiple //'s, trailing /'s
    $srcdir = $ARGV[0];
    if (! -d $srcdir) {
    	error(11, "srcdir does not exist: $srcdir");
    }
    $srcdir = abs_path($srcdir);
    $srcdir =~ s|^(\./+)+||;
    $srcdir =~ s|//+|/|g;
    $srcdir =~ s|(.)/+$|$1|;
    if (! -d $srcdir) {
    	error(12, "revised srcdir does not exist: $srcdir");
    }
    $srcdir = abs_path($srcdir);
    if (! -d $srcdir) {
    	error(13, "absolute path of srcdir does not exist: $srcdir");
    }
    # canonicalize destdir removing leading ./'s, multiple //'s, trailing /'s
    $destdir = $ARGV[1];
    if (! -d $destdir) {
    	error(14, "destdir does not exist: $destdir");
    }
    $destdir = abs_path($destdir);
    $destdir =~ s|^(\./+)+||;
    $destdir =~ s|//+|/|g;
    $destdir =~ s|(.)/+$|$1|;
    if (! -d $destdir) {
    	error(15, "revised destdir does not exist: $destdir");
    }
    $destdir = abs_path($destdir);
    if (! -d $destdir) {
    	error(16, "absolute path of destdir does not exist: $destdir");
    }
    $mv_fwd_chars = $opt_y if defined $opt_y;
    $mv_end_chars = $opt_z if defined $opt_z;

    # verbose arg debug
    #
    dbg(1,
      "options:" .
      (defined $opt_a ? " -a" : "") .
      (defined $opt_c ? " -c" : "") .
      (defined $opt_d ? " -d" : "") .
      (defined $opt_e ? " -e $opt_e" : "") .
      (defined $opt_h ? " -h" : "") .
      (defined $opt_k ? " -k $opt_k" : "") .
      (defined $opt_m ? " -m" : "") .
      (defined $opt_n ? " -n $opt_n" : "") .
      (defined $opt_o ? " -o" : "") .
      (defined $opt_r ? " -r $opt_r" : "") .
      (defined $opt_s ? " -s $opt_s" : "") .
      (defined $opt_t ? " -t" : "") .
      (defined $opt_u ? " -u" : "") .
      (defined $opt_v ? " -v $opt_v" : "") .
      (defined $opt_y ? " -y $opt_y" : "") .
      (defined $opt_z ? " -z $opt_z" : "") .
      " $srcdir $destdir");
    if ($opt_c) {
	dbg(1, "won't verify/compare files afterwords");
    }
    if ($opt_m) {
	dbg(1, "will move (not copy) files");
    } else {
	dbg(1, "will copy (not move) files");
    }
    if ($opt_o) {
	dbg(1, "override existing files");
    } else {
	dbg(1, "change new filenames so as to not overwrite existing files");
    }
    dbg(1, "~/exifroll file: $rollfile");
    dbg(1, "roll_sub max length is " .
	   ($roll_sub_maxlen > 0 ? $roll_sub_maxlen : "unlimited"));
    dbg(1, ($opt_t ? "don't" : "do") . " touch file modtimes");
    if ($opt_r) {
	dbg(1, "will special process readme file: $opt_r");
    }
    if ($opt_u) {
	dbg(1, "will ignore src if dest file exists with same length");
    }
    dbg(1, "srcdir: $srcdir");
    dbg(1, "destdir: $destdir");

    # sanity check readme if -r readme was given
    #
    if (defined $opt_r) {
	$readme_path = readme_check($opt_r);
	dbg(1, "-r readme file is sane: $opt_r");
	($readme_dev, $readme_ino,) = stat($readme_path);
	if (! defined $readme_dev || ! defined $readme_ino) {
	    error(17, "stat error on $readme_path: $!");
	}
	if (!defined $readme_path) {
	    error(18, "-r $opt_r but we have no readme_path");
	}
	if (!defined $readme_path) {
	    error(19, "-r $opt_r but we have no readme_timestamp");
	}
	if (!defined $readme_dev) {
	    error(20, "-r $opt_r but we have no readme_dev");
	}
	if (!defined $readme_ino) {
	    error(21, "-r $opt_r but we have no readme_ino");
	}
    }

    # untaint $srcdir, $destdir, and $rollfile
    #
    if ($srcdir =~ /$untaint/o) {
	$srcdir = $1;
    } else {
	error(22, "bogus chars in srcdir");
    }
    if ($destdir =~ /$untaint/o) {
	$destdir = $1;
    } else {
	error(23, "bogus chars in destdir");
    }
    if ($rollfile =~ /$untaint/o) {
	$rollfile = $1;
    } else {
	error(24, "bogus chars in -e filename");
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
#	do under just $destdir/$dir1-$dir2.
#
# returns:
#	($dir0, $dir1, $dir2, $dir3) == the directory names for a given path,
#	The destination directory will be:
#
#	    $destdir/$dir0/$dir1/$dir1-$dir2/$dir1-$dir2-$dir3
#
# or if $dir3 is not used:
#
#	    $destdir/$dir0/$dir1/$dir1-$dir2
#
# NOTE: Does not return on error.
#
sub destdir_path($$$)
{
    my ($timestamp, $roll, $roll_sub) = @_;
    my $yyyy;		# EXIF or filename timestamp UTC year
    my $yyyymm;		# EXIF or filename timestamp UTC year and UTC month

    # convert timestamp into a yyyy date in UTC
    #
    $yyyy = strftime("%Y", gmtime($timestamp));
    if (defined $yyyy && $yyyy =~ /$untaint/o) {
	$yyyy = $1;
    } else {
	error(30, "strange chars in yyyy for timestamp: $timestamp");
    }

    # convert timestamp into a yyyymm date in UTC
    #
    $yyyymm = $yyyy . strftime("%m", gmtime($timestamp));
    if (defined $yyyymm && $yyyymm =~ /$untaint/o) {
	$yyyymm = $1;
    } else {
	error(31, "strange chars in yyyymm for timestamp: $timestamp");
    }

    # firewall - untaint and sanity check roll number
    #
    if ($roll =~ /$untaint_file/o) {
	$roll = $1;
    } else {
	error(32, "bogus chars in roll");
    }
    if ($roll =~ /^\s*$/) {
	error(33, "roll is empty or only has whitespace");
    } elsif ($roll =~ /^\./) {
	error(34, "roll start with a .");
    }

    # firewall - untaint and sanity check roll_sub
    #
    if (defined $roll_sub) {
	if ($roll_sub =~ /$untaint_file/o) {
	    $roll_sub = $1;
	} else {
	    error(35, "bogus chars in roll_sub");
	}
	if ($roll_sub =~ /^\s*$/) {
	    error(36, "roll_sub is empty or only has whitespace");
	} elsif ($roll_sub =~ /^\./) {
	    error(37, "roll_sub start with a .");
	}
    } else {
	$roll_sub = undef;
    }

    # return the directory levels
    #
    return ($yyyy, $yyyymm, $roll, $roll_sub);
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
    my $dir0;			# top level yyyy name
    my $dir1;			# 1st level yyyymm name
    my $dir2;			# 2nd level rolnum name
    my $dir3;			# 3rd level sub-rolnum name
    my $err;			# >0 ==> fatal error number, 0 ==> OK

    # firewall - check for a sane srcdir
    #
    if (! -e $srcdir) {
	error(40, "srcdir does not exist: $srcdir");
    }
    if (! -d $srcdir) {
	error(41, "srcdir is not a directory: $srcdir");
    }
    if (! -r $srcdir) {
	error(42, "srcdir is not readable: $srcdir");
    }
    if (! -x $srcdir) {
	error(43, "srcdir is not searchable: $srcdir");
    }

    # setup the destination directory if needed
    #
    ($errcode, $errmsg) = form_dir($destdir);
    if ($errcode != 0) {
	error(44, "destdir mkdir error: $errmsg for $destdir");
    }

    # record the device and inode number of $destdir
    #
    ($destdev, $destino,) = stat($destdir);

    # create, if needed, all the required sub-directories under destdir
    #
    for $path ( sort keys %path_basenoext ) {

	# get the 3 subdir levels
	#
	# NOTE: In the case of the -r readme.txt file, the roll_sub will
	#	be undef and $dir3 will be undef because that file will
	#	do under just $destdir/$dir1-$dir2.
	#
	($dir0, $dir1, $dir2, $dir3) = destdir_path(
	    $pathset_timestamp{$path_basenoext{$path}},
	    $rollnum,
	    $path_roll_sub{$path});

	# add the 3 paths to the set of directories to check
	#
	if (defined $dir3) {
	    push(@need_subdir,
		    "$destdir/$dir0",
		    "$destdir/$dir0/$dir1",
		    "$destdir/$dir0/$dir1/$dir1-$dir2",
		    "$destdir/$dir0/$dir1/$dir1-$dir2/$dir1-$dir2-$dir3");
	    $path_destdir{$path} =
	        "$destdir/$dir0/$dir1/$dir1-$dir2/$dir1-$dir2-$dir3";
	} else {
	    push(@need_subdir,
		    "$destdir/$dir0",
		    "$destdir/$dir0/$dir1",
		    "$destdir/$dir0/$dir1/$dir1-$dir2");
	    $path_destdir{$path} = "$destdir/$dir0/$dir1/$dir1-$dir2";
	}
	dbg(4, "destination of $path is $path_destdir{$path}");
    }

    # now form all of the required destdir subdirs
    #
    $err = 0;
    foreach $path ( sort @need_subdir ) {
	($errcode, $errmsg) = form_dir("$path");
	if ($errcode != 0) {
	    error(-$errcode, "subdir mkdir error: $errmsg for: $path");
	    $err = $errcode;	# delayed exit
	    next;
	}
    }
    exit($err) if ($err != 0);
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
# We maintain a file timestamp for each path to a file.	 This
# timestamp is usually the file create time or file modification time,
# which ever is older.	When selecting the older of create and mod times,
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
# These .DS_Store files should be ignored by the tool.	The Titanium
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
#	/DCIM/EOSMISC/		# Canon Miscellaneous .CTG extension files
#	*.CTG			# helps storage / maint. of files on CF card
#
# In addition, for path purposes, we do not create DCIM as a path component
# when forming files and links in destdir.
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
#	$File::Find::name	complete pathname to the file
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
    my $roll_sub;		# roll sub directory

    # canonicalize the path by removing leading ./'s, multiple //'s
    # and trailing /'s
    #
    dbg(4, "in wanted(): $file");
    ($pathname = $File::Find::name) =~ s|^(\./+)+||;
    $pathname =~ s|//+|/|g;
    $pathname =~ s|(.)/+$|$1|;
    if ($pathname =~ /$untaint/o) {
	$pathname = $1;
    } else {
	warning("tainted filename prune #1 $pathname");
	$File::Find::prune = 1;
	return;
    }
    dbg(5, "in wanted(): pathname: $pathname");

    # prune out anything that is not a directory
    #
    if (! -d $file) {
	# skip non-dir/non-files
	dbg(4, "non-directory prune #2 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # prune out certain top level paths
    #
    # As noted in detail above, we will prune off any .Trashes,
    # .comstate.tof qne DCIM/EOSMISC dirs that are directly under $srcdir
    #
    if ($pathname eq "$srcdir/.Trashes") {
	# skip this useless camera node
	dbg(4, ".Trashes prune #3 $pathname");
	$File::Find::prune = 1;
	return;
    }
    if ($pathname eq "$srcdir/comstate.tof") {
	# skip this useless camera node
	dbg(4, "comstate.tof prune #4 $pathname");
	$File::Find::prune = 1;
	return;
    }
    if ($pathname eq "$srcdir/DCIM/EOSMISC") {
	# skip Canon misc. non-photo directory
	dbg(4, "DCIM/EOSMISC prune #5 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # prune out .DS_Store files
    #
    if ($file eq ".DS_Store") {
	# skip OS X .DS_Store files
	dbg(4, ".DS_Store prune #6 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # prune out files that end in .Trashes
    #
    if ($file =~ /.Trashes$/) {
	# skip OS X .DS_Store files
	dbg(4, "*.Trashes prune #7 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # prune out Titanium Toast files
    #
    if ($file =~ /^desktop d[bf]$/i) {
	# skip Titanium Toast files
	dbg(4, "desktop prune #8 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # prune out Spotlight index directories
    #
    if ($file =~ /^\.Spotlight-/i) {
	# skip Spotlight index directories
	dbg(4, "Spotlight prune #9 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # prune out anything that start with . except for . itself
    #
    if ($file =~ /^\../) {
	# skip . files and dirs
	dbg(4, "dot-file/dir prune #10 $pathname");
	$File::Find::prune = 1;
	return;
    }

    # ignore non-readable directories
    #
    if (! -r $file) {
	error(50 * ($opt_a?-1:1), "skipping non-readable directory: $pathname");
	$File::Find::prune = 1;
	return;
    }

    # open this directory for filename collection
    #
    if (! opendir DIR,$file) {
	error(51 * ($opt_a?-1:1), "opendir failed on: $pathname: $!");
	$File::Find::prune = 1;
	return;
    }
    dbg(1, "scanning source directory: $pathname");

    # collect useful filenames from this open directory
    #
    while (defined($entry = readdir(DIR))) {

	# ignore these names (listed as file globs, not reg expressions):
	#
	#	*.tof
	#	desktop*
	#	*.Trashes
	#	.*
	#	*.ctg
	#
	if ($entry =~ /\.tof$/i || $entry =~ /^desktop/i ||
	    $entry =~ /\.Trashes$/i || $entry =~ /^\./ ||
	    entry =~ /\.ctg$/i) {
	    dbg(6, "under $pathname ignoring name of: $entry");
	    next;
	}
	$path = "$pathname/$entry";

	# ignore any entry that is not a file
	#
	if (! -f $path) {
	    dbg(6, "under $pathname ignoring non-file: $entry");
	    next;
	}

	# ignore any non-readable file
	#
	if (! -r $path) {
	    warning("ignoring non-readable file: $pathname/$entry");
	    next;
	}

	# stat the file
	#
	# NOTE: We stat here because perl will have cached the stat data
	#	due to the above -f and -r tests.  Doing the stat now
	#	rather than later saves on system calls.
	#
	dbg(4, "under $pathname found: $entry");
	($dev, $ino, undef, undef, undef, undef, undef, undef,
	 undef, $mtime, $ctime) = stat($path);
	if (! defined $dev || ! defined $ino ||
	    ! defined $mtime || ! defined $ctime) {
	    error(52 * ($opt_a?-1:1), "stat failed for: $path $!");
	    $File::Find::prune = 1;
	    return;
	}

	# ignore if we happen to find the -r readme.txt file
	#
	# This is to avoid duplicate processing and to ensure that
	# readme file is processed in a special way.
	#
	if (defined $readme_dev && $dev == $readme_dev &&
	    defined $readme_ino && $ino == $readme_ino) {
	    dbg(6, "for now, skipping -r readme file: $pathname/$entry");
	    dbg(1, "readme skip file #16 $path");
	    next;
	}

	# firewall - must not have seen this device/inode number combo before
	#
	if (defined $devino_path{"$dev/$ino"}) {
	    warning("dup dev/ino found: dev: $dev inum: $ino");
	    dbg(1, "duplicate skip #17 $path same file as " .
		   "$devino_path{$dev/$ino}");
	    next;
	}

	# save the found basename w/o .ext
	#
	($basenoext = $entry) =~ s/\.[^.]*$//;
	if ($basenoext eq "readme" && defined $opt_r) {
	    warning("-r was given found file with a basename of readme " .
		 "(w/o .extension)");
	    dbg(1, "duplicate prune #18 $path readme basename w/o " .
		   ".extension: $path");
	    next;
	}
	dbg(3, "recording information about $path");
	$path_basenoext{$path} = $basenoext;

	# save the found device/inum for duplicate detection
	#
	$devino_path{"$dev/$ino"} = $path;

	# track which paths have the same basename w/o .ext
	#
	if (defined $basenoext_pathset{$basenoext}) {
	    # multi-file pathset, mark both paths
	    $need_plus{$path} = 1;
	    $need_plus{@{$basenoext_pathset{$basenoext}}[0]} = 1;
	    # save this base w/o .ext in the pathset
	    push(@{$basenoext_pathset{$basenoext}}, $path);
	    dbg(5, "added $path to $basenoext pathset, pathset size: " .
		   scalar(@{$basenoext_pathset{$basenoext}}));
	} else {
	    # not a dup (yet)
	    $need_plus{$path} = 0;
	    # save this base w/o .ext in the pathset
	    push(@{$basenoext_pathset{$basenoext}}, $path);
	    dbg(5, "added $path to new $basenoext pathset, pathset size: " .
		   scalar(@{$basenoext_pathset{$basenoext}}));
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
	dbg(4, "file timestamp: $path_filetime{$path} for $path");

	# calculate the roll_sub
	#
	# The roll_sub is the directory name, converted to lower case,
	# under which we found this file.
	#
	# If the directory name is not usable, then the roll_sub will be undef.
	# These are directory names that are not usable:
	#
	#	is DCIM in any case
	#	an empty string
	#	contains only whitespace
	#	contain a /
	#	starts with a .
	#	is the same as the top level directory (srcdir)
	#
	$roll_sub = lc(basename($pathname));
	dbg(5, "original lowercase roll_sub: $roll_sub");
	if ($roll_sub =~ /^dcim$/) {
	    $roll_sub = undef;
	    dbg(4, "converted DCIM roll_sub to undef");
	} elsif ($roll_sub =~ /^\s*$/) {
	    $roll_sub = undef;
	    dbg(4, "converted empty/blank roll_sub to undef");
	} elsif ($roll_sub =~ /\//) {
	    $roll_sub = undef;
	    dbg(4, "converted /-based roll_sub to undef");
	} elsif ($roll_sub =~ /^\./) {
	    $roll_sub = undef;
	    dbg(4, "converted .-based roll_sub to undef");
	} elsif ($dev == $File::Find::topdev && $ino == $File::Find::topino) {
	    $roll_sub = undef;
	    dbg(4, "converted srcdir roll_sub to undef");

	# roll-subs that were part of a old historic or new sub-directory
	# are parsed and the non-roll_sub part is removed.
	#
	} elsif ($roll_sub =~ /^\d{3}-(\d{3})$/) {
	    $roll_sub = $1;
	    dbg(4, "converted roll-roll_sub to: $roll_sub");
	} elsif ($roll_sub =~ /^\d{3}-$/) {
	    $roll_sub = undef;
	    dbg(4, "converted roll- into undef");
	} elsif ($roll_sub =~ /^\d{6}-\d{3}-(\d{3})$/) {
	    $roll_sub = $1;
	    dbg(4, "converted yyyymm-roll-roll_sub to: $roll_sub");
	} elsif ($roll_sub =~ /^\d{6}-\d{3}-$/) {
	    $roll_sub = undef;
	    dbg(4, "converted yyyymm-roll- into undef");
	} elsif ($roll_sub =~ /^\d{6}-\d{3}$/) {
	    $roll_sub = undef;
	    dbg(4, "converted yyyymm-roll into undef");

	# if we have a roll_sub, canonicalize it
	#
	} else {

	    # We convert all -'s (dashed) in the roll_sub to _'s (underscores)
	    #
	    if ($roll_sub =~ /-/) {
		$roll_sub = s/-/_/g;
		dbg(6, "changed all - to _ in roll_sub");
	    }

	    # We truncate the roll_sub to the first roll_sub_maxlen (which can
	    # be changed from the default by -s roll_sublen) if roll_sub_maxlen
	    # is > 0.  A 0 roll_sub_maxlen means we use the full roll_sub.
	    #
	    # We will skip the first roll_sub_skip chars (which can be changed
	    # from the default by -k roll_subskip).
	    #
	    $roll_sub = substr($roll_sub, $roll_sub_skip, $roll_sub_maxlen);

	    # save the final roll_sub
	    #
	    dbg(4, "using roll_sub: $roll_sub");
	}

	# save the roll_sub for this path, which may be undef
	#
	$path_roll_sub{$path} = $roll_sub;
    }

    # cleanup
    #
    closedir DIR;
    dbg(3, "finished scanning dir: $pathname");
    return;
}


# set_destname - determine the destination basenames
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
#    /destdir/2005/200505/200505-043/200505-043-101/12152545-5627-200505-043-101-pg5v.cr2
#
# The created file path is:
#
#	/destdir			# destdir path of image library
#	/2005				# image year
#	/200505				# image year & month
#	/200505-043			# year & month, -, roll
#	/200505-043-010			# year & month, -, roll, -, roll-subdir
#	/12152545-5627-200505-043-101-pg5v.cr2 # image filename (see below)
#
# NOTE: The property of directory names under /destdir that they are
#	unique and standalone.	 One can look at one of these sub-directories
#	and know where it belongs.  That is why the yyyymm and yyyymm-roll
#	are repeated in the lower level directories.
#
# NOTE: The property of a filename is that they completely define the
#	directory path under whey they belong.	One can look at a filename
#	and know where it belongs.
#
# NOTE: Another important property of a filename is that the original
#	image filename can be re-constructed.  Consider these filenames:
#
#		12152545+5627-200505-043-101-pg5v.cr2
#		12152545+5627_01-200505-043-101-pg5v~stuff.cr2
#
#	the original image filenames were:
#
#		PGV55627.CR2
#		PGV55627STUFF.CR2
#
# Consider this filename:
#
#	12152545+5627-200505-043-101-pg5v.cr2
#
# If another image was taken during the same second, that 2nd image becomes:
#
#	12152545+5627_01-200505-043-101-pg5v.cr2
#
# is constructed out of the following:
#
#	12		# image day of month (UTC), 2 digits [01-31]
#	15		# image hour (UTC), 2 digits [00-23]
#	25		# image minute of hour (UTC), 2 digits [00-59]
#	45		# image second of minutes (UTC), 2 digits [00-60]
#	- or +		# + ==> multi-file set (.cr2 & .wav), - ==> just 1 file
#	5627		# image sequence number (see NOTE below)
#	     _		# (underscore) optional
#	     01		# optional 2 de-duplicate digits
#	-		# (dash) separator
#	2005		# image 4 digit Year (UTC)
#	05		# image month (UTC), 2 digits [01-12]
#	-		# (dash) separator
#	043		# roll number, 3 digits, 0 padded
#	-		# (dash) separator
#	101		# optional subdir lead chars, w/o -'s lowercase
#	-		# (dash) separator
#	pg5v		# imagename w/o 5th-8th chars, lowercase no -'s
#	    _		# (underscore) optional if trailing chars
#	    rest	# optional trailing image filename chars
#	.cr2		# .extension
#
# NOTE: The number of leading image filename chars defaults to 4 characters.
#	The default length can be changed by the -y seqlen option.  These
#	chars come from the image filename after it has been lower cased and
#	had -'s removed AND the initial image filename chars (which also
#	defaults to 4 and may be changed by the -z skchars option) have been
#	skipped.
#
#	By default, the 1st 4 chars of the image filename are not used as part
#	of the image sequence number.  These initial image filename characters
#	are usually fixed for a given camera and are left on the end of
#	the filename.  This default not-used length can be changed by
#	the -z skchars option.
#
#	If there are any remaining image filename chars beyond the sequence
#	number and before the .file extension, we put them after an _
#	(underscore) character.
#
#	A typical Canon EOS 1D Mark II N image filename:
#
#		pg5v5627.cr2
#
#	would, by default, have its chars moved into a filename of this form:
#
#		dddhhmmss-5627-...-pg5v.cr2
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
# generation of this tool.  These older filenames are of the form:
#
#	999-999-99999999-999999-zzzz9999.xyz
#
# Example: If the lowercase name is already of the form:
#
#	12152545+5627-200505-043-101-pg5v.cr2
#	12152645+5628_01-200505-043-101-pg5v.cr2
#	043-101-20050512-152745-ls1f5629.cr2
#	043-101-20050512-152845_01-ls1f5630.cr2
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
#	12152745+5631-200505-043-101-pg5v~stuff.cr2
#	12152845+5632_01-200505-043-101-pg5v~stuff.cr2
#
# are converted into:
#
#	pg5v5631stuff.cr2
#	pg5v5632stuff.cr2
#
# as well.
#
sub set_destname()
{
    my $basename_noext; # pathset basename without .extension
    my $path;		# a path in the pathset
    my $pathset;	# array of parts from a single %basenoext_pathset
    my $srcbase;	# basename of the source path
    my $lc_srcbase;	# lowercase basename of the source path
    my $destbase;	# basename of the destination path
    my $timestamp;	# EXIF or filename timestamp of OK, or error msg
    my $yyyymm;		# EXIF or filename timestamp year and month
    my $ddhhmmss;	# EXIF or filename day, hour, minute, second
    my $dup;		# de-duplicate number
    my $dup_dig2;	# optional 2 digit de-duplicate number or empty string
    my $err;		# >0 ==> fatal error number, 0 ==> OK
    my $multifound;	# 0 ==> only one .ext found, 1 ==> 2+ .ext found
    my $roll_sub;	# roll sub directory
    my $srcext;		# .extension of the source path
    my $destpath;;	# full destination path
    my $highest_dup;	# highest dup timestamp / dest number, 0 ==> no dups
    my $pathset_err;	# 0 ==> pathset is OK, != 0 ==> the $err of a member
    my %path_lc_srcbase;	# key: paths value: cached lc_srcbase value
    my $forget;		# 1 ==> forget the current path

    # process all paths
    #
    $err = 0;
    $forget = 0;
    foreach $basename_noext ( sort keys %basenoext_pathset ) {

	# get the current pathset
	#
	$pathset = $basenoext_pathset{$basename_noext};
	if (! defined $pathset) {
	    warning("undef pathset in set_destname for: $basename_noext");
	    next;
	}
	if (scalar @{$pathset} <= 0) {
	    warning("empty pathset in set_destname for: $basename_noext");
	    next;
	}

	# compute the intermediate values based on the pathset timestamp
	#
	$timestamp = $pathset_timestamp{$basename_noext};
	if (! defined $timestamp) {
	    error(-60, "undef 2nd get of timestamp for $basename_noext");
	    $err = 60;	# delay exit(50);
	    last;
	}
	$yyyymm = strftime("%Y%m", gmtime($timestamp));
	$ddhhmmss = strftime("%d%H%M%S", gmtime($timestamp));
	$multifound = $need_plus{@{$pathset}[0]};
	$roll_sub = $path_roll_sub{@{$pathset}[0]};
	$roll_sub = "" if ! defined $roll_sub;
	if (! defined $yyyymm || ! defined $ddhhmmss ||
	    ! defined $multifound) {
	    error(-61, "undef of some intermediate var for @{$pathset}[0]");
	    $err = 61;	# delay exit(51);
	    last;
	}

	# look for unique filenames for all members of this pathset
	#
	$pathset_err = 0;
	for ($dup = 0; $dup < $max_dup; ++$dup) {

	    # debug
	    #
	    if ($dup > 0) {
		dbg(4, "dup $dup on base $basename_noext");
	    } else {
		dbg(4, "1st try for base $basename_noext");
	    }

	    # look for duplicates in each element of the pathset
	    #
	    # Duplicates can arise if the path in the destination exists.
	    # We first will compute the highest $dup duplication value.
	    # A highest $dup value of 0 means no duplicates were found in the
	    # pathset.
	    #
	    foreach $path ( sort @{$pathset} ) {

		# get the basename of the source path in lowercase
		#
		$srcbase = $path_basenoext{$path};
		$lc_srcbase = lc($srcbase);

		# deal with filenames in old style destination form
		#
		# If the lowercase name is already of the form:
		#
		#	043-101-20050512-152545-ls1f5629.cr2
		#	043-101-20050512-152545_01-ls1f5630.cr2
		#
		# convert it to just ls1f5629.cr2 and ls1f5630.cr2 so we can
		# reprocess the destination tree if we want to later on.
		#
		if ($lc_srcbase =~ /^\d{3}-[^-]*-\d{8}-\d{6}(_\d+)?-(.*)$/) {
		    dbg(2, "found old style filename: $lc_srcbase");
		    $lc_srcbase = $2;
		    if ($lc_srcbase =~ /-/) {
			$lc_srcbase = s/-/~/g;
			dbg(4, "conv -'s to ~'s in old srcbase");
		    }
		    dbg(2, "preconverted old style to: $lc_srcbase");

		# deal with filenames in the new style destination form
		#
		# If the lowercase name is already of the form:
		#
		#	12152545+5627-200505-043-101-pg5v.cr2
		#	12152645+5628_01-200505-043-101-pg5v.cr2
		#
		# convert it to just pg5v5627.cr2 and pg5v5628.cr2 so we can
		# reprocess the destination tree if we want later on.
		#
		} elsif ($lc_srcbase =~
			m{
			  \d{8}		# ddhhmmss
			  [-+]		# - (dash) or + (plus) separator
			  ([^-]*)	# $1: sequence number
			  (_\d{2})?	# $2: optional 2 de-duplicate digits
			  -		# - (dash) separator
			  \d{6}		# yyyymm
			  -		# - (dash) separator
			  [^-]*		# roll number
			  -		# - (dash) separator
			  [^-]*		# sub-roll number
			  -		# - (dash) separator
			  ([^.~]*)	# $3: image filename chars pre .ext
			  (~[^.]*)?	# $4: optional extra imagename chars
			  (\..*)?$	# $5: optional .extension
			 }ix) {
		    dbg(2, "found new style filename: $lc_srcbase");
		    if (defined $1) {
			dbg(6, "1: sequence number match: $1");
		    } else {
			dbg(6, "1: sequence number match is undefined");
		    }
		    if (defined $2) {
			dbg(6, "2: optional de-duplicate digits: $2");
		    } else {
			dbg(6, "2: optional de-duplicate digits is undefined");
		    }
		    if (defined $3) {
			dbg(6, "3: image filename chars pre .ext: $3");
		    } else {
			dbg(6, "3: image filename chars pre .ext is undefined");
		    }
		    if (defined $4) {
			dbg(6, "4: optional imagename chars: $4");
		    } else {
			dbg(6, "4: optional imagename chars is undefined");
		    }
		    if (defined $5) {
			dbg(6, "5: optional .extension: $5");
		    } else {
			dbg(6, "5: optional .extension is undefined");
		    }
		    $lc_srcbase = $3 . $1;
		    if (defined $4) {
			$lc_srcbase .= substr($4, 1);
		    }
		    if (defined $5) {
			$lc_srcbase .= $5;
		    }
		    if ($lc_srcbase =~ /-/) {
			$lc_srcbase = s/-/~/g;
			dbg(4, "conv -'s to ~'s in new srcbase");
		    }
		    dbg(2, "preconverted new style to: $lc_srcbase");

		# -'s (dash) become ~'s (underscore) to avoid
		# filename field confusion
		#
		} elsif ($lc_srcbase =~ /-/) {
		    dbg(4, "conv -'s to ~'s in srcbase");
		    $lc_srcbase =~ s/-/~/g;
		}
		# cache the lc_srcbase value
		$path_lc_srcbase{$path} = $lc_srcbase;

		# note the .extension, if any
		#
		if ($path =~ /\./) {
		    ($srcext = lc($path)) =~ s/^.*\././;
		} else {
		    $srcext = "";
		}

		# form the new destination filename
		#
		# An example of a new destination filename:
		#
		#	12152545+5627-200505-043-101-pg5v.cr2
		#	12152545+5627_01-200505-043-101-pg5v.cr2
		#
		if ($dup > 0) {
		    $dup_dig2 = "_" . sprintf("%02d", $dup);
		} else {
		    $dup_dig2 = "";
		}
		$destbase = $ddhhmmss;
		$destbase .= ($multifound ? "+" : "-");
		$destbase .= substr($lc_srcbase, $mv_end_chars, $mv_fwd_chars);
		$destbase .= "$dup_dig2-$yyyymm-$rollnum-";
		$destbase .= substr($roll_sub, $roll_sub_skip,
				    $roll_sub_maxlen);
		$destbase .= "-";
		$destbase .= substr($lc_srcbase, 0, $mv_end_chars);
		if (length($lc_srcbase) > $mv_fwd_chars+$mv_end_chars) {
		    $destbase .= "~";
		    $destbase .= substr($lc_srcbase,
					$mv_fwd_chars+$mv_end_chars);
		}
		$destbase .= $srcext;

		# firewall - must already have path_destdir
		#
		if (! defined $path_destdir{$path}) {
		    error(-62, "missing destdir path for: $path");
		    $err = 62;	# delay exit(52)
		    $pathset_err = $err;
		    last;
		}
		$destpath = $path_destdir{$path};

		# if -u, a collision is only if dest exists with
		# different length
		#
		if (defined $opt_u &&
		    -e $path && -e "$destpath/$destbase" &&
		    (-s $path == -s "$destpath/$destbase")) {
		    dbg(1, "ignoring already copied: $path");
		    dbg(4, "src length: " . (-s $path));
		    dbg(4, "dest length: " . (-s "$destpath/$destbase"));
		    forget_path($basename_noext);
		    $forget = 1;
		    last;
		}

		# look for a collision unless -o
		#
		if (! defined $opt_o) {
		    # -o colission processing
		    if (-e "$destpath/$destbase") {
			dbg(4, "destination exists $destpath/$destbase");
			last;
		    } elsif (defined $destpath_path{"$destpath/$destbase"}) {
			dbg(4, "planning to create $destpath/$destbase");
			last;
		    }
		}
	    }

	    # We finished processing the pathset, determine why
	    # we finished
	    #
	    # If there was a pathset_err, then we can do nothing else
	    # with this pathset.
	    #
	    if ($pathset_err != 0) {
		last;

	    # if we forgot this path, do nothing else with it
	    #
	    } elsif ($forget) {
	    	last;

	    # If there was a collision and no -o, then try for the
	    # next dup number, unless -u in which case we don't treat it
	    # as a collision - just ifnore this pathset
	    #
	    } elsif (! defined $opt_o &&
		     (-e "$destpath/$destbase" ||
		      defined $destpath_path{"$destpath/$destbase"})) {
		next;

	    # No errors AND either there was no dup or we have -o, so
	    # we can now compute filenames for this pathset
	    #
	    } else {
		$highest_dup = $dup;
		last;
	    }
	}

	# if we forgot the last path, move on to the next path
	#
	if ($forget) {
	    # stop forgetting
	    $forget = 0;
	    next;

	# If we failed to find a unique dup value for this pastset,
	# of it we failed to process all members of the pathset,
	# then do nothing more with this pathset.
	#
	} elsif ($pathset_err != 0) {
	    # The $err value has already # been set, so we just carry on
	    # with the next pathset in this case.
	    next;

	# otherwise use the highest dup level for all of the paths
	# in the pathset.  Note that a dup level of 0 means that
	# no duplicates were found.
	#
	} else {

	    # process each element of the pathset in the same way
	    #
	    foreach $path ( sort @{$pathset} ) {

		# start from the cached lc_srcbase value
		#
		$lc_srcbase = $path_lc_srcbase{$path};
		if (! defined $lc_srcbase) {
		    error(-63, "undef lc_srcbase cache value for $path");
		    $err = 63;	# delay exit(53);
		    last;
		}

		# note the .extension, if any
		#
		if ($path =~ /\./) {
		    ($srcext = lc($path)) =~ s/^.*\././;
		} else {
		    $srcext = "";
		}

		# recompute the intermediate values again
		#
		$timestamp = $pathset_timestamp{$path_basenoext{$path}};
		if (! defined $timestamp) {
		    error(-64, "undef 2nd get of timestamp for $path");
		    $err = 64;	# delay exit(54);
		    last;
		}
		$yyyymm = strftime("%Y%m", gmtime($timestamp));
		$ddhhmmss = strftime("%d%H%M%S", gmtime($timestamp));
		$multifound = $need_plus{$path};
		$roll_sub = $path_roll_sub{$path};
		$roll_sub = "" if ! defined $roll_sub;
		if (! defined $yyyymm || ! defined $ddhhmmss ||
		    ! defined $multifound) {
		    error(-65, "undef of some intermediate var for $path");
		    $err = 65;	# delay exit(55);
		    last;
		}

		# form the next filename and retry using the same
		# dup level for all members of the pathset
		#
		if ($highest_dup > 0) {
		    $dup_dig2 = "_" . sprintf("%02d", $dup);
		} else {
		    $dup_dig2 = "";
		}
		$destbase = $ddhhmmss;
		$destbase .= ($multifound ? "+" : "-");
		$destbase .= substr($lc_srcbase, $mv_end_chars, $mv_fwd_chars);
		$destbase .= "$dup_dig2-$yyyymm-$rollnum-";
		$destbase .= substr($roll_sub, $roll_sub_skip,
				    $roll_sub_maxlen);
		$destbase .= "-";
		$destbase .= substr($lc_srcbase, 0, $mv_end_chars);
		if (length($lc_srcbase) > $mv_fwd_chars+$mv_end_chars) {
		    $destbase .= "~";
		    $destbase .= substr($lc_srcbase,
					$mv_fwd_chars+$mv_end_chars);
		}
		$destbase .= $srcext;

		# note our final destination filename
		#
		$path_destfile{$path} = $destbase;
		$destpath_path{"$destpath/$destbase"} = $path;
		dbg(2, "src: $path will become: $destpath/$destbase");
	    }
	}
    }

    # process a delayed fatal error exit if needed
    #
    exit($err) if ($err > 0);
    return;
}


# get_timestamp - determine the timestamp of EXIF or file dates
#
# given:
#	\@pathset	    array of paths to to check
#	$basename_noext	    pathset name
#
# returns:
#	timestamp or
#	undef ==> no valid EXIF timestamp and file timestamp(s) too old
#
sub get_timestamp($$)
{
    my ($pathset, $basename_noext) = @_;		# get args
    my $path;		# a path in the pathset
    my $path_ext;	# .extension of a path in the pathset
    my $exitcode;	# 0 ==> OK, else ==> could not get an EXIF timestamp
    my $message;	# $exitcode==0 ==> timestamp, else error message
    my $oldest;		# oldest timestamp found
    my $oldest_exif;	# path of oldest EXIF timestamp
    my %has_exif_ext;	# $has_exif_ext{$path} == 1 ==> $path's as EXIF .ext
    my $i;

    # see which paths in pathset have .extensions that might have EXIF data
    #
    dbg(5, "getting timestamp for pathset: $basename_noext");
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
		dbg(6, "found EXIF type extension: $path");
		last;
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
	    if ($exitcode == 0) {
	        if ($oldest == 0 || $message < $oldest) {
		    dbg(4, "get_timestamp EXIF type: $path" .
			    " EXIF time: $message");
		    $oldest = $message;
		    $oldest_exif = $path;
		} elsif ($oldest > 0 || $message < $oldest) {
		    dbg(4, "get_timestamp EXIF type: $path " .
			   "older EXIF time: $message");
		}
	    } else  {
		dbg(6, "non-fatal/non-warn exif_date error " .
		       "code $exitcode: $message");
	    }
	}
    }

    # If we found EXIF timestamps, return the oldest timestamp
    #
    if ($oldest > 0) {
	dbg(3, "EXIF .extension EXIF timestamp: $oldest for $oldest_exif");
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
	    if ($exitcode == 0) {
	        if ($oldest == 0 || $message < $oldest) {
		    dbg(4, "get_timestamp non-EXIF type: $path " .
			   "EXIF time: $message");
		    $oldest = $message;
		    $oldest_exif = $path;
		} elsif ($oldest > 0 || $message < $oldest) {
		    dbg(4, "get_timestamp non-EXIF type: $path " .
			   "older EXIF time: $message");
		}
	    } else {
		dbg(6, "non-fatal/non-warn exif_date error " .
		       "code $exitcode: $message");
	    }
	}
    }

    # If we found EXIF timestamps, return the oldest timestamp
    #
    if ($oldest > 0) {
	dbg(3, "non-EXIF .extension EXIF timestamp: $oldest for $oldest_exif");
	return $oldest;
    }
    dbg(5, "found no valid EXIF timestamp for pathset: $basename_noext");

    # no EXIF timestamps in set, look for the oldest file timestamp that
    # is not too old
    #
    foreach $path ( @{$pathset} ) {

	# if the file timestamp is not too old
	#
	if ($path_filetime{$path} >= $mintime &&
	    ($oldest == 0 || $path_filetime{$path} < $oldest)) {
	    $oldest = $path_filetime{$path};
	    $oldest_exif = $path;
	}
    }

    # If we found a file timestamp that is not too old, use the oldest
    #
    if ($oldest > 0) {
	dbg(3, "file timestamp: $oldest for $oldest_exif");
	return $oldest;
    }

    # We have no EXIF timestamp and no file timestamp we can use
    #
    dbg(4, "found no valid timestamp for pathset: $basename_noext");
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
	return (60, "cannot open");	# exit(70)
    }
    if (! -r $filename) {
	return (61, "cannot read");	# exit(71)
    }

    # extract meta information from an image
    #
    $info = $exiftool->ImageInfo($filename, @tag_list);
    if (! defined $info || defined $$info{Error}) {
	# failure to get a EXIF data
	if (defined $$info{Error}) {
	    return (62, "EXIF data error: $$info{Error}");	# exit(72)
	} else {
	    return (63, "no EXIF data");	# exit(73)
	}
    }

    # look at each EXIF tag value we found
    #
    # We are looking for the earliest timestamp that is not before
    # $mintime.	 A < 0 timestamp means nothing found so far.
    #
    $timestamp = -1;	# no timestamp yet
    foreach $tag (@tag_list) {

	# ignore if no EXIF value or non-numeric
	#
	if (! defined $$info{$tag}) {
	    dbg(5, "ignoring undef EXIF tag value: $tag");
	} elsif ($$info{$tag} !~ /^\d+$/) {
	    dbg(5, "ignoring non-numeric tag: $tag: $$info{$tag}");
	} elsif ($$info{$tag} <= $mintime) {
	    dbg(5, "ignoring pre-mintime: $tag: $$info{$tag} <= $mintime");
	} elsif ($timestamp > 0 && $$info{$tag} == $timestamp) {
	    dbg(5, "ignoring timestamp tag: $tag: $$info{$tag} same value");
	} elsif ($timestamp > 0 && $$info{$tag} > $timestamp) {
	    dbg(5, "ignoring timestamp tag: $tag: " .
		   "$$info{$tag} that is not earliest > $timestamp");
	} else {
	    dbg(5, "found useful numeric timestamp tag: $tag $$info{$tag}");
	    $timestamp = $$info{$tag};
	}
    }
    if ($timestamp < 0) {
	return (64, "no timestamp in EXIF data");	# exit(74)
    }

    # Avoid very old EXIF timestamps
    #
    if ($timestamp < $mintime) {
	return (65, "timestamp: $timestamp < min: $mintime");	# exit(75)
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
#	xx    xxxxx		xxxxxxxx    xxx... <== x's mark optional fields
#
# NOTE: SS (seconds of minute) default to 0 if it is not given.
#
# or of these forms:
#
#	# date: YYYY/MM/dd hh:mm:ss
#	xx    x		  xxxxxxxxx	       <== x's mark optional fields
#	# date: YYYY-MM-dd hh:mm:ss
#	xx    x		   xxxxxxxx	       <== x's mark optional fields
#	# date: YYYY.MM.dd hh:mm:ss
#	xx    x		  xxxxxxxxx	       <== x's mark optional fields
#
# NOTE: hh:mm:ss default to 00:00:00 if it is not given
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
	return (70, "cannot open");	# exit(80)
    }
    if (! -r $filename) {
	return (71, "cannot read");	# exit(81)
    }

    # open the text file
    #
    dbg(4, "looking for date in text file: $filename");
    if (! open TEXT, '<', $filename) {
	return (72, "cannot open: $!"); # exit(82)
    }

    # read the 1st $datelines of a file looking for a timestamp
    #
    for ($i=0; $i < $datelines; ++$i) {

	# read a line
	#
	if (! defined($line = <TEXT>)) {
	    return (73, "EOF or text read error");	# exit(83)
	}
	chomp $line;
	dbg(6, "read text line $i in $filename: $line");

	# look for a date string of the form:
	#
	#	# date: Xyz Oct dd HH:MM:SS ABC YYYY
	#	xx    xxxxx		xxxxxxxx    xxx... <== optional fields
	#
	# NOTE: SS (seconds of minute) default to 0 if it is not given.
	#
	if ($line =~  m{
		      ^
		      (\#\s*)?	# 1: optional # space (ignored)
		      date(:)?	# 2: date with optional : (ignored)
		      (\s*\S+)? # 3: day of week (ignored)
		      \s+
		      (\S+)	# 4: short name of month
		      \s+
		      (\d+)	# 5: day of month
		      \s+
		      (\d+)	# 6: hour of day
		      :
		      (\d+)	# 7: minute of hour
		      (:\d+)?	# 8: optional :seconds (defaults to "00")
		      (\s+\S+)? # 9: optional timezone (ignored)
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
	    dbg(6, "#1 parsed $year-$monname-$mday $hour:$min" .
		   (defined $sec ? ":$sec" : ""));

	    # convert short name of month to month number [0..11]
	    #
	    dbg(5, "line $i, found possible date string in $filename: $line");
	    foreach ( keys %mname ) {
		$mon = $mname{$_} if $monname =~ /^$_$/i;
	    }
	    if ($mon < 0) {
		dbg(4, "ignoring bad month name $monname on line $i " .
		       "in $filename");
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
	    dbg(6, "#1 will parse date: " .
		   sprintf("%04d-%02d-%02d %02d:%02d:%02d\n",
			   $year, $mon, $mday, $hour, $min, $sec));
	    $timestamp = timegm_nocheck($sec, $min, $hour, $mday, $mon, $year);
	    if (! defined $timestamp) {
		dbg(4, "#1 ignoring malformed date on line $i " .
		       "in $filename");
		next;	# bad month name
	    }
	    if ($timestamp < $mintime) {
		dbg(4, "#1 ignoring very early date on line $i in $filename");
		next;	# bad month name
	    }
	    dbg(2, "#1 $filename timestamp: $timestamp");

	    # return the timestamp according to this date line we read
	    #
	    return (0, $timestamp);

	# look for a date string of the form:
	#
	#	# date: YYYY/MM/dd hh:mm:ss
	#	xx    x		  xxxxxxxxxxxx	   <== x's mark optional fields
	#
	#	# date: YYYY-MM-dd hh:mm:ss
	#	xx    x		  xxxxxxxxxxxx	   <== x's mark optional fields
	#
	#	# date: YYYY.MM.dd hh:mm:ss
	#	xx    x		  xxxxxxxxxxxx	   <== x's mark optional fields
	#
	# NOTE: hh:mm:ss default to 00:00:00 if it is not given
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
		      (\d{2})	# 5: 2	2 digit day of month [01-31]
		      (\s+\d{2}:\d{2}:\d{2})?  # 6: optional hh:mm:ss timestamp
		      }ix) {

	    my $sec;		# seconds of minute
	    my $min;		# minute of hour
	    my $hour;		# hour of day
	    my $timeofday = $6; # optional hh:mm:ss timestamp
	    my $mday = $5;	# day of month
	    my $mon = $4;	# month of year [01-12]
	    my $year = $3;	# year
	    my $timestamp;	# date string converted into a timestamp
	    dbg(6, "#2 parsed $year-$mon-$mday" .
		   (defined $timeofday ? " $timeofday" : ""));

	    # parse timeofday, if given
	    #
	    if (defined $timeofday &&
		$timeofday =~ m{\s+(\d{2}):(\d{2}):(\d{2})$}) {
		$hour = $1;
		$min = $2;
		$sec = $3;
	    } else {
		# no time of day, use noon
		$hour = 0;
		$min = 0;
		$sec = 0;
	    }

	    # convert fields to a timestamp
	    #
	    dbg(6, "#2 will parse date: " .
		   sprintf("%04d-%02d-%02d %02d:%02d:%02d",
			   $year, $mon, $mday, $hour, $min, $sec));
	    $timestamp = timegm_nocheck($sec, $min, $hour,
					$mday, $mon-1, $year);
	    if (! defined $timestamp) {
		dbg(4, "#2 ignoring malformed date on line $i in $filename");
		next;	# bad month name
	    }
	    if ($timestamp < $mintime) {
		dbg(4, "#2 ignoring very early date on line $i in $filename");
		next;	# bad month name
	    }
	    dbg(2, "#2 $filename timestamp: $timestamp");

	    # return the timestamp according to this date line we read
	    #
	    return (0, $timestamp);
	}
    }

    # no date stamp found
    #
    return (74, "no date stamp found in initial lines");	# exit(84)
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

    # firewall - fast exit if we already created or found this dir
    #
    if (defined $have_mkdir{$dir_name}) {
	return (0, undef);
    }

    # setup the destination directory if needed
    #
    if (-e $dir_name && ! -d $dir_name) {
	return (80, "is a non-directory: $dir_name");	# exit(90)
    }
    if (! -d $dir_name) {
	if ($opt_d || mkdir($dir_name, 0775)) {
	    dbg(1, "mkdir $dir_name");
	    $have_mkdir{$dir_name} = 1;
	} else {
	    return (81, "cannot mkdir: $dir_name: $!"); # exit(91)
	}
    } else {
	$have_mkdir{$dir_name} = 0;
    }
    if (! $opt_d && ! -w $dir_name) {
	return (82, "directory is not writable: $dir_name");	# exit(92)
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
	    error(90, "roll number must be 3 digits");
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
	    error(91, "cannot read exifroll file: $rollfile");
	} elsif (! -w $rollfile) {
	    error(92, "cannot write exifroll file: $rollfile");
	}

	# open ~/.exifroll file
	#
	if (! open EXIFROLL, '<', $rollfile) {
	    error(93, "cannot open for reading exifroll: $rollfile: $!");
	}

	# read only the first line
	#
	$rollnum = <EXIFROLL>;
	chomp $rollnum;
	close EXIFROLL;

	# assume roll number of 000 if bad line or no line
	#
	if ($rollnum !~ /^\d{3}$/) {
	    warning("invalid roll number in $rollfile");
	    warning("will use roll number 000 instead");
	    $rollnum = "000";
	}
    }

    # write the next roll number into ~/.exifroll
    #
    dbg(0, "will use roll number: $rollnum");
    if (! $opt_d && ! open EXIFROLL, '>', $rollfile) {
	error(94, "cannot open for writing exifroll: $rollfile: $!");
    }
    if ($rollnum > 999) {
	if ($opt_d || ! print EXIFROLL "000\n") {
	    dbg(1, "next roll number will be 000");
	} else {
	    error(95, "cannot write 000 rollnum to exifroll: $rollfile: $!");
	}
    } else {
	if ($opt_d || printf EXIFROLL "%03d\n", $rollnum+1) {
	    dbg(1, sprintf("next roll number will be %03d", $rollnum+1));
	} else {
	    error(96, "cannot write next rollnum to exifroll: $rollfile: $!");
	}
    }
    close EXIFROLL unless $opt_d;
    return;
}


# create_destination - copy or move src files to their destinations
#
sub create_destination()
{
    my $err;		# >0 ==> fatal error number, 0 ==> OK
    my $destpath;	# full path to
    my $path;		# source path
    my $timestamp;	# EXIF or filename timestamp of OK, or error msg

    # process all source paths
    #
    $err = 0;
    foreach $path ( sort keys %path_basenoext ) {

	# get the timestamp for this path
	#
	$timestamp = $pathset_timestamp{$path_basenoext{$path}};
	if (! defined $timestamp) {
	    error(-100, "timestamp not found for: $path");
	    $err = 100; # delay exit(80)
	    next;
	}

	# determine destination path
	#
	if (! defined $path_destdir{$path}) {
	    error(-101, "no destination directory info for: $path");
	    $err = 101; # delayed exit(101)
	    next;
	}
	if (! defined $path_destfile{$path}) {
	    error(-102, "no destination filename info for: $path");
	    $err = 102; # delayed exit(102)
	    next;
	}
	$destpath = "$path_destdir{$path}/$path_destfile{$path}";

	# untaint source filename
	#
	if ($path =~ /$untaint/o) {
	    $path = $1;
	} else {
	    error(-103, "bogus chars in source path");
	    $err = 103; # delayed exit(103)
	    next;
	}

	# untaint destination filename
	#
	if ($destpath =~ /$untaint/o) {
	    $destpath = $1;
	} else {
	    error(-104, "bogus chars in destination path");
	    $err = 104; # delayed exit(104)
	    next;
	}

	# untaint timestamp
	#
	if ($timestamp =~ /^(\d+)$/) {
	    $timestamp = $1;
	} else {
	    error(-105, "bogus chars in timestamp");
	    $err = 105; # delayed exit(105)
	    next;
	}

	# copy (or move of -m) the image file
	#
	if (defined $opt_m) {
	    if (! $opt_d && move($path, $destpath) == 0) {
		error(-106, "mv $path $destpath failed: $!");
		$err = 106;	# delayed exit(106)
		next;
	    }
	    dbg(2, "mv $path $destpath");
	} else {
	    if (! $opt_d && copy($path, $destpath) == 0) {
		error(-107, "cp $path $destpath failed: $!");
		$err = 107;	# delayed exit(107)
		next;
	    }
	    dbg(2, "cp $path $destpath");
	}

	# compare unless -m
	#
	if (! $opt_d && ! defined $opt_m && compare($path, $destpath) != 0) {
	    error(-108, "compare of $path and $destpath failed");
	    $err = 108; # delayed exit(108)
	    next;
	}
	if (! defined $opt_m) {
	    dbg(3, "cmp $path $destpath");
	}

	# set the access and modification time unless -t
	#
	if (! defined $opt_t) {
	    if (! $opt_d && utime($timestamp, $timestamp, $destpath) < 1) {
		error(-109, "compare of $path and $destpath failed");
		$err = 109;	# delayed exit(109)
		next;
	    }
	    dbg(3, "utime($timestamp, $timestamp, $destpath)");
	}
	dbg(1, "created: $destpath");
    }
    exit($err) if ($err != 0);
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
	error(120, "-r $readme does not exist");
    }
    if (! -f $readme) {
	error(121, "-r $readme is not a file");
    }
    if (! -r $readme) {
	error(122, "-r $readme is not readable");
    }

    # must have a text date
    #
    ($exitcode, $message) = text_date($readme);
    if ($exitcode != 0) {
	error(-123, "-r $readme does not have a date timestamp line");
	error(123,  "try adding '# date: yyyy-mm-dd' line to $readme");
    }

    # same the timestamp for later
    #
    $readme_timestamp = $message;

    # return the absolute path of readme
    #
    $ret = abs_path($readme);
    if (! defined $ret) {
	error(124, "cannot determine absolute path of $readme");
    }
    return $ret;
}


# create_readme_link - setup the readme.txt link
#
sub create_readme_link()
{
    my $readme_txt;	# path to the readme.txt file
    my $inforeadme;	# existing readinfome file to be linked to readme.txt

    # determine readme.txt file we will link to
    #
    $readme_txt = "$path_destdir{$readme_path}/readme.txt";
    if ($readme_txt =~ /$untaint/o) {
	$readme_txt = $1;
    } else {
	error(130 * ($opt_a?-1:1), "bogus chars in readme.txt path");
    	return;
    }

    # see if we must pre-remove the readme file
    #
    if (-e $readme_txt) {
	dbg(2, "rm -f $readme_txt");
	if (! $opt_d) {
	    unlink($readme_txt);
	    if (-e $readme_txt) {
		error(131 * ($opt_a?-1:1), "cannot remove: $readme_txt: $!");
		return;
	    }
	}
    }

    # create the link
    #
    $inforeadme = "$path_destdir{$readme_path}/$path_destfile{$readme_path}";
    if ($inforeadme =~ /$untaint/o) {
	$inforeadme = $1;
    } else {
	error(132 * ($opt_a?-1:1), "bogus chars in inforeadme path");
    	return;
    }
    dbg(1, "ln $inforeadme $readme_txt");
    if (! $opt_d) {
	if (! link($inforeadme , $readme_txt)) {
	    error(133 * ($opt_a?-1:1), "link failed: $!");
	}
    }
    return;
}


# set_timestamp - set the timestamps for all path sets
#
sub set_timestamps()
{
    my $err;		# >0 ==> fatal error number, 0 ==> OK
    my $basename_noext; # pathset basename without .extension

    # process each pathset and determine timestamps for each set
    #
    $err = 0;
    foreach $basename_noext ( sort keys %basenoext_pathset ) {

	# set the timestamp for this pathset
	#
	$pathset_timestamp{$basename_noext} =
	  get_timestamp($basenoext_pathset{$basename_noext}, $basename_noext);

	# firewall
	#
	if (defined $pathset_timestamp{$basename_noext}) {
	    dbg(1, "pathset $basename_noext timestamp: " .
		   gmtime($pathset_timestamp{$basename_noext}) . " UTC");
	} else {
	    error(-140, "no valid EXIF timestamp and file " .
		       "timestamp(s) too old for pathset: $basename_noext");
	    $err = 140;	# delayed exit(140);
	    next;

	}
    }
    exit($err) if ($err > 0);
    return;
}


# forget_path - forget that we saw a path, remove it from all hashs
#
# given:
#	$basename_noext		# basename without .extension to ignore
#
sub forget_path($)
{
    my ($basename_noext) = @_;    # get args
    my $pathset;	# array of parts from a single %basenoext_pathset
    my $path;		# a path in the pathset

    # get the pathset to delete
    #
    $pathset = $basenoext_pathset{$basename_noext};
    if (! defined $pathset) {
	warning("undef pathset when ignoring: $basename_noext");
	return;
    }

    # ignore each element of the pathset
    #
    foreach $path ( sort @{$pathset} ) {
	if (defined $path_destdir{$path} && defined $path_destfile{$path}) {
	    delete $destpath_path{"$path_destdir{$path}/$path_destfile{$path}"};
	}
	delete $path_destdir{$path};
	delete $path_destfile{$path};
	delete $path_basenoext{$path};
	delete $path_roll_sub{$path};
	delete $path_filetime{$path};
	delete $need_plus{$path};
    }
    delete $basenoext_pathset{$basename_noext};
    delete $pathset_timestamp{$basename_noext};
    return;
}


# warning - report an warning
#
# given:
#	$msg		the message to print
#
sub warning($)
{
    my ($msg) = @_;    # get args

    # parse args
    #
    if (!defined $msg) {
	$msg = "<<< no message supplied >>>";
    }

    # issue the error message
    #
    print STDERR "$0: Warning: $msg\n";
    return;
}


# error - report an error and exit
#
# given:
#	$exitval	exit code value, <= 0 ==> do not exit
#	$msg		the message to print
#
sub error($$)
{
    my ($exitval, $msg) = @_;	 # get args

    # parse args
    #
    if (!defined $exitval) {
	$exitval = 254;
    }
    if (!defined $msg) {
	$msg = "<<< no message supplied >>>";
    }
    if ($exitval !~ /^-?\d+$/) {
	$msg .= "<<< non-numeric exit code: $exitval >>>";
	$exitval = 253;
    }

    # issue the error message
    #
    if ($exitval == 0) {
	print STDERR "$0: FATAL: $msg\n";
    } elsif ($exitval < 0) {
	print STDERR "$0: FATAL[delayed ", -$exitval,"]: $msg\n";
    } else {
	print STDERR "$0: FATAL[$exitval]: $msg\n";
    }

    # issue an error message
    #
    if ($exitval > 0) {
	exit($exitval);
    }
    return;
}


# dbg - print a debug message is debug level is high enough
#
# given:
#	$min_lvl	minimum debug level required to print
#	$msg		message to print
#
sub dbg($$)
{
    my ($min_lvl, $msg) = @_;	 # get args

    # firewall
    #
    if (!defined $min_lvl) {
	error(140, "debug called without a minimum debug level");
    }
    if ($min_lvl =~ /\D/) {
	error(141, "debug called with non-numeric debug level: $min_lvl");
    }
    if ($opt_v < $min_lvl) {
	return;
    }
    if (!defined $msg) {
	error(142, "debug called without a message");
    }
    chomp $msg;

    # issue the debug message
    #
    print STDERR "dbg[$min_lvl]: $msg\n";
}
