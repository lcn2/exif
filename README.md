# exif

* exif - print EXIF information that may be in a file

* exifforceorder - force DateTimeOriginal order in a directory for iPad

* exifrename - copy files based on EXIF or file time data


# To install

```sh
sudo make install
```


# To use

## exif

```
/usr/local/bin/exif [-h][-v lvl][-V] [-n][-m][-g][-i] [-u][-b][-p] [-d][-e] [-t tag] ...
		[-f fmt] imgfile ...

    -h      print this help message
    -v      verbose / debug level
    -V      print version and exit

    -n      output EXIF tag name before value (default: don't)
    -m      output EXIF tag name instead of value (default: don't)
    -g      output EXIF tag group before EXIF tag value (default: don't)
    -i      output imgfile filename at start of line (default: don't)

    -u      output unknown EXIF tags (default: don't)
    -b      output binary values (implies -p) (default: print binary len)
    -p      disable conversion (default: printable data, shorter lists)

    -d      output duplicate EXIF tag names (default: don't)
    -e      output ExitTool tag names (defailt: output canonical names)

    -t tag  only just EXIF tag (default: output any tag (see also -u))
		(NOTE: multiple -t tags are allowed)

    -f fmt  format for date related strings (default: %F %T)

	%a short weekday name  %A full weekday name
	%b short month name    %B full month name
	%c default format      %C 2 digit century
	%d day [01-31]         %D %m/%d/%y
	%e dat [ 1-31]         %E locale modifier for cCxXyY
				%F %Y-%m-%d (ISO 8601)
	%g 2 digit year of %V	%G 4 digit year of %V
	%h == %b              %H hour [00-23]
				%I hour [01-12]
	%j day of year [001-366]
	%k hour [0-23]
	%l hour [ 1-12]
	%m month [01-12]       %M minute [00-59]
	%n \n
				%O modifier for deHImMSuUVwWy
	%p AM or PM            %P am or pm
	%r %I:%M:%S %p	   %R %H:%M
	%s seconds since Epoch %S seconds [00-61]
	%t \t                 %T %H:%M:%S
	%u day of week [1-7]   %U week num [00-53] 1st Sun week 01
				%V week num [01-53] ISO 8601:1988
	%w day of week [0-6]   %W week num [00-53] 1st Mon week 01
	%x locate date         %X locate time
	%y year [00-99]        %Y 4 digit year
	%z UTC timezone offset %Z time zone or name or abbreviation
	%+ date(1) format      %% %

    imgfile ...     files to look for EXIF data

Exit codes:
     0         all OK
     1      `  problems were encountered while extracting EXIF info
     2         cannot open or read filename
     3         fatal error during EXIF processing
 >= 10         internal error

exif version: 4.12.1 2025-04-03
```


## exifforceorder

```
/usr/local/bin/exifforceorder [-h] [-v level] [-V] [-n] [-N] [-o arg] [-d] [-f] dir

    -h          print help message and exit
    -v level    set verbosity level (def level: )
    -V          print version string and exit

    -n          go thru the actions, but do not update any files (def: do the action)
    -N          do not process anything, just parse arguments (def: process something)

    -o arg      obsolete - ignored
    -d          obsolete - ignored
    -f          obsolete - ignored

    dir         directory containing images

Exit codes:
     0         all OK
     1         some internal tool exited non-zero
     2         -h and help string printed or -V and version string printed
     3         command line error
     4	       dir is not a direcotry
 >= 10         internal error

exifforceorder version: 4.12.1 2025-04-03
```


## exifrename

```
/usr/local/bin//exifrename [-h][-v lvl][-V] [-a] [-c] [-e exifroll] [-k roll_subskip] [-m] [-n rollnum]
  [-o] [-r readme] [-s roll_sublen] [-t] [-u] [-y seqlen] [-z skchars]
  [-d] srcdir destdir
    -h		 print this help message
    -v lvl	 set verbose / debug level to lvl (def: 0)
    -V		 print version and exit

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

    -d		 do nothing / "dry run", do not create/alter any file (def: do)

    srcdir	 source directory (must exist)
    destdir	 destination directory (must exist)

    NOTE: exit 0 means all is OK, exit !=0 means some fatal error

    Version: 4.12.1 2025-04-03
```


# Reporting Security Issues

To report a security issue, please visit "[Reporting Security Issues](https://github.com/lcn2/exif/security/policy)".
