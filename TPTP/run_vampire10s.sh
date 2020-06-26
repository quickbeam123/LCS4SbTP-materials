#!/bin/bash
# run as in: ./run_vampire_generic.sh exectuable(starting ./) problem "extra options" folder
# the folder must exists
timelimit -t 11 -T 1 $1 -m 90000 -p off -tstat on -stat full -t 10 "$2" $3 > "$4"/`(./filenamify_path.sh "$2")`.log 2>&1
