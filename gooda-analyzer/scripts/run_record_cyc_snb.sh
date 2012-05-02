#/bin/sh
ulimit -n 32768
perf record  $(grep -v '^$' snb_cyc_account.txt | grep -v ^# | sed -e 's/^/--pfm-events /') -a -R  -- $1 $2 $3 $4

