#/bin/sh
ulimit -n 32768
perf record  $(grep -v '^$' wsm_ep_cyc_account_only.txt | grep -v ^# | sed -e 's/^/--prf-events /') -a -R  -- $1 $2 $3 $4

