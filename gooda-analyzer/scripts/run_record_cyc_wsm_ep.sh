#/bin/sh
ulimit -n 32768
SCRIPT=`readlink -f $0`
SCRIPTPATH=`dirname $SCRIPT`
perf record  $(grep -v '^$' ${SCRIPTPATH}/wsm_ep_cyc_account_only.txt | grep -v ^# | sed -e 's/^/--prf-events /') -a -R  -- $1 $2 $3 $4

