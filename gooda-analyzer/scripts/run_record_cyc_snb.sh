#/bin/sh
ulimit -n 32768
SCRIPT=`readlink -f $0`
SCRIPTPATH=`dirname $SCRIPT`
perf record  $(grep -v '^$' ${SCRIPTPATH}/snb_cyc_account.txt | grep -v ^# | sed -e 's/^/--pfm-events /') -a -R  -- $1 $2 $3 $4

