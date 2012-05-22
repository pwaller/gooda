#/bin/sh
ulimit -n 32768
SCRIPT=`readlink -f $0`
SCRIPTPATH=`dirname $SCRIPT`
perf stat  $(grep -v '^$' ${SCRIPTPATH}/wsm-event1.txt | grep -v ^# | sed -e 's/^/-e /') -a -x @ -- $1 $2 $3 $4
perf stat  $(grep -v '^$' ${SCRIPTPATH}/wsm-event2.txt | grep -v ^# | sed -e 's/^/-e /') -a -x @ -- $1 $2 $3 $4
perf stat  $(grep -v '^$' ${SCRIPTPATH}/wsm-event3.txt | grep -v ^# | sed -e 's/^/-e /') -a -x @ -- $1 $2 $3 $4

