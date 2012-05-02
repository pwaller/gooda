#/bin/sh
ulimit -n 32768
perf stat  $(grep -v '^$' wsm-event1.txt | grep -v ^# | sed -e 's/^/-e /') -a -x @ -- $1 $2 $3 $4
perf stat  $(grep -v '^$' wsm-event2.txt | grep -v ^# | sed -e 's/^/-e /') -a -x @ -- $1 $2 $3 $4
perf stat  $(grep -v '^$' wsm-event3.txt | grep -v ^# | sed -e 's/^/-e /') -a -x @ -- $1 $2 $3 $4

