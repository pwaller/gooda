#/bin/sh
ulimit -n 32768
perf record  -e cycles:period=2000000,instructions:period=2000000 -a -R  -- $1 $2 $3 $4
