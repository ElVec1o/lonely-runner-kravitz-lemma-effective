#!/bin/bash
# sequential driver: one job at a time, each through launch_lite.sh (ceiling 400 MB,
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
run(){ n=$1; shift; bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 400 $D/logs $n $D/bin/ins "$@"; }
run rnd1 rnd 20261125 500 40 2 7 25
run rnd2 rnd 77 250 24 5 8 25
run d3 d3
run d1 d1 5 250
run d5_20 d5 20 100
run d5_30 d5 30 120
echo ALLDONE > $D/logs/ALLDONE
