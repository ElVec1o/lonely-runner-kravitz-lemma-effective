#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
run(){ n=$1; b=$2; shift 2; bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 400 $D/logs $n $D/bin/$b "$@"; }
run d2 ins2 d2 24
run pp ins2 pp 14 150
run d5b_20 ins2 d5 20 400
run d5b_30 ins2 d5 30 700
echo ALLDONE > $D/logs/ALLDONE
