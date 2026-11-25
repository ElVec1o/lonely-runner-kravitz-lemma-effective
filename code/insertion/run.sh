#!/bin/bash
# usage: run.sh NAME CEIL_MB args...  (small single-thread Rust job
NAME=$1; CEIL=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/bq "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"
