#!/bin/bash
# usage: run23.sh NAME CEIL_MB args...  -> launch_lite.sh (small single-thread Rust job
NAME=p23_$1; CEIL=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/bq23 "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; cut -c1-${COLS:-400} $D/logs/$NAME.out | head -${LINES_OUT:-40}
