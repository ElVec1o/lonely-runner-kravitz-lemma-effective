#!/bin/bash
# usage: run.sh NAME CEIL_MB args...  (small single-thread Rust job
NAME=pf_$1; CEIL=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/pf "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; cut -c1-${COLS:-300} $D/logs/$NAME.out | head -${LINES_OUT:-40}
