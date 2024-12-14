#!/bin/sh
set -e
if [ $# -ne 1 ]; then
  echo "Usage: $0 day_name" >&2
  exit 1
fi
DAY_NAME="$1"
DAY="$(echo "$DAY_NAME" | sed 's/day\([0-9]\+\).*/\1/')"
TPL_DIR='day00_template'
TPL_DAY='Day00.scala'
TPL_TEST='Day00Test.scala'

conv_fname() {
    echo "$1" | sed "s/00/$DAY/g"
}
DST_DAY="$(conv_fname "$TPL_DAY")"
DST_TEST="$(conv_fname "$TPL_TEST")"

mkdir -p "$DAY_NAME"

conv_tpl() {
   sed "s/00/$DAY/g"
}
<"$TPL_DIR/$TPL_DAY" conv_tpl >"$DAY_NAME/$DST_DAY"
<"$TPL_DIR/$TPL_TEST" conv_tpl >"$DAY_NAME/$DST_TEST"
