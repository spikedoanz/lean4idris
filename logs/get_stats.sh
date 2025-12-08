#!/bin/bash
echo "Commit hash: $1"
FILES=$(find "$1" | grep "log")
ALL_CHECKED=$(echo "$FILES" | xargs cat | sed 's/\[cached\]//g')
TOTAL=$(echo "$ALL_CHECKED" | grep Checking             | sort | uniq | wc -l)
FAIL=$(echo "$ALL_CHECKED"  | grep Checking | grep FAIL | sort | uniq | wc -l)
OK=$(echo "$ALL_CHECKED"  | grep Checking | grep ok | sort | uniq | wc -l)
HANG=$(echo "$ALL_CHECKED"  | grep Checking | grep -v -e ok -e FAIL | sed 's/\.\.\..*/.../' | sort | uniq | sed 's/Checking: //')
echo "------------------------------------------------------------"
echo "Total: $TOTAL"
echo "OK: $OK"
echo "Fail: $FAIL"
echo "OK%: $(echo "scale=2; 100 * ($TOTAL - $FAIL) / $TOTAL" | bc)%"
echo "------------------------------------------------------------"
echo "Hang:"
echo "$HANG"
echo "------------------------------------------------------------"
for f in $FILES; do
  echo $f
  cat $f | grep TOTAL || echo "Hanged on $(tail -1 $f)"
done
