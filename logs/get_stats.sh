#!/bin/bash
echo "Commit hash: $1"
FILES=$(find "$1" -name "*.log" | sort)

# Normalize: remove [cached] and collapse multiple spaces
ALL_CHECKED=$(echo "$FILES" | xargs cat | sed 's/\[cached\] *//g' | tr -s ' ')

# Count unique declarations by status (same declaration in multiple files counts once)
TOTAL=$(echo "$ALL_CHECKED" | grep 'Checking:' | sort -u | wc -l)
FAIL=$(echo "$ALL_CHECKED" | grep 'Checking:' | grep 'FAIL$' | sort -u | wc -l)
OK=$(echo "$ALL_CHECKED" | grep 'Checking:' | grep 'ok$' | sort -u | wc -l)
TIMEOUT=$(echo "$ALL_CHECKED" | grep 'Checking:' | grep 'TIMEOUT$' | sort -u | wc -l)
HANG=$(echo "$ALL_CHECKED" | grep 'Checking:' | grep -v -e 'ok$' -e 'FAIL$' -e 'TIMEOUT$' | sed 's/\.\.\..*/.../' | sort -u | sed 's/Checking: //')

echo "------------------------------------------------------------"
echo "Total: $TOTAL"
echo "OK: $OK"
echo "Fail: $FAIL"
echo "TIMEOUT: $TIMEOUT"
echo "OK%: $(echo "scale=2; 100 * ($TOTAL - $FAIL - $TIMEOUT) / $TOTAL" | bc)%"
echo "------------------------------------------------------------"
echo "Hang:"
echo "$HANG"
echo "------------------------------------------------------------"
for f in $FILES; do
  echo $f
  cat $f | grep TOTAL || echo "Hanged on $(tail -1 $f)"
done
