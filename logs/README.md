```
find . -maxdepth 1 -mindepth 1 -type d | xargs -I {} ./get_stats.sh {}
```
