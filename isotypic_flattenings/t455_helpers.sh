# t455_helpers.sh: job/worker naming shared by t455_runner.sh and t455_checkin.sh (sourced; needs NW and MAIN).
# Job lines of t455_jobs.txt: "<d> <MAXDIM> [<name>]".  name = V: V-stack pass (sweep_fast WITHOUT noV: gN, HN and VN),
# logs hwv455V_d<d>[_max<M>]_w<id>.log, claims claims455V_d<d>[_max<M>], worker ids 1..NW of NW+1; id 0 is the spare-core
# runner t455V_runner.sh (log hwv455V_d<d>.log), which shares the claim directory, so all four cores split the degree.
# Any other name: only the components listed in only455_<name>.txt (noV).  No name: all components (noV).
tag() { local t; if [ "$2" = inf ]; then t=d$1; else t=d$1_max$2; fi; [ -n "$3" ] && t=${t}_$3; echo $t; }
vtag() { if [ "$2" = inf ]; then echo d$1; else echo d$1_max$2; fi; }
wid() { if [ "$3" = V ]; then echo $(($4 + 1)); else echo $4; fi; }                     # d M O k -> worker id
logf() { if [ "$3" = V ]; then echo hwv455V_$(vtag $1 $2)_w$(wid "$@").log; else echo hwv455_$(tag $1 $2 $3)_w$4.log; fi; }
cmdpat() { if [ "$3" = V ]; then echo "sweep_fast.py 4,5,5 $1 8,9 5 $(wid "$@") $((NW+1))\$"; else echo "sweep_fast.py 4,5,5 $1 8,9 5 $4 $NW noV"; fi; }
alive() { ps -eo args | grep -v grep | grep -q "$(cmdpat "$@")"; }                         # d M O k
finished() { local L; L=$(logf "$@"); [ -f "$L" ] && tail -1 "$L" | grep -q "^n=4,5,5 d=.* FOUND:"; }
joblogs() { if [ "$3" = V ]; then ls hwv455V_$(vtag $1 $2).log hwv455V_$(vtag $1 $2)_w*.log 2>/dev/null; else ls hwv455_$(tag $1 $2 $3)_w*.log 2>/dev/null; fi; }
launch() {  # d M O k
  local d=$1 M=$2 O=$3 k=$4 L W CD OF="" ALL FLAG=noV NWA=$NW
  L=$(logf "$@"); W=$(wid "$@")
  if [ "$O" = V ]; then CD=claims455V_$(vtag $d $M); ALL=$(ls hwv455V_d$d*.log 2>/dev/null | tr '\n' ':'); FLAG=""; NWA=$((NW + 1))
  else CD=claims455_$(tag $d $M $O); [ -n "$O" ] && OF=$MAIN/only455_$O.txt; ALL=$(ls hwv455_d$d*.log 2>/dev/null | tr '\n' ':'); fi
  mkdir -p $CD
  for f in $CD/*; do [ -f "$f" ] && [ "$(cat $f)" = "$W" ] && rm -f "$f"; done      # drop the dead worker's claims
  RESUME=$ALL MAXDIM=$M CLAIMDIR=$CD ONLY=$OF setsid nohup python3 sweep_fast.py 4,5,5 $d 8,9 5 $W $NWA $FLAG >> $L 2>&1 < /dev/null &
  echo "runner: launched $(tag $d $M $O) worker $W -> $L ($(date -u +%FT%TZ))"
}
