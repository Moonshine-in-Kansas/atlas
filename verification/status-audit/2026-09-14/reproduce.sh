#!/usr/bin/env bash
set -euo pipefail
cd /home/gerald/atlas
audit_dir=verification/status-audit/2026-09-14
lake_bin=/home/gerald/.elan/bin/lake
ruby "$audit_dir/verify_snapshot.rb"
"$lake_bin" build > "$audit_dir/build.log" 2>&1
for driver in Inventory Extract Definitions Extra Auxiliary Evidence; do
  case "$driver" in
    Inventory) log=inventory;; Extract) log=extract;; Definitions) log=definitions;;
    Extra) log=extra;; Auxiliary) log=aux;; Evidence) log=example;;
  esac
  "$lake_bin" env lean "$audit_dir/$driver.lean" > "$audit_dir/$log.log" 2>&1
done
ruby "$audit_dir/parent_list.rb"
"$lake_bin" env lean "$audit_dir/Ranges.lean" > "$audit_dir/ranges.log" 2>&1
rg -n '\b(sorry|admit|axiom|native_decide)\b' Atlas --glob '*.lean' > "$audit_dir/source-token-scan.txt" || test "$?" -eq 1
ruby "$audit_dir/analyze.rb" > "$audit_dir/analysis.log" 2>&1
ruby "$audit_dir/catalogue.rb"
ruby "$audit_dir/report.rb"
ruby "$audit_dir/enrich.rb"
ruby "$audit_dir/validate.rb" > "$audit_dir/VALIDATION.txt"
