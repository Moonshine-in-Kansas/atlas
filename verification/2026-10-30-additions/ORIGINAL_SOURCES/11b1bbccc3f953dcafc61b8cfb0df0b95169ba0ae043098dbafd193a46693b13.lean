import ComparisonWork.J1WhitelawSSearch

/-!
Uncompiled source-only rows for seeds 7, 8, 9.
Each new search fixes both the input seed and its sign. Nine frozen witness
rows are reused across the three files. No combined 80-row decision is used.
-/
namespace Atlas.Janko1

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_0 : WhitelawSRow 7 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_1 : WhitelawSRow 7 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_2 : WhitelawSRow 7 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_3 : WhitelawSRow 7 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_4 : WhitelawSRow 7 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_5 : WhitelawSRow 7 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_6 : WhitelawSRow 7 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_7_7 : WhitelawSRow 7 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_7 (a : Fin 8) : WhitelawSRow 7 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_7_0
  · exact whitelaw_S_row_7_1
  · exact whitelaw_S_row_7_2
  · exact whitelaw_S_row_7_3
  · exact whitelaw_S_row_7_4
  · exact whitelaw_S_row_7_5
  · exact whitelaw_S_row_7_6
  · exact whitelaw_S_row_7_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_0 : WhitelawSRow 8 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_1 : WhitelawSRow 8 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_2 : WhitelawSRow 8 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_3 : WhitelawSRow 8 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_4 : WhitelawSRow 8 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_5 : WhitelawSRow 8 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_6 : WhitelawSRow 8 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_8_7 : WhitelawSRow 8 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_8 (a : Fin 8) : WhitelawSRow 8 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_8_0
  · exact whitelaw_S_row_8_1
  · exact whitelaw_S_row_8_2
  · exact whitelaw_S_row_8_3
  · exact whitelaw_S_row_8_4
  · exact whitelaw_S_row_8_5
  · exact whitelaw_S_row_8_6
  · exact whitelaw_S_row_8_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_0 : WhitelawSRow 9 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_1 : WhitelawSRow 9 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_2 : WhitelawSRow 9 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_3 : WhitelawSRow 9 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_4 : WhitelawSRow 9 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_5 : WhitelawSRow 9 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_6 : WhitelawSRow 9 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_9_7 : WhitelawSRow 9 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_9 (a : Fin 8) : WhitelawSRow 9 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_9_0
  · exact whitelaw_S_row_9_1
  · exact whitelaw_S_row_9_2
  · exact whitelaw_S_row_9_3
  · exact whitelaw_S_row_9_4
  · exact whitelaw_S_row_9_5
  · exact whitelaw_S_row_9_6
  · exact whitelaw_S_row_9_7

end Atlas.Janko1
