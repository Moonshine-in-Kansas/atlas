import ComparisonWork.J1WhitelawSSearch

/-!
Uncompiled source-only rows for seeds 4, 5, 6.
Each new search fixes both the input seed and its sign. Nine frozen witness
rows are reused across the three files. No combined 80-row decision is used.
-/
namespace Atlas.Janko1

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_0 : WhitelawSRow 4 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_1 : WhitelawSRow 4 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_2 : WhitelawSRow 4 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_3 : WhitelawSRow 4 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_4 : WhitelawSRow 4 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_5 : WhitelawSRow 4 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_6 : WhitelawSRow 4 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_4_7 : WhitelawSRow 4 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_4 (a : Fin 8) : WhitelawSRow 4 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_4_0
  · exact whitelaw_S_row_4_1
  · exact whitelaw_S_row_4_2
  · exact whitelaw_S_row_4_3
  · exact whitelaw_S_row_4_4
  · exact whitelaw_S_row_4_5
  · exact whitelaw_S_row_4_6
  · exact whitelaw_S_row_4_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_0 : WhitelawSRow 5 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_1 : WhitelawSRow 5 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_2 : WhitelawSRow 5 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_3 : WhitelawSRow 5 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_4 : WhitelawSRow 5 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_5 : WhitelawSRow 5 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_6 : WhitelawSRow 5 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_5_7 : WhitelawSRow 5 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_5 (a : Fin 8) : WhitelawSRow 5 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_5_0
  · exact whitelaw_S_row_5_1
  · exact whitelaw_S_row_5_2
  · exact whitelaw_S_row_5_3
  · exact whitelaw_S_row_5_4
  · exact whitelaw_S_row_5_5
  · exact whitelaw_S_row_5_6
  · exact whitelaw_S_row_5_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_0 : WhitelawSRow 6 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_1 : WhitelawSRow 6 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_2 : WhitelawSRow 6 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_3 : WhitelawSRow 6 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_4 : WhitelawSRow 6 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_5 : WhitelawSRow 6 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_6 : WhitelawSRow 6 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_6_7 : WhitelawSRow 6 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_6 (a : Fin 8) : WhitelawSRow 6 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_6_0
  · exact whitelaw_S_row_6_1
  · exact whitelaw_S_row_6_2
  · exact whitelaw_S_row_6_3
  · exact whitelaw_S_row_6_4
  · exact whitelaw_S_row_6_5
  · exact whitelaw_S_row_6_6
  · exact whitelaw_S_row_6_7

end Atlas.Janko1
