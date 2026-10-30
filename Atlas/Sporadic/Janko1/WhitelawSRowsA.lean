import Atlas.Sporadic.Janko1.WhitelawSSearch

/-!
Uncompiled source-only rows for seeds 0, 1, 2, 3.
Each new search fixes both the input seed and its sign. Nine frozen witness
rows are reused across the three files. No combined 80-row decision is used.
-/
namespace Atlas.Janko1

theorem whitelaw_S_row_0_0 : WhitelawSRow 0 (whitelawSearchSign 0) := by
  exact whitelawSRow_of_transport whitelaw_S_link_0_3

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_0_1 : WhitelawSRow 0 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_row_0_2 : WhitelawSRow 0 (whitelawSearchSign 2) := by
  exact whitelawSRow_of_transport whitelaw_S_link_0_4

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_0_3 : WhitelawSRow 0 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_row_0_4 : WhitelawSRow 0 (whitelawSearchSign 4) := by
  exact whitelawSRow_of_transport whitelaw_S_link_0_5

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_0_5 : WhitelawSRow 0 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_row_0_6 : WhitelawSRow 0 (whitelawSearchSign 6) := by
  exact whitelawSRow_of_transport whitelaw_S_link_0_6

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_0_7 : WhitelawSRow 0 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_0 (a : Fin 8) : WhitelawSRow 0 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_0_0
  · exact whitelaw_S_row_0_1
  · exact whitelaw_S_row_0_2
  · exact whitelaw_S_row_0_3
  · exact whitelaw_S_row_0_4
  · exact whitelaw_S_row_0_5
  · exact whitelaw_S_row_0_6
  · exact whitelaw_S_row_0_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_0 : WhitelawSRow 1 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_1 : WhitelawSRow 1 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_2 : WhitelawSRow 1 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_3 : WhitelawSRow 1 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_4 : WhitelawSRow 1 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_5 : WhitelawSRow 1 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_6 : WhitelawSRow 1 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_1_7 : WhitelawSRow 1 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_1 (a : Fin 8) : WhitelawSRow 1 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_1_0
  · exact whitelaw_S_row_1_1
  · exact whitelaw_S_row_1_2
  · exact whitelaw_S_row_1_3
  · exact whitelaw_S_row_1_4
  · exact whitelaw_S_row_1_5
  · exact whitelaw_S_row_1_6
  · exact whitelaw_S_row_1_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_0 : WhitelawSRow 2 (whitelawSearchSign 0) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_1 : WhitelawSRow 2 (whitelawSearchSign 1) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_2 : WhitelawSRow 2 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_3 : WhitelawSRow 2 (whitelawSearchSign 3) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_4 : WhitelawSRow 2 (whitelawSearchSign 4) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_5 : WhitelawSRow 2 (whitelawSearchSign 5) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_6 : WhitelawSRow 2 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_2_7 : WhitelawSRow 2 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_2 (a : Fin 8) : WhitelawSRow 2 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_2_0
  · exact whitelaw_S_row_2_1
  · exact whitelaw_S_row_2_2
  · exact whitelaw_S_row_2_3
  · exact whitelaw_S_row_2_4
  · exact whitelaw_S_row_2_5
  · exact whitelaw_S_row_2_6
  · exact whitelaw_S_row_2_7

theorem whitelaw_S_row_3_0 : WhitelawSRow 3 (whitelawSearchSign 0) := by
  exact whitelawSRow_of_transport whitelaw_S_link_3_2

theorem whitelaw_S_row_3_1 : WhitelawSRow 3 (whitelawSearchSign 1) := by
  exact whitelawSRow_of_transport whitelaw_S_link_3_1

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_3_2 : WhitelawSRow 3 (whitelawSearchSign 2) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_row_3_3 : WhitelawSRow 3 (whitelawSearchSign 3) := by
  exact whitelawSRow_of_transport whitelaw_S_link_3_9

theorem whitelaw_S_row_3_4 : WhitelawSRow 3 (whitelawSearchSign 4) := by
  exact whitelawSRow_of_transport whitelaw_S_link_3_8

theorem whitelaw_S_row_3_5 : WhitelawSRow 3 (whitelawSearchSign 5) := by
  exact whitelawSRow_of_transport whitelaw_S_link_3_7

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_3_6 : WhitelawSRow 3 (whitelawSearchSign 6) := by
  apply whitelawSSearch_sound
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_S_row_3_7 : WhitelawSRow 3 (whitelawSearchSign 7) := by
  apply whitelawSSearch_sound
  decide

theorem whitelaw_S_seed_3 (a : Fin 8) : WhitelawSRow 3 (whitelawSearchSign a) := by
  fin_cases a
  · exact whitelaw_S_row_3_0
  · exact whitelaw_S_row_3_1
  · exact whitelaw_S_row_3_2
  · exact whitelaw_S_row_3_3
  · exact whitelaw_S_row_3_4
  · exact whitelaw_S_row_3_5
  · exact whitelaw_S_row_3_6
  · exact whitelaw_S_row_3_7

end Atlas.Janko1
