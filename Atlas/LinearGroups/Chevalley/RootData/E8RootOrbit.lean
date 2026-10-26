import Atlas.LinearGroups.Chevalley.RootData.E8
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords
import Mathlib.Data.Fin.VecNotation

/-! The literal 240-root E8 orbit, with local shortest-path certificates.
Only eight simple-reflection transitions and a parent for each root are
checked. No Weyl group enumeration or group-order formula is assumed. -/
noncomputable section
namespace Atlas.Chevalley.E8RootOrbit
open Classical RootData E8Data
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

abbrev W := pairing.weylGroupToPerm.range
def label (c : Fin 240) : E8Data.Root := c
def seed : E8Data.Root := label 238

theorem label_injective : Function.Injective label := fun _ _ h => h

/-- The actual simple-reflection transition, retaining the original root labels. -/
def step : Fin 8 → Fin 240 → Fin 240 := E8Table.simpleReflectionIndex

theorem reflection_label (i : Fin 8) (c : Fin 240) :
    pairing.reflectionPerm (baseIndexEquiv i).val (label c) = label (step i c) := by
  apply pairing.root.injective
  rw [pairing.root_reflectionPerm, pairing.reflection_apply_root]
  change E8Table.coordinates c -
      ExceptionalData.form 8 (E8Table.coordinates (E8Table.simpleIndex i))
        (E8Table.coordinates c) • E8Table.coordinates (E8Table.simpleIndex i) =
      E8Table.coordinates (E8Table.simpleReflectionIndex i c)
  rw [E8Table.simple_coordinates]
  exact (datum.simple_reflection_coordinates i c).symm

/-- The distance from the literal dominant root 238. -/
def distance (c : Fin 240) : ℕ :=
  (#[28,29,27,30,28,26,29,31,27,25,25,30,32,32,26,28,26,24,24,31,29,31,33,33,27,25,27,25,23,23,23,30,32,30,32,34,34,34,28,26,24,24,28,26,24,22,22,22,22,29,31,33,33,29,31,33,35,35,35,35,25,23,23,27,25,23,21,21,21,21,32,34,34,30,32,34,36,36,36,36,24,22,22,22,28,26,24,20,20,20,20,33,35,35,35,29,31,33,37,37,37,37,23,21,21,27,25,19,19,19,19,19,34,36,36,30,32,38,38,38,38,38,20,20,28,26,18,18,18,18,18,37,37,29,31,39,39,39,39,39,19,27,17,17,17,17,17,38,30,40,40,40,40,40,18,28,16,16,16,16,16,39,29,41,41,41,41,41,15,15,15,15,42,42,42,42,14,14,14,14,43,43,43,43,13,13,13,13,44,44,44,44,12,12,12,12,45,45,45,45,11,11,11,46,46,46,10,10,10,47,47,47,9,9,48,48,8,8,49,49,7,7,50,50,6,6,51,51,5,52,4,53,3,54,2,55,1,56,0,57] : Array ℕ)[c.val]!

private def predecessor (c : Fin 240) : Fin 240 :=
  Fin.ofNat 240 ((#[2,0,5,6,8,10,4,11,16,17,18,20,19,21,25,26,27,29,30,31,15,33,32,34,39,41,43,44,46,47,48,20,50,53,54,22,52,55,24,60,61,62,63,64,65,66,68,69,69,38,33,32,70,42,73,74,35,36,72,75,80,82,83,85,86,83,88,89,90,90,54,52,91,95,96,97,57,57,58,94,102,103,104,104,105,106,65,108,109,111,111,74,71,72,112,84,115,116,76,78,78,79,83,123,123,125,86,127,129,129,130,130,97,93,94,133,134,98,99,101,100,101,140,140,141,106,142,144,145,145,146,113,114,124,148,117,118,118,119,121,154,125,157,159,159,160,160,132,162,136,136,138,138,139,146,141,169,169,170,171,171,147,155,149,151,150,151,152,177,178,179,179,163,164,166,166,185,186,186,187,172,173,173,174,193,194,195,195,180,181,181,183,200,201,202,202,188,189,189,190,206,207,208,197,197,198,212,213,213,203,204,205,216,217,209,210,220,220,214,215,225,224,218,219,228,228,222,222,230,226,232,229,234,231,236,233,238,235,238,237] : Array ℕ)[c.val]!)

private def predecessorStep (c : Fin 240) : Fin 8 :=
  Fin.ofNat 8 ((#[2,0,3,0,3,4,2,0,4,4,5,2,0,0,4,4,5,5,6,2,3,2,0,0,4,5,5,6,5,6,7,1,2,3,2,3,0,0,3,5,5,6,5,6,7,5,6,7,1,1,1,3,2,4,3,2,2,3,0,0,6,6,7,6,7,1,6,6,7,3,1,3,2,4,3,2,2,4,3,0,7,6,7,3,6,7,2,6,7,7,4,1,4,3,2,5,4,3,4,2,4,3,2,7,4,7,3,6,7,4,7,5,1,4,3,5,4,3,4,2,5,4,7,5,7,4,6,7,7,5,6,5,4,6,5,1,3,5,4,5,6,5,7,7,5,6,2,5,6,1,5,3,5,6,0,6,7,5,7,6,3,6,7,5,1,4,5,6,7,6,6,4,4,5,4,6,7,6,4,5,3,4,6,6,7,6,5,1,2,3,6,5,7,6,5,3,0,2,6,5,6,5,4,0,6,5,5,4,2,6,5,4,4,3,5,4,3,0,4,3,2,0,3,1,2,1,1,2,3,2,4,3,5,4,6,5,7,6,0,7] : Array ℕ)[c.val]!)

private theorem distance_step_le_0 : ∀ c : Fin 240,
    distance (step 0 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_1 : ∀ c : Fin 240,
    distance (step 1 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_2 : ∀ c : Fin 240,
    distance (step 2 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_3 : ∀ c : Fin 240,
    distance (step 3 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_4 : ∀ c : Fin 240,
    distance (step 4 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_5 : ∀ c : Fin 240,
    distance (step 5 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_6 : ∀ c : Fin 240,
    distance (step 6 c) ≤ distance c + 1 := by decide +kernel

private theorem distance_step_le_7 : ∀ c : Fin 240,
    distance (step 7 c) ≤ distance c + 1 := by decide +kernel

theorem distance_step_le (i : Fin 8) : ∀ c : Fin 240,
    distance (step i c) ≤ distance c + 1 := by
  fin_cases i
  · exact distance_step_le_0
  · exact distance_step_le_1
  · exact distance_step_le_2
  · exact distance_step_le_3
  · exact distance_step_le_4
  · exact distance_step_le_5
  · exact distance_step_le_6
  · exact distance_step_le_7


theorem distance_eq_zero_iff : ∀ c : Fin 240, distance c = 0 ↔ c = 238 := by
  decide +kernel

private theorem predecessor_spec_0 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((0 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((0 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((0 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((0 : Fin 8), k))) (predecessor (finProdFinEquiv ((0 : Fin 8), k))) =
        finProdFinEquiv ((0 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_1 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((1 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((1 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((1 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((1 : Fin 8), k))) (predecessor (finProdFinEquiv ((1 : Fin 8), k))) =
        finProdFinEquiv ((1 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_2 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((2 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((2 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((2 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((2 : Fin 8), k))) (predecessor (finProdFinEquiv ((2 : Fin 8), k))) =
        finProdFinEquiv ((2 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_3 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((3 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((3 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((3 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((3 : Fin 8), k))) (predecessor (finProdFinEquiv ((3 : Fin 8), k))) =
        finProdFinEquiv ((3 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_4 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((4 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((4 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((4 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((4 : Fin 8), k))) (predecessor (finProdFinEquiv ((4 : Fin 8), k))) =
        finProdFinEquiv ((4 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_5 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((5 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((5 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((5 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((5 : Fin 8), k))) (predecessor (finProdFinEquiv ((5 : Fin 8), k))) =
        finProdFinEquiv ((5 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_6 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((6 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((6 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((6 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((6 : Fin 8), k))) (predecessor (finProdFinEquiv ((6 : Fin 8), k))) =
        finProdFinEquiv ((6 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec_7 : ∀ k : Fin 30,
    0 < distance (finProdFinEquiv ((7 : Fin 8), k)) →
    distance (predecessor (finProdFinEquiv ((7 : Fin 8), k))) + 1 = distance (finProdFinEquiv ((7 : Fin 8), k)) ∧
      step (predecessorStep (finProdFinEquiv ((7 : Fin 8), k))) (predecessor (finProdFinEquiv ((7 : Fin 8), k))) =
        finProdFinEquiv ((7 : Fin 8), k) := by decide +kernel

private theorem predecessor_spec : ∀ c : Fin 240, 0 < distance c →
    distance (predecessor c) + 1 = distance c ∧
      step (predecessorStep c) (predecessor c) = c := by
  intro c
  obtain ⟨⟨i, k⟩, rfl⟩ := (finProdFinEquiv : Fin 8 × Fin 30 ≃ Fin 240).surjective c
  fin_cases i
  · exact predecessor_spec_0 k
  · exact predecessor_spec_1 k
  · exact predecessor_spec_2 k
  · exact predecessor_spec_3 k
  · exact predecessor_spec_4 k
  · exact predecessor_spec_5 k
  · exact predecessor_spec_6 k
  · exact predecessor_spec_7 k

theorem exists_predecessor (c : Fin 240) (hc : 0 < distance c) :
    ∃ d : Fin 240, ∃ i : Fin 8,
      distance d + 1 = distance c ∧ step i d = c :=
  ⟨predecessor c, predecessorStep c, predecessor_spec c hc⟩

def word : List base.support → Fin 240 → Fin 240
  | [], c => c
  | i :: l, c => step (baseIndexEquiv.symm i) (word l c)

theorem word_label (l : List base.support) (c : Fin 240) :
    simpleReflectionWord pairing base l (label c) = label (word l c) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
    change pairing.reflectionPerm (baseIndexEquiv k).val
      (simpleReflectionWord pairing base l (label c)) = _
    rw [ih, reflection_label]
    simp only [word, Equiv.symm_apply_apply]

theorem distance_word_le (l : List base.support) (c : Fin 240) :
    distance (word l c) ≤ distance c + l.length := by
  induction l with
  | nil => simp only [word, List.length_nil, add_zero, le_refl]
  | cons i l ih =>
    have hs := distance_step_le (baseIndexEquiv.symm i) (word l c)
    change distance (step (baseIndexEquiv.symm i) (word l c)) ≤ _
    simp only [List.length_cons]
    omega

theorem exists_distance_word (c : Fin 240) :
    ∃ l : List base.support, l.length = distance c ∧ word l 238 = c := by
  have aux : ∀ k : ℕ, ∀ c : Fin 240, distance c = k →
      ∃ l : List base.support, l.length = distance c ∧ word l 238 = c := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hc
      by_cases hk : k = 0
      · have hz := (distance_eq_zero_iff c).mp (hc.trans hk)
        subst c
        exact ⟨[], rfl, rfl⟩
      · obtain ⟨d, i, hd, hs⟩ := exists_predecessor c (by omega)
        obtain ⟨l, hlen, hw⟩ := ih (distance d) (by omega) d rfl
        refine ⟨baseIndexEquiv i :: l, ?_, ?_⟩
        · simpa only [List.length_cons, hlen] using hd
        · simpa only [word, Equiv.symm_apply_apply, hw] using hs
  exact aux (distance c) c rfl

theorem image_seed_label (w : W) : ∃ c : Fin 240, w.val seed = label c := by
  obtain ⟨l, _hlen, hl⟩ := rootWeylLength_spec pairing base w
  exact ⟨word l 238, by simpa only [hl, seed] using word_label l 238⟩

theorem distance_le_rootWeylLength (w : W) (c : Fin 240)
    (hc : w.val seed = label c) : distance c ≤ rootWeylLength pairing base w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec pairing base w
  have he : label (word l 238) = label c := by
    rw [← word_label, hl]
    exact hc
  have hd := distance_word_le l 238
  have hz : distance (238 : Fin 240) = 0 := rfl
  simpa only [label_injective he, hz, zero_add, hlen] using hd

theorem exists_shortest_seed_word (c : Fin 240) :
    ∃ l : List base.support, IsReducedRootWord pairing base l ∧
      l.length = distance c ∧ (rootWeylWord pairing base l).val seed = label c := by
  obtain ⟨l, hlen, hw⟩ := exists_distance_word c
  have hc : (rootWeylWord pairing base l).val seed = label c := by
    simpa only [rootWeylWord_val, seed, hw] using word_label l 238
  refine ⟨l, ?_, hlen, hc⟩
  change rootWeylLength pairing base (rootWeylWord pairing base l) = l.length
  apply Nat.le_antisymm (rootWeylWord_length_le pairing base l)
  rw [hlen]
  exact distance_le_rootWeylLength _ c hc

def rootOrbitEquiv : Fin 240 ≃ {β : E8Data.Root // ∃ w : W, w.val seed = β} :=
  Equiv.ofBijective
    (fun c => ⟨label c, by
      obtain ⟨l, _hr, _hlen, hc⟩ := exists_shortest_seed_word c
      exact ⟨rootWeylWord pairing base l, hc⟩⟩)
    ⟨by intro c d h; exact label_injective (congrArg Subtype.val h), by
      rintro ⟨β, w, hw⟩
      obtain ⟨c, hc⟩ := image_seed_label w
      exact ⟨c, Subtype.ext (hc.symm.trans hw)⟩⟩

theorem rootOrbit_card : Nat.card {β : E8Data.Root // ∃ w : W, w.val seed = β} = 240 := by
  rw [← Nat.card_congr rootOrbitEquiv]
  simp

end Atlas.Chevalley.E8RootOrbit
