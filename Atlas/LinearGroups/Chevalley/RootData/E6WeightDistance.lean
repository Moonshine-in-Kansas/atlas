import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Orbit
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! The actual 27-weight E6 orbit as integral functionals on roots, with
shortest paths certified by the six local simple-reflection transitions.
No Weyl group enumeration or target order is used. -/
noncomputable section
namespace Atlas.Chevalley.E6WeightOrbit
open Classical RootData E6Data Integral.Minuscule
open scoped BigOperators
set_option maxRecDepth 32768
local instance : Fintype E6Data.Root := Fintype.ofFinite _

abbrev W := pairing.weylGroupToPerm.range

/-- Evaluate the actual minuscule weight on the actual coroot. -/
def coordinate (c : Fin 27) (β : E6Data.Root) : ℤ :=
  E6Minuscule.weight c (corootElement pairing β)

theorem coordinate_eq (c : Fin 27) (β : E6Data.Root) :
    coordinate c β = ∑ i : Fin 6,
      E6MinusculeTable.coordinates c i * β.val (nodeEquiv.symm i) :=
  E6Data.weight_labels_coroot_evaluation _ _

theorem coordinate_simple_root (c : Fin 27) (i : Fin 6) :
    coordinate c (baseIndexEquiv i).val = E6MinusculeTable.coordinates c i := by
  rw [coordinate_eq]
  simp [baseIndexEquiv_apply, simpleRoot, Pi.single_apply]

theorem coordinate_zero (β : E6Data.Root) :
    coordinate 0 β = β.val 0 := by
  rw [coordinate_eq, E6MinusculeTable.initial_coordinates]
  simp [Pi.single_apply, E6MinusculeTable.selectedNode,
    show nodeEquiv.symm (0 : Fin 6) = 0 from rfl]

theorem coordinate_injective : Function.Injective coordinate := by
  intro c d h
  apply E6MinusculeTable.coordinates_injective
  funext i
  simpa only [coordinate_simple_root] using congrFun h (baseIndexEquiv i).val

/-- Pullback by a simple root reflection is the existing weight transition. -/
theorem coordinate_simple (i : Fin 6) (c : Fin 27) (β : E6Data.Root) :
    coordinate c (pairing.reflectionPerm (baseIndexEquiv i).val β) =
      coordinate (E6MinusculeTable.simpleReflectionIndex i c) β := by
  have hw : weightReflection pairing (baseIndexEquiv i).val (E6Minuscule.weight c) =
      E6Minuscule.weight (E6MinusculeTable.simpleReflectionIndex i c) := by
    change weightReflection pairing (baseIndexEquiv i).val
        (weightOfLabels pairing base baseIndexEquiv (E6MinusculeTable.coordinates c)) =
      weightOfLabels pairing base baseIndexEquiv
        (E6MinusculeTable.coordinates (E6MinusculeTable.simpleReflectionIndex i c))
    rw [E6Minuscule.simple_reflection_labels]
    exact congrArg (weightOfLabels pairing base baseIndexEquiv)
      (E6MinusculeTable.simple_reflection_coordinates c i).symm
  have hc : corootElement pairing (pairing.reflectionPerm (baseIndexEquiv i).val β) =
      corootElement pairing β - pairing.pairing (baseIndexEquiv i).val β •
        corootElement pairing (baseIndexEquiv i).val := by
    apply Subtype.ext
    change pairing.coroot (pairing.reflectionPerm (baseIndexEquiv i).val β) =
      pairing.coroot β - pairing.pairing (baseIndexEquiv i).val β •
        pairing.coroot (baseIndexEquiv i).val
    rw [pairing.coroot_reflectionPerm, pairing.coreflection_apply_coroot]
  have he := congrArg (fun μ : WeightLattice pairing => μ (corootElement pairing β)) hw
  rw [coordinate, hc, map_sub, map_smul]
  simpa only [coordinate, weightReflection_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, rootWeight_corootElement, smul_eq_mul, mul_comm] using he

/-- The retained path length, to be proved minimal by local transitions. -/
def distance (c : Fin 27) : ℕ := (E6MinusculeTable.weightWord c).length

theorem distance_zero : distance 0 = 0 := rfl

set_option maxHeartbeats 8000000 in
/-- Only 162 transitions on the already constructed weight orbit are checked. -/
theorem distance_step_le : ∀ i : Fin 6, ∀ c : Fin 27,
    distance (E6MinusculeTable.simpleReflectionIndex i c) ≤ distance c + 1 := by
  decide +kernel

/-- Functional pullback follows the word from left to right. -/
def word : List base.support → Fin 27 → Fin 27
  | [], c => c
  | i :: l, c => word l (E6MinusculeTable.simpleReflectionIndex (baseIndexEquiv.symm i) c)

theorem coordinate_word (l : List base.support) (c : Fin 27) (β : E6Data.Root) :
    coordinate c (simpleReflectionWord pairing base l β) = coordinate (word l c) β := by
  induction l generalizing c with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
    change coordinate c (pairing.reflectionPerm (baseIndexEquiv k).val
      (simpleReflectionWord pairing base l β)) = _
    rw [coordinate_simple, ih]
    simp only [word, Equiv.symm_apply_apply]

theorem word_coordinates (l : List (Fin 6)) (c : Fin 27) :
    E6MinusculeTable.coordinates (word (l.map baseIndexEquiv) c) =
      E6MinusculeTable.wordAction l (E6MinusculeTable.coordinates c) := by
  induction l generalizing c with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, word, Equiv.symm_apply_apply, E6MinusculeTable.wordAction]
    rw [ih, E6MinusculeTable.simple_reflection_coordinates]

theorem word_path (c : Fin 27) :
    word ((E6MinusculeTable.weightWord c).map baseIndexEquiv) 0 = c := by
  apply E6MinusculeTable.coordinates_injective
  rw [word_coordinates, E6MinusculeTable.initial_coordinates,
    E6MinusculeTable.weight_word_coordinates]

theorem distance_word_le (l : List base.support) (c : Fin 27) :
    distance (word l c) ≤ distance c + l.length := by
  induction l generalizing c with
  | nil => simp only [word, List.length_nil, add_zero, le_refl]
  | cons i l ih =>
    have h := ih (E6MinusculeTable.simpleReflectionIndex (baseIndexEquiv.symm i) c)
    have hs := distance_step_le (baseIndexEquiv.symm i) c
    change distance (word l (E6MinusculeTable.simpleReflectionIndex
      (baseIndexEquiv.symm i) c)) ≤ _
    simp only [List.length_cons]
    omega

/-- Every actual Weyl image of the selected row is one of the actual weights. -/
theorem image_coordinate (w : W) : ∃ c : Fin 27, ∀ β : E6Data.Root,
    (w.val β).val 0 = coordinate c β := by
  obtain ⟨l, _, hl⟩ := rootWeylLength_spec pairing base w
  refine ⟨word l 0, ?_⟩
  intro β
  simpa only [coordinate_zero, hl] using coordinate_word l 0 β

theorem distance_le_rootWeylLength (w : W) (c : Fin 27)
    (hc : ∀ β : E6Data.Root, (w.val β).val 0 = coordinate c β) :
    distance c ≤ rootWeylLength pairing base w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec pairing base w
  have he : coordinate (word l 0) = coordinate c := by
    funext β
    rw [← coordinate_word, coordinate_zero, hl]
    exact hc β
  have hlabel := coordinate_injective he
  have hd := distance_word_le l 0
  simpa only [hlabel, distance_zero, zero_add, hlen] using hd

/-- Every retained path is an actual minimum-length word for its orbit label. -/
theorem exists_shortest_coordinate_word (c : Fin 27) :
    ∃ l : List base.support, IsReducedRootWord pairing base l ∧
      l.length = distance c ∧ ∀ β : E6Data.Root,
        ((rootWeylWord pairing base l).val β).val 0 = coordinate c β := by
  let l := (E6MinusculeTable.weightWord c).map baseIndexEquiv
  have hlen : l.length = distance c := by simp only [l, List.length_map, distance]
  have hc : ∀ β : E6Data.Root,
      ((rootWeylWord pairing base l).val β).val 0 = coordinate c β := by
    intro β
    simpa only [rootWeylWord_val, coordinate_zero, l, word_path] using coordinate_word l 0 β
  refine ⟨l, ?_, hlen, hc⟩
  change rootWeylLength pairing base (rootWeylWord pairing base l) = l.length
  apply Nat.le_antisymm (rootWeylWord_length_le pairing base l)
  rw [hlen]
  exact distance_le_rootWeylLength _ c hc

end Atlas.Chevalley.E6WeightOrbit
