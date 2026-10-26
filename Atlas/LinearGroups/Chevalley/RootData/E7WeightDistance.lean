import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Orbit
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! The actual 56-weight E7 orbit as integral functionals on roots, with
shortest paths certified by the seven local simple-reflection transitions.
No Weyl group enumeration or target order is used. -/
noncomputable section
namespace Atlas.Chevalley.E7WeightOrbit
open Classical RootData E7Data Integral.Minuscule
open scoped BigOperators
set_option maxRecDepth 32768

abbrev W := pairing.weylGroupToPerm.range

/-- Evaluate the actual minuscule weight on the actual coroot. -/
def coordinate (c : Fin 56) (β : E7Data.Root) : ℤ :=
  E7Minuscule.weight c (corootElement pairing β)

theorem coordinate_eq (c : Fin 56) (β : E7Data.Root) :
    coordinate c β = ∑ i : Fin 7,
      E7MinusculeTable.coordinates c i * E7Table.coordinates β i :=
  E7Data.weight_labels_coroot_evaluation _ _

theorem coordinate_simple_root (c : Fin 56) (i : Fin 7) :
    coordinate c (baseIndexEquiv i).val = E7MinusculeTable.coordinates c i := by
  rw [coordinate_eq]
  have hs : E7Table.coordinates (baseIndexEquiv i).val = Pi.single i 1 :=
    datum.simple_coordinates i
  rw [hs]
  simp [Pi.single_apply]

theorem coordinate_zero (β : E7Data.Root) :
    coordinate 0 β = E7Table.coordinates β 6 := by
  rw [coordinate_eq, E7MinusculeTable.initial_coordinates]
  simp [Pi.single_apply, E7MinusculeTable.selectedNode]

theorem coordinate_injective : Function.Injective coordinate := by
  intro c d h
  apply E7MinusculeTable.coordinates_injective
  funext i
  simpa only [coordinate_simple_root] using congrFun h (baseIndexEquiv i).val

/-- Pullback by a simple root reflection is the existing weight transition. -/
theorem coordinate_simple (i : Fin 7) (c : Fin 56) (β : E7Data.Root) :
    coordinate c (pairing.reflectionPerm (baseIndexEquiv i).val β) =
      coordinate (E7MinusculeTable.simpleReflectionIndex i c) β := by
  have hw : weightReflection pairing (baseIndexEquiv i).val (E7Minuscule.weight c) =
      E7Minuscule.weight (E7MinusculeTable.simpleReflectionIndex i c) := by
    change weightReflection pairing (baseIndexEquiv i).val
        (weightOfLabels pairing base baseIndexEquiv (E7MinusculeTable.coordinates c)) =
      weightOfLabels pairing base baseIndexEquiv
        (E7MinusculeTable.coordinates (E7MinusculeTable.simpleReflectionIndex i c))
    rw [E7Minuscule.simple_reflection_labels]
    exact congrArg (weightOfLabels pairing base baseIndexEquiv)
      (E7MinusculeTable.simple_reflection_coordinates c i).symm
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
def distance (c : Fin 56) : ℕ := (E7MinusculeTable.weightWord c).length

theorem distance_zero : distance 0 = 0 := rfl

set_option maxHeartbeats 8000000 in
/-- Only 392 transitions on the already constructed weight orbit are checked. -/
theorem distance_step_le : ∀ i : Fin 7, ∀ c : Fin 56,
    distance (E7MinusculeTable.simpleReflectionIndex i c) ≤ distance c + 1 := by
  decide +kernel

/-- Functional pullback follows the word from left to right. -/
def word : List base.support → Fin 56 → Fin 56
  | [], c => c
  | i :: l, c => word l (E7MinusculeTable.simpleReflectionIndex (baseIndexEquiv.symm i) c)

theorem coordinate_word (l : List base.support) (c : Fin 56) (β : E7Data.Root) :
    coordinate c (simpleReflectionWord pairing base l β) = coordinate (word l c) β := by
  induction l generalizing c with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
    change coordinate c (pairing.reflectionPerm (baseIndexEquiv k).val
      (simpleReflectionWord pairing base l β)) = _
    rw [coordinate_simple, ih]
    simp only [word, Equiv.symm_apply_apply]

theorem word_coordinates (l : List (Fin 7)) (c : Fin 56) :
    E7MinusculeTable.coordinates (word (l.map baseIndexEquiv) c) =
      E7MinusculeTable.wordAction l (E7MinusculeTable.coordinates c) := by
  induction l generalizing c with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, word, Equiv.symm_apply_apply, E7MinusculeTable.wordAction]
    rw [ih, E7MinusculeTable.simple_reflection_coordinates]

theorem word_path (c : Fin 56) :
    word ((E7MinusculeTable.weightWord c).map baseIndexEquiv) 0 = c := by
  apply E7MinusculeTable.coordinates_injective
  rw [word_coordinates, E7MinusculeTable.initial_coordinates,
    E7MinusculeTable.weight_word_coordinates]

theorem distance_word_le (l : List base.support) (c : Fin 56) :
    distance (word l c) ≤ distance c + l.length := by
  induction l generalizing c with
  | nil => simp only [word, List.length_nil, add_zero, le_refl]
  | cons i l ih =>
    have h := ih (E7MinusculeTable.simpleReflectionIndex (baseIndexEquiv.symm i) c)
    have hs := distance_step_le (baseIndexEquiv.symm i) c
    change distance (word l (E7MinusculeTable.simpleReflectionIndex
      (baseIndexEquiv.symm i) c)) ≤ _
    simp only [List.length_cons]
    omega

/-- Every actual Weyl image of the selected row is one of the actual weights. -/
theorem image_coordinate (w : W) : ∃ c : Fin 56, ∀ β : E7Data.Root,
    E7Table.coordinates (w.val β) 6 = coordinate c β := by
  obtain ⟨l, _, hl⟩ := rootWeylLength_spec pairing base w
  refine ⟨word l 0, ?_⟩
  intro β
  simpa only [coordinate_zero, hl] using coordinate_word l 0 β

theorem distance_le_rootWeylLength (w : W) (c : Fin 56)
    (hc : ∀ β : E7Data.Root, E7Table.coordinates (w.val β) 6 = coordinate c β) :
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
theorem exists_shortest_coordinate_word (c : Fin 56) :
    ∃ l : List base.support, IsReducedRootWord pairing base l ∧
      l.length = distance c ∧ ∀ β : E7Data.Root,
        E7Table.coordinates ((rootWeylWord pairing base l).val β) 6 = coordinate c β := by
  let l := (E7MinusculeTable.weightWord c).map baseIndexEquiv
  have hlen : l.length = distance c := by simp only [l, List.length_map, distance]
  have hc : ∀ β : E7Data.Root,
      E7Table.coordinates ((rootWeylWord pairing base l).val β) 6 = coordinate c β := by
    intro β
    simpa only [rootWeylWord_val, coordinate_zero, l, word_path] using coordinate_word l 0 β
  refine ⟨l, ?_, hlen, hc⟩
  change rootWeylLength pairing base (rootWeylWord pairing base l) = l.length
  apply Nat.le_antisymm (rootWeylWord_length_le pairing base l)
  rw [hlen]
  exact distance_le_rootWeylLength _ c hc

end Atlas.Chevalley.E7WeightOrbit
