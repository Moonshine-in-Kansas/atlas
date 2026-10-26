import Atlas.LinearGroups.Chevalley.RootData.E6WeightDistance
import Atlas.LinearGroups.Chevalley.RootData.E6ParabolicFunctional
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! The actual 27 minimal right-parabolic representatives in E6.
The minuscule table follows pullback chronologically, so the actual right-coset
representative is the inverse of the retained word. Minimality follows from
the proved local orbit-distance bound, not an assumed Weyl order. -/
noncomputable section
namespace Atlas.Chevalley.E6WeightOrbit
open Classical RootData E6Data
open scoped BigOperators
local instance : Fintype E6Data.Root := Fintype.ofFinite _
local notation "J" => E6Parabolic.J
local instance : Fintype (rootParabolicRepresentatives pairing base J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup pairing base J) := Fintype.ofFinite _

private def path (c : Fin 27) : List base.support :=
  (exists_shortest_coordinate_word c).choose

private theorem path_spec (c : Fin 27) :
    IsReducedRootWord pairing base (path c) ∧ (path c).length = distance c ∧
      ∀ β : E6Data.Root,
        ((rootWeylWord pairing base (path c)).val β).val 0 = coordinate c β :=
  (exists_shortest_coordinate_word c).choose_spec

/-- Inverse of the chronological pullback word, for right cosets x W_J. -/
def representative (c : Fin 27) : W :=
  (rootWeylWord pairing base (path c))⁻¹

theorem representative_inverse_coordinate (c : Fin 27) (β : E6Data.Root) :
    (((representative c)⁻¹).val β).val 0 = coordinate c β := by
  simpa only [representative, inv_inv] using (path_spec c).2.2 β

theorem representative_length (c : Fin 27) :
    rootWeylLength pairing base (representative c) = distance c := by
  rw [representative, rootWeylLength_inv]
  exact (path_spec c).1.trans (path_spec c).2.1

theorem representative_minimal (c : Fin 27) :
    ∀ i ∈ J, base.IsPos ((representative c).val i.val) := by
  apply (rootWeyl_simple_positive_iff_parabolic_minimal pairing base J _).mpr
  intro v hv
  have hfix : ∀ β : E6Data.Root, (v.val.symm β).val 0 = β.val 0 :=
    (E6Parabolic.mem_parabolic_iff_preserves_first v⁻¹).mp
      ((rootParabolicSubgroup pairing base J).inv_mem hv)
  have hc : ∀ β : E6Data.Root,
      (((representative c * v)⁻¹).val β).val 0 = coordinate c β := by
    intro β
    change (v.val.symm ((representative c).val.symm β)).val 0 = coordinate c β
    rw [hfix]
    exact representative_inverse_coordinate c β
  rw [representative_length]
  simpa only [rootWeylLength_inv] using
    distance_le_rootWeylLength (representative c * v)⁻¹ c hc

def representativeMap : Fin 27 → rootParabolicRepresentatives pairing base J :=
  fun c => ⟨representative c, representative_minimal c⟩

theorem representativeMap_bijective : Function.Bijective representativeMap := by
  constructor
  · intro c d h
    have he : representative c = representative d := congrArg Subtype.val h
    apply coordinate_injective
    funext β
    calc
      coordinate c β = (((representative c)⁻¹).val β).val 0 :=
        (representative_inverse_coordinate c β).symm
      _ = (((representative d)⁻¹).val β).val 0 := by rw [he]
      _ = coordinate d β := representative_inverse_coordinate d β
  · intro x
    obtain ⟨c, hc⟩ := image_coordinate x.val⁻¹
    have hcos : (representative c)⁻¹ * x.val ∈ rootParabolicSubgroup pairing base J := by
      apply (E6Parabolic.mem_parabolic_iff_preserves_first _).mpr
      intro β
      change (((representative c)⁻¹).val (x.val.val β)).val 0 = β.val 0
      rw [representative_inverse_coordinate, ← hc]
      change (x.val.val.symm (x.val.val β)).val 0 = β.val 0
      rw [Equiv.symm_apply_apply]
    have he := rootWeyl_parabolic_minimal_unique pairing base J
      (representative c) x.val (representative_minimal c) x.property hcos
    exact ⟨c, Subtype.ext he⟩

def representativeEquiv : Fin 27 ≃ rootParabolicRepresentatives pairing base J :=
  Equiv.ofBijective representativeMap representativeMap_bijective

theorem representativeEquiv_length (c : Fin 27) :
    rootWeylLength pairing base (representativeEquiv c).val = distance c :=
  representative_length c

/-- Three overlapping length intervals, with the actual weight labels retained. -/
theorem distance_sum (q : ℕ) :
    (∑ c : Fin 27, q ^ distance c) =
    (∑ k : Fin 9, q ^ k.val) * (1 + q ^ 4 + q ^ 8) := by
  let f : Fin 9 × Fin 3 → Fin 27 := fun p =>
    (![![0,1,2,3,4,6,8,10,12], ![5,7,9,11,13,15,17,19,21],
      ![14,16,18,20,22,23,24,25,26]] : Fin 3 → Fin 9 → Fin 27) p.2 p.1
  have hf : Function.Bijective f := by decide +kernel
  have hd : ∀ p : Fin 9 × Fin 3,
      distance (f p) = p.1.val + 4 * p.2.val := by decide +kernel
  let e : Fin 9 × Fin 3 ≃ Fin 27 := Equiv.ofBijective f hf
  calc
    _ = ∑ p : Fin 9 × Fin 3, q ^ (p.1.val + 4 * p.2.val) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      exact (congrArg (fun n : ℕ => q ^ n) (hd p)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_three]
      change (∑ k : Fin 9, (q ^ k.val + q ^ (k.val + 4) + q ^ (k.val + 8))) = _
      simp only [pow_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

/-- The quotient polynomial follows from actual shortest representatives;
the smaller factor still denotes the literal E6 parabolic subgroup. -/
theorem rootWeylPoincareEval_E6_parabolic (q : ℕ) :
    rootWeylPoincareEval pairing base q =
      ((∑ k : Fin 9, q ^ k.val) * (1 + q ^ 4 + q ^ 8)) *
        ∑ v : rootParabolicSubgroup pairing base J,
          q ^ rootWeylLength pairing base v.val := by
  have hr : (∑ x : rootParabolicRepresentatives pairing base J,
      q ^ rootWeylLength pairing base x.val) =
        (∑ k : Fin 9, q ^ k.val) * (1 + q ^ 4 + q ^ 8) := by
    calc
      _ = ∑ c : Fin 27, q ^ rootWeylLength pairing base (representativeEquiv c).val :=
        (Equiv.sum_comp representativeEquiv
          (fun x => q ^ rootWeylLength pairing base x.val)).symm
      _ = ∑ c : Fin 27, q ^ distance c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact congrArg (fun n : ℕ => q ^ n) (representativeEquiv_length c)
      _ = _ := distance_sum q
  rw [rootWeylPoincareEval_parabolic_factor pairing base J, hr]

end Atlas.Chevalley.E6WeightOrbit
