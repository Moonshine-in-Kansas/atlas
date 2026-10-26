import Atlas.LinearGroups.Chevalley.RootData.E7WeightDistance
import Atlas.LinearGroups.Chevalley.RootData.E7WeightParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! The actual56 minimal right-parabolic representatives in E7. The retained
weight word describes pullback, so the representative of x W_J is its inverse.
Minimality follows from the proved local orbit-distance bound. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
noncomputable section
namespace Atlas.Chevalley.E7WeightOrbit
open Classical RootData E7Data
open scoped BigOperators
local instance : Fintype (rootParabolicRepresentatives pairing base J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup pairing base J) := Fintype.ofFinite _

private def path (c : Fin 56) : List base.support :=
  (exists_shortest_coordinate_word c).choose

private theorem path_spec (c : Fin 56) :
    IsReducedRootWord pairing base (path c) ∧ (path c).length = distance c ∧
      ∀ β : E7Data.Root,
        E7Table.coordinates ((rootWeylWord pairing base (path c)).val β) 6 = coordinate c β :=
  (exists_shortest_coordinate_word c).choose_spec

/-- Inverse of the chronological pullback word, for right cosets x W_J. -/
def representative (c : Fin 56) : W :=
  (rootWeylWord pairing base (path c))⁻¹

theorem representative_inverse_coordinate (c : Fin 56) (β : E7Data.Root) :
    E7Table.coordinates (((representative c)⁻¹).val β) 6 = coordinate c β := by
  simpa only [representative, inv_inv] using (path_spec c).2.2 β

theorem representative_length (c : Fin 56) :
    rootWeylLength pairing base (representative c) = distance c := by
  rw [representative, rootWeylLength_inv]
  exact (path_spec c).1.trans (path_spec c).2.1

theorem representative_minimal (c : Fin 56) :
    ∀ i ∈ J, base.IsPos ((representative c).val i.val) := by
  apply (rootWeyl_simple_positive_iff_parabolic_minimal pairing base J _).mpr
  intro v hv
  have hfix : ∀ β : E7Data.Root,
      E7Table.coordinates (v.val.symm β) 6 = E7Table.coordinates β 6 :=
    (mem_parabolic_iff_preserves_coordinate v⁻¹).mp
      ((rootParabolicSubgroup pairing base J).inv_mem hv)
  have hc : ∀ β : E7Data.Root,
      E7Table.coordinates (((representative c * v)⁻¹).val β) 6 = coordinate c β := by
    intro β
    change E7Table.coordinates (v.val.symm ((representative c).val.symm β)) 6 = coordinate c β
    rw [hfix]
    exact representative_inverse_coordinate c β
  rw [representative_length]
  simpa only [rootWeylLength_inv] using
    distance_le_rootWeylLength (representative c * v)⁻¹ c hc

def representativeMap : Fin 56 → rootParabolicRepresentatives pairing base J :=
  fun c => ⟨representative c, representative_minimal c⟩

theorem representativeMap_bijective : Function.Bijective representativeMap := by
  constructor
  · intro c d h
    have he : representative c = representative d := congrArg Subtype.val h
    apply coordinate_injective
    funext β
    calc
      coordinate c β = E7Table.coordinates (((representative c)⁻¹).val β) 6 :=
        (representative_inverse_coordinate c β).symm
      _ = E7Table.coordinates (((representative d)⁻¹).val β) 6 := by rw [he]
      _ = coordinate d β := representative_inverse_coordinate d β
  · intro x
    obtain ⟨c, hc⟩ := image_coordinate x.val⁻¹
    have hcos : (representative c)⁻¹ * x.val ∈ rootParabolicSubgroup pairing base J := by
      apply (mem_parabolic_iff_preserves_coordinate _).mpr
      intro β
      change E7Table.coordinates (((representative c)⁻¹).val (x.val.val β)) 6 =
        E7Table.coordinates β 6
      rw [representative_inverse_coordinate, ← hc]
      change E7Table.coordinates (x.val.val.symm (x.val.val β)) 6 = E7Table.coordinates β 6
      rw [Equiv.symm_apply_apply]
    have he := rootWeyl_parabolic_minimal_unique pairing base J
      (representative c) x.val (representative_minimal c) x.property hcos
    exact ⟨c, Subtype.ext he⟩

def representativeEquiv : Fin 56 ≃ rootParabolicRepresentatives pairing base J :=
  Equiv.ofBijective representativeMap representativeMap_bijective

theorem representativeEquiv_length (c : Fin 56) :
    rootWeylLength pairing base (representativeEquiv c).val = distance c :=
  representative_length c

/-- Four explicit intervals of lengths0–13,5–18,9–22,14–27, retaining every
actual weight label. The bijection and distances are kernel computations. -/
theorem distance_sum (q : ℕ) :
    (∑ c : Fin 56, q ^ distance c) =
      (∑ k : Fin 14, q ^ k.val) * (1 + q ^ 5) * (1 + q ^ 9) := by
  let f : Fin 14 × Fin 4 → Fin 56 := fun p =>
    (![![0,1,2,3,4,5,7,9,11,13,16,19,22,25],
       ![6,8,10,12,14,17,20,23,26,28,31,34,37,40],
       ![15,18,21,24,27,29,32,35,38,41,43,45,47,49],
       ![30,33,36,39,42,44,46,48,50,51,52,53,54,55]] :
      Fin 4 → Fin 14 → Fin 56) p.2 p.1
  have hf : Function.Bijective f := by decide +kernel
  have hd : ∀ p : Fin 14 × Fin 4,
      distance (f p) = p.1.val + (![0,5,9,14] : Fin 4 → ℕ) p.2 := by decide +kernel
  let e : Fin 14 × Fin 4 ≃ Fin 56 := Equiv.ofBijective f hf
  calc
    _ = ∑ p : Fin 14 × Fin 4,
        q ^ (p.1.val + (![0,5,9,14] : Fin 4 → ℕ) p.2) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      exact (congrArg (fun n : ℕ => q ^ n) (hd p)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_four]
      change (∑ k : Fin 14,
        (q ^ k.val + q ^ (k.val + 5) + q ^ (k.val + 9) + q ^ (k.val + 14))) = _
      simp only [pow_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

/-- The quotient polynomial follows from actual shortest representatives;
the smaller factor still denotes the literal E7 parabolic subgroup. -/
theorem rootWeylPoincareEval_E7_parabolic (q : ℕ) :
    rootWeylPoincareEval pairing base q =
      ((∑ k : Fin 14, q ^ k.val) * (1 + q ^ 5) * (1 + q ^ 9)) *
        ∑ v : rootParabolicSubgroup pairing base J,
          q ^ rootWeylLength pairing base v.val := by
  have hr : (∑ x : rootParabolicRepresentatives pairing base J,
      q ^ rootWeylLength pairing base x.val) =
        (∑ k : Fin 14, q ^ k.val) * (1 + q ^ 5) * (1 + q ^ 9) := by
    calc
      _ = ∑ c : Fin 56, q ^ rootWeylLength pairing base (representativeEquiv c).val :=
        (Equiv.sum_comp representativeEquiv
          (fun x => q ^ rootWeylLength pairing base x.val)).symm
      _ = ∑ c : Fin 56, q ^ distance c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact congrArg (fun n : ℕ => q ^ n) (representativeEquiv_length c)
      _ = _ := distance_sum q
  rw [rootWeylPoincareEval_parabolic_factor pairing base J, hr]

end Atlas.Chevalley.E7WeightOrbit
