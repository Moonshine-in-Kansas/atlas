import Atlas.LinearGroups.Chevalley.RootData.F4ShortParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! The24 actual minimal right-parabolic representatives in F4 and their
length sum. The marked parabolic is not identified with an abstract B3 group
here; the factorization retains its literal subgroup as the smaller factor. -/
noncomputable section
namespace Atlas.Chevalley.F4ShortOrbit
open Classical RootData F4Data

local instance : Fintype (rootParabolicRepresentatives pairing base J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup pairing base J) := Fintype.ofFinite _

private def path (c : Fin 24) : List base.support :=
  (exists_shortest_seed_word c).choose

private theorem path_spec (c : Fin 24) :
    IsReducedRootWord pairing base (path c) ∧ (path c).length = distance c ∧
      (rootWeylWord pairing base (path c)).val seed = label c :=
  (exists_shortest_seed_word c).choose_spec

def representative (c : Fin 24) : W := rootWeylWord pairing base (path c)

theorem representative_seed (c : Fin 24) : (representative c).val seed = label c :=
  (path_spec c).2.2

theorem representative_length (c : Fin 24) :
    rootWeylLength pairing base (representative c) = distance c :=
  (path_spec c).1.trans (path_spec c).2.1

theorem representative_minimal (c : Fin 24) :
    ∀ i ∈ J, base.IsPos ((representative c).val i.val) := by
  let p := (rootParabolicProductEquiv pairing base J).symm (representative c)
  have hp : p.1.val * p.2.val = representative c :=
    (rootParabolicProductEquiv pairing base J).apply_symm_apply _
  have hfix := (fixes_seed_iff_parabolic p.2.val).mpr p.2.property
  have himage : p.1.val.val seed = label c := by
    have h := representative_seed c
    rw [← hp] at h
    change p.1.val.val (p.2.val.val seed) = _ at h
    rwa [hfix] at h
  have hbound := distance_le_rootWeylLength p.1.val c himage
  have hlen := rootParabolicProductEquiv_length pairing base J p
  change rootWeylLength pairing base (p.1.val * p.2.val) = _ at hlen
  rw [hp, representative_length] at hlen
  have hv0 : rootWeylLength pairing base p.2.val = 0 := by omega
  have hv1 := (rootWeylLength_eq_zero_iff pairing base p.2.val).mp hv0
  have hx : p.1.val = representative c := by simpa only [hv1, mul_one] using hp
  simpa only [hx] using p.1.property

def representativeMap : Fin 24 → rootParabolicRepresentatives pairing base J :=
  fun c => ⟨representative c, representative_minimal c⟩

theorem representativeMap_bijective : Function.Bijective representativeMap := by
  constructor
  · intro c d h
    have he : representative c = representative d := congrArg Subtype.val h
    apply label_injective
    rw [← representative_seed, ← representative_seed, he]
  · intro x
    obtain ⟨c, hc⟩ := image_seed_label x.val
    have hfix : ((representative c)⁻¹ * x.val).val seed = seed := by
      change (representative c).val.symm (x.val.val seed) = seed
      rw [hc, ← representative_seed]
      exact (representative c).val.symm_apply_apply seed
    have he := rootWeyl_parabolic_minimal_unique pairing base J
      (representative c) x.val (representative_minimal c) x.property
      ((fixes_seed_iff_parabolic _).mp hfix)
    exact ⟨c, Subtype.ext he⟩

def representativeEquiv : Fin 24 ≃ rootParabolicRepresentatives pairing base J :=
  Equiv.ofBijective representativeMap representativeMap_bijective

theorem representativeEquiv_length (c : Fin 24) :
    rootWeylLength pairing base (representativeEquiv c).val = distance c :=
  representative_length c

/-- The histogram keeps both labels in degrees4 through11. -/
theorem distance_sum (q : ℕ) :
    (∑ c : Fin 24, q ^ distance c) = (∑ k : Fin 12, q ^ k.val) * (1 + q ^ 4) := by
  let f : Fin 12 × Bool → Fin 24 := fun p =>
    if p.2 then (![12,13,14,15,16,17,18,20,21,22,23,1] : Fin 12 → Fin 24) p.1
    else (![0,8,9,10,11,2,4,6,7,5,3,19] : Fin 12 → Fin 24) p.1
  have hf : Function.Bijective f := by decide +kernel
  have hd : ∀ p : Fin 12 × Bool,
      distance (f p) = p.1.val + if p.2 then 4 else 0 := by decide +kernel
  let e : Fin 12 × Bool ≃ Fin 24 := Equiv.ofBijective f hf
  calc
    _ = ∑ p : Fin 12 × Bool, q ^ (p.1.val + if p.2 then 4 else 0) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      exact (congrArg (fun n : ℕ => q ^ n) (hd p)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, Bool.true_eq, Bool.false_eq_true,
        ite_true, ite_false, add_zero, pow_add]
      rw [Finset.sum_add_distrib]
      simp only [← Finset.sum_mul]
      ring

/-- The quotient factor is obtained from actual shortest representatives.
The remaining parabolic sum still refers to the original F4 subgroup. -/
theorem rootWeylPoincareEval_F4_parabolic (q : ℕ) :
    rootWeylPoincareEval pairing base q =
      ((∑ k : Fin 12, q ^ k.val) * (1 + q ^ 4)) *
        ∑ w : rootParabolicSubgroup pairing base J,
          q ^ rootWeylLength pairing base w.val := by
  have hr : (∑ x : rootParabolicRepresentatives pairing base J,
      q ^ rootWeylLength pairing base x.val) =
        (∑ k : Fin 12, q ^ k.val) * (1 + q ^ 4) := by
    calc
      _ = ∑ c : Fin 24, q ^ rootWeylLength pairing base (representativeEquiv c).val :=
        (Equiv.sum_comp representativeEquiv
          (fun x => q ^ rootWeylLength pairing base x.val)).symm
      _ = ∑ c : Fin 24, q ^ distance c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact congrArg (fun n : ℕ => q ^ n) (representativeEquiv_length c)
      _ = _ := distance_sum q
  rw [rootWeylPoincareEval_parabolic_factor pairing base J, hr]

end Atlas.Chevalley.F4ShortOrbit
