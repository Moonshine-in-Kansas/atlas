import Atlas.LinearGroups.Chevalley.RootData.E8RootOrbit
import Atlas.LinearGroups.Chevalley.RootData.E8RootParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! The 240 actual minimal right-parabolic representatives in E8, obtained
from root paths and the actual dominant-root stabilizer. The length histogram
is checked on those labels; the Weyl group is never enumerated. -/
noncomputable section
namespace Atlas.Chevalley.E8RootOrbit
open Classical RootData E8Data
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
local notation "J" => E8Parabolic.J

private theorem fixes_seed_iff_parabolic (w : W) :
    w.val seed = seed ↔ w ∈ rootParabolicSubgroup pairing base J :=
  E8Parabolic.fixes_seed_iff_parabolic w

local instance : Fintype (rootParabolicRepresentatives pairing base J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup pairing base J) := Fintype.ofFinite _

private def path (c : Fin 240) : List base.support :=
  (exists_shortest_seed_word c).choose

private theorem path_spec (c : Fin 240) :
    IsReducedRootWord pairing base (path c) ∧ (path c).length = distance c ∧
      (rootWeylWord pairing base (path c)).val seed = label c :=
  (exists_shortest_seed_word c).choose_spec

def representative (c : Fin 240) : W := rootWeylWord pairing base (path c)

theorem representative_seed (c : Fin 240) : (representative c).val seed = label c :=
  (path_spec c).2.2

theorem representative_length (c : Fin 240) :
    rootWeylLength pairing base (representative c) = distance c :=
  (path_spec c).1.trans (path_spec c).2.1

theorem representative_minimal (c : Fin 240) :
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

def representativeMap : Fin 240 → rootParabolicRepresentatives pairing base J :=
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

def representativeEquiv : Fin 240 ≃ rootParabolicRepresentatives pairing base J :=
  Equiv.ofBijective representativeMap representativeMap_bijective

theorem representativeEquiv_length (c : Fin 240) :
    rootWeylLength pairing base (representativeEquiv c).val = distance c :=
  representative_length c

private def histogramLabel : Fin 30 × (Fin 4 × Bool) → Fin 240 := fun p =>
  if p.2.2 then
    (![![208,202,195,187,179,171,159,145,130,111,122,103,81,62,44,60,43,63,42,53,33,50,34,52,71,59,78,100,119,137],
    ![160,146,154,140,123,104,82,65,80,64,85,105,84,95,73,54,70,55,72,92,79,101,120,138,151,165,173,181,189,197],
    ![83,102,86,106,125,141,124,133,115,96,74,91,75,93,113,131,121,139,152,166,174,182,190,198,204,210,214,218,222,226],
    ![155,162,148,134,116,97,112,94,114,132,147,161,153,167,175,183,191,199,205,211,215,219,223,227,229,231,233,235,237,239]] : Fin 4 → Fin 30 → Fin 240) p.2.1 p.1
  else
    (![![238,236,234,232,230,228,224,220,216,212,206,200,192,184,176,168,156,142,126,107,87,66,45,28,17,9,5,2,0,1],
    ![225,221,217,213,207,201,193,185,177,169,157,143,127,108,88,67,46,29,18,10,14,8,4,6,3,7,12,22,35,56],
    ![194,186,178,170,158,144,128,109,89,68,47,30,40,25,16,24,15,20,11,19,13,23,36,57,76,98,117,135,149,163],
    ![129,110,90,69,48,61,41,27,39,26,38,49,31,21,32,51,37,58,77,99,118,136,150,164,172,180,188,196,203,209]] : Fin 4 → Fin 30 → Fin 240) p.2.1 p.1

/-- Explicit inverse labels, used only to prove injectivity in linear work. -/
private def histogramInverse (c : Fin 240) : Fin 30 × (Fin 4 × Bool) :=
  let n := (#[224,232,216,194,178,208,186,202,170,200,154,148,210,164,162,132,116,192,146,156,140,110,218,172,124,108,78,62,184,138,92,102,118,161,177,226,180,134,86,70,100,54,145,129,113,176,130,84,38,94,169,126,185,153,123,139,234,188,142,201,121,46,105,137,75,59,168,122,76,30,131,193,147,115,85,101,196,150,209,163,67,97,51,5,99,83,21,160,114,68,22,93,155,109,63,107,77,47,204,158,217,171,13,89,43,91,29,152,106,60,14,73,55,117,71,69,39,212,166,225,179,133,81,35,53,37,144,98,52,6,65,125,79,61,31,220,174,233,187,141,27,45,136,90,44,57,11,87,23,228,182,195,149,103,19,7,128,82,36,49,3,95,15,236,190,203,157,111,120,74,28,41,198,211,165,119,112,66,20,33,206,219,173,127,104,58,12,25,214,227,181,135,96,50,4,17,222,235,189,143,88,42,9,230,197,151,80,34,1,238,205,159,72,26,213,167,64,18,221,175,56,10,229,183,48,2,237,191,40,199,32,207,24,215,16,223,8,231,0,239] : Array ℕ)[c.val]!
  (Fin.ofNat 30 (n / 8), Fin.ofNat 4 (n / 2), n % 2 == 1)

private theorem histogramInverse_0_false : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (0, false))) = (k, (0, false)) := by
  decide +kernel

private theorem histogramInverse_0_true : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (0, true))) = (k, (0, true)) := by
  decide +kernel

private theorem histogramInverse_1_false : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (1, false))) = (k, (1, false)) := by
  decide +kernel

private theorem histogramInverse_1_true : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (1, true))) = (k, (1, true)) := by
  decide +kernel

private theorem histogramInverse_2_false : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (2, false))) = (k, (2, false)) := by
  decide +kernel

private theorem histogramInverse_2_true : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (2, true))) = (k, (2, true)) := by
  decide +kernel

private theorem histogramInverse_3_false : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (3, false))) = (k, (3, false)) := by
  decide +kernel

private theorem histogramInverse_3_true : ∀ k : Fin 30,
    histogramInverse (histogramLabel (k, (3, true))) = (k, (3, true)) := by
  decide +kernel

private theorem histogramInverse_left : Function.LeftInverse histogramInverse histogramLabel := by
  rintro ⟨k, i, b⟩
  fin_cases i <;> cases b
  · exact histogramInverse_0_false k
  · exact histogramInverse_0_true k
  · exact histogramInverse_1_false k
  · exact histogramInverse_1_true k
  · exact histogramInverse_2_false k
  · exact histogramInverse_2_true k
  · exact histogramInverse_3_false k
  · exact histogramInverse_3_true k

private theorem histogramLabel_bijective : Function.Bijective histogramLabel := by
  apply (Fintype.bijective_iff_injective_and_card histogramLabel).mpr
  exact ⟨histogramInverse_left.injective, by decide⟩

private theorem histogramDistance_0_false : ∀ k : Fin 30,
    distance (histogramLabel (k, (0, false))) =
      k.val + 6 * (0 : Fin 4).val + if false then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_0_true : ∀ k : Fin 30,
    distance (histogramLabel (k, (0, true))) =
      k.val + 6 * (0 : Fin 4).val + if true then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_1_false : ∀ k : Fin 30,
    distance (histogramLabel (k, (1, false))) =
      k.val + 6 * (1 : Fin 4).val + if false then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_1_true : ∀ k : Fin 30,
    distance (histogramLabel (k, (1, true))) =
      k.val + 6 * (1 : Fin 4).val + if true then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_2_false : ∀ k : Fin 30,
    distance (histogramLabel (k, (2, false))) =
      k.val + 6 * (2 : Fin 4).val + if false then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_2_true : ∀ k : Fin 30,
    distance (histogramLabel (k, (2, true))) =
      k.val + 6 * (2 : Fin 4).val + if true then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_3_false : ∀ k : Fin 30,
    distance (histogramLabel (k, (3, false))) =
      k.val + 6 * (3 : Fin 4).val + if false then 10 else 0 := by
  decide +kernel

private theorem histogramDistance_3_true : ∀ k : Fin 30,
    distance (histogramLabel (k, (3, true))) =
      k.val + 6 * (3 : Fin 4).val + if true then 10 else 0 := by
  decide +kernel

private theorem histogramLabel_distance (p : Fin 30 × (Fin 4 × Bool)) :
    distance (histogramLabel p) = p.1.val + 6 * p.2.1.val + if p.2.2 then 10 else 0 := by
  rcases p with ⟨k, i, b⟩
  fin_cases i <;> cases b
  · exact histogramDistance_0_false k
  · exact histogramDistance_0_true k
  · exact histogramDistance_1_false k
  · exact histogramDistance_1_true k
  · exact histogramDistance_2_false k
  · exact histogramDistance_2_true k
  · exact histogramDistance_3_false k
  · exact histogramDistance_3_true k

/-- Eight explicit intervals from the actual distance table. Repeated
lengths retain their distinct root labels. -/
theorem distance_sum (q : ℕ) :
    (∑ c : Fin 240, q ^ distance c) =
      (∑ k : Fin 30, q ^ k.val) *
        (1 + q ^ 6 + q ^ 12 + q ^ 18) * (1 + q ^ 10) := by
  let f := histogramLabel
  have hf : Function.Bijective f := histogramLabel_bijective
  have hd : ∀ p : Fin 30 × (Fin 4 × Bool),
      distance (f p) = p.1.val + 6 * p.2.1.val + if p.2.2 then 10 else 0 :=
    histogramLabel_distance
  let e : Fin 30 × (Fin 4 × Bool) ≃ Fin 240 := Equiv.ofBijective f hf
  calc
    _ = ∑ p : Fin 30 × (Fin 4 × Bool),
          q ^ (p.1.val + 6 * p.2.1.val + if p.2.2 then 10 else 0) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      exact (congrArg (fun n : ℕ => q ^ n) (hd p)).symm
    _ = ∑ k : Fin 30,
        (q ^ k.val * (1 + q ^ 6 + q ^ 12 + q ^ 18) * (1 + q ^ 10)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_four, Fintype.sum_bool,
        Bool.false_eq_true, ite_true, ite_false]
      change
        ((q ^ (k.val + 0 + 10) + q ^ (k.val + 0 + 0)) +
        (q ^ (k.val + 6 + 10) + q ^ (k.val + 6 + 0)) +
        (q ^ (k.val + 12 + 10) + q ^ (k.val + 12 + 0)) +
        (q ^ (k.val + 18 + 10) + q ^ (k.val + 18 + 0))) = _
      simp only [pow_add, Nat.add_zero, pow_zero, mul_one, mul_add, add_mul]
      ac_rfl
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]

theorem rootWeylPoincareEval_E8_parabolic (q : ℕ) :
    rootWeylPoincareEval pairing base q =
      ((∑ k : Fin 30, q ^ k.val) *
        (1 + q ^ 6 + q ^ 12 + q ^ 18) * (1 + q ^ 10)) *
        ∑ w : rootParabolicSubgroup pairing base J,
          q ^ rootWeylLength pairing base w.val := by
  have hr : (∑ x : rootParabolicRepresentatives pairing base J,
      q ^ rootWeylLength pairing base x.val) =
        (∑ k : Fin 30, q ^ k.val) *
          (1 + q ^ 6 + q ^ 12 + q ^ 18) * (1 + q ^ 10) := by
    calc
      _ = ∑ c : Fin 240, q ^ rootWeylLength pairing base (representativeEquiv c).val :=
        (Equiv.sum_comp representativeEquiv
          (fun x => q ^ rootWeylLength pairing base x.val)).symm
      _ = ∑ c : Fin 240, q ^ distance c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact congrArg (fun n : ℕ => q ^ n) (representativeEquiv_length c)
      _ = _ := distance_sum q
  rw [rootWeylPoincareEval_parabolic_factor pairing base J, hr]

end Atlas.Chevalley.E8RootOrbit
