import Atlas.Lattices.EisensteinClassSaturation

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eisensteinNorm_neg (x : EisensteinLattice) : eisensteinNorm (-x) = eisensteinNorm x := by
  simp only [eisensteinNorm, Submodule.coe_neg, map_neg,
    eisensteinBilinear_neg_left, eisensteinBilinear_neg_right, neg_neg]

theorem eisensteinShellClasses_neg {r : ℤ} {c : EisensteinClasses}
    (hc : c ∈ eisensteinShellClasses r) : -c ∈ eisensteinShellClasses r := by
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
  refine Finset.mem_image.mpr ⟨⟨-x.val, (eisensteinNorm_neg x.val).trans x.property⟩,
    Finset.mem_univ _, ?_⟩
  change eisensteinClass (-x.val) = -c
  rw [map_neg, hx]

theorem eisensteinClasses_three (c : EisensteinClasses) : (3 : ℕ) • c = 0 := by
  obtain ⟨x, rfl⟩ := eisensteinThetaEnd.range.mkQ_surjective c
  rw [← map_nsmul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨-eisensteinThetaEnd x, ?_⟩
  have h := LinearMap.congr_fun eisensteinThetaEnd_square x
  change eisensteinThetaEnd (eisensteinThetaEnd x) = (-3 : ℤ) • x at h
  rw [map_neg, h]
  simp only [neg_smul, neg_neg]
  exact natCast_zsmul x 3

theorem eisensteinClasses_neg_ne {c : EisensteinClasses} (hc : c≠0) : -c≠c := by
  intro h
  have hs := neg_add_cancel c
  rw [h] at hs
  have ht := eisensteinClasses_three c
  have he : (3 : ℕ) • c = c+c+c := by simp [succ_nsmul] <;> abel
  rw [he, hs, zero_add] at ht
  exact hc ht

def eisensteinFramePair (c : EisensteinClasses) : Finset EisensteinClasses := {c,-c}

theorem eisensteinFramePair_neg (c : EisensteinClasses) :
    eisensteinFramePair (-c) = eisensteinFramePair c := by
  simp [eisensteinFramePair, Finset.pair_comm]

theorem eisensteinFramePair_eq_iff (c d : EisensteinClasses) :
    eisensteinFramePair c = eisensteinFramePair d ↔ c=d ∨ c= -d := by
  constructor
  · intro h
    have hc : c ∈ eisensteinFramePair d := h ▸ (by simp [eisensteinFramePair])
    simpa [eisensteinFramePair] using hc
  · rintro (rfl | rfl)
    · rfl
    · exact eisensteinFramePair_neg d

/-- Intrinsic complex frames are pairs of opposite norm-six theta-classes. -/
def eisensteinFrames : Finset (Finset EisensteinClasses) :=
  (eisensteinShellClasses 6).image eisensteinFramePair

abbrev EisensteinFrame := ↥eisensteinFrames

theorem eisensteinFrames_fiber (c : EisensteinClasses)
    (hc : c ∈ eisensteinShellClasses 6) :
    ((eisensteinShellClasses 6).filter (fun d => eisensteinFramePair d = eisensteinFramePair c)).card = 2 := by
  have he : (eisensteinShellClasses 6).filter
      (fun d => eisensteinFramePair d = eisensteinFramePair c) = {c,-c} := by
    ext d
    simp only [Finset.mem_filter, eisensteinFramePair_eq_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨hc, Or.inl rfl⟩
      · exact ⟨eisensteinShellClasses_neg hc, Or.inr rfl⟩
  rw [he, Finset.card_pair]
  exact Ne.symm (eisensteinClasses_neg_ne
    (fun h => eisensteinShellClasses_zero_not_mem 6 (by decide) (h ▸ hc)))

theorem eisensteinFrames_card : eisensteinFrames.card = 232960 := by
  have h := Finset.card_eq_sum_card_image (s := eisensteinShellClasses 6) (f := eisensteinFramePair)
  have hs : (∑ d ∈ (eisensteinShellClasses 6).image eisensteinFramePair,
      ((eisensteinShellClasses 6).filter (fun c => eisensteinFramePair c = d)).card) =
      ∑ _d ∈ (eisensteinShellClasses 6).image eisensteinFramePair, 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact eisensteinFrames_fiber c hc
  rw [hs, eisensteinShellClasses_counts.2] at h
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  change 465920 = eisensteinFrames.card * 2 at h
  omega

theorem eisensteinFrame_card : Nat.card EisensteinFrame = 232960 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, eisensteinFrames_card]

def eisensteinFrameOfVector (x : EisensteinShell 6) : EisensteinFrame :=
  ⟨eisensteinFramePair (eisensteinClass x.val), Finset.mem_image.mpr
    ⟨eisensteinClass x.val, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, rfl⟩⟩

end Atlas.Lattices
