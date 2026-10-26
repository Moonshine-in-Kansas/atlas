import Atlas.Tits.MonomialSmallQuotient
import Atlas.Tits.FusionGeneration

/-! Reduction of the actual normal-subgroup index bound to two explicit odd
word identities. The identities are visible hypotheses, to be discharged by
separate certificates before exporting an unconditional group theorem. -/

namespace Atlas.Tits
open Atlas.Rudvalis

noncomputable def pointU : codeReferenceStabilizer :=
  ⟨codeU,localCodeU_fixes_reference⟩
noncomputable def pointE3 : codeReferenceStabilizer :=
  ⟨seedARowSign (binaryLabel 3),seedARowSign_mem_point _⟩

theorem pointE3_mem_normalPreimage : pointE3 ∈ pointNormalPreimage := by
  apply (pointNormalPreimage_iff_image _).mpr
  apply signKernel_le_codeNormalImage
  rfl

/-- The two odd relations kill g and R in every nontrivial normal quotient. -/
theorem normal_contains_g_and_R_of_odd_relations
    (hgu : (localG * codePointHom pointU)^3 = 1)
    (hreg : (codePointHom pointR * codePointHom pointE3 *
      codePointHom pointU * localG)^3 = 1)
    (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥) :
    localG ∈ N ∧ codePointHom pointR ∈ N := by
  have hclosure := monomialNormalClosure_le_normal N hN
  have hu : codePointHom pointU ∈ N := hclosure monomialU_mem_normalClosure
  have he : codePointHom pointE3 ∈ N := hclosure pointE3_mem_normalPreimage
  have hguN := cube_eq_one_mem_normal N hN _ hgu
  have hg : localG ∈ N := (N.mul_mem_cancel_right hu).mp hguN
  have hregN := cube_eq_one_mem_normal N hN _ hreg
  have hre := (N.mul_mem_cancel_right hu).mp ((N.mul_mem_cancel_right hg).mp hregN)
  exact ⟨hg,(N.mul_mem_cancel_right he).mp hre⟩

/-- Conditional reduction only: once the two actual odd identities are checked,
every nontrivial normal subgroup of the actual cross stabilizer has index at
most two. No Tits order, transfer character or simplicity theorem is assumed. -/
theorem normal_index_le_two_of_odd_relations
    (hgu : (localG * codePointHom pointU)^3 = 1)
    (hreg : (codePointHom pointR * codePointHom pointE3 *
      codePointHom pointU * localG)^3 = 1)
    (N : Subgroup Ambient) [N.Normal] (hN : N ≠ ⊥) : N.index ≤ 2 := by
  let f := QuotientGroup.mk' N
  let q : Ambient := codePointHom pointQ
  obtain ⟨hg,hr⟩ := normal_contains_g_and_R_of_odd_relations hgu hreg N hN
  have hfg : f localG = 1 := (QuotientGroup.eq_one_iff _).mpr hg
  have hfr : f (codePointHom pointR) = 1 := (QuotientGroup.eq_one_iff _).mpr hr
  let kf : monomialPointGroup →* (Ambient ⧸ N) := f.comp monomialPointGroup.subtype
  have hkill : monomialNormalClosure ≤ kf.ker := by
    intro k hk
    exact (QuotientGroup.eq_one_iff _).mpr ((monomialNormalClosure_le_normal N hN) hk)
  let φ : MonomialSmallQuotient →* (Ambient ⧸ N) :=
    QuotientGroup.lift monomialNormalClosure kf hkill
  have hφq : φ monomialSmallQ = f q := rfl
  have hφr : φ monomialSmallR = 1 := hfr
  have hk (k : monomialPointGroup) : f k.val ∈ Subgroup.zpowers (f q) := by
    have hc := monomialSmallQuotient_four_representatives
      (QuotientGroup.mk' monomialNormalClosure k)
    rcases hc with h | h | h | h
    · have hh := congrArg φ h
      change f k.val = φ 1 at hh
      rw [map_one] at hh
      rw [hh]
      exact Subgroup.one_mem _
    · have hh := congrArg φ h
      change f k.val = φ monomialSmallQ at hh
      rw [hφq] at hh
      rw [hh]
      exact Subgroup.mem_zpowers _
    · have hh := congrArg φ h
      change f k.val = φ monomialSmallR at hh
      rw [hφr] at hh
      rw [hh]
      exact Subgroup.one_mem _
    · have hh := congrArg φ h
      change f k.val = φ (monomialSmallQ*monomialSmallR) at hh
      rw [map_mul,hφq,hφr,mul_one] at hh
      rw [hh]
      exact Subgroup.mem_zpowers _
  have hpre : (⊤ : Subgroup Ambient) ≤ (Subgroup.zpowers (f q)).comap f := by
    rw [← ambient_generated_by_monomial_g]
    apply sup_le
    · intro k hk'
      exact hk ⟨k,hk'⟩
    · apply Subgroup.zpowers_le.mpr
      change f localG ∈ Subgroup.zpowers (f q)
      rw [hfg]
      exact Subgroup.one_mem _
  have htop : Subgroup.zpowers (f q) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    exact hpre (Subgroup.mem_top x)
  have hq2 : (f q)^2 = 1 := by
    rw [← hφq,← map_pow,monomialSmallQ_square,map_one]
  have ho : orderOf (f q) ≤ 2 :=
    Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hq2)
  have hc : Nat.card (Ambient ⧸ N) = orderOf (f q) := by
    rw [← Nat.card_zpowers,htop,Subgroup.card_top]
  rw [N.index_eq_card,hc]
  exact ho

end Atlas.Tits
