import Atlas.LinearGroups.Triality.ParabolicCoreReduction

/-! A subgroup normal under all root generators cannot remain in the torus. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem torusScale_fixed_all (h : Kˣ × Fˣ)
    (he : ∀ p : PositiveParameters F K, torusScale F K h p=p) : h=1 := by
  let p : PositiveParameters F K := ⟨1,1,1,1,1,1⟩
  have hs := he p
  have hb : h.2=1 := by
    apply Units.ext
    simpa [torusScale,p] using congrArg PositiveParameters.v hs
  have ha : (h.1 : K)^2=1 := by
    simpa [torusScale,p,hb,baseUnit] using congrArg PositiveParameters.a hs
  have hc := congrArg PositiveParameters.c hs
  rcases (sq_eq_one_iff).mp ha with ha|ha
  · exact Prod.ext (Units.ext ha) hb
  · have hh : h.1 = -1 := Units.ext ha
    have hm : (-1 : K)=1 := by
      simpa [torusScale,p,hb,hh,sigmaUnit,baseUnit] using hc
    exact Prod.ext (Units.ext (ha.trans hm)) hb

include hdeg in
theorem normal_in_torus_eq_bot (N : Subgroup (O_DPlus 4 K))
    (hNT : N ≤ torus F K)
    (hconj : ∀ a ∈ generated F K, ∀ g ∈ N, a*g*a⁻¹ ∈ N) : N=⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨h,he⟩ := hNT hg
  have hs : ∀ p : PositiveParameters F K, torusScale F K h p=p := by
    intro p
    have hp : positiveMatrix F K p ∈ generated F K := positiveWord_mem F K _ _ _ _ _ _
    have hc := hNT (hconj ((positiveMatrix F K p)⁻¹) ((generated F K).inv_mem hp) g hg)
    obtain ⟨k,hk⟩ := hc
    have hh : borelWord F K (torusScale F K h p) h = borelWord F K p k := by
      change positiveMatrix F K (torusScale F K h p)*torusMap F K h =
        positiveMatrix F K p*torusMap F K k
      rw [← torus_positive_intertwine F K hdeg h p,he,hk]
      group
    have hinj : (torusScale F K h p,h)=(p,k) := by
      apply borelWord_injective F K
      exact hh
    exact congrArg Prod.fst hinj
  have hh := torusScale_fixed_all F K h hs
  change g=1
  rw [← he,hh,map_one]

theorem normal_in_longParabolic_eq_bot (N : Subgroup (O_DPlus 4 K))
    (hNP : N ≤ longParabolic F K hdeg)
    (hconj : ∀ a ∈ generated F K, ∀ g ∈ N, a*g*a⁻¹ ∈ N) : N=⊥ :=
  normal_in_torus_eq_bot F K hdeg N
    (normal_in_longParabolic_le_torus F K hdeg N hNP hconj) hconj

end Atlas.Triality
