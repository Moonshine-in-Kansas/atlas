import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2CompanionNormalGeneration
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2CompanionPerfectness

/-! Normal generation from the actual two short simple-root subgroups.
The Perfectness module supplies only its all-ring same-root Weyl conjugation
identity here. No perfectness theorem or field hypothesis is used. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open Group
local instance c2NormalLoweringRankNeZero : NeZero C2.rank := ⟨by decide⟩

variable {R : Type*} [CommRing R]

theorem companion_Ylong_mem_normal_of_Xshort
    (H : Subgroup (Companion R)) [H.Normal]
    (hshort : ∀ u : R, selectedWeightCompanionX C2 R 0 u ∈ H) (t : R) :
    selectedWeightCompanionY C2 R 1 t ∈ H := by
  have h := (inferInstance : H.Normal).conj_mem _
    (companion_Xlong_mem_normal_of_Xshort H hshort (-t)) (weyl 1)
  simpa only [companion_weyl_long_conjugate_X, neg_neg] using h

/-- Both signs of the short simple-root subgroup normally generate the actual
selected companion, over every commutative ring. -/
theorem companion_normal_eq_top_of_short_roots
    (H : Subgroup (Companion R)) [H.Normal]
    (hx : ∀ t : R, selectedWeightCompanionX C2 R 0 t ∈ H)
    (hy : ∀ t : R, selectedWeightCompanionY C2 R 0 t ∈ H) : H = ⊤ := by
  apply top_unique
  intro g hg
  apply weightCompanion_induction (rootDatum C2).pairing (rootDatum C2).base
    (selectedWeightOrbits C2) (selectedWeightOrbits_closed C2)
    (selectedWeightOrbits_minuscule C2) R ?_ ?_ H.one_mem
    (fun _ _ => H.mul_mem) (fun _ => H.inv_mem) g
  · intro i t
    obtain ⟨k,rfl⟩ := (rootDatum C2).indexEquiv.surjective i
    fin_cases k
    · exact hx t
    · exact companion_Xlong_mem_normal_of_Xshort H hx t
  · intro i t
    obtain ⟨k,rfl⟩ := (rootDatum C2).indexEquiv.surjective i
    fin_cases k
    · exact hy t
    · exact companion_Ylong_mem_normal_of_Xshort H hx t

/-- The short-root premises remain explicit, including over the binary field. -/
theorem companion_isPerfect_of_short_roots_mem_commutator
    (hx : ∀ t : R, selectedWeightCompanionX C2 R 0 t ∈ commutator (Companion R))
    (hy : ∀ t : R, selectedWeightCompanionY C2 R 0 t ∈ commutator (Companion R)) :
    IsPerfect (Companion R) :=
  isPerfect_def.mpr (companion_normal_eq_top_of_short_roots (commutator _) hx hy)

variable {G : Type*} [Group G]

/-- The whole image of a certified local C2 homomorphism lies in a normal
subgroup containing the images of both short-root subgroups. -/
theorem companion_image_le_normal_of_short_roots
    (f : Companion R →* G) (H : Subgroup G) [H.Normal]
    (hx : ∀ t : R, f (selectedWeightCompanionX C2 R 0 t) ∈ H)
    (hy : ∀ t : R, f (selectedWeightCompanionY C2 R 0 t) ∈ H) :
    f.range ≤ H := by
  have htop : H.comap f = ⊤ := companion_normal_eq_top_of_short_roots (H.comap f) hx hy
  intro g hg
  obtain ⟨a,rfl⟩ := hg
  have ha : a ∈ H.comap f := by
    rw [htop]
    exact Subgroup.mem_top a
  exact ha

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule
