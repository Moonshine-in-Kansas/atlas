import Atlas.LinearGroups.F4.LeviSpecialImage
import Atlas.LinearGroups.F4.RootGeneratedElements
import Atlas.LinearGroups.F4.TorusGenerated

/-! The Levi quotient lifts can be chosen in the actual root-generated subgroup.
This strengthens image existence without asserting full generation of F₄. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def generatedParabolic : Subgroup (parabolicPointStabilizer (F:=F)) :=
  (rootGenerated (F:=F)).subgroupOf parabolicPointStabilizer

def generatedLeviImage : Subgroup (Atlas.Orthogonal.O_B 3 F) :=
  (generatedParabolic (F:=F)).map parabolicOrthogonalHom

theorem leviShortRoot_mem_generatedParabolic (k : Fin 6) (t : F) :
    leviShortRoot k t∈generatedParabolic := shortRoot_mem_rootGenerated _ _ _

theorem leviLongRoot_mem_generatedParabolic (k : Fin 12) (t : F) :
    leviLongRoot k t∈generatedParabolic := longRoot_mem_rootGenerated _ _

theorem leviDiagonal_mem_generatedLeviImage (d : Fin 3 → Fˣ) :
    leviDiagonal d∈generatedLeviImage := by
  refine ⟨leviTorus (leviTorusLift d),?_,leviTorusLift_quotient d⟩
  exact diagonalTorus_mem_rootGenerated _

private theorem singular_siegel_swap (u v x : Atlas.Orthogonal.VectorB 3 F) (c : F)
    (hu : Atlas.Orthogonal.formB 3 F u=0) (hv : Atlas.Orthogonal.formB 3 F v=0) :
    Atlas.Quadratic.siegel (Atlas.Orthogonal.formB 3 F) u (c • v) x=
      Atlas.Quadratic.siegel (Atlas.Orthogonal.formB 3 F) v ((-c) • u) x := by
  simp only [Atlas.Quadratic.siegel,(Atlas.Orthogonal.formB 3 F).map_smul,
    map_smul,hu,hv,smul_zero,zero_smul,mul_zero,sub_zero]
  module

private theorem levi_long_pair_cover : ∀ k l : Fin 6, k≠l → l.val≠5-k.val →
    ∃ m : Fin 12, (leviLongDirection m=k ∧ leviLongParameterDirection m=l) ∨
      (leviLongDirection m=l ∧ leviLongParameterDirection m=k) := by
  decide +kernel

private theorem levi_long_sign_sq (m : Fin 12) : (leviLongParameterSign m:F)^2=1 := by
  fin_cases m <;> norm_num [leviLongParameterSign]

set_option maxHeartbeats 2000000 in
-- Six coordinate directions and their opposites are checked before lifting the root.
private theorem generated_pair_siegel_mem (k l : Fin 6) (c : F)
    (h : (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection k)
      (c • leviSingularDirection l)=0) :
    Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
      (leviSingularDirection k) (c • leviSingularDirection l)
      (leviSingularDirection_singular k) h∈generatedLeviImage := by
  by_cases he : k=l
  · subst l
    have hg : Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) (c • leviSingularDirection k)
        (leviSingularDirection_singular k) h=1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change Atlas.Quadratic.siegel _ _ _ x=x
      simpa using Atlas.Quadratic.siegel_parameter_mod_line (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) 0 x c (leviSingularDirection_singular k) (by simp)
    rw [hg]
    exact Subgroup.one_mem _
  by_cases ho : l.val=5-k.val
  · have hc : c=0 := by
      fin_cases k <;> fin_cases l <;>
        simp_all [leviSingularDirection,leviShortDirection,QuadraticMap.polar,
          Atlas.Orthogonal.formD_apply,Fin.sum_univ_succ,Pi.single_apply]
    subst c
    have hg : Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) ((0:F) • leviSingularDirection l)
        (leviSingularDirection_singular k) h=1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change Atlas.Quadratic.siegel _ _ _ x=x
      simp
    rw [hg]
    exact Subgroup.one_mem _
  obtain ⟨m,hm⟩ := levi_long_pair_cover k l he ho
  rcases hm with ⟨hk,hl⟩ | ⟨hl,hk⟩
  · refine ⟨leviLongRoot m ((leviLongParameterSign m:F)*c),
      leviLongRoot_mem_generatedParabolic _ _,?_⟩
    rw [leviLongRoot_quotient]
    have hp : leviLongParameter m ((leviLongParameterSign m:F)*c)=c • leviSingularDirection l := by
      unfold leviLongParameter
      rw [hl,←mul_assoc,←pow_two,levi_long_sign_sq,one_mul]
    simp only [hp,hk]
  · refine ⟨leviLongRoot m ((leviLongParameterSign m:F)*(-c)),
      leviLongRoot_mem_generatedParabolic _ _,?_⟩
    rw [leviLongRoot_quotient]
    have hp : leviLongParameter m ((leviLongParameterSign m:F)*(-c))=(-c) • leviSingularDirection k := by
      unfold leviLongParameter
      rw [hk,←mul_assoc,←pow_two,levi_long_sign_sq,one_mul]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change Atlas.Quadratic.siegel _ _ _ x=Atlas.Quadratic.siegel _ _ _ x
    rw [hp,hl]
    exact (singular_siegel_swap _ _ x c (leviSingularDirection_singular k)
      (leviSingularDirection_singular l)).symm

private theorem generated_direction_surjective : Function.Surjective leviShortDirection := by
  unfold Function.Surjective
  decide +kernel

private theorem generated_coordinate_basis (k : Fin 6) :
    Atlas.Orthogonal.coordinateBasisB 3 (Sum.inl (leviShortDirection k))=
      (leviSingularDirection k : Atlas.Orthogonal.VectorB 3 F) := by
  simp [Atlas.Orthogonal.coordinateBasisB,Atlas.Orthogonal.coordinateBasisD,leviSingularDirection]

theorem elementaryB3_le_generatedLeviImage :
    Atlas.Orthogonal.elementarySubgroup (Atlas.Orthogonal.formB 3 F) ≤ generatedLeviImage := by
  rw [←Atlas.Orthogonal.coordinateRootSubgroupB_eq_elementary_of_pos 3 (by decide)]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,j,c,hu,huv,rfl⟩
  cases i with
  | inr i =>
      cases i
      exfalso
      simpa [Atlas.Orthogonal.coordinateBasisB] using hu
  | inl i =>
      obtain ⟨k,rfl⟩ := generated_direction_surjective i
      simp only [generated_coordinate_basis] at hu huv ⊢
      cases j with
      | inl j =>
          obtain ⟨l,rfl⟩ := generated_direction_surjective j
          simp only [generated_coordinate_basis] at huv ⊢
          exact generated_pair_siegel_mem k l c huv
      | inr j =>
          cases j
          have hv : c • Atlas.Orthogonal.coordinateBasisB 3 (Sum.inr ())=
              leviAnisotropicParameter c := by
            simp [Atlas.Orthogonal.coordinateBasisB,leviAnisotropicParameter]
          simp only [hv] at huv ⊢
          exact ⟨leviShortRoot k c,leviShortRoot_mem_generatedParabolic _ _,leviShortRoot_quotient k c⟩


/-- All seven-dimensional special isometries have lifts in the intersection
of the actual parabolic with the actual root-generated subgroup. -/
theorem specialB3_le_generatedLeviImage [Finite F] :
    Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) ≤ generatedLeviImage := by
  by_cases h2 : (2:F)=0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    intro g _
    apply elementaryB3_le_generatedLeviImage
    rw [Atlas.Orthogonal.even_elementary_eq_top]
    trivial
  intro g hg
  let σ := Atlas.Orthogonal.spinorNorm (Atlas.Orthogonal.formB 3 F)
    (Atlas.Orthogonal.polarB_nondegenerate h2) h2
  obtain ⟨a,ha⟩ := Atlas.squareClass_surjective F (σ g)
  have ht : leviHyperbolicTorus a∈generatedLeviImage := by
    rw [leviHyperbolicTorus_eq]
    exact leviDiagonal_mem_generatedLeviImage _
  have he : g*(leviHyperbolicTorus a)⁻¹∈
      Atlas.Orthogonal.elementarySubgroup (Atlas.Orthogonal.formB 3 F) := by
    rw [Atlas.Orthogonal.elementaryB_eq_intrinsicKernel 1 h2]
    refine ⟨(Atlas.Orthogonal.specialSubgroup _).mul_mem hg
      ((Atlas.Orthogonal.specialSubgroup _).inv_mem (leviHyperbolicTorus_special a)),?_⟩
    change σ (g*(leviHyperbolicTorus a)⁻¹)=1
    rw [map_mul,map_inv]
    change σ g*(Atlas.Orthogonal.spinorNorm _ _ h2 (leviHyperbolicTorus a))⁻¹=1
    rw [leviHyperbolicTorus_spinor,ha,mul_inv_cancel]
  have hh := (generatedLeviImage (F:=F)).mul_mem (elementaryB3_le_generatedLeviImage he) ht
  simpa using hh

end Atlas.F4
