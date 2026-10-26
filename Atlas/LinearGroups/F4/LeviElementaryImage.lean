import Atlas.LinearGroups.F4.LeviLongRootImages
import Atlas.LinearGroups.Orthogonal.CoordinateRootGenerationB1

/-! The actual parabolic quotient image contains the complete elementary B₃ group. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]
private def leviPairIndex : Fin 6 → Fin 6 → Fin 12 := ![![0,0,4,5,1,0],![0,0,8,9,0,2],![4,8,0,0,10,6],![5,9,0,0,11,7],![1,0,10,11,0,3],![0,2,6,7,3,0]]
private def leviPairSign : Fin 6 → Fin 6 → ℤ := ![![1,1,-1,1,-1,1],![-1,1,1,-1,1,1],![1,-1,1,1,1,-1],![-1,1,1,1,-1,1],![1,1,-1,1,1,-1],![1,-1,1,-1,1,1]]

private theorem levi_siegel_self (k : Fin 6) (c : F)
    (h : (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection k)
      (c • leviSingularDirection k)=0) :
    Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
      (leviSingularDirection k) (c • leviSingularDirection k)
      (leviSingularDirection_singular k) h=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Atlas.Quadratic.siegel _ _ _ x=x
  simpa using Atlas.Quadratic.siegel_parameter_mod_line (Atlas.Orthogonal.formB 3 F)
    (leviSingularDirection k) 0 x c (leviSingularDirection_singular k) (by simp)

set_option maxHeartbeats 2000000 in
private theorem levi_pair_opposite_parameter (k l : Fin 6) (c : F)
    (ho : l.val=5-k.val)
    (h : (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection k)
      (c • leviSingularDirection l)=0) : c=0 := by
  fin_cases k <;> fin_cases l <;>
    simp_all [leviSingularDirection,leviShortDirection,QuadraticMap.polar,
      Atlas.Orthogonal.formD_apply,Fin.sum_univ_succ,Pi.single_apply]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem levi_pair_siegel_eq (k l : Fin 6) (c : F) (hne : k≠l)
    (hop : l.val≠5-k.val)
    (h : (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection k)
      (c • leviSingularDirection l)=0) :
    parabolicOrthogonalHom (leviLongRoot (leviPairIndex k l) ((leviPairSign k l : F)*c))=
      Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) (c • leviSingularDirection l)
        (leviSingularDirection_singular k) h := by
  rw [leviLongRoot_quotient]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Atlas.Quadratic.siegel _ _ _ x=Atlas.Quadratic.siegel _ _ _ x
  fin_cases k <;> fin_cases l
  all_goals try exact (hne rfl).elim
  all_goals try exact (hop rfl).elim
  all_goals
    apply Prod.ext
    · ext i; cases i with
      | inl i => fin_cases i <;>
          simp [Atlas.Quadratic.siegel,QuadraticMap.polar,Atlas.Orthogonal.formD_apply,
            leviPairIndex,leviPairSign,leviLongDirection,leviLongParameterDirection,
            leviLongParameterSign,leviLongParameter,leviSingularDirection,leviShortDirection,
            Pi.single_apply,Fin.sum_univ_succ] <;> ring
      | inr i => fin_cases i <;>
          simp [Atlas.Quadratic.siegel,QuadraticMap.polar,Atlas.Orthogonal.formD_apply,
            leviPairIndex,leviPairSign,leviLongDirection,leviLongParameterDirection,
            leviLongParameterSign,leviLongParameter,leviSingularDirection,leviShortDirection,
            Pi.single_apply,Fin.sum_univ_succ] <;> ring
    · simp [Atlas.Quadratic.siegel,QuadraticMap.polar,Atlas.Orthogonal.formD_apply,
        leviPairIndex,leviPairSign,leviLongDirection,leviLongParameterDirection,
        leviLongParameterSign,leviLongParameter,leviSingularDirection,leviShortDirection,
        Pi.single_apply,Fin.sum_univ_succ] <;> ring

private theorem levi_pair_siegel_mem (k l : Fin 6) (c : F)
    (h : (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection k)
      (c • leviSingularDirection l)=0) :
    Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
      (leviSingularDirection k) (c • leviSingularDirection l)
      (leviSingularDirection_singular k) h∈parabolicOrthogonalHom.range := by
  by_cases he : k=l
  · subst l
    rw [levi_siegel_self]
    exact Subgroup.one_mem _
  by_cases ho : l.val=5-k.val
  · have hc := levi_pair_opposite_parameter k l c ho h
    subst c
    have hg : Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) ((0 : F) • leviSingularDirection l)
        (leviSingularDirection_singular k) h=1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change Atlas.Quadratic.siegel _ _ _ x=x
      simp
    rw [hg]
    exact Subgroup.one_mem _
  exact ⟨leviLongRoot (leviPairIndex k l) ((leviPairSign k l : F)*c),
    levi_pair_siegel_eq k l c he ho h⟩

private theorem leviShortDirection_surjective : Function.Surjective leviShortDirection := by
  unfold Function.Surjective
  decide +kernel

private theorem levi_coordinate_basis (k : Fin 6) :
    Atlas.Orthogonal.coordinateBasisB 3 (Sum.inl (leviShortDirection k))=
      (leviSingularDirection k : Atlas.Orthogonal.VectorB 3 F) := by
  simp [Atlas.Orthogonal.coordinateBasisB,Atlas.Orthogonal.coordinateBasisD,
    leviSingularDirection]

/-- The old coordinate-root generation theorem is reused; no new orthogonal
transitivity or abstract B₃ recognition is required. -/
theorem elementaryB3_le_parabolic_image :
    Atlas.Orthogonal.elementarySubgroup (Atlas.Orthogonal.formB 3 F) ≤
      parabolicOrthogonalHom.range := by
  rw [←Atlas.Orthogonal.coordinateRootSubgroupB_eq_elementary_of_pos 3 (by decide)]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,j,c,hu,huv,rfl⟩
  cases i with
  | inr i =>
      cases i
      exfalso
      simpa [Atlas.Orthogonal.coordinateBasisB] using hu
  | inl i =>
      obtain ⟨k,rfl⟩ := leviShortDirection_surjective i
      simp only [levi_coordinate_basis] at hu huv ⊢
      cases j with
      | inl j =>
          obtain ⟨l,rfl⟩ := leviShortDirection_surjective j
          simp only [levi_coordinate_basis] at huv ⊢
          exact levi_pair_siegel_mem k l c huv
      | inr j =>
          cases j
          have hv : c • Atlas.Orthogonal.coordinateBasisB 3 (Sum.inr ())=
              leviAnisotropicParameter c := by
            simp [Atlas.Orthogonal.coordinateBasisB,leviAnisotropicParameter]
          simp only [hv] at huv ⊢
          exact ⟨leviShortRoot k c,leviShortRoot_quotient k c⟩

end Atlas.F4
