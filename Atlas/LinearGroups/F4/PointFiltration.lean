import Atlas.LinearGroups.F4.PointCrossMarked

noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

abbrev ParabolicKernelParameters (F : Type*) :=
  (Fin 2→F) × (Fin 4→F) × (Fin 4→F) × (Fin 7→F)

def parabolicKernelChart : ParabolicKernelParameters F ≃ₗ[F] (parabolicCross (F:=F)).ker where
  toFun v := ⟨(![v.1 0,v.1 1,0],
    ![![v.2.1 0,v.2.1 1,v.2.1 2,v.2.1 3,0,0,0,0],
      ![v.2.2.1 0,v.2.2.1 1,v.2.2.1 2,0,v.2.2.1 3,0,0,0],
      ![v.2.2.2 0,v.2.2.2 1,v.2.2.2 2,v.2.2.2 3,v.2.2.2 4,v.2.2.2 5,v.2.2.2 6,0]]),
    (parabolicCross_eq_zero_iff _).mpr (by simp)⟩
  invFun x := (![x.val.1 0,x.val.1 1],![x.val.2 0 0,x.val.2 0 1,x.val.2 0 2,x.val.2 0 3],
    ![x.val.2 1 0,x.val.2 1 1,x.val.2 1 2,x.val.2 1 4],
    ![x.val.2 2 0,x.val.2 2 1,x.val.2 2 2,x.val.2 2 3,x.val.2 2 4,x.val.2 2 5,x.val.2 2 6])
  left_inv v := by
    rcases v with ⟨a,b,c,d⟩
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · apply Prod.ext
        · ext i; fin_cases i <;> rfl
        · ext i; fin_cases i <;> rfl
  right_inv x := by
    have h := (parabolicCross_eq_zero_iff x.val).mp x.prop
    apply Subtype.ext
    apply Prod.ext
    · ext i; fin_cases i <;> simp_all
    · ext i j; fin_cases i <;> fin_cases j <;> simp_all
  map_add' v w := by
    apply Subtype.ext
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' s v := by
    apply Subtype.ext
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp

theorem parabolicCross_kernel_finrank : Module.finrank F (parabolicCross (F:=F)).ker=17 := by
  rw [←parabolicKernelChart.finrank_eq]
  simp [ParabolicKernelParameters]

theorem parabolicCross_range_finrank : Module.finrank F (parabolicCross (F:=F)).range=10 := by
  have h := (parabolicCross (F:=F)).finrank_range_add_finrank_ker
  rw [parabolicCross_kernel_finrank,carrier_finrank] at h
  omega

end Atlas.F4
