import Atlas.LinearGroups.F4.PointFiltrationCovariance
import Atlas.LinearGroups.F4.WhiteZeroPoints
import Atlas.LinearGroups.F4.ShortRoots

/-! The C-slot marking and its actual projective point stabilizer. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

theorem coordinateCycle_baseVector :
    (coordinateCycle (F:=F)).val baseVector = parabolicVector := by
  rw [coordinateCycle_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Atlas.Albert.coordinateCycle,baseVector,parabolicVector,
        SplitOctonion.basisVector]

theorem parabolicVector_adjoint : adjoint (parabolicVector (F:=F))=0 := by
  rw [←coordinateCycle_baseVector,stabilizer_adjoint,baseVector_adjoint,map_zero]

theorem parabolicVector_trace : trace (parabolicVector (F:=F))=0 := by
  simp [parabolicVector,trace]

def parabolicPoint : WhiteZeroPoints F :=
  whiteZeroPointMk F parabolicVector parabolicVector_ne_zero
    parabolicVector_trace parabolicVector_adjoint

def parabolicPointStabilizer : Subgroup (Model F) :=
  MulAction.stabilizer (Model F) (parabolicPoint (F:=F))

theorem mem_parabolicPointStabilizer_iff (g : Model F) :
    g ∈ parabolicPointStabilizer ↔
      ∃ t : Fˣ, g.val parabolicVector = t.val • parabolicVector := by
  change g • (parabolicPoint (F:=F)) = parabolicPoint ↔ _
  rw [Subtype.ext_iff]
  change g.val • Projectivization.mk F parabolicVector _ =
    Projectivization.mk F parabolicVector _ ↔ _
  rw [Projectivization.smul_mk,Projectivization.mk_eq_mk_iff]
  simp only [LinearEquiv.smul_def,Units.smul_def,eq_comm]

theorem parabolicPointStabilizer_preserves_kernel (g : parabolicPointStabilizer (F:=F))
    (x : Carrier F) : parabolicCross (g.val.val x)=0 ↔ parabolicCross x=0 := by
  obtain ⟨t,ht⟩ := (mem_parabolicPointStabilizer_iff g.val).mp g.prop
  exact parabolicCross_kernel_stable g.val t ht x

theorem parabolicPointStabilizer_preserves_imageZero (g : parabolicPointStabilizer (F:=F))
    {x : Carrier F} (hx : x∈parabolicImageZero (F:=F)) :
    g.val.val x∈parabolicImageZero (F:=F) := by
  obtain ⟨t,ht⟩ := (mem_parabolicPointStabilizer_iff g.val).mp g.prop
  exact parabolicImageZero_stable g.val t ht hx

end Atlas.F4
