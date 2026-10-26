import Atlas.LinearGroups.F4.PointFlag
import Atlas.LinearGroups.F4.Basic
import Atlas.Algebra.Albert.StabilizerInvariants

/-! Covariance of the intrinsic marked-point filtration under every element
of the full Albert group preserving the marked line. No Levi image is assumed. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem parabolicCross_covariant (g : Model F) (t : Fˣ)
    (hg : g.val parabolicVector = t.val • parabolicVector) (x : Carrier F) :
    g.val (parabolicCross x) = t.val • parabolicCross (g.val x) := by
  change g.val (cross parabolicVector x) = t.val • cross parabolicVector (g.val x)
  rw [←stabilizer_cross, hg, cross_smul_left]

theorem parabolicCross_kernel_stable (g : Model F) (t : Fˣ)
    (hg : g.val parabolicVector = t.val • parabolicVector) (x : Carrier F) :
    parabolicCross (g.val x) = 0 ↔ parabolicCross x = 0 := by
  have h := parabolicCross_covariant g t hg x
  constructor
  · intro hx
    have hz : g.val (parabolicCross x) = g.val 0 := by simp [h,hx]
    exact g.val.injective hz
  · intro hx
    have ht : t.val • parabolicCross (g.val x) = 0 := by
      rw [←h,hx]; exact g.val.map_zero
    exact (smul_eq_zero.mp ht).resolve_left t.ne_zero

theorem parabolicCross_range_stable (g : Model F) (t : Fˣ)
    (hg : g.val parabolicVector = t.val • parabolicVector)
    {x : Carrier F} (hx : x ∈ (parabolicCross (F:=F)).range) :
    g.val x ∈ (parabolicCross (F:=F)).range := by
  obtain ⟨y,rfl⟩ := hx
  refine ⟨t.val • g.val y, ?_⟩
  rw [map_smul, ←parabolicCross_covariant g t hg y]

theorem parabolicImageZero_stable (g : Model F) (t : Fˣ)
    (hg : g.val parabolicVector = t.val • parabolicVector)
    {x : Carrier F} (hx : x ∈ parabolicImageZero (F:=F)) :
    g.val x ∈ parabolicImageZero (F:=F) := by
  refine ⟨parabolicCross_range_stable g t hg hx.1, ?_⟩
  change trace (g.val x)=0
  rw [stabilizer_trace]
  exact hx.2

end Atlas.F4
