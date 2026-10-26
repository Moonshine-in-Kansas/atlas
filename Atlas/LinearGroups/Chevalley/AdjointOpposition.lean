import Atlas.LinearGroups.Chevalley.Adjoint
import Mathlib.Algebra.Group.End

/-! The actual Geck opposition matrix restricts to an involutive automorphism
of the root-generated adjoint group over every commutative coefficient ring. -/

noncomputable section
namespace Atlas.Chevalley
open Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

private theorem opposition_conjugation_involutive :
    Function.Involutive (MulAut.conj (oppositionUnit P b R)) := by
  intro g
  have hinv : (oppositionUnit P b R)⁻¹ = oppositionUnit P b R := by
    apply Units.ext
    rfl
  have hsquare : oppositionUnit P b R * oppositionUnit P b R = 1 := by
    apply Units.ext
    exact oppositionOver_mul_self P b R
  simp only [MulAut.conj_apply, hinv]
  calc
    oppositionUnit P b R * (oppositionUnit P b R * g * oppositionUnit P b R) *
        oppositionUnit P b R =
      (oppositionUnit P b R * oppositionUnit P b R) * g *
        (oppositionUnit P b R * oppositionUnit P b R) := by
      simp only [mul_assoc]
    _ = g := by rw [hsquare, one_mul, mul_one]

private theorem opposition_conjugation_mem (g : Adjoint P b R) :
    MulAut.conj (oppositionUnit P b R) g.val ∈ adjointSubgroup P b R := by
  apply adjoint_induction P b R
    (C := fun g => MulAut.conj (oppositionUnit P b R) g.val ∈ adjointSubgroup P b R)
    ?_ ?_ ?_ ?_ ?_ g
  · intro i t
    change loweringRootElement P b R i t ∈ adjointSubgroup P b R
    exact lowering_mem_adjoint P b R i t
  · intro i t
    change MulAut.conj (oppositionUnit P b R)
      (MulAut.conj (oppositionUnit P b R) (raisingRootElement P b R i t)) ∈
        adjointSubgroup P b R
    rw [opposition_conjugation_involutive P b R]
    exact raising_mem_adjoint P b R i t
  · change MulAut.conj (oppositionUnit P b R) 1 ∈ adjointSubgroup P b R
    rw [map_one]
    exact (adjointSubgroup P b R).one_mem
  · intro g h hg hh
    change MulAut.conj (oppositionUnit P b R) (g.val * h.val) ∈ adjointSubgroup P b R
    rw [map_mul]
    exact (adjointSubgroup P b R).mul_mem hg hh
  · intro g hg
    change MulAut.conj (oppositionUnit P b R) g.val⁻¹ ∈ adjointSubgroup P b R
    rw [map_inv]
    exact (adjointSubgroup P b R).inv_mem hg

/-- Conjugation by the existing opposition matrix, restricted to the actual
generated subgroup. This does not assert the opposition unit lies in that subgroup. -/
def adjointOppositionEquiv : Adjoint P b R ≃* Adjoint P b R where
  toFun g := ⟨MulAut.conj (oppositionUnit P b R) g.val,
    opposition_conjugation_mem P b R g⟩
  invFun g := ⟨MulAut.conj (oppositionUnit P b R) g.val,
    opposition_conjugation_mem P b R g⟩
  left_inv g := Subtype.ext (opposition_conjugation_involutive P b R g.val)
  right_inv g := Subtype.ext (opposition_conjugation_involutive P b R g.val)
  map_mul' g h := Subtype.ext (map_mul (MulAut.conj (oppositionUnit P b R)) g.val h.val)

@[simp] theorem adjointOppositionEquiv_X (i : b.support) (t : R) :
    adjointOppositionEquiv P b R (adjointX P b R i t) = adjointY P b R i t := by
  apply Subtype.ext
  rfl

@[simp] theorem adjointOppositionEquiv_Y (i : b.support) (t : R) :
    adjointOppositionEquiv P b R (adjointY P b R i t) = adjointX P b R i t := by
  apply Subtype.ext
  exact opposition_conjugation_involutive P b R (raisingRootElement P b R i t)

end Atlas.Chevalley
