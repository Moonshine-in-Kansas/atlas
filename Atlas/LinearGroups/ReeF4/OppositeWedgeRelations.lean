import Atlas.LinearGroups.ReeF4.DiagonalProductTables
import Atlas.LinearGroups.ReeF4.ExteriorDomain
import Atlas.LinearAlgebra.CharTwoAdditiveRelations

/-! Opposite-pair sums lie in the actual domain although their summands do not.
The additive relation detects the overbroad printed rule R2 (3.14). -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def oppositeWedge (r : ShortRootLabel) : ⋀[F]^2 (TraceZero F) :=
  wedge (rootVector r) (rootVector (r.1, Fin.rev r.2))

theorem oppositeWedge_pair_mem (r s : ShortRootLabel) (h : r.1 = s.1) :
    oppositeWedge (F:=F) r + oppositeWedge s ∈ StarCarrier := by
  constructor
  · change exteriorPolar (oppositeWedge r + oppositeWedge s) = 0
    simp [oppositeWedge, rootPolar, CharTwo.add_self_eq_zero]
  · change exteriorCross (oppositeWedge r + oppositeWedge s) = 0
    simp only [_root_.map_add, oppositeWedge, exteriorCross_wedge, rootCross_opposite]
    rw [h]
    rw [← two_smul F, (CharTwo.two_eq_zero (R:=F)), zero_smul]

def oppositePair (r s : ShortRootLabel) (h : r.1 = s.1) : StarCarrier (F:=F) :=
  ⟨oppositeWedge r + oppositeWedge s, oppositeWedge_pair_mem r s h⟩

theorem oppositePair_add (r s t : ShortRootLabel)
    (hrs : r.1=s.1) (hst : s.1=t.1) :
    oppositePair (F:=F) r s hrs + oppositePair s t hst = oppositePair r t (hrs.trans hst) := by
  apply Subtype.ext
  change (oppositeWedge r + oppositeWedge s) + (oppositeWedge s + oppositeWedge t) = _
  have h : oppositeWedge (F:=F) s + oppositeWedge s = 0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R:=F)), zero_smul]
  calc (oppositeWedge r + oppositeWedge s) + (oppositeWedge s + oppositeWedge t) =
      (oppositeWedge r + oppositeWedge t) + (oppositeWedge s + oppositeWedge s) := by abel
       _ = oppositeWedge r + oppositeWedge t := by rw [h, add_zero]

theorem oppositePair_constant_forces_zero (f : StarCarrier (F:=F) →+ TraceZero F)
    (z : TraceZero F)
    (h01 : f (oppositePair (0,0) (0,1) rfl)=z)
    (h12 : f (oppositePair (0,1) (0,2) rfl)=z)
    (h02 : f (oppositePair (0,0) (0,2) rfl)=z) : z=0 :=
  Atlas.charTwo_equal_values_of_sum_force_zero (F:=F) f _ _ _ z
    (oppositePair_add (0,0) (0,1) (0,2) rfl rfl) h01 h12 h02

theorem firstDiagonal_ne_zero [Nontrivial F] : diagonalVector (F:=F) 0 ≠ 0 := by
  intro h
  have hh := congrArg (fun w : TraceZero F => w.val.1 1) h
  simpa [diagonalVector, traceZeroProjection, trace, unit, Pi.single_apply, CharTwo.neg_eq] using hh

theorem printed_constant_rule_impossible [Nontrivial F]
    (f : StarCarrier (F:=F) →+ TraceZero F) :
    ¬ (f (oppositePair (0,0) (0,1) rfl)=diagonalVector 0 ∧
       f (oppositePair (0,1) (0,2) rfl)=diagonalVector 0 ∧
       f (oppositePair (0,0) (0,2) rfl)=diagonalVector 0) := by
  rintro ⟨h1,h2,h3⟩
  exact firstDiagonal_ne_zero (oppositePair_constant_forces_zero f _ h1 h2 h3)

end Atlas.ReeF4
