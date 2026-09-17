import Atlas.LinearGroups.TypeReeG2
import Atlas.LinearGroups.ReeG2.FieldChecks

noncomputable section
namespace Atlas.ReeG2.Checks

theorem parameters2187 : Parameters (GaloisField 3 7) 3 :=
  ⟨by omega,by simpa using GaloisField.card 3 7 (by omega)⟩

theorem order27 : Nat.card (Model (GaloisField 3 3) 1) = 10073444472 := by
  rw [order 1 parameters27.cardinality,parameters27.cardinality]
  norm_num

theorem order243 : Nat.card (Model (GaloisField 3 5) 2) = 49825657439340552 := by
  rw [order 2 parameters243.cardinality,parameters243.cardinality]
  norm_num

theorem order2187 : Nat.card (Model (GaloisField 3 7) 3) = 239189910264352349332632 := by
  rw [order 3 parameters2187.cardinality,parameters2187.cardinality]
  norm_num

theorem simple27 : IsSimpleGroup (Model (GaloisField 3 3) 1) := simple 1 parameters27
theorem simple243 : IsSimpleGroup (Model (GaloisField 3 5) 2) := simple 2 parameters243

theorem nonabelian27 : ∃ g h : Model (GaloisField 3 3) 1, g*h ≠ h*g :=
  model_noncommutative 1 parameters27.cardinality
theorem nonabelian243 : ∃ g h : Model (GaloisField 3 5) 2, g*h ≠ h*g :=
  model_noncommutative 2 parameters243.cardinality

theorem rootOrder27 : Nat.card (rootSubgroup 1 parameters27.cardinality) = 19683 := by
  rw [card_rootSubgroup,parameters27.cardinality]
  norm_num

theorem pointCount27 : Nat.card (pointSet (F := GaloisField 3 3) 1) = 19684 := by
  rw [card_pointSet,parameters27.cardinality]
  norm_num

theorem borelOrder27 : Nat.card (borel 1 parameters27.cardinality) = 511758 := by
  rw [card_borel,parameters27.cardinality]
  norm_num

theorem action27 : letI := pointAction 1 parameters27.cardinality
    MulAction.IsMultiplyPretransitive (Model (GaloisField 3 3) 1)
      (pointSet (F := GaloisField 3 3) 1) 2 := pointAction_two_pretransitive 1 parameters27.cardinality

theorem action243 : letI := pointAction 2 parameters243.cardinality
    MulAction.IsMultiplyPretransitive (Model (GaloisField 3 5) 2)
      (pointSet (F := GaloisField 3 5) 2) 2 := pointAction_two_pretransitive 2 parameters243.cardinality

theorem rootOrder243 : Nat.card (rootSubgroup 2 parameters243.cardinality) = 243^3 := by
  rw [card_rootSubgroup,parameters243.cardinality]
  norm_num

theorem pointCount243 : Nat.card (pointSet (F := GaloisField 3 5) 2) = 243^3+1 := by
  rw [card_pointSet,parameters243.cardinality]
  norm_num

theorem borelOrder243 : Nat.card (borel 2 parameters243.cardinality) = 243^3*242 := by
  rw [card_borel,parameters243.cardinality]
  norm_num

theorem inverseTwist27 (x : GaloisField 3 3) : theta _ 1 (sigma _ 1 x) = x :=
  theta_sigma parameters27.cardinality x

theorem inverseTwist243 (x : GaloisField 3 5) : theta _ 2 (sigma _ 2 x) = x :=
  theta_sigma parameters243.cardinality x

end Atlas.ReeG2.Checks

