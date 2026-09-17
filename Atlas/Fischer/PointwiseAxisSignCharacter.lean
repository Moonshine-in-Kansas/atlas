import Atlas.Fischer.PointwiseAxisCoordinateAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual binary sign of an octad basis vector under a pointwise axis map. -/
def pointwiseAxisOctadSign (e : SemilinearAlgebraAutomorphism) (D : Octad) : Bit :=
  if e.val (xOctad D)=xOctad D then 0 else 1

theorem pointwiseAxisOctadSign_action (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (D : Octad) :
    e.val (xOctad D)=parkerScalarSign (pointwiseAxisOctadSign e D) • xOctad D := by
  unfold pointwiseAxisOctadSign
  split_ifs with h
  · simpa [parkerScalarSign] using h
  · have hn := (pointwiseAxis_octad_sign e he D).resolve_left h
    simpa [parkerScalarSign] using hn

theorem pointwiseAxisOctadSign_scalar (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (D : Octad) :
    parkerScalarSign (pointwiseAxisOctadSign e D)=e.val (xOctad D) (.inr D) := by
  have h := congrFun (pointwiseAxisOctadSign_action e he D) (.inr D)
  simpa using h.symm

end Atlas.Fischer
