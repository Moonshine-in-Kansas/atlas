import Atlas.Fischer.OctadicNineBlock
import Atlas.Fischer.SignedCoordinateIndependence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev OctadicNineIndex (O : Octad) := O.val ⊕ Unit

def octadicNineFamily {O : Octad} (Q : OctadCalibration O) : OctadicNineIndex O → Coordinates :=
  Sum.elim (fun i => u i.val) (fun _ => signedOctadVector Q.octadLift)

theorem octadicNineFamily_independent {O : Octad} (Q : OctadCalibration O) :
    LinearIndependent Scalar (octadicNineFamily Q) := by
  let j : OctadicNineIndex O → CoordinateIndex := Sum.elim (fun i => Sum.inl i.val) (fun _ => Sum.inr O)
  have hj : Function.Injective j := by
    intro a b h
    cases a <;> cases b <;> simp_all [j]
  let s : OctadicNineIndex O → Bit := Sum.elim (fun _ => 0) (fun _ => Q.octadLift.val.2)
  have hv : octadicNineFamily Q = fun i => parkerScalarSign (s i) • coordinateVector (j i) := by
    funext i
    cases i with
    | inl i => simp [octadicNineFamily,s,j,parkerScalarSign,u]
    | inr i =>
      have ho : signedOctadSupport Q.octadLift=O := (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
      simp [octadicNineFamily,s,j,signedOctadVector,ho,xOctad]
  rw [hv]
  exact signedCoordinate_linearIndependent j hj s

theorem octadicNineFamily_range {O : Octad} (Q : OctadCalibration O) :
    Set.range (octadicNineFamily Q)=octadicNineGenerators Q := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i,rfl⟩
    | inr i => exact Or.inr rfl
  · rintro (⟨i,rfl⟩ | rfl)
    · exact ⟨Sum.inl i,rfl⟩
    · exact ⟨Sum.inr (),rfl⟩

theorem octadicNineSpace_dimension {O : Octad} (Q : OctadCalibration O) :
    Module.finrank Scalar (octadicNineSpace Q)=9 := by
  classical
  rw [octadicNineSpace,← octadicNineFamily_range,
    finrank_span_eq_card (octadicNineFamily_independent Q)]
  rw [Fintype.card_sum,Fintype.card_coe,Fintype.card_unit,octad_size O.val O.prop]

end Atlas.Fischer
