import Atlas.Fischer.OctadRationalGradeCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Actual E-coordinate support of the pair of complementary rational grades. -/
def octadScalarBlockCoordinates (O : Octad) (S : Finset Omega) : Set CoordinateIndex :=
  {i | ∃ k : Fin 2, octadRationalLabel O (i,k)=S}

def octadScalarBlock (O : Octad) (S : Finset Omega) : Submodule Scalar Coordinates :=
  Pi.spanSubset Scalar (octadScalarBlockCoordinates O S)

theorem octadRationalLabel_zero_ne_one (O : Octad) (i : CoordinateIndex) :
    octadRationalLabel O (i,0) ≠ octadRationalLabel O (i,1) := by
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < O.val.card by rw [octad_size O.val O.prop]; decide)
  intro h
  have he := Finset.ext_iff.mp h j
  cases i with
  | inl i => simp [octadRationalLabel,hj] at he
  | inr D =>
    by_cases hd : j ∈ D.val <;> simp [octadRationalLabel,hj,hd] at he

theorem octadRationalLabel_direction_injective (O : Octad) (i : CoordinateIndex) :
    Function.Injective (fun k : Fin 2 => octadRationalLabel O (i,k)) := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exact False.elim (octadRationalLabel_zero_ne_one O i h)
  · exact False.elim (octadRationalLabel_zero_ne_one O i h.symm)
  · rfl

/-- Forgetting the real/theta direction is a bijection from an actual rational
grade basis to the E-coordinate basis of its complementary pair. -/
def octadScalarBlockIndexEquiv (O : Octad) (S : Finset Omega) :
    OctadRationalGradeIndex O S ≃ octadScalarBlockCoordinates O S :=
  Equiv.ofBijective (fun p => ⟨p.val.1,⟨p.val.2,p.prop⟩⟩) ⟨by
    intro p q h
    apply Subtype.ext
    have hi : p.val.1=q.val.1 := congrArg Subtype.val h
    apply Prod.ext hi
    apply octadRationalLabel_direction_injective O p.val.1
    exact p.prop.trans (by rw [hi]; exact q.prop.symm), by
    intro i
    obtain ⟨k,hk⟩ := i.prop
    exact ⟨⟨(i.val,k),hk⟩,rfl⟩⟩

theorem octadScalarBlock_dimension (O : Octad) (S : Finset Omega) :
    Module.finrank Scalar (octadScalarBlock O S)=Module.finrank ℚ (octadRationalGrade O S) := by
  rw [octadScalarBlock,Pi.dim_spanSubset,octadRationalGrade_finrank,
    ← Nat.card_coe_set_eq]
  exact Nat.card_congr (octadScalarBlockIndexEquiv O S).symm

theorem octadScalarBlock_empty_dimension (O : Octad) :
    Module.finrank Scalar (octadScalarBlock O ∅)=55 := by
  rw [octadScalarBlock_dimension,octadRationalGrade_empty_dimension]

theorem octadScalarBlock_full_dimension (O : Octad) :
    Module.finrank Scalar (octadScalarBlock O O.val)=55 := by
  rw [octadScalarBlock_dimension,octadRationalGrade_full_dimension]

theorem octadScalarBlock_duad_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=2) :
    Module.finrank Scalar (octadScalarBlock O S)=16 := by
  rw [octadScalarBlock_dimension,octadRationalGrade_duad_dimension O S hSO hS]

theorem octadScalarBlock_six_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=6) :
    Module.finrank Scalar (octadScalarBlock O S)=16 := by
  rw [octadScalarBlock_dimension,octadRationalGrade_six_dimension O S hSO hS]

theorem octadScalarBlock_tetrad_dimension (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card=4) :
    Module.finrank Scalar (octadScalarBlock O S)=8 := by
  rw [octadScalarBlock_dimension,octadRationalGrade_tetrad_dimension O S hSO hS]

end Atlas.Fischer
