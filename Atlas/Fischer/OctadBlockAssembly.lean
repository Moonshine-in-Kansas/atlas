import Atlas.Fischer.OctadicZeroBlock

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- A reusable assembly theorem on the actual orthogonal coordinate blocks.
All local invariance and antiunitarity obligations remain explicit. -/
theorem rootMap_antiunitary_of_octadBlocks (r : Coordinates) (O : Octad)
    (hinv : ∀ i : CoordinateIndex, Set.MapsTo (rootMap r)
      (octadScalarBlock O (octadRationalLabel O (i,0)))
      (octadScalarBlock O (octadRationalLabel O (i,0))))
    (hanti : ∀ i : CoordinateIndex,
      RootMapAntiunitaryOn r (octadScalarBlock O (octadRationalLabel O (i,0)))) :
    ∀ x y, hermitian (rootMap r x) (rootMap r y)=star (hermitian x y) := by
  have ht : Submodule.span Scalar (Set.range coordinateVector)=⊤ := by
    apply top_unique
    intro x _
    rw [← coordinates_sum_basis x]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  have ha := rootMap_antiunitary_span r (Set.range coordinateVector) (by
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    have hi := coordinateVector_mem_octadScalarBlock O (octadRationalLabel O (i,0)) i ⟨0,rfl⟩
    have hj := coordinateVector_mem_octadScalarBlock O (octadRationalLabel O (j,0)) j ⟨0,rfl⟩
    by_cases he : octadRationalLabel O (i,0)=octadRationalLabel O (j,0)
    · exact hanti i _ hi _ (he.symm ▸ hj)
    by_cases hc : O.val \ octadRationalLabel O (i,0)=octadRationalLabel O (j,0)
    · have hb : octadScalarBlock O (octadRationalLabel O (j,0))=
          octadScalarBlock O (octadRationalLabel O (i,0)) := by
        rw [← hc,octadScalarBlock_complement O _ (octadRationalLabel_subset O (i,0))]
      exact hanti i _ hi _ (hb ▸ hj)
    · rw [octadScalarBlock_orthogonal O _ _ he hc _ _ (hinv i hi) (hinv j hj),
        octadScalarBlock_orthogonal O _ _ he hc _ _ hi hj,star_zero])
  rw [ht] at ha
  exact fun x y => ha x (Submodule.mem_top) y (Submodule.mem_top)

/-- Every coordinate block is either the completed zero block or an actual
16-dimensional duad block or 8-dimensional tetrad block. -/
theorem octadCoordinateBlock_cases (O : Octad) (i : CoordinateIndex) :
    octadScalarBlock O (octadRationalLabel O (i,0))=octadScalarBlock O ∅ ∨
      ∃ S : Finset Omega, S ⊆ O.val ∧ (S.card=2 ∨ S.card=4) ∧
        octadScalarBlock O (octadRationalLabel O (i,0))=octadScalarBlock O S := by
  cases i with
  | inl i => exact Or.inl rfl
  | inr D =>
    change octadScalarBlock O (D.val ∩ O.val)=_ ∨ _
    rcases octad_intersection_sizes D.val O.val D.prop O.prop with h | h | h | h
    · exact Or.inl (congrArg (octadScalarBlock O) (Finset.card_eq_zero.mp h))
    · exact Or.inr ⟨_,Finset.inter_subset_right,Or.inl h,rfl⟩
    · exact Or.inr ⟨_,Finset.inter_subset_right,Or.inr h,rfl⟩
    · have he : D.val ∩ O.val=O.val := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        (by rw [octad_size O.val O.prop,h])
      left
      rw [he]
      simpa only [Finset.sdiff_empty] using octadScalarBlock_complement O ∅ (Finset.empty_subset _)

/-- The remaining global octadic antiunitarity obligation is exactly the actual
16- and 8-dimensional local maps. Their proofs are not assumed completed. -/
theorem rootMap_octadic_antiunitary_of_local_blocks {O : Octad} (Q : OctadCalibration O)
    (hinv : ∀ S : Finset Omega, S ⊆ O.val → (S.card=2 ∨ S.card=4) →
      Set.MapsTo (rootMap (octadicRoot Q 0)) (octadScalarBlock O S) (octadScalarBlock O S))
    (hanti : ∀ S : Finset Omega, S ⊆ O.val → (S.card=2 ∨ S.card=4) →
      RootMapAntiunitaryOn (octadicRoot Q 0) (octadScalarBlock O S)) :
    ∀ x y, hermitian (rootMap (octadicRoot Q 0) x) (rootMap (octadicRoot Q 0) y)=
      star (hermitian x y) := by
  apply rootMap_antiunitary_of_octadBlocks _ O
  · intro i
    rcases octadCoordinateBlock_cases O i with h | ⟨S,hSO,hS,h⟩
    · rw [h]; exact rootMap_octadic_zeroBlock_invariant Q
    · rw [h]; exact hinv S hSO hS
  · intro i
    rcases octadCoordinateBlock_cases O i with h | ⟨S,hSO,hS,h⟩
    · rw [h]; exact rootMap_octadic_zeroBlock_antiunitary Q
    · rw [h]; exact hanti S hSO hS

end Atlas.Fischer
