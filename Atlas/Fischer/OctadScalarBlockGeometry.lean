import Atlas.Fischer.OctadScalarBlocks
import Atlas.Fischer.ParkerMultiplicativity
import Atlas.Fischer.RationalCocodeLabels
import Atlas.Fischer.CoordinateHermitianSums

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadScalarBlock_mem (O : Octad) (S : Finset Omega) (x : Coordinates) :
    x ∈ octadScalarBlock O S ↔ ∀ i ∉ octadScalarBlockCoordinates O S, x i=0 :=
  Pi.mem_spanSubset_iff

theorem octadScalarBlockCoordinates_iff (O : Octad) (S : Finset Omega) (i : CoordinateIndex) :
    i ∈ octadScalarBlockCoordinates O S ↔
      octadRationalLabel O (i,0)=S ∨ octadRationalLabel O (i,1)=S := by
  constructor
  · rintro ⟨k,hk⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  · rintro (h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

theorem octadRationalLabel_one_eq_complement (O : Octad) (i : CoordinateIndex) :
    octadRationalLabel O (i,1)=O.val \ octadRationalLabel O (i,0) := by
  cases i <;> simp [octadRationalLabel]

theorem octadScalarBlockCoordinates_complement (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val) :
    octadScalarBlockCoordinates O (O.val \ S)=octadScalarBlockCoordinates O S := by
  ext i
  rw [octadScalarBlockCoordinates_iff,octadScalarBlockCoordinates_iff,
    octadRationalLabel_one_eq_complement]
  have hi := octadRationalLabel_subset O (i,0)
  have hc : O.val \ octadRationalLabel O (i,0)=O.val \ S ↔
      octadRationalLabel O (i,0)=S := by
    constructor
    · intro h
      have he := congrArg (fun T => O.val \ T) h
      simpa only [Finset.sdiff_sdiff_eq_self hi,Finset.sdiff_sdiff_eq_self hSO] using he
    · exact congrArg _
  rw [hc]
  have hc' : octadRationalLabel O (i,0)=O.val \ S ↔
      O.val \ octadRationalLabel O (i,0)=S := by
    constructor
    · intro h
      rw [h,Finset.sdiff_sdiff_eq_self hSO]
    · intro h
      have he := congrArg (fun T => O.val \ T) h
      simpa only [Finset.sdiff_sdiff_eq_self hi] using he
  rw [hc',or_comm]

theorem octadScalarBlock_complement (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val) :
    octadScalarBlock O (O.val \ S)=octadScalarBlock O S :=
  congrArg (Pi.spanSubset Scalar) (octadScalarBlockCoordinates_complement O S hSO)

theorem coordinateVector_mem_octadScalarBlock (O : Octad) (S : Finset Omega)
    (i : CoordinateIndex) (hi : i ∈ octadScalarBlockCoordinates O S) :
    coordinateVector i ∈ octadScalarBlock O S := by
  rw [octadScalarBlock_mem]
  intro j hj
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  simp [coordinateVector,Pi.single_apply,hji]

theorem octadScalarBlockCoordinates_disjoint (O : Octad) (S T : Finset Omega)
    (hST : S ≠ T) (hScT : O.val \ S ≠ T) :
    Disjoint (octadScalarBlockCoordinates O S) (octadScalarBlockCoordinates O T) := by
  rw [Set.disjoint_left]
  intro i hi hj
  rw [octadScalarBlockCoordinates_iff] at hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hST (hi.symm.trans hj)
  · exact hScT (by rw [← hi,← octadRationalLabel_one_eq_complement]; exact hj)
  · have he := octadRationalLabel_one_eq_complement O i
    rw [hi,hj] at he
    have ht := octadRationalLabel_subset O (i,0)
    rw [hj] at ht
    exact hScT (by rw [he,Finset.sdiff_sdiff_eq_self ht])
  · exact hST (hi.symm.trans hj)

theorem octadScalarBlock_orthogonal (O : Octad) (S T : Finset Omega)
    (hST : S ≠ T) (hScT : O.val \ S ≠ T)
    (x y : Coordinates) (hx : x ∈ octadScalarBlock O S) (hy : y ∈ octadScalarBlock O T) :
    hermitian x y=0 := by
  have hd := octadScalarBlockCoordinates_disjoint O S T hST hScT
  unfold hermitian weightedHermitian
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ octadScalarBlockCoordinates O S
  · have hj : i ∉ octadScalarBlockCoordinates O T := fun h => Set.disjoint_left.mp hd hi h
    rw [(octadScalarBlock_mem O T y).mp hy i hj,star_zero,mul_zero]
  · rw [(octadScalarBlock_mem O S x).mp hx i hi,mul_zero,zero_mul]

/-- The actual complementary coordinate blocks exhaust the existing algebra. -/
theorem octadScalarBlocks_span (O : Octad) :
    (⨆ S : Finset Omega, octadScalarBlock O S)=⊤ := by
  apply top_unique
  intro x _
  rw [← coordinates_sum_basis x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact (le_iSup (fun S => octadScalarBlock O S) (octadRationalLabel O (i,0)))
    (coordinateVector_mem_octadScalarBlock O _ i ⟨0,rfl⟩)

end Atlas.Fischer
