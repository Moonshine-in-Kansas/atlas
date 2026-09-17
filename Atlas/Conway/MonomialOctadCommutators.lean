import Atlas.Conway.DisjointOctadCount
import Atlas.GroupTheory.NonabelianSimplePerfect
import Atlas.Mathieu.Mathieu24Simplicity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped commutatorElement
attribute [local instance] Classical.propDecidable

def octadCode (O : Finset Omega) (hO : O ∈ octads) : golay :=
  ⟨supportWord O,octad_supportWord_mem O hO⟩

theorem permutation_octadCode (g : Mathieu24CodeModel) (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (hg : permuteBlock g.val O = P) :
    golayPermutationEquiv g (octadCode O hO) = octadCode P hP := by
  apply Subtype.ext
  funext i
  have hi : g.val.symm i ∈ O ↔ i ∈ P := by
    rw [← hg]
    constructor
    · intro h; exact Finset.mem_image.mpr ⟨g.val.symm i,h,g.val.apply_symm_apply i⟩
    · rintro h; obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      simpa [← he] using hj
  change (if g.val.symm i ∈ O then (1 : Bit) else 0) = (if i ∈ P then 1 else 0)
  simp only [hi]

theorem monomial_sign_commutator (g : Mathieu24CodeModel) (c : golay) :
    (SemidirectProduct.inl (Multiplicative.ofAdd (golayPermutationEquiv g c - c)) :
      GolayMonomialGroup) =
      ⁅(SemidirectProduct.inr g : GolayMonomialGroup),SemidirectProduct.inl (Multiplicative.ofAdd c)⁆ := by
  rw [sub_eq_add_neg]
  change (SemidirectProduct.inl ((golayPermutationAction g) (Multiplicative.ofAdd c) *
    (Multiplicative.ofAdd c)⁻¹) : GolayMonomialGroup) = _
  rw [map_mul,SemidirectProduct.inl_aut,map_inv]
  simp only [commutatorElement_def,map_inv]

def seedOctadP : Finset Omega := tetrad (0,0) ∪ tetrad (0,1)
def seedOctadQ : Finset Omega := tetrad (0,0) ∪ tetrad (1,0)
def seedOctadO : Finset Omega := tetrad (0,1) ∪ tetrad (1,0)

theorem seedOctadP_mem : seedOctadP ∈ octads := tetrad_pair_octad _ _ (by decide)
theorem seedOctadQ_mem : seedOctadQ ∈ octads := tetrad_pair_octad _ _ (by decide)
theorem seedOctadO_mem : seedOctadO ∈ octads := tetrad_pair_octad _ _ (by decide)

theorem seedOctad_difference : octadCode seedOctadQ seedOctadQ_mem -
    octadCode seedOctadP seedOctadP_mem = octadCode seedOctadO seedOctadO_mem := by
  apply Subtype.ext
  decide

theorem seedOctad_sign_mem_commutator :
    (SemidirectProduct.inl (Multiplicative.ofAdd (octadCode seedOctadO seedOctadO_mem)) :
      GolayMonomialGroup) ∈ commutator GolayMonomialGroup := by
  obtain ⟨g,hg⟩ := mathieu24_octad_transitive seedOctadP seedOctadQ seedOctadP_mem seedOctadQ_mem
  have he := monomial_sign_commutator g (octadCode seedOctadP seedOctadP_mem)
  rw [permutation_octadCode g _ _ seedOctadP_mem seedOctadQ_mem hg,seedOctad_difference] at he
  rw [he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem octad_sign_mem_commutator (O : Finset Omega) (hO : O ∈ octads) :
    (SemidirectProduct.inl (Multiplicative.ofAdd (octadCode O hO)) : GolayMonomialGroup) ∈
      commutator GolayMonomialGroup := by
  obtain ⟨g,hg⟩ := mathieu24_octad_transitive seedOctadO O seedOctadO_mem hO
  have he := SemidirectProduct.inl_aut (φ := golayPermutationAction) g
    (Multiplicative.ofAdd (octadCode seedOctadO seedOctadO_mem))
  change (SemidirectProduct.inl (Multiplicative.ofAdd
    (golayPermutationEquiv g (octadCode seedOctadO seedOctadO_mem))) : GolayMonomialGroup) = _ at he
  rw [permutation_octadCode g _ _ seedOctadO_mem hO hg] at he
  rw [he,map_inv]
  exact (inferInstance : (commutator GolayMonomialGroup).Normal).conj_mem _
    seedOctad_sign_mem_commutator (SemidirectProduct.inr g)

end Atlas.Conway
