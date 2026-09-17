import Atlas.Fischer.ParkerCodeAction
import Atlas.Fischer.CubicTriangleAveraging
import Atlas.Fischer.MathieuOctadStabilizer
import Atlas.Mathieu.OrderedTripleTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicTriangle_word_smul (g : Mathieu24CodeModel) (D : Octad) :
    octadWord (g • D)=parkerCodeEquiv g (octadWord D) := by
  apply Subtype.ext
  apply support_injective
  rw [octadWord_support,parkerCodeEquiv_coe,coordinatePermutation_support,octadWord_support]
  rfl

theorem cubicTriangle_one_fixed (g : Mathieu24CodeModel) : parkerCodeEquiv g golayOne=golayOne := by
  apply Subtype.ext
  rfl

def cubicSextetTriangleAction (g : Mathieu24CodeModel) (t : OrderedCubicSextetTriangle) :
    OrderedCubicSextetTriangle :=
  ⟨(g • t.val.1,g • t.val.2.1,g • t.val.2.2),by
    simp only [cubicTriangle_word_smul,t.property,map_add]⟩

def cubicTrioAction (g : Mathieu24CodeModel) (t : OrderedCubicTrio) : OrderedCubicTrio :=
  ⟨(g • t.val.1,g • t.val.2.1,g • t.val.2.2),by
    simp only [cubicTriangle_word_smul,t.property,map_add,cubicTriangle_one_fixed]⟩

def cubicSextetTriangleEquiv (g : Mathieu24CodeModel) : Equiv.Perm OrderedCubicSextetTriangle where
  toFun := cubicSextetTriangleAction g
  invFun := cubicSextetTriangleAction g⁻¹
  left_inv t := by apply Subtype.ext; simp [cubicSextetTriangleAction]
  right_inv t := by apply Subtype.ext; simp [cubicSextetTriangleAction]

def cubicTrioEquiv (g : Mathieu24CodeModel) : Equiv.Perm OrderedCubicTrio where
  toFun := cubicTrioAction g
  invFun := cubicTrioAction g⁻¹
  left_inv t := by apply Subtype.ext; simp [cubicTrioAction]
  right_inv t := by apply Subtype.ext; simp [cubicTrioAction]

theorem cubicTriangle_incidence_smul (g : Mathieu24CodeModel) (i : Omega) (D : Octad) :
    cubicPointOctadIncidence (g.val i) (g • D)=cubicPointOctadIncidence i D := by
  have hm : g.val i ∈ (g • D).val ↔ i ∈ D.val := by
    simp [mathieuOctadAction_val,permuteBlock]
  simp only [cubicPointOctadIncidence,hm]

def cubicSextetIncidenceSum (i j k : Omega) : Scalar :=
  ∑ t : OrderedCubicSextetTriangle,cubicPointOctadIncidence i t.val.1*
    cubicPointOctadIncidence j t.val.2.1*cubicPointOctadIncidence k t.val.2.2

def cubicTrioIncidenceSum (i j k : Omega) : Scalar :=
  ∑ t : OrderedCubicTrio,cubicPointOctadIncidence i t.val.1*
    cubicPointOctadIncidence j t.val.2.1*cubicPointOctadIncidence k t.val.2.2

theorem cubicSextetIncidenceSum_invariant (g : Mathieu24CodeModel) (i j k : Omega) :
    cubicSextetIncidenceSum (g.val i) (g.val j) (g.val k)=cubicSextetIncidenceSum i j k := by
  unfold cubicSextetIncidenceSum
  rw [← Equiv.sum_comp (cubicSextetTriangleEquiv g)]
  apply Finset.sum_congr rfl
  intro t ht
  change cubicPointOctadIncidence (g.val i) (g • t.val.1)*
    cubicPointOctadIncidence (g.val j) (g • t.val.2.1)*
    cubicPointOctadIncidence (g.val k) (g • t.val.2.2)=_
  simp only [cubicTriangle_incidence_smul]

theorem cubicTrioIncidenceSum_invariant (g : Mathieu24CodeModel) (i j k : Omega) :
    cubicTrioIncidenceSum (g.val i) (g.val j) (g.val k)=cubicTrioIncidenceSum i j k := by
  unfold cubicTrioIncidenceSum
  rw [← Equiv.sum_comp (cubicTrioEquiv g)]
  apply Finset.sum_congr rfl
  intro t ht
  change cubicPointOctadIncidence (g.val i) (g • t.val.1)*
    cubicPointOctadIncidence (g.val j) (g • t.val.2.1)*
    cubicPointOctadIncidence (g.val k) (g • t.val.2.2)=_
  simp only [cubicTriangle_incidence_smul]

end Atlas.Fischer
