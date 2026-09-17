import Atlas.Lattices.IcosianRoots
import Atlas.Algebra.IcosianModuloTwoKernel

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

theorem icosianCoordinateEmbedding_single (i : Fin 3) (z : icosianOrder) :
    icosianCoordinateEmbedding (icosianSingle i z)=Pi.single i z.val := by
  funext j
  by_cases h : j=i <;> simp [icosianCoordinateEmbedding,icosianSingle,Pi.single_apply,h]

theorem icosianAxisIntersection (i : Fin 3) (a : IcosianQuaternion) :
    Pi.single i a∈rationalIcosianLattice ↔
      ∃ u : icosianOrder, a=2*u.val := by
  constructor
  · rintro ⟨x,hx,he⟩
    have hxi : (x i).val=a := by
      simpa [icosianCoordinateEmbedding] using congrFun he i
    have hsingle : x=icosianSingle i (x i) := by
      funext j
      apply Subtype.ext
      have hj := congrFun he j
      by_cases hji : j=i
      · subst j; simp [icosianSingle]
      · simpa [icosianCoordinateEmbedding,icosianSingle,Pi.single_apply,hji] using hj
    change x∈icosianLeechModule at hx
    rw [hsingle,icosianSingle_mem] at hx
    obtain ⟨u,hu⟩ := (icosianModuloTwo_eq_zero_iff_two_mul (x i)).mp hx
    refine ⟨u,?_⟩
    rw [← hxi,hu]
    rfl
  · rintro ⟨u,rfl⟩
    refine ⟨icosianSingle i (2*u),?_,?_⟩
    · change icosianSingle i (2*u)∈icosianLeechModule
      rw [icosianSingle_mem,icosianModuloTwo_eq_zero_iff_two_mul]
      exact ⟨u,rfl⟩
    · exact icosianCoordinateEmbedding_single i (2*u)

end Atlas.Lattices
