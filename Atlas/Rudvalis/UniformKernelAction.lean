import Atlas.Rudvalis.FanoBlockAffine
import Atlas.Rudvalis.UniformBlockLinear

/-! Uniform affine action of the intrinsic block kernel on the actual weave. -/
namespace Atlas.Rudvalis

theorem affine_coefficients_unique (a d : Bit) (b e : E)
    (h : ∀ x : E, a + dot b x = d + dot e x) : b = e := by
  have hz : b+e=0 := (affine_quadratic_zero (a+d) (b+e) 0 (by
    intro x
    rw [dot_add_left]
    have hq : quadratic (0 : E) x = 0 := by simp [quadratic]
    rw [hq,add_zero]
    calc
      a+d+(dot b x+dot e x) = (a+dot b x)+(d+dot e x) := by ring
      _ = 0 := by rw [h x]; exact Atlas.Codes.bit_self_add _)).2.1
  have he := congrArg (fun v : E => v+e) hz
  simpa only [add_assoc,vector_add_self,add_zero,zero_add] using he

theorem bilinear_affine_evaluation (b u : E) (A : BinaryMatrix) (t x : E) (p : Point) :
    binaryNormalMap (0,outerMatrix b u,0) (p,matrixAt A x+t) =
      dot u p.val * dot b t + dot (dot u p.val • matrixAt A.transpose b) x := by
  change 0 + dot (matrixAt (outerMatrix b u) p.val) (matrixAt A x+t) +
    theta p 0 (matrixAt A x+t) = _
  have ht : theta p 0 (matrixAt A x+t) = 0 := by simp [theta,eta,quadratic,dot]
  rw [zero_add,ht,add_zero,matrixAt_outer,dot_smul_left,dot_smul_left,dot_add_right]
  rw [dot_comm b (matrixAt A x),matrixAt_transpose_pair]
  ring

theorem block_kernel_uniform_affine (g : binaryPermutationGroup)
    (hg : binaryBlockHom g = 1) :
    ∃ A : BinaryMatrix, ∃ t : Point → E, IsUnit A ∧
      ∀ p : Point, ∀ x : E, g.val (p,x) = (p,matrixAt A x+t p) := by
  classical
  choose A t hunit hlocal using binaryPermutation_block_affine g
  have hcoords (p : Point) (x : E) : g.val (p,x) = (p,matrixAt (A p) x+t p) := by
    apply Prod.ext
    · have he := binaryBlockPermutation_coordinates g (p,x)
      change (g.val (p,x)).1 = binaryBlockHom g p at he
      simpa [hg] using he
    · exact hlocal p x
  have hcoeff (b u : E) : ∃ M : BinaryMatrix, ∀ p : Point,
      dot u p.val • matrixAt (A p).transpose b = matrixAt M p.val := by
    have hw : binaryNormalMap (0,outerMatrix b u,0) ∈ binaryResidue := ⟨_,rfl⟩
    obtain ⟨a,ha⟩ := (g.prop _).mp hw
    have hrow (p : Point) (x : E) : binaryNormalMap a (p,x) =
        dot u p.val * dot b (t p) + dot (dot u p.val • matrixAt (A p).transpose b) x := by
      have he := congrFun ha (p,x)
      change binaryNormalMap a (p,x) = binaryNormalMap (0,outerMatrix b u,0) (g.val (p,x)) at he
      rw [hcoords,bilinear_affine_evaluation] at he
      exact he
    have hc : a.2.2=0 := (normal_block_isAffineFunction_iff a (basisPoint 0)).mp
      ⟨_,_,hrow (basisPoint 0)⟩
    refine ⟨a.2.1,?_⟩
    intro p
    apply affine_coefficients_unique (dot u p.val * dot b (t p)) (a.1 p)
    intro x
    rw [← hrow]
    change a.1 p + dot (matrixAt a.2.1 p.val) x + theta p a.2.2 x = _
    simp [hc,theta,eta,quadratic,dot]
  have hsame := uniform_block_linear A hcoeff
  refine ⟨A (basisPoint 0),t,hunit (basisPoint 0),?_⟩
  intro p x
  rw [hcoords,hsame p (basisPoint 0)]


theorem block_kernel_uniform_linearEquiv (g : binaryPermutationGroup)
    (hg : binaryBlockHom g = 1) :
    ∃ A : E ≃ₗ[Bit] E, ∃ t : Point → E,
      ∀ p : Point, ∀ x : E, g.val (p,x) = (p,A x+t p) := by
  obtain ⟨M,t,hM,hact⟩ := block_kernel_uniform_affine g hg
  have hi : Function.Injective (binaryMatrixLinear M) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hM
  let A : E ≃ₗ[Bit] E := LinearEquiv.ofBijective (binaryMatrixLinear M)
    ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨A,t,hact⟩

end Atlas.Rudvalis

