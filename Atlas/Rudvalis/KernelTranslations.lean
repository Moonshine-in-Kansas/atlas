import Atlas.Rudvalis.UniformKernelAction
import Atlas.Rudvalis.KernelLinearTrivial

namespace Atlas.Rudvalis

theorem block_kernel_row_translations (g : binaryPermutationGroup)
    (hg : binaryBlockHom g=1) : ∃ t : Point → E,
      ∀ p x, g.val (p,x)=(p,x+t p) := by
  obtain ⟨A,t,hact⟩ := block_kernel_uniform_linearEquiv g hg
  have hA := blockFixed_common_linear_trivial g hg A t hact
  subst A
  exact ⟨t,hact⟩

theorem translation_polar_linear (g : binaryPermutationGroup)
    (hg : binaryBlockHom g=1) (t : Point → E)
    (hact : ∀ p x, g.val (p,x)=(p,x+t p)) (c : E) :
    ∃ M : BinaryMatrix, ∀ p x, polar c (t p) x = dot (matrixAt M p.val) x := by
  by_cases hc : c=0
  · refine ⟨0,?_⟩
    intro p x
    simp [hc,polar,dot,matrixAt]
  obtain ⟨a,ha,hw⟩ := quadratic_minimum_exists c hc
  obtain ⟨d,hd⟩ := (g.prop (binaryNormalMap a)).mp ⟨a,rfl⟩
  have hdc : d.2.2=c := (blockFixed_minimum_quadratic_class g hg a d
    (ha.symm ▸ hc) hw hd).trans ha
  have he (p : Point) (x : E) :
      d.1 p + dot (matrixAt d.2.1 p.val) x + theta p c x =
      a.1 p + dot (matrixAt a.2.1 p.val) (x+t p) + theta p c (x+t p) := by
    have h := congrFun hd (p,x)
    rw [Function.comp_apply,hact] at h
    change d.1 p + dot (matrixAt d.2.1 p.val) x + theta p d.2.2 x =
      a.1 p + dot (matrixAt a.2.1 p.val) (x+t p) + theta p a.2.2 (x+t p) at h
    simpa only [ha,hdc] using h
  refine ⟨d.2.1+a.2.1,?_⟩
  intro p x
  have hx := he p x
  have hz := he p 0
  have htheta0 : theta p c 0=0 := by simp [theta,quadratic,dot]
  have hdot0 (b : E) : dot b 0=0 := by simp [dot]
  simp only [zero_add,hdot0,htheta0,add_zero] at hz
  rw [dot_add_right,theta_translate,hz] at hx
  rw [matrixAt_add,dot_add_left]
  have hh : ∀ a b d e f k v : Bit,
      (a+b+d)+e+f=a+(k+b)+(f+d+v) → v=e+k := by decide +kernel
  exact hh _ _ _ _ _ _ _ hx


theorem polar_linear_reconstruction (t : Point → E)
    (ht : ∀ c : E, ∃ M : BinaryMatrix, ∀ p x,
      polar c (t p) x = dot (matrixAt M p.val) x) :
    ∃ A : BinaryMatrix, ∀ p : Point, t p = matrixAt A p.val := by
  obtain ⟨M0,h0⟩ := ht (basisPoint 0).val
  obtain ⟨M1,h1⟩ := ht (basisPoint 1).val
  let A : BinaryMatrix := ![M1 2,M0 2,M0 1]
  refine ⟨A,?_⟩
  intro p
  ext i
  fin_cases i
  · have h := h1 p (basisPoint 2).val
    simpa [polar,dot,matrixAt,basisPoint,binaryLabel,A,Fin.sum_univ_succ] using h
  · have h := h0 p (basisPoint 2).val
    simpa [polar,dot,matrixAt,basisPoint,binaryLabel,A,Fin.sum_univ_succ] using h
  · have h := h0 p (basisPoint 1).val
    simpa [polar,dot,matrixAt,basisPoint,binaryLabel,A,Fin.sum_univ_succ] using h

theorem block_kernel_translation (g : binaryPermutationGroup)
    (hg : binaryBlockHom g=1) :
    ∃ A : BinaryMatrix, g=coordinateTranslationHom (Multiplicative.ofAdd A) := by
  obtain ⟨t,hact⟩ := block_kernel_row_translations g hg
  obtain ⟨A,hA⟩ := polar_linear_reconstruction t (translation_polar_linear g hg t hact)
  refine ⟨A,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨p,x⟩
  change g.val (p,x)=(p,x+matrixAt A p.val)
  rw [hact,hA]

theorem binaryBlockHom_kernel_translations :
    binaryBlockHom.ker = binaryTranslationSubgroup := by
  ext g
  constructor
  · intro hg
    obtain ⟨A,hA⟩ := block_kernel_translation g (MonoidHom.mem_ker.mp hg)
    exact ⟨Multiplicative.ofAdd A,hA.symm⟩
  · rintro ⟨A,rfl⟩
    exact MonoidHom.mem_ker.mpr (coordinateTranslation_block_trivial A.toAdd)

theorem binaryBlockHom_kernel_order : Nat.card binaryBlockHom.ker = 512 := by
  rw [binaryBlockHom_kernel_translations]
  exact binaryTranslationSubgroup_order

end Atlas.Rudvalis

