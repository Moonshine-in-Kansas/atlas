import Atlas.Algebra.SplitOctonion.NormComposition
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-! The exact residual ambiguity of a split-octonion norm isometry on trace zero.
Fixing the unit removes it outside characteristic two; it does not remove it in
characteristic two. No multiplication-preservation or Spin comparison is assumed. -/
noncomputable section
namespace Atlas.SplitOctonion
variable {F : Type*} [Field F]

theorem normIsometry_traceKernel (g : Carrier F ≃ₗ[F] Carrier F)
    (hn : ∀x,norm (g x)=norm x)
    (hk : ∀x,trace x=0→g x=x) :
    (∀x,g x=x) ∨ (∀x,g x= -conjugate x) := by
  let w : Carrier F := g (basisVector 3)-basisVector 3
  have hshift (x : Carrier F) : g x=x+trace x • w := by
    have ht : trace (x-trace x • basisVector 3)=0 := by
      simp [trace,basisVector,Pi.single_apply]
    have h := hk (x-trace x • basisVector 3) ht
    rw [map_sub,map_smul] at h
    dsimp [w]
    rw [smul_sub]
    linear_combination h
  have h3 := hn (basisVector 3)
  rw [hshift] at h3
  simp [norm,trace,basisVector,Pi.single_apply] at h3
  have hw0 : w 0=0 := by
    have h := hn (basisVector 3+basisVector 7)
    rw [hshift] at h
    simp [norm,trace,basisVector,Pi.single_apply] at h
    linear_combination h-h3
  have hw1 : w 1=0 := by
    have h := hn (basisVector 3+basisVector 6)
    rw [hshift] at h
    simp [norm,trace,basisVector,Pi.single_apply] at h
    linear_combination h-h3
  have hw2 : w 2=0 := by
    have h := hn (basisVector 3+basisVector 5)
    rw [hshift] at h
    simp [norm,trace,basisVector,Pi.single_apply] at h
    linear_combination h-h3
  have hw5 : w 5=0 := by
    have h := hn (basisVector 3+basisVector 2)
    rw [hshift] at h
    simp [norm,trace,basisVector,Pi.single_apply] at h
    linear_combination h-h3
  have hw6 : w 6=0 := by
    have h := hn (basisVector 3+basisVector 1)
    rw [hshift] at h
    simp [norm,trace,basisVector,Pi.single_apply] at h
    linear_combination h-h3
  have hw7 : w 7=0 := by
    have h := hn (basisVector 3+basisVector 0)
    rw [hshift] at h
    simp [norm,trace,basisVector,Pi.single_apply] at h
    linear_combination h-h3
  have h4 := hn (basisVector 4)
  rw [hshift] at h4
  simp [norm,trace,basisVector,Pi.single_apply,hw0,hw1,hw2,hw5,hw6,hw7] at h4
  simp only [hw0,hw1,hw2,hw5,hw6,hw7,zero_mul,zero_add,add_zero] at h3
  have h4eq : w 3 * (1 + w 4) = 0 := mul_eq_zero.mpr h4
  have he : w 3=w 4 := by linear_combination h4eq-h3
  have hf : (w 3+1)*w 3=0 := by
    rw [←he] at h3
    simpa only [add_comm] using h3
  rcases mul_eq_zero.mp hf with hneg | hzero
  · right
    have hw : w= -unit := by
      have hn : w 3 = -1 := by linear_combination hneg
      ext i
      fin_cases i <;> simp [unit,hw0,hw1,hw2,hw5,hw6,hw7,←he,hn]
    intro x
    rw [hshift,hw]
    unfold conjugate
    module
  · left
    have hw : w=0 := by
      ext i
      fin_cases i <;> simp [hw0,hw1,hw2,hw5,hw6,hw7,←he,hzero]
    intro x
    rw [hshift,hw,smul_zero,add_zero]

theorem normIsometry_unit_traceKernel (g : Carrier F ≃ₗ[F] Carrier F)
    (hn : ∀x,norm (g x)=norm x) (hu : g unit=unit)
    (hk : ∀x,trace x=0→g x=x) :
    (∀x,g x=x) ∨ ((2 : F)=0 ∧ ∀x,g x=conjugate x) := by
  rcases normIsometry_traceKernel g hn hk with h | h
  · exact Or.inl h
  · right
    have he := h unit
    rw [hu] at he
    have hc := congrFun he 3
    simp [unit,conjugate,trace] at hc
    have h2 : (2 : F)=0 := by linear_combination hc
    refine ⟨h2,?_⟩
    letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    intro x
    rw [h]
    ext i
    exact CharTwo.neg_eq _

end Atlas.SplitOctonion
