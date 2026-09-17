import Atlas.Fischer.SignedOctads
import Mathlib.Algebra.Star.Basic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Scalar conjugation as an actual automorphism of the retained quadratic field. -/
def scalarConjugationEquiv : Scalar ≃+* Scalar := {
  starRingEnd Scalar with
  invFun := star
  left_inv := star_star
  right_inv := star_star }

/-- The scalar automorphism prescribed by the actual parity bit. -/
def scalarParityAut (b : Bit) : Scalar ≃+* Scalar :=
  if b=0 then RingEquiv.refl Scalar else scalarConjugationEquiv

@[simp] theorem scalarParityAut_zero (z : Scalar) : scalarParityAut 0 z=z := by
  simp [scalarParityAut]

@[simp] theorem scalarParityAut_one (z : Scalar) : scalarParityAut 1 z=star z := by
  simp [scalarParityAut,scalarConjugationEquiv,starRingEnd_apply]

@[simp] theorem scalarParityAut_involutive (b : Bit) (z : Scalar) :
    scalarParityAut b (scalarParityAut b z)=z := by
  by_cases hb : b=0 <;> simp [scalarParityAut,hb,scalarConjugationEquiv,starRingEnd_apply]

instance scalarParityAut_invPair (b : Bit) : RingHomInvPair
    (scalarParityAut b).toRingHom (scalarParityAut b).toRingHom :=
  ⟨by apply RingHom.ext; intro z; exact scalarParityAut_involutive b z,
   by apply RingHom.ext; intro z; exact scalarParityAut_involutive b z⟩

@[simp] theorem scalarParityAut_star (b : Bit) (z : Scalar) :
    scalarParityAut b (star z)=star (scalarParityAut b z) := by
  by_cases hb : b=0 <;> simp [scalarParityAut,hb,scalarConjugationEquiv,starRingEnd_apply]

@[simp] theorem scalarParityAut_rat (b : Bit) (q : ℚ) : scalarParityAut b (q : Scalar)=q :=
  map_ratCast (scalarParityAut b) q

@[simp] theorem parkerScalarSign_square (s : Bit) : parkerScalarSign s*parkerScalarSign s=1 := by
  by_cases hs : s=0 <;> simp [parkerScalarSign,hs]

@[simp] theorem parkerScalarSign_star (s : Bit) : star (parkerScalarSign s)=parkerScalarSign s := by
  by_cases hs : s=0 <;> simp [parkerScalarSign,hs]

@[simp] theorem scalarParityAut_sign (b s : Bit) :
    scalarParityAut b (parkerScalarSign s)=parkerScalarSign s := by
  by_cases hs : s=0 <;> simp [parkerScalarSign,hs]

theorem scalarParityAut_add (b c : Bit) (z : Scalar) :
    scalarParityAut (b+c) z=scalarParityAut b (scalarParityAut c z) := by
  have hc : ∀ a : Bit, a=0 ∨ a=1 := by decide
  rcases hc b with rfl | rfl <;> rcases hc c with rfl | rfl <;>
    simp only [zero_add,add_zero,show (1 : Bit)+1=0 from rfl,
      scalarParityAut_zero,scalarParityAut_one,star_star]

/-- Arbitrary signed monomial semilinear changes of exact coordinates. Signs
are attached to the source coordinate, matching the marked Parker action. -/
def parkerSignedMonomial {ι : Type*} (b : Bit) (p : Equiv.Perm ι) (s : ι → Bit) :
    (ι → Scalar) ≃ₛₗ[(scalarParityAut b).toRingHom] (ι → Scalar) where
  toFun x i := parkerScalarSign (s (p.symm i))*scalarParityAut b (x (p.symm i))
  invFun y i := parkerScalarSign (s i)*scalarParityAut b (y (p i))
  left_inv x := by
    funext i
    simp only [p.symm_apply_apply,map_mul,scalarParityAut_sign,scalarParityAut_involutive]
    rw [← mul_assoc,parkerScalarSign_square,one_mul]
  right_inv y := by
    funext i
    simp only [p.apply_symm_apply,map_mul,scalarParityAut_sign,scalarParityAut_involutive]
    rw [← mul_assoc,parkerScalarSign_square,one_mul]
  map_add' x y := by
    funext i
    simp only [Pi.add_apply,map_add,mul_add]
  map_smul' r x := by
    funext i
    change parkerScalarSign (s (p.symm i))*scalarParityAut b (r*x (p.symm i))=
      scalarParityAut b r*(parkerScalarSign (s (p.symm i))*scalarParityAut b (x (p.symm i)))
    rw [map_mul]
    ring

@[simp] theorem parkerSignedMonomial_apply {ι : Type*} (b : Bit) (p : Equiv.Perm ι)
    (s : ι → Bit) (x : ι → Scalar) (i : ι) :
    parkerSignedMonomial b p s x i=
      parkerScalarSign (s (p.symm i))*scalarParityAut b (x (p.symm i)) := rfl

/-- Weighted Hermitian covariance is proved termwise and by reindexing the
actual coordinate permutation; no dense matrix certificate is used. -/
theorem parkerSignedMonomial_hermitian {ι : Type*} [Fintype ι]
    (b : Bit) (p : Equiv.Perm ι) (s : ι → Bit) (w : ι → ℚ)
    (hw : ∀ i, w (p i)=w i) (x y : ι → Scalar) :
    weightedHermitian w (parkerSignedMonomial b p s x) (parkerSignedMonomial b p s y)=
      scalarParityAut b (weightedHermitian w x y) := by
  unfold weightedHermitian
  calc
    _ = ∑ i, scalarParityAut b ((w (p.symm i) : Scalar)*x (p.symm i)*star (y (p.symm i))) := by
      apply Finset.sum_congr rfl
      intro i _
      have hwi : w (p.symm i)=w i := by simpa using (hw (p.symm i)).symm
      simp only [parkerSignedMonomial_apply,map_mul,scalarParityAut_rat,
        scalarParityAut_star,star_mul,parkerScalarSign_star,hwi]
      calc
        _ = (parkerScalarSign (s (p.symm i))*parkerScalarSign (s (p.symm i)))*
          ((w i : Scalar)*scalarParityAut b (x (p.symm i))*star (scalarParityAut b (y (p.symm i)))) := by ring
        _ = _ := by rw [parkerScalarSign_square,one_mul]
    _ = ∑ i, scalarParityAut b ((w i : Scalar)*x i*star (y i)) :=
      Equiv.sum_comp p.symm (fun i => scalarParityAut b ((w i : Scalar)*x i*star (y i)))
    _ = _ := (map_sum (scalarParityAut b) _ _).symm


theorem scalarParityAut_theta (b : Bit) : scalarParityAut b theta=parkerScalarSign b*theta := by
  have hc : ∀ a : Bit, a=0 ∨ a=1 := by decide
  rcases hc b with rfl | rfl
  · simp [parkerScalarSign]
  · rw [scalarParityAut_one,theta_conjugate]
    simp [parkerScalarSign]


@[simp] theorem parkerSignedMonomial_one {ι : Type*} (x : ι → Scalar) :
    parkerSignedMonomial 0 (1 : Equiv.Perm ι) (fun _ => 0) x=x := by
  funext i
  change parkerScalarSign 0*scalarParityAut 0 (x i)=x i
  simp [parkerScalarSign]

/-- Composition follows the actual source-coordinate sign rule. -/
theorem parkerSignedMonomial_comp {ι : Type*} (b c : Bit) (p q : Equiv.Perm ι)
    (s t : ι → Bit) (x : ι → Scalar) :
    parkerSignedMonomial (b+c) (p*q) (fun i => s (q i)+t i) x=
      parkerSignedMonomial b p s (parkerSignedMonomial c q t x) := by
  funext i
  change parkerScalarSign (s (q (q.symm (p.symm i)))+t (q.symm (p.symm i)))*
      scalarParityAut (b+c) (x (q.symm (p.symm i)))=
    parkerScalarSign (s (p.symm i))*scalarParityAut b
      (parkerScalarSign (t (q.symm (p.symm i)))*scalarParityAut c (x (q.symm (p.symm i))))
  rw [q.apply_symm_apply,parkerScalarSign_add,scalarParityAut_add,map_mul,
    scalarParityAut_sign,mul_assoc]


@[simp] theorem parkerScalarSign_eq_one_iff (s : Bit) : parkerScalarSign s=1 ↔ s=0 := by
  by_cases hs : s=0
  · simp [parkerScalarSign,hs]
  · simp only [parkerScalarSign,if_neg hs,hs,iff_false]
    intro h
    have he := congrArg (fun z : Scalar => z.re) h
    change (-1 : ℚ)=1 at he
    norm_num at he

end Atlas.Fischer
