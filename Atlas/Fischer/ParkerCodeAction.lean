import Atlas.Fischer.ParkerGolayFactorSet
import Atlas.Mathieu.GolayAutomorphisms

namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

def parkerCodeEquiv (g : Mathieu24CodeModel) : golay ≃ₗ[Bit] golay where
  toFun a := ⟨coordinatePermutation g.val a.val, (g.property a.val).mp a.property⟩
  invFun a := ⟨coordinatePermutation g.val⁻¹ a.val,
    ((g⁻¹).property a.val).mp a.property⟩
  left_inv a := by
    apply Subtype.ext
    change coordinatePermutation g.val⁻¹ (coordinatePermutation g.val a.val) = a.val
    rw [← coordinatePermutation_mul, inv_mul_cancel, coordinatePermutation_one]
  right_inv a := by
    apply Subtype.ext
    change coordinatePermutation g.val (coordinatePermutation g.val⁻¹ a.val) = a.val
    rw [← coordinatePermutation_mul, mul_inv_cancel, coordinatePermutation_one]
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r a := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem parkerCodeEquiv_coe (g : Mathieu24CodeModel) (a : golay) :
    (parkerCodeEquiv g a : BinaryWord) = coordinatePermutation g.val a.val := rfl

theorem parkerCodeEquiv_weight (g : Mathieu24CodeModel) (a : golay) :
    hammingNorm (parkerCodeEquiv g a : BinaryWord) = hammingNorm a.val :=
  coordinatePermutation_weight g.val a.val

theorem parkerCodeEquiv_triple (g : Mathieu24CodeModel) (a b c : golay) :
    parkerTripleIntersection (parkerCodeEquiv g a) (parkerCodeEquiv g b)
      (parkerCodeEquiv g c) = parkerTripleIntersection a b c := by
  exact Equiv.sum_comp g.val.symm (fun p => a.val p * b.val p * c.val p)

@[simp] theorem parkerCodeEquiv_one (a : golay) : parkerCodeEquiv 1 a = a := by
  apply Subtype.ext
  rfl

theorem parkerCodeEquiv_mul (g h : Mathieu24CodeModel) (a : golay) :
    parkerCodeEquiv (g * h) a = parkerCodeEquiv g (parkerCodeEquiv h a) := by
  apply Subtype.ext
  rfl

theorem parkerGolay_coordinates_separate (p q : Omega)
    (h : ∀ a : golay, a.val p = a.val q) : p = q := by
  classical
  by_contra hpq
  let w : BinaryWord := Pi.single p 1 + Pi.single q 1
  have hw : w ∈ golay := by
    rw [golay_selfDual]
    intro a ha
    have he := h ⟨a, ha⟩
    change a p = a q at he
    have hb : ∀ x : Bit, x + x = 0 := by decide
    simpa [w, binaryDot_apply, mul_add, Pi.single_apply, mul_ite,
      Finset.sum_add_distrib, he, hb]
  have hw0 : w ≠ 0 := by
    intro hz
    have he := congrFun hz p
    simp [w, Pi.single_apply, hpq, Ne.symm hpq] at he
  have hbound := binary_weight_add (Pi.single p 1 : BinaryWord) (Pi.single q 1)
  have hsingle : ∀ r : Omega, hammingNorm (Pi.single r (1 : Bit) : BinaryWord) = 1 := by
    intro r
    simp [hammingNorm, Pi.single_apply]
    have he : (Finset.univ.filter (fun x : Omega => x = r)) = {r} := by ext; simp
    rw [he]
    rfl
  rw [hsingle p, hsingle q] at hbound
  have hmin := golay_minimum w hw hw0
  change 8 ≤ hammingNorm ((Pi.single p (1 : Bit) : BinaryWord) + Pi.single q 1) at hmin
  omega

theorem parkerCodeEquiv_faithful (g h : Mathieu24CodeModel)
    (he : ∀ a, parkerCodeEquiv g a = parkerCodeEquiv h a) : g = h := by
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro p
  apply parkerGolay_coordinates_separate
  intro a
  exact congrArg (fun z : golay => z.val p) (he a)

end Atlas.Fischer
