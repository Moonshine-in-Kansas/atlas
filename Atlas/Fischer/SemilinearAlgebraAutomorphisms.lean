import Atlas.Fischer.ParkerCoordinateAction
import Atlas.Fischer.CoordinateProduct

namespace Atlas.Fischer
open Atlas.Codes

/-- Untagged permutations of the actual coordinate space preserving addition,
the nonassociative product, and one of the two scalar automorphisms. -/
def IsSemilinearAlgebraAutomorphism (e : Equiv.Perm Coordinates) : Prop :=
  (∀ x y, e (x + y) = e x + e y) ∧
  (∀ x y, e (product x y) = product (e x) (e y)) ∧
  ∃ b : Bit, ∀ r x, e (r • x) = scalarParityAut b r • e x

def semilinearAlgebraAutomorphisms : Subgroup (Equiv.Perm Coordinates) where
  carrier := IsSemilinearAlgebraAutomorphism
  one_mem' := by
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, 0, ?_⟩
    intro r x
    simp
  mul_mem' := by
    rintro e f ⟨he, hpe, b, hse⟩ ⟨hf, hpf, c, hsf⟩
    refine ⟨?_, ?_, b + c, ?_⟩
    · intro x y
      change e (f (x + y)) = _
      rw [hf, he]
      rfl
    · intro x y
      change e (f (product x y)) = _
      rw [hpf, hpe]
      rfl
    · intro r x
      change e (f (r • x)) = _
      rw [hsf, hse, scalarParityAut_add]
      rfl
  inv_mem' := by
    rintro e ⟨he, hp, b, hs⟩
    refine ⟨?_, ?_, b, ?_⟩
    · intro x y
      apply e.injective
      change e (e.symm (x + y)) = e (e.symm x + e.symm y)
      rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]
    · intro x y
      apply e.injective
      change e (e.symm (product x y)) = e (product (e.symm x) (e.symm y))
      rw [e.apply_symm_apply, hp, e.apply_symm_apply, e.apply_symm_apply]
    · intro r x
      apply e.injective
      change e (e.symm (r • x)) = e (scalarParityAut b r • e.symm x)
      rw [e.apply_symm_apply, hs, scalarParityAut_involutive, e.apply_symm_apply]

abbrev SemilinearAlgebraAutomorphism := semilinearAlgebraAutomorphisms

theorem coordinateVector_ne_zero (i : CoordinateIndex) : coordinateVector i ≠ 0 := by
  classical
  intro h
  have hi := congrFun h i
  simpa [coordinateVector, Pi.single_apply] using hi

theorem semilinearAlgebra_map_zero (e : SemilinearAlgebraAutomorphism) : e.val 0 = 0 := by
  have h : e.val 0 + 0 = e.val 0 + e.val 0 := by simpa using e.property.1 0 0
  exact (add_left_cancel h).symm

theorem scalarParityAut_unique (e : Equiv.Perm Coordinates) (hz : e 0 = 0) (b c : Bit)
    (hb : ∀ r x, e (r • x) = scalarParityAut b r • e x)
    (hc : ∀ r x, e (r • x) = scalarParityAut c r • e x) : b = c := by
  have hbit : ∀ s : Bit, s = 0 ∨ s = 1 := by decide
  have hn : omega ≠ star omega := by
    intro h
    have ht : theta = 0 := sub_eq_zero.mpr h
    have hh := theta_sq
    rw [ht] at hh
    norm_num at hh
  have he (h0 : ∀ r x, e (r • x) = scalarParityAut 0 r • e x)
      (h1 : ∀ r x, e (r • x) = scalarParityAut 1 r • e x) : False := by
    let i : CoordinateIndex := Sum.inl (Classical.arbitrary Omega)
    have hx : e (coordinateVector i) ≠ 0 := by
      intro hx
      exact coordinateVector_ne_zero i (e.injective (hx.trans hz.symm))
    have hh := (h0 omega (coordinateVector i)).symm.trans (h1 omega (coordinateVector i))
    simp only [scalarParityAut_zero, scalarParityAut_one] at hh
    exact hn ((smul_left_injective Scalar hx) hh)
  rcases hbit b with rfl | rfl <;> rcases hbit c with rfl | rfl
  · rfl
  · exact (he hb hc).elim
  · exact (he hc hb).elim
  · rfl

noncomputable def semilinearAlgebraParity (e : SemilinearAlgebraAutomorphism) : Bit :=
  Classical.choose e.property.2.2

theorem semilinearAlgebraParity_spec (e : SemilinearAlgebraAutomorphism) (r : Scalar)
    (x : Coordinates) : e.val (r • x) = scalarParityAut (semilinearAlgebraParity e) r • e.val x :=
  Classical.choose_spec e.property.2.2 r x

theorem semilinearAlgebraParity_unique (e : SemilinearAlgebraAutomorphism) (b : Bit)
    (hb : ∀ r x, e.val (r • x) = scalarParityAut b r • e.val x) :
    semilinearAlgebraParity e = b :=
  scalarParityAut_unique e.val (semilinearAlgebra_map_zero e) _ _
    (semilinearAlgebraParity_spec e) hb

noncomputable def semilinearAlgebraParityHom : SemilinearAlgebraAutomorphism →* Multiplicative Bit where
  toFun e := Multiplicative.ofAdd (semilinearAlgebraParity e)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change semilinearAlgebraParity 1 = 0
    apply semilinearAlgebraParity_unique
    intro r x
    simp
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    change semilinearAlgebraParity (e * f) = semilinearAlgebraParity e + semilinearAlgebraParity f
    apply semilinearAlgebraParity_unique
    intro r x
    change e.val (f.val (r • x)) = _
    rw [semilinearAlgebraParity_spec f, semilinearAlgebraParity_spec e, scalarParityAut_add]
    rfl

noncomputable def linearAlgebraAutomorphisms : Subgroup SemilinearAlgebraAutomorphism :=
  semilinearAlgebraParityHom.ker

theorem linearAlgebraAutomorphisms_iff (e : SemilinearAlgebraAutomorphism) :
    e ∈ linearAlgebraAutomorphisms ↔ ∀ (r : Scalar) (x : Coordinates), e.val (r • x) = r • e.val x := by
  change semilinearAlgebraParity e = 0 ↔ _
  constructor
  · intro h r x
    simpa only [h, scalarParityAut_zero] using semilinearAlgebraParity_spec e r x
  · intro h
    apply semilinearAlgebraParity_unique
    intro r x
    simpa only [scalarParityAut_zero] using h r x

end Atlas.Fischer
