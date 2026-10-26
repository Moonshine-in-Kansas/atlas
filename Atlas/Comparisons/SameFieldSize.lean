import Atlas.LinearGroups.Unitary.BaseFieldTransport
import Atlas.LinearGroups.Orthogonal.Minus.FieldTransport
import Atlas.LinearGroups.Orthogonal.Minus.Family
import Atlas.LinearGroups.Triality.FieldTransport
import Atlas.LinearGroups.PSLFieldTransport
import Atlas.LinearGroups.Symplectic.FieldTransport
import Atlas.LinearGroups.Orthogonal.BFamilyTransport
import Atlas.LinearGroups.Orthogonal.DFamilyTransport
import Atlas.LinearGroups.G2.FieldTransport
import Atlas.LinearGroups.F4.FieldTransport
import Atlas.LinearGroups.SuzukiFamily.FieldTransport
import Atlas.LinearGroups.ReeG2.FieldTransport

/-! Field-independence is proved by transport of the actual coordinates, never by
recognition from the group cardinality. -/
noncomputable section
namespace Atlas.Comparisons.SameFieldSize

variable {F K E L : Type*} [Field F] [Field K] [Field E] [Field L]
  [Finite F] [Finite K] [Finite E] [Finite L]

def fieldEquiv (h : Nat.card F = Nat.card E) : F ≃+* E := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite E
  exact FiniteField.ringEquivOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using h)

section Extension
variable [Algebra F K] [Algebra E L]

private def restrictedHom (f : K ≃+* L)
    (h : ∀ a : F, ∃ b : E, algebraMap E L b = f (algebraMap F K a)) : F →+* E where
  toFun a := Classical.choose (h a)
  map_one' := by
    apply (algebraMap E L).injective
    rw [Classical.choose_spec (h 1), map_one, map_one, map_one]
  map_mul' a b := by
    apply (algebraMap E L).injective
    rw [Classical.choose_spec (h (a*b)), map_mul, map_mul, map_mul,
      Classical.choose_spec (h a), Classical.choose_spec (h b)]
  map_zero' := by
    apply (algebraMap E L).injective
    rw [Classical.choose_spec (h 0), map_zero, map_zero, map_zero]
  map_add' a b := by
    apply (algebraMap E L).injective
    rw [Classical.choose_spec (h (a+b)), map_add, map_add, map_add,
      Classical.choose_spec (h a), Classical.choose_spec (h b)]

private theorem restrictedHom_compat (f : K ≃+* L)
    (h : ∀ a : F, ∃ b : E, algebraMap E L b = f (algebraMap F K a)) (a : F) :
    algebraMap E L (restrictedHom f h a) = f (algebraMap F K a) :=
  Classical.choose_spec (h a)

private def restrictedEquiv (f : K ≃+* L)
    (h : ∀ a : F, ∃ b : E, algebraMap E L b = f (algebraMap F K a))
    (hi : ∀ b : E, ∃ a : F, algebraMap F K a = f.symm (algebraMap E L b)) : F ≃+* E :=
  RingEquiv.ofBijective (restrictedHom f h) ⟨(restrictedHom f h).injective, by
    intro b
    obtain ⟨a, ha⟩ := hi b
    refine ⟨a, (algebraMap E L).injective ?_⟩
    rw [restrictedHom_compat, ha, f.apply_symm_apply]⟩

private theorem quadratic_image (hL : Module.finrank E L = 2)
    (f : K ≃+* L) (hc : Nat.card F = Nat.card E) (a : F) :
    ∃ b : E, algebraMap E L b = f (algebraMap F K a) := by
  apply (Atlas.FiniteQuadratic.conjugation_fixed_iff hL _).mp
  rw [Atlas.FiniteQuadratic.conjugation_apply, ← hc, ← map_pow, ← map_pow]
  congr 2
  let := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a

private theorem cubic_image (hL : Module.finrank E L = 3)
    (f : K ≃+* L) (hc : Nat.card F = Nat.card E) (a : F) :
    ∃ b : E, algebraMap E L b = f (algebraMap F K a) := by
  apply (Atlas.FiniteCubic.sigma_fixed_iff hL _).mp
  rw [Atlas.FiniteCubic.sigma_apply, ← hc, ← map_pow, ← map_pow]
  congr 2
  let := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a

def minusEquiv (hK : Module.finrank F K = 2) (hL : Module.finrank E L = 2)
    (hc : Nat.card F = Nat.card E) (r : ℕ) :
    Atlas.Orthogonal.DMinus r F K hK ≃* Atlas.Orthogonal.DMinus r E L hL := by
  let f : K ≃+* L := Atlas.Unitary.quadraticFieldEquivOfBaseCardEq hK hL hc
  let e : F ≃+* E := restrictedEquiv f (quadratic_image hL f hc)
    (quadratic_image hK f.symm hc.symm)
  exact Atlas.Orthogonal.Minus.fieldEquivProjective e f
    (fun a => (restrictedHom_compat f (quadratic_image hL f hc) a).symm) hK hL (r-1)

def trialityEquiv (hK : Module.finrank F K = 3) (hL : Module.finrank E L = 3)
    (hc : Nat.card F = Nat.card E) : Atlas.Triality.Group F K ≃* Atlas.Triality.Group E L := by
  have hext : Nat.card K = Nat.card L := by
    rw [Atlas.FiniteCubic.card_extension hK, Atlas.FiniteCubic.card_extension hL, hc]
  let f : K ≃+* L := fieldEquiv hext
  let e : F ≃+* E := restrictedEquiv f (cubic_image hL f hc)
    (cubic_image hK f.symm hc.symm)
  exact Atlas.Triality.fieldEquiv e f
    (fun a => (restrictedHom_compat f (cubic_image hL f hc) a).symm)

end Extension
end Atlas.Comparisons.SameFieldSize
