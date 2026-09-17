import Atlas.LinearGroups.Symplectic.Basic
import Atlas.LinearAlgebra.SymplecticBasis
import Atlas.LinearAlgebra.LinearFunctionalFiber

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

abbrev HyperbolicPairs (n : ℕ) (F : Type*) [Field F] :=
  {p : Vector n F × Vector n F // form p.1 p.2 = 1}

/-- Count first vectors and normalized partners, before any group-order calculation. -/
def pairFiberEquiv : HyperbolicPairs n F ≃
    Σ e : {v : Vector n F // v ≠ 0}, {f : Vector n F // form e.val f = 1} where
  toFun p := ⟨⟨p.val.1,by intro h; simpa [h] using p.prop⟩,⟨p.val.2,p.prop⟩⟩
  invFun p := ⟨(p.1.val,p.2.val),p.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vector_finrank : Module.finrank F (Vector n F) = 2*n := by
  simp [Vector,Index,Module.finrank_pi, Fintype.card_sum, two_mul]

theorem partner_card [Finite F] {e : Vector n F} (he : e ≠ 0) :
    Nat.card {f : Vector n F // form e f = 1} = Nat.card F ^ (2*n-1) := by
  obtain ⟨v,hv⟩ := Atlas.AlternatingForm.exists_partner form form_nondegenerate he
  simpa only [vector_finrank] using Atlas.LinearFunctional.card_fiber (form e) v hv 1

theorem nonzero_vector_card [Finite F] :
    Nat.card {v : Vector n F // v ≠ 0} = Nat.card F ^ (2*n)-1 := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc : Fintype.card (Vector n F) = Nat.card F ^ (2*n) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F), vector_finrank]
  rw [hc, Fintype.card_unique]

theorem hyperbolicPairs_card [Finite F] :
    Nat.card (HyperbolicPairs n F) = (Nat.card F ^ (2*n)-1) * Nat.card F ^ (2*n-1) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr pairFiberEquiv, Nat.card_sigma]
  have hs : (∑ e : {v : Vector n F // v ≠ 0}, Nat.card {f : Vector n F // form e.val f = 1}) =
      ∑ _e : {v : Vector n F // v ≠ 0}, Nat.card F ^ (2*n-1) := by
    apply Finset.sum_congr rfl
    intro e _
    exact partner_card e.prop
  rw [hs]
  rw [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,← Nat.card_eq_fintype_card,
    nonzero_vector_card]
  simp
end Atlas.Symplectic
