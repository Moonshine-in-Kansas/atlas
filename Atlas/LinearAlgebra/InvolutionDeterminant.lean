import Atlas.LinearAlgebra.InvolutionEigenspaceRestrictions
import Mathlib.LinearAlgebra.Determinant

/-! # Determinant of an involution from its actual minus eigenspace -/
noncomputable section
namespace Atlas.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem determinant (t : V →ₗ[F] V) (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    t.det = (-1 : F) ^ Module.finrank F (minus t) := by
  let e := decomposition t ht h2
  let f : (plus t × minus t) →ₗ[F] (plus t × minus t) :=
    LinearMap.prodMap LinearMap.id ((-1 : F) • LinearMap.id)
  have he : e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap = t := by
    ext x
    obtain ⟨⟨p,m⟩,rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    simp only [f, LinearMap.prodMap_apply, LinearMap.id_apply, neg_one_smul]
    change e (p,-m) = t (decomposition t ht h2 (p,m))
    rw [decomposition_action]
    change p.val + (-m).val = p.val - m.val
    simp [sub_eq_add_neg]
  have hd := LinearMap.det_conj f e
  rw [he] at hd
  change t.det = f.det at hd
  rw [hd, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id]
  simp
theorem even_finrank_minus_of_det_one (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) (hd : t.det = 1) :
    Even (Module.finrank F (minus t)) := by
  have hn : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  apply (neg_one_pow_eq_one_iff_even hn).mp
  rw [← determinant t ht h2, hd]

theorem finrank_minus_pos_of_ne_id (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) (hn : t ≠ LinearMap.id) :
    0 < Module.finrank F (minus t) := by
  by_contra h
  have hz : Module.finrank F (minus t) = 0 := by omega
  have hb : minus t = ⊥ := Submodule.finrank_eq_zero.mp hz
  apply hn
  ext x
  obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition t ht h2).surjective x
  have hm : m.val = 0 := by
    exact (show minus t ≤ ⊥ from le_of_eq hb) m.prop
  rw [decomposition_action]
  change p.val - m.val = p.val + m.val
  simp [hm]

theorem two_le_finrank_minus_of_det_one (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0)
    (hd : t.det = 1) (hn : t ≠ LinearMap.id) :
    2 ≤ Module.finrank F (minus t) := by
  have hp := finrank_minus_pos_of_ne_id t ht h2 hn
  obtain ⟨k,hk⟩ := even_finrank_minus_of_det_one t ht h2 hd
  omega

end Atlas.LinearInvolution

