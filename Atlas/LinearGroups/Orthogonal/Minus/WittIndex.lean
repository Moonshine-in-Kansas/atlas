import Atlas.LinearGroups.Orthogonal.Minus.StandardComplement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Maximal totally singular dimension in the actual
hyperbolic-plus-norm-plane model. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The upper bound retains vanishing of Q itself, including characteristic two. -/
theorem totallySingular_finrank_le (hdeg : Module.finrank F K = 2) (k : ℕ)
    (W : Submodule F (Vector k F K))
    (hW : ∀ x ∈ W, form hdeg k x = 0) : Module.finrank F W ≤ k := by
  classical
  induction k with
  | zero =>
    have hbot : W = ⊥ := by
      apply bot_unique
      intro x hx
      apply (Submodule.mem_bot F).mpr
      have hxD : x.1 = 0 := Subsingleton.elim _ _
      have hn := hW x hx
      rw [form_apply, hxD, map_zero, zero_add, ← normForm_apply hdeg] at hn
      exact Prod.ext hxD ((normForm_eq_zero_iff hdeg x.2).mp hn)
    simp [hbot]
  | succ k ih =>
    by_cases hbot : W = ⊥
    · rw [hbot, finrank_bot]
      omega
    obtain ⟨e, heW, he0⟩ := W.ne_bot_iff.mp hbot
    have he : form hdeg (k+1) e = 0 := hW e heW
    obtain ⟨f,hf,hef⟩ := exists_hyperbolic_partner hdeg (k+1) e he0 he
    obtain ⟨c⟩ := complement_isometry hdeg e f he hf hef
    let Q := form hdeg (k+1)
    let C := complement Q e f
    let S := split Q e f he hf hef
    have hxe (x : W) : Q.polarBilin x.val e = 0 := by
      change Q (x.val+e) - Q x.val - Q e = 0
      rw [hW _ (W.add_mem x.prop heW), hW _ x.prop, he]
      ring
    let L : W →ₗ[F] Vector k F K :=
      c.toLinearEquiv.toLinearMap.comp
        ((LinearMap.snd F (F×F) C).comp (S.toLinearMap.comp W.subtype))
    have hL : ∀ y ∈ LinearMap.range L, form hdeg k y = 0 := by
      rintro y ⟨x,rfl⟩
      change form hdeg k (c (S x.val).2) = 0
      rw [c.map_app]
      have hh := form_split Q e f he hf hef x.val
      change Q x.val = Q.polarBilin x.val f * Q.polarBilin x.val e + Q (S x.val).2.val at hh
      rw [hW _ x.prop, hxe x, mul_zero, zero_add] at hh
      exact hh.symm
    let J : W →ₗ[F] F × LinearMap.range L :=
      ((Q.polarBilin.flip f).comp W.subtype).prod L.rangeRestrict
    have hJ : Function.Injective J := by
      intro x y hxy
      have hfirst := congrArg Prod.fst hxy
      have hsecond := congrArg (fun z : F × LinearMap.range L => z.2.val) hxy
      change Q.polarBilin x.val f = Q.polarBilin y.val f at hfirst
      change c (S x.val).2 = c (S y.val).2 at hsecond
      apply Subtype.ext
      apply S.injective
      apply Prod.ext
      · exact Prod.ext hfirst ((hxe x).trans (hxe y).symm)
      · exact c.injective hsecond
    have hd := LinearMap.finrank_le_finrank_of_injective hJ
    have hi := ih (LinearMap.range L) hL
    simp only [Module.finrank_prod, Module.finrank_self] at hd
    omega

/-- The retained x-coordinate half of the hyperbolic summand. -/
def singularCoordinateInclusion (k : ℕ) : (Fin k → F) →ₗ[F] Vector k F K where
  toFun x := (Sum.elim x (fun _ => 0), 0)
  map_add' x y := by
    apply Prod.ext
    · funext i; cases i <;> simp
    · simp
  map_smul' a x := by
    apply Prod.ext
    · funext i; cases i <;> simp
    · simp

omit [Finite F] [Finite K] in
theorem singularCoordinateInclusion_injective (k : ℕ) :
    Function.Injective (singularCoordinateInclusion (F := F) (K := K) k) := by
  intro x y h
  funext i
  exact congrArg (fun z : Vector k F K => z.1 (.inl i)) h

theorem singularCoordinateInclusion_isotropic (hdeg : Module.finrank F K = 2)
    (k : ℕ) (x : Fin k → F) :
    form hdeg k (singularCoordinateInclusion k x) = 0 := by
  change formD k F (Sum.elim x (fun _ => 0)) + Atlas.FiniteQuadratic.norm F K 0 = 0
  rw [← normForm_apply hdeg, map_zero, add_zero]
  simp [formD_apply]

/-- An actual totally singular subspace attains the upper bound. -/
theorem exists_totallySingular_finrank_eq (hdeg : Module.finrank F K = 2) (k : ℕ) :
    ∃ W : Submodule F (Vector k F K),
      (∀ x ∈ W, form hdeg k x = 0) ∧ Module.finrank F W = k := by
  refine ⟨LinearMap.range (singularCoordinateInclusion k), ?_, ?_⟩
  · rintro x ⟨y,rfl⟩
    exact singularCoordinateInclusion_isotropic hdeg k y
  · rw [LinearMap.finrank_range_of_inj (singularCoordinateInclusion_injective k),
      Module.finrank_fin_fun]

/-- Exact Witt index expressed without an unproved abstract classification API. -/
theorem witt_index_exact (hdeg : Module.finrank F K = 2) (k : ℕ) :
    (∀ W : Submodule F (Vector k F K),
      (∀ x ∈ W, form hdeg k x = 0) → Module.finrank F W ≤ k) ∧
    (∃ W : Submodule F (Vector k F K),
      (∀ x ∈ W, form hdeg k x = 0) ∧ Module.finrank F W = k) :=
  ⟨totallySingular_finrank_le hdeg k, exists_totallySingular_finrank_eq hdeg k⟩
end Atlas.Orthogonal.Minus
