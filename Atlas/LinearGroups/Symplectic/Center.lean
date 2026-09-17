import Atlas.LinearGroups.Symplectic.TransvectionImage
import Atlas.LinearGroups.Symplectic.Isometry
import Mathlib.LinearAlgebra.Center
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- Central commutation with genuine transvections forces preservation of every line. -/
theorem central_preserves_lines (g : Sp n F) (hg : g ∈ Subgroup.center (Sp n F))
    (v : Vector n F) (hv : v ≠ 0) : ∃ a : F, a • v = g • v := by
  have hgv : g • v ≠ 0 := by
    change toLinear g v ≠ 0
    exact (map_ne_zero_iff (toLinear g) (toLinear g).injective).mpr hv
  obtain ⟨x,hx⟩ := exists_form_left hgv 1
  have ht := transvection_conjugate g v 1
  rw [← Subgroup.mem_center_iff.mp hg (transvection v 1), mul_assoc,
    mul_inv_cancel, mul_one] at ht
  have h := congrArg (fun t : Sp n F => t • x) ht
  refine ⟨form x v, ?_⟩
  simpa [transvection_apply,hx] using h

/-- This scalar conclusion uses neither order nor transvection generation. -/
theorem central_is_scalar (g : Sp n F) (hg : g ∈ Subgroup.center (Sp n F)) :
    ∃ a : F, ∀ x : Vector n F, g • x = a • x := by
  obtain ⟨a,ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (fun v => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        obtain ⟨a,ha⟩ := central_preserves_lines g hg v hv
        exact fun h => h a ha)
  refine ⟨a,fun x => ?_⟩
  exact congrArg (fun l : Vector n F →ₗ[F] Vector n F => l x) ha

theorem scalar_is_central (g : Sp n F) (a : F)
    (ha : ∀ x : Vector n F, g • x = a • x) : g ∈ Subgroup.center (Sp n F) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply ext_action
  intro x
  rw [mul_smul, mul_smul, ha, ha]
  exact (toLinear h).map_smul a x

theorem scalar_square_eq_one (hn : 0 < n) (g : Sp n F) (a : F)
    (ha : ∀ x : Vector n F, g • x = a • x) : a^2 = 1 := by
  let i : Fin n := ⟨0,hn⟩
  have h := preserves g (e (F := F) i) (f (F := F) i)
  change form (g • e (F := F) i) (g • f (F := F) i) = form (e (F := F) i) (f (F := F) i) at h
  rw [ha,ha] at h
  simpa [map_smul,e,Pi.single_apply,pow_two] using h

theorem mem_center_iff_scalar (hn : 0 < n) (g : Sp n F) :
    g ∈ Subgroup.center (Sp n F) ↔
      ∃ a : F, a^2 = 1 ∧ ∀ x : Vector n F, g • x = a • x := by
  constructor
  · intro hg
    obtain ⟨a,ha⟩ := central_is_scalar g hg
    exact ⟨a,scalar_square_eq_one hn g a ha,ha⟩
  · rintro ⟨a,_,ha⟩
    exact scalar_is_central g a ha

abbrev ScalarKernel (F : Type*) [Field F] := (powMonoidHom 2 : Fˣ →* Fˣ).ker

theorem scalarKernel_square (a : ScalarKernel F) : (a.val.val : F)^2 = 1 := by
  have h : a.val^2 = 1 := a.prop
  exact congrArg Units.val h

/-- Actual scalar matrices with square-one scalar, in the primary full group. -/
def scalarElement (a : ScalarKernel F) : Sp n F :=
  ofLinear (LinearEquiv.smulOfUnit a.val) (by
    intro x y
    change form (a.val.val • x) (a.val.val • y) = form x y
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [← mul_assoc,← pow_two,scalarKernel_square,one_mul])

@[simp] theorem scalarElement_apply (a : ScalarKernel F) (x : Vector n F) :
    scalarElement (n := n) a • x = a.val.val • x := ofLinear_apply _ _ _

def scalarToCenter : ScalarKernel F →* Subgroup.center (Sp n F) where
  toFun a := ⟨scalarElement (n := n) a,scalar_is_central _ a.val.val (scalarElement_apply a)⟩
  map_one' := by
    apply Subtype.ext
    apply ext_action
    intro x
    simp [scalarElement_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ext_action
    intro x
    simp [scalarElement_apply,mul_smul]

theorem scalarToCenter_injective (hn : 0 < n) :
    Function.Injective (scalarToCenter (n := n) (F := F)) := by
  intro a b h
  let i : Fin n := ⟨0,hn⟩
  have he := congrArg (fun z : Subgroup.center (Sp n F) => (z.val • e (F := F) i) (.inl i)) h
  change (scalarElement (n := n) a • e (F := F) i) (.inl i) = (scalarElement (n := n) b • e (F := F) i) (.inl i) at he
  simp only [scalarElement_apply,Pi.smul_apply,smul_eq_mul] at he
  have hab : a.val.val = b.val.val := by simpa [e,Pi.single_apply] using he
  exact Subtype.ext (Units.ext hab)

theorem scalarToCenter_surjective (hn : 0 < n) :
    Function.Surjective (scalarToCenter (n := n) (F := F)) := by
  intro g
  obtain ⟨a,ha₂,ha⟩ := (mem_center_iff_scalar hn g.val).mp g.prop
  have ha₀ : a ≠ 0 := by intro h; simp [h] at ha₂
  let u : ScalarKernel F := ⟨Units.mk0 a ha₀,by
    change (Units.mk0 a ha₀)^2 = 1
    apply Units.ext
    simpa using ha₂⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply ext_action
  intro x
  change scalarElement (n := n) u • x = g.val • x
  rw [scalarElement_apply,ha]
  rfl

def centerEquivScalarKernel (hn : 0 < n) :
    Subgroup.center (Sp n F) ≃* ScalarKernel F :=
  (MulEquiv.ofBijective scalarToCenter
    ⟨scalarToCenter_injective hn,scalarToCenter_surjective hn⟩).symm

/-- The center is counted independently of the symplectic order and simplicity. -/
theorem card_center (hn : 0 < n) [Finite F] :
    Nat.card (Subgroup.center (Sp n F)) = Nat.gcd 2 (Nat.card F - 1) := by
  rw [Nat.card_congr (centerEquivScalarKernel hn).toEquiv,
    IsCyclic.card_powMonoidHom_ker,Nat.card_units,Nat.gcd_comm]

end Atlas.Symplectic

