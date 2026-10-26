import Atlas.Comparisons.Exceptional.E6.RootRepresentatives
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Pi

/-! E6 integral norm-shell root pairing. Only the pre-existing elementary integral
lattice and its verified root exhaustion are used, not any group construction. -/

namespace Atlas.Chevalley.E6Data

abbrev Lattice := Fin 6 → ℤ
abbrev Root := Atlas.Comparisons.E6Lattice.Root

open Atlas.Comparisons.E6Lattice

/-- The integral polar form, used as a map into the exact integral dual lattice. -/
def polar : Lattice →ₗ[ℤ] Module.Dual ℤ Lattice := (form ℤ).polarBilin

@[simp] theorem polar_self (x : Lattice) : polar x x = 2 * Atlas.Comparisons.E6Lattice.norm x := by
  simp [polar, QuadraticMap.polarBilin_apply_apply]

theorem polar_symm (x y : Lattice) : polar x y = polar y x := by
  exact QuadraticMap.polar_comm (form ℤ) x y

theorem polar_injective : Function.Injective polar := by
  intro x y h
  have hz : polar (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hs := congrArg (fun f : Module.Dual ℤ Lattice => f (x - y)) hz
  have hn : Atlas.Comparisons.E6Lattice.norm (x - y) = 0 := by
    change polar (x - y) (x - y) = 0 at hs
    rw [polar_self] at hs
    omega
  exact sub_eq_zero.mp ((norm_eq_zero_iff (x - y)).mp hn)

/-- Reflection in an actual norm-one lattice vector. -/
def reflect (a : Root) (x : Lattice) : Lattice := x - polar a.val x • a.val

theorem norm_sub_smul (x y : Lattice) (t : ℤ) :
    Atlas.Comparisons.E6Lattice.norm (y - t • x) = Atlas.Comparisons.E6Lattice.norm y - t * polar x y + t^2 * Atlas.Comparisons.E6Lattice.norm x := by
  simp [polar, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Atlas.Comparisons.E6Lattice.norm]
  ring

theorem reflect_norm (a : Root) (x : Lattice) : Atlas.Comparisons.E6Lattice.norm (reflect a x) = Atlas.Comparisons.E6Lattice.norm x := by
  rw [reflect, norm_sub_smul, a.property]
  ring

theorem reflect_involutive (a : Root) : Function.Involutive (reflect a) := by
  intro x
  have haa : polar a.val a.val = 2 := by rw [polar_self, a.property]; rfl
  have hp : polar a.val (reflect a x) = -polar a.val x := by
    rw [reflect, map_sub, map_smul, haa]
    simp
    ring
  ext k
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hp ⊢
  rw [hp]
  ring

def reflectionPerm (a : Root) : Equiv.Perm Root where
  toFun b := ⟨reflect a b.val, (reflect_norm a b.val).trans b.property⟩
  invFun b := ⟨reflect a b.val, (reflect_norm a b.val).trans b.property⟩
  left_inv b := Subtype.ext (reflect_involutive a b.val)
  right_inv b := Subtype.ext (reflect_involutive a b.val)

set_option maxHeartbeats 800000 in
/-- A genuine perfect root pairing on the existing E6 norm shell. -/
def pairing : RootPairing Root ℤ Lattice (Module.Dual ℤ Lattice) where
  toLinearMap := Module.Dual.eval ℤ Lattice
  root := Function.Embedding.subtype (fun x => Atlas.Comparisons.E6Lattice.norm x = 1)
  coroot := ⟨fun a => polar a.val, fun _ _ h => Subtype.ext (polar_injective h)⟩
  root_coroot_two a := by change polar a.val a.val = 2; rw [polar_self, a.property]; rfl
  reflectionPerm := reflectionPerm
  reflectionPerm_root a b := rfl
  reflectionPerm_coroot a b := by
    change polar b.val - polar b.val a.val • polar a.val = polar (reflect a b.val)
    rw [reflect, map_sub, map_smul, polar_symm a.val b.val]

/-- Reducedness follows from the actual positive quadratic norm. -/
instance reduced : pairing.IsReduced where
  eq_or_eq_neg a b h := by
    have he := pairing.pairing_smul_root_eq_of_not_linearIndependent h
    change polar a.val b.val • a.val = (2 : ℤ) • b.val at he
    have hn := congrArg Atlas.Comparisons.E6Lattice.norm he
    have hnsmul (t : ℤ) (v : Lattice) :
        Atlas.Comparisons.E6Lattice.norm (t • v) = t^2 * Atlas.Comparisons.E6Lattice.norm v := by
      simpa [form_apply, pow_two, smul_eq_mul] using (form ℤ).map_smul t v
    have hsq : (polar a.val b.val)^2 = 4 := by
      rw [hnsmul, hnsmul, a.property, b.property] at hn
      simpa using hn
    have hs : polar a.val b.val = 2 ∨ polar a.val b.val = -2 := by
      exact (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
    rcases hs with hp | hp
    · left
      change a.val = b.val
      funext k
      have hk := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hp] at hk
      omega
    · right
      change a.val = -b.val
      funext k
      have hk := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hp, Pi.neg_apply] at hk ⊢
      omega

/-- The six coordinate vectors are actual roots of the inherited lattice. -/
def simpleRoot (i : Fin 6) : Root :=
  ⟨Pi.single i 1, (by decide : ∀ i : Fin 6, Atlas.Comparisons.E6Lattice.norm (Pi.single i (1 : ℤ)) = 1) i⟩

theorem simpleRoot_injective : Function.Injective simpleRoot := by
  intro i j h
  have hv := congrArg Subtype.val h
  have he : (Pi.basisFun ℤ (Fin 6)) i = (Pi.basisFun ℤ (Fin 6)) j := by
    simpa only [Pi.basisFun_apply, simpleRoot] using hv
  exact (Pi.basisFun ℤ (Fin 6)).injective he

theorem simple_root_independent :
    LinearIndependent ℤ (fun i : Fin 6 => (simpleRoot i).val) := by
  have he : (fun i : Fin 6 => (simpleRoot i).val) = Pi.basisFun ℤ (Fin 6) := by
    funext i
    simp [simpleRoot]
  rw [he]
  exact (Pi.basisFun ℤ (Fin 6)).linearIndependent

theorem simple_coroot_independent :
    LinearIndependent ℤ (fun i : Fin 6 => polar (simpleRoot i).val) := by
  exact simple_root_independent.map' polar (LinearMap.ker_eq_bot.mpr polar_injective)

/-- Every coordinate of each of the previously verified positive representatives is nonnegative. -/
theorem representative_nonnegative :
    ∀ i : Fin 36, ∀ j : Fin 6, 0 ≤ rootRepresentative i j := by decide

private theorem nonnegative_expansion (x : Lattice) (hx : ∀ i, 0 ≤ x i) :
    ∑ i : Fin 6, (x i).toNat • (Pi.single i (1 : ℤ)) = x := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]
  exact hx k

private theorem nonnegative_map_mem {M : Type*} [AddCommGroup M] (f : Lattice →+ M)
    (x : Lattice) (hx : ∀ i, 0 ≤ x i) :
    f x ∈ AddSubmonoid.closure (Set.range fun i : Fin 6 => f (Pi.single i 1)) := by
  rw [← nonnegative_expansion x hx, map_sum]
  apply AddSubmonoid.sum_mem
  intro i _
  rw [map_nsmul]
  have hg : f (Pi.single i 1) ∈ AddSubmonoid.closure
      (Set.range fun i : Fin 6 => f (Pi.single i 1)) :=
    AddSubmonoid.subset_closure ⟨i, rfl⟩
  exact AddSubmonoid.nsmul_mem _ hg _

/-- Actual simple support in the original lattice numbering. -/
def simpleSupport : Finset Root := Finset.univ.image simpleRoot

theorem simpleSupport_set : (simpleSupport : Set Root) = Set.range simpleRoot := by
  simp [simpleSupport]

private theorem root_positive_or_negative (a : Root) :
    (∀ i, 0 ≤ a.val i) ∨ (∀ i, 0 ≤ (-a.val) i) := by
  obtain ⟨i, hi | hi⟩ := root_representative_exhaustion a.val a.property
  · left; simpa only [hi] using representative_nonnegative i
  · right; simpa only [hi, neg_neg] using representative_nonnegative i

set_option maxHeartbeats 800000 in
/-- A genuine explicit base of the integral E6 root pairing. -/
def base : pairing.Base where
  support := simpleSupport
  linearIndepOn_root := by
    change LinearIndepOn ℤ Subtype.val (simpleSupport : Set Root)
    rw [simpleSupport_set]
    exact (linearIndepOn_range_iff simpleRoot_injective Subtype.val).2 simple_root_independent
  linearIndepOn_coroot := by
    change LinearIndepOn ℤ (fun a : Root => polar a.val) (simpleSupport : Set Root)
    rw [simpleSupport_set]
    exact (linearIndepOn_range_iff simpleRoot_injective (fun a : Root => polar a.val)).2
      simple_coroot_independent
  root_mem_or_neg_mem a := by
    change a.val ∈ AddSubmonoid.closure (Subtype.val '' (simpleSupport : Set Root)) ∨
      -a.val ∈ AddSubmonoid.closure (Subtype.val '' (simpleSupport : Set Root))
    rw [simpleSupport_set, ← Set.range_comp]
    change a.val ∈ AddSubmonoid.closure (Set.range (fun i : Fin 6 => Pi.single i 1)) ∨
      -a.val ∈ AddSubmonoid.closure (Set.range (fun i : Fin 6 => Pi.single i 1))
    rcases root_positive_or_negative a with h | h
    · exact Or.inl (nonnegative_map_mem (AddMonoidHom.id Lattice) a.val h)
    · exact Or.inr (nonnegative_map_mem (AddMonoidHom.id Lattice) (-a.val) h)
  coroot_mem_or_neg_mem a := by
    change polar a.val ∈ AddSubmonoid.closure
        ((fun a : Root => polar a.val) '' (simpleSupport : Set Root)) ∨
      -polar a.val ∈ AddSubmonoid.closure
        ((fun a : Root => polar a.val) '' (simpleSupport : Set Root))
    rw [simpleSupport_set, ← Set.range_comp]
    change polar a.val ∈ AddSubmonoid.closure (Set.range (fun i : Fin 6 => polar (Pi.single i 1))) ∨
      -polar a.val ∈ AddSubmonoid.closure (Set.range (fun i : Fin 6 => polar (Pi.single i 1)))
    rcases root_positive_or_negative a with h | h
    · exact Or.inl (nonnegative_map_mem polar.toAddMonoidHom a.val h)
    · right
      simpa only [LinearMap.toAddMonoidHom_coe, map_neg] using
        nonnegative_map_mem polar.toAddMonoidHom (-a.val) h

/-- Original lattice node labels mapped to the pinned mathlib E6 numbering. -/
def nodeEquiv : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide
  right_inv := by decide

theorem simple_cartan (i j : Fin 6) :
    polar (simpleRoot i).val (simpleRoot j).val =
      CartanMatrix.E 6 (nodeEquiv i) (nodeEquiv j) := by
  revert i j
  decide

/-- Explicit simple-base indexing in the pinned mathlib E6 numbering. -/
noncomputable def baseIndexEquiv : Fin 6 ≃ base.support :=
  nodeEquiv.symm.trans (Equiv.ofBijective
    (fun i => ⟨simpleRoot i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨by
      intro i j h
      exact simpleRoot_injective (congrArg Subtype.val h), by
      intro a
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.2
      exact ⟨i, Subtype.ext hi⟩⟩)

@[simp] theorem baseIndexEquiv_apply (i : Fin 6) :
    (baseIndexEquiv i : Root) = simpleRoot (nodeEquiv.symm i) := rfl

/-- The certified base has exactly the pinned E6 Cartan matrix. -/
theorem base_cartan (i j : Fin 6) :
    base.cartanMatrix (baseIndexEquiv i) (baseIndexEquiv j) = CartanMatrix.E 6 i j := by
  change pairing.pairingIn ℤ (simpleRoot (nodeEquiv.symm i)) (simpleRoot (nodeEquiv.symm j)) = _
  have hp := pairing.algebraMap_pairingIn ℤ
    (simpleRoot (nodeEquiv.symm i)) (simpleRoot (nodeEquiv.symm j))
  change pairing.pairingIn ℤ (simpleRoot (nodeEquiv.symm i)) (simpleRoot (nodeEquiv.symm j)) =
    polar (simpleRoot (nodeEquiv.symm j)).val (simpleRoot (nodeEquiv.symm i)).val at hp
  rw [hp, polar_symm]
  simpa using simple_cartan (nodeEquiv.symm i) (nodeEquiv.symm j)

end Atlas.Chevalley.E6Data
