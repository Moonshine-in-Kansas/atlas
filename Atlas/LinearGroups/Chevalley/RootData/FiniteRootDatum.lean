import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Group.Int.Units

/-! Actual root pairings and bases from finite integral root/coroot certificates.
The independent coroot coordinates preserve nonsymmetric Cartan orientation
and the two root lengths. No finite-group conclusions occur as hypotheses. -/
namespace Atlas.Chevalley

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.IsTorsionFree ℤ M]

theorem reduced_of_root_primitive (P : RootPairing ι ℤ M N)
    (hprimitive : ∀ i, ∃ f : Module.Dual ℤ M, f (P.root i) = 1) : P.IsReduced := by
  constructor
  intro a b h
  obtain ⟨fa, ha⟩ := hprimitive a
  obtain ⟨fb, hb⟩ := hprimitive b
  have he := P.pairing_smul_root_eq_of_not_linearIndependent h
  have ht : P.pairing b a = (2 : ℤ) * fa (P.root b) := by
    simpa only [map_smul, smul_eq_mul, ha, mul_one] using congrArg fa he
  have hab : fa (P.root b) • P.root a = P.root b := by
    apply smul_right_injective M (show (2 : ℤ) ≠ 0 by decide)
    change (2 : ℤ) • (fa (P.root b) • P.root a) = (2 : ℤ) • P.root b
    rw [← mul_smul, ← ht]
    exact he
  have hu : fa (P.root b) * fb (P.root a) = 1 := by
    calc
      _ = fb (fa (P.root b) • P.root a) := (fb.map_smul _ _).symm
      _ = 1 := (congrArg fb hab).trans hb
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with hk | hk
  · left
    simpa only [hk, one_smul] using hab
  · right
    simpa only [hk, neg_one_smul, neg_neg] using congrArg Neg.neg hab

end Atlas.Chevalley

namespace Atlas.Chevalley.FiniteRootDatum
abbrev Lattice (r : ℕ) := Fin r → ℤ

structure Data (r N : ℕ) where
  root : Fin N ↪ Lattice r
  coroot : Fin N ↪ Module.Dual ℤ (Lattice r)
  root_coroot_two : ∀ a, coroot a (root a) = 2
  reflectionIndex : Fin N → Fin N → Fin N
  reflection_involutive : ∀ a, Function.Involutive (reflectionIndex a)
  reflection_root : ∀ a b,
    root (reflectionIndex a b) = root b - coroot a (root b) • root a
  reflection_coroot : ∀ a b,
    coroot (reflectionIndex a b) = coroot b - coroot b (root a) • coroot a
  primitive : ∀ a, ∃ f : Module.Dual ℤ (Lattice r), f (root a) = 1
  simpleIndex : Fin r → Fin N
  simple_coordinates : ∀ i, root (simpleIndex i) = Pi.single i 1
  corootMap : Lattice r →ₗ[ℤ] Module.Dual ℤ (Lattice r)
  corootMap_injective : Function.Injective corootMap
  corootCoordinates : Fin N → Lattice r
  coroot_coordinates : ∀ a, corootMap (corootCoordinates a) = coroot a
  simple_coroot_coordinates : ∀ i, coroot (simpleIndex i) = corootMap (Pi.single i 1)
  root_sign : ∀ a, (∀ i, 0 ≤ root a i) ∨ (∀ i, root a i ≤ 0)
  coroot_sign : ∀ a, (∀ i, 0 ≤ corootCoordinates a i) ∨
    (∀ i, corootCoordinates a i ≤ 0)

namespace Data
variable {r N : ℕ} (d : Data r N)

def pairing : RootPairing (Fin N) ℤ (Lattice r) (Module.Dual ℤ (Lattice r)) where
  toLinearMap := Module.Dual.eval ℤ (Lattice r)
  root := d.root
  coroot := d.coroot
  root_coroot_two := d.root_coroot_two
  reflectionPerm a := (d.reflection_involutive a).toPerm
  reflectionPerm_root a b := (d.reflection_root a b).symm
  reflectionPerm_coroot a b := (d.reflection_coroot a b).symm

instance reduced : d.pairing.IsReduced :=
  Atlas.Chevalley.reduced_of_root_primitive d.pairing d.primitive

theorem simpleIndex_injective : Function.Injective d.simpleIndex := by
  intro i j h
  have he := congrArg d.root h
  rw [d.simple_coordinates, d.simple_coordinates] at he
  exact (Pi.basisFun ℤ (Fin r)).injective (by simpa only [Pi.basisFun_apply] using he)

theorem simple_root_independent :
    LinearIndependent ℤ (fun i => d.root (d.simpleIndex i)) := by
  have he : (fun i => d.root (d.simpleIndex i)) = Pi.basisFun ℤ (Fin r) := by
    funext i
    simp only [d.simple_coordinates, Pi.basisFun_apply]
  rw [he]
  exact (Pi.basisFun ℤ (Fin r)).linearIndependent

theorem simple_coroot_independent :
    LinearIndependent ℤ (fun i => d.coroot (d.simpleIndex i)) := by
  have he : (fun i => d.coroot (d.simpleIndex i)) =
      fun i => d.corootMap ((Pi.basisFun ℤ (Fin r)) i) := by
    funext i
    simp only [d.simple_coroot_coordinates, Pi.basisFun_apply]
  rw [he]
  exact (Pi.basisFun ℤ (Fin r)).linearIndependent.map' d.corootMap
    (LinearMap.ker_eq_bot.mpr d.corootMap_injective)

private theorem nonnegative_expansion (x : Lattice r) (hx : ∀ i, 0 ≤ x i) :
    ∑ i : Fin r, (x i).toNat • (Pi.single i (1 : ℤ)) = x := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]
  exact hx k

private theorem nonnegative_map_mem {M : Type*} [AddCommGroup M]
    (f : Lattice r →+ M) (x : Lattice r) (hx : ∀ i, 0 ≤ x i) :
    f x ∈ AddSubmonoid.closure (Set.range fun i : Fin r => f (Pi.single i 1)) := by
  rw [← nonnegative_expansion x hx, map_sum]
  apply AddSubmonoid.sum_mem
  intro i _
  rw [map_nsmul]
  have hg : f (Pi.single i 1) ∈ AddSubmonoid.closure
      (Set.range fun i : Fin r => f (Pi.single i 1)) :=
    AddSubmonoid.subset_closure ⟨i, rfl⟩
  exact AddSubmonoid.nsmul_mem _ hg _

def simpleSupport : Finset (Fin N) := Finset.univ.image d.simpleIndex

theorem simpleSupport_set : (d.simpleSupport : Set (Fin N)) = Set.range d.simpleIndex := by
  simp [simpleSupport]

/-- The actual standard-coordinate base, using the checked coefficient signs. -/
def base : d.pairing.Base where
  support := d.simpleSupport
  linearIndepOn_root := by
    change LinearIndepOn ℤ d.root (d.simpleSupport : Set (Fin N))
    rw [d.simpleSupport_set]
    exact (linearIndepOn_range_iff d.simpleIndex_injective d.root).2
      d.simple_root_independent
  linearIndepOn_coroot := by
    change LinearIndepOn ℤ (fun a => d.coroot a) (d.simpleSupport : Set (Fin N))
    rw [d.simpleSupport_set]
    exact (linearIndepOn_range_iff d.simpleIndex_injective (fun a => d.coroot a)).2
      d.simple_coroot_independent
  root_mem_or_neg_mem a := by
    change d.root a ∈ AddSubmonoid.closure (d.root '' (d.simpleSupport : Set (Fin N))) ∨
      -d.root a ∈ AddSubmonoid.closure (d.root '' (d.simpleSupport : Set (Fin N)))
    rw [d.simpleSupport_set, ← Set.range_comp]
    simp only [Function.comp_def, d.simple_coordinates]
    rcases d.root_sign a with h | h
    · exact Or.inl (nonnegative_map_mem (AddMonoidHom.id (Lattice r)) (d.root a) h)
    · exact Or.inr (nonnegative_map_mem (AddMonoidHom.id (Lattice r)) (-d.root a)
        (fun i => neg_nonneg.mpr (h i)))
  coroot_mem_or_neg_mem a := by
    change d.coroot a ∈ AddSubmonoid.closure
        (d.coroot '' (d.simpleSupport : Set (Fin N))) ∨
      -d.coroot a ∈ AddSubmonoid.closure
        (d.coroot '' (d.simpleSupport : Set (Fin N)))
    rw [d.simpleSupport_set, ← Set.range_comp]
    simp only [Function.comp_def, d.simple_coroot_coordinates]
    rw [← d.coroot_coordinates a]
    rcases d.coroot_sign a with h | h
    · exact Or.inl (nonnegative_map_mem d.corootMap.toAddMonoidHom
        (d.corootCoordinates a) h)
    · right
      rw [← map_neg]
      exact nonnegative_map_mem d.corootMap.toAddMonoidHom (-d.corootCoordinates a)
        (fun i => neg_nonneg.mpr (h i))

noncomputable def baseIndexEquiv : Fin r ≃ d.base.support :=
  Equiv.ofBijective
    (fun i => ⟨d.simpleIndex i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun _ _ h => d.simpleIndex_injective (congrArg Subtype.val h), by
      intro a
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem base_cartan (i j : Fin r) :
    d.base.cartanMatrix (d.baseIndexEquiv i) (d.baseIndexEquiv j) =
      d.corootMap (Pi.single j 1) (Pi.single i 1) := by
  change d.pairing.pairingIn ℤ (d.simpleIndex i) (d.simpleIndex j) = _
  have hp := d.pairing.algebraMap_pairingIn ℤ (d.simpleIndex i) (d.simpleIndex j)
  change d.pairing.pairingIn ℤ (d.simpleIndex i) (d.simpleIndex j) =
    d.coroot (d.simpleIndex j) (d.root (d.simpleIndex i)) at hp
  rw [hp, d.simple_coordinates, d.simple_coroot_coordinates]

end Data
end Atlas.Chevalley.FiniteRootDatum
