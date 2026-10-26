import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Finite simply-laced root tables yield an actual integral root datum.
All hypotheses are explicit elementary certificates, supplied by the checked E7/E8
root tables and the pinned integral Cartan-form nondegeneracy lemmas. There is no
assumption about a finite group, its order, its generation or its simplicity. -/
namespace Atlas.Chevalley.FiniteSimplyLaced

abbrev Lattice (r : ℕ) := Fin r → ℤ

def reflectVector {r : ℕ} (B : Lattice r →ₗ[ℤ] Module.Dual ℤ (Lattice r))
    (i : Fin r) (x : Lattice r) : Lattice r :=
  x - B (Pi.single i 1) x • Pi.single i 1

def wordAction {r : ℕ} (B : Lattice r →ₗ[ℤ] Module.Dual ℤ (Lattice r)) :
    List (Fin r) → Lattice r → Lattice r
  | [], x => x
  | i :: w, x => wordAction B w (reflectVector B i x)

/-- Finite root coordinates and elementary arithmetic certificates. -/
structure Data (r N : ℕ) [NeZero r] where
  form : Lattice r →ₗ[ℤ] Module.Dual ℤ (Lattice r)
  form_symm : ∀ x y, form x y = form y x
  form_injective : Function.Injective form
  root : Fin N ↪ Lattice r
  norm_two : ∀ a, form (root a) (root a) = 2
  simpleIndex : Fin r → Fin N
  simple_coordinates : ∀ i, root (simpleIndex i) = Pi.single i 1
  simpleReflectionIndex : Fin r → Fin N → Fin N
  simple_reflection_coordinates : ∀ i a,
    root (simpleReflectionIndex i a) = reflectVector form i (root a)
  word : Fin N → List (Fin r)
  word_coordinates : ∀ a, wordAction form (word a) (Pi.single 0 1) = root a
  sign_coherent : ∀ a, (∀ i, 0 ≤ root a i) ∨ (∀ i, root a i ≤ 0)

namespace Data
variable {r N : ℕ} [NeZero r] (d : Data r N)

private theorem simple_norm (i : Fin r) :
    d.form (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [← d.simple_coordinates i]
  exact d.norm_two (d.simpleIndex i)

def simpleLinear (i : Fin r) : Lattice r ≃ₗ[ℤ] Lattice r :=
  Module.reflection (d.simple_norm i)

@[simp] theorem simpleLinear_apply (i : Fin r) (x : Lattice r) :
    d.simpleLinear i x = reflectVector d.form i x := rfl

private theorem simple_index_involutive (i : Fin r) :
    Function.Involutive (d.simpleReflectionIndex i) := by
  intro a
  apply d.root.injective
  rw [d.simple_reflection_coordinates, d.simple_reflection_coordinates]
  exact Module.involutive_preReflection (d.simple_norm i) (d.root a)

def simplePerm (i : Fin r) : Equiv.Perm (Fin N) :=
  (d.simple_index_involutive i).toPerm

@[simp] theorem simplePerm_root (i : Fin r) (a : Fin N) :
    d.root (d.simplePerm i a) = d.simpleLinear i (d.root a) :=
  d.simple_reflection_coordinates i a

private theorem simpleLinear_isometry (i : Fin r) (x y : Lattice r) :
    d.form (d.simpleLinear i x) (d.simpleLinear i y) = d.form x y := by
  simp only [simpleLinear_apply, reflectVector, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    d.simple_norm]
  rw [d.form_symm x (Pi.single i 1)]
  ring

def wordLinear : List (Fin r) → Lattice r ≃ₗ[ℤ] Lattice r
  | [] => LinearEquiv.refl ℤ (Lattice r)
  | i :: w => (d.simpleLinear i).trans (wordLinear w)

def wordPerm : List (Fin r) → Equiv.Perm (Fin N)
  | [] => Equiv.refl (Fin N)
  | i :: w => (d.simplePerm i).trans (wordPerm w)

theorem wordLinear_apply (w : List (Fin r)) (x : Lattice r) :
    d.wordLinear w x = wordAction d.form w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change d.wordLinear w (d.simpleLinear i x) =
      wordAction d.form w (reflectVector d.form i x)
    rw [ih, d.simpleLinear_apply]

theorem wordPerm_root (w : List (Fin r)) (a : Fin N) :
    d.root (d.wordPerm w a) = d.wordLinear w (d.root a) := by
  induction w generalizing a with
  | nil => rfl
  | cons i w ih =>
    change d.root (d.wordPerm w (d.simplePerm i a)) =
      d.wordLinear w (d.simpleLinear i (d.root a))
    rw [ih, d.simplePerm_root]

theorem wordLinear_isometry (w : List (Fin r)) (x y : Lattice r) :
    d.form (d.wordLinear w x) (d.wordLinear w y) = d.form x y := by
  induction w generalizing x y with
  | nil => rfl
  | cons i w ih =>
    change d.form (d.wordLinear w (d.simpleLinear i x))
      (d.wordLinear w (d.simpleLinear i y)) = d.form x y
    rw [ih, d.simpleLinear_isometry]

/-- Reflection at an arbitrary root is conjugate to the first simple reflection.
No all-root reflection table or enumeration of a Weyl group is used. -/
def reflectionPerm (a : Fin N) : Equiv.Perm (Fin N) :=
  (((d.wordPerm (d.word a)).symm).trans (d.simplePerm 0)).trans
    (d.wordPerm (d.word a))

theorem reflectionPerm_root_formula (a b : Fin N) :
    d.root (d.reflectionPerm a b) =
      d.root b - d.form (d.root a) (d.root b) • d.root a := by
  let g := d.wordPerm (d.word a)
  let e := d.wordLinear (d.word a)
  have hg (c : Fin N) : d.root (g c) = e (d.root c) :=
    d.wordPerm_root (d.word a) c
  have he0 : e (Pi.single 0 1) = d.root a := by
    exact (d.wordLinear_apply (d.word a) (Pi.single 0 1)).trans (d.word_coordinates a)
  have hi : e (d.root (g.symm b)) = d.root b := by
    rw [← hg, g.apply_symm_apply]
  have hp : d.form (Pi.single 0 1) (d.root (g.symm b)) =
      d.form (d.root a) (d.root b) := by
    rw [← d.wordLinear_isometry (d.word a) (Pi.single 0 1) (d.root (g.symm b))]
    rw [he0, hi]
  change d.root (g (d.simplePerm 0 (g.symm b))) = _
  rw [hg, d.simplePerm_root, d.simpleLinear_apply, reflectVector, map_sub, map_smul,
    hi, he0, hp]

/-- The actual root datum on the integral root lattice and its exact dual.
This does not identify the character lattice of a simply-connected realization. -/
def pairing : RootPairing (Fin N) ℤ (Lattice r) (Module.Dual ℤ (Lattice r)) where
  toLinearMap := Module.Dual.eval ℤ (Lattice r)
  root := d.root
  coroot := ⟨fun a => d.form (d.root a), d.form_injective.comp d.root.injective⟩
  root_coroot_two := d.norm_two
  reflectionPerm := d.reflectionPerm
  reflectionPerm_root a b := (d.reflectionPerm_root_formula a b).symm
  reflectionPerm_coroot a b := by
    change d.form (d.root b) - d.form (d.root b) (d.root a) • d.form (d.root a) =
      d.form (d.root (d.reflectionPerm a b))
    rw [d.reflectionPerm_root_formula, map_sub, map_smul,
      d.form_symm (d.root a) (d.root b)]

instance reduced : d.pairing.IsReduced where
  eq_or_eq_neg a b h := by
    have he := d.pairing.pairing_smul_root_eq_of_not_linearIndependent h
    change d.form (d.root a) (d.root b) • d.root a = (2 : ℤ) • d.root b at he
    have hn := congrArg (fun x : Lattice r => d.form x x) he
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      d.norm_two] at hn
    have hsq : (d.form (d.root a) (d.root b))^2 = 4 := by nlinarith [hn]
    have hs : d.form (d.root a) (d.root b) = 2 ∨
        d.form (d.root a) (d.root b) = -2 := (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
    rcases hs with hp | hp
    · left
      change d.root a = d.root b
      funext i
      have hi := congrFun he i
      simp only [Pi.smul_apply, smul_eq_mul, hp] at hi
      omega
    · right
      change d.root a = -d.root b
      funext i
      have hi := congrFun he i
      simp only [Pi.smul_apply, smul_eq_mul, hp, Pi.neg_apply] at hi ⊢
      omega

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
    LinearIndependent ℤ (fun i => d.form (d.root (d.simpleIndex i))) :=
  d.simple_root_independent.map' d.form (LinearMap.ker_eq_bot.mpr d.form_injective)

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
    change LinearIndepOn ℤ (fun a => d.form (d.root a)) (d.simpleSupport : Set (Fin N))
    rw [d.simpleSupport_set]
    exact (linearIndepOn_range_iff d.simpleIndex_injective (fun a => d.form (d.root a))).2
      d.simple_coroot_independent
  root_mem_or_neg_mem a := by
    change d.root a ∈ AddSubmonoid.closure (d.root '' (d.simpleSupport : Set (Fin N))) ∨
      -d.root a ∈ AddSubmonoid.closure (d.root '' (d.simpleSupport : Set (Fin N)))
    rw [d.simpleSupport_set, ← Set.range_comp]
    simp only [Function.comp_def, d.simple_coordinates]
    rcases d.sign_coherent a with h | h
    · exact Or.inl (nonnegative_map_mem (AddMonoidHom.id (Lattice r)) (d.root a) h)
    · exact Or.inr (nonnegative_map_mem (AddMonoidHom.id (Lattice r)) (-d.root a)
        (fun i => neg_nonneg.mpr (h i)))
  coroot_mem_or_neg_mem a := by
    change d.form (d.root a) ∈ AddSubmonoid.closure
        ((fun a => d.form (d.root a)) '' (d.simpleSupport : Set (Fin N))) ∨
      -d.form (d.root a) ∈ AddSubmonoid.closure
        ((fun a => d.form (d.root a)) '' (d.simpleSupport : Set (Fin N)))
    rw [d.simpleSupport_set, ← Set.range_comp]
    simp only [Function.comp_def, d.simple_coordinates]
    rcases d.sign_coherent a with h | h
    · exact Or.inl (nonnegative_map_mem d.form.toAddMonoidHom (d.root a) h)
    · right
      rw [← map_neg]
      exact nonnegative_map_mem d.form.toAddMonoidHom (-d.root a)
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
      d.form (Pi.single i 1) (Pi.single j 1) := by
  change d.pairing.pairingIn ℤ (d.simpleIndex i) (d.simpleIndex j) = _
  have hp := d.pairing.algebraMap_pairingIn ℤ (d.simpleIndex i) (d.simpleIndex j)
  change d.pairing.pairingIn ℤ (d.simpleIndex i) (d.simpleIndex j) =
    d.form (d.root (d.simpleIndex j)) (d.root (d.simpleIndex i)) at hp
  rw [hp]
  rw [d.simple_coordinates, d.simple_coordinates, d.form_symm]

end Data
end Atlas.Chevalley.FiniteSimplyLaced
