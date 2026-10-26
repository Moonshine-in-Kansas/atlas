import Atlas.LinearGroups.Chevalley.RootData.A
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.GroupTheory.Perm.Sign

/-! The actual type-A Weyl root-permutation image is the coordinate permutation
group. This identifies the existing root datum, including its empty rank-zero
case; it does not use a presentation, a Weyl order formula or a linear group. -/
noncomputable section
namespace Atlas.Chevalley.TypeAData
open Classical

def permuteHom (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Root n) where
  toFun := permute
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    rfl
  map_mul' e f := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    rfl

theorem permute_injective (n : ℕ) : Function.Injective (@permute n) := by
  by_cases hn : n ≤ 1
  · letI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
    exact fun _ _ _ => Subsingleton.elim _ _
  · letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    intro e f h
    apply Equiv.ext
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    let a : Root n := ⟨(i, j), hj.symm⟩
    have ha := congrArg (fun p : Equiv.Perm (Root n) => (p a).val.1) h
    exact ha

theorem permute_mem_weylImage (n : ℕ) (e : Equiv.Perm (Fin n)) :
    permute e ∈ (pairing n).weylGroupToPerm.range := by
  induction e using Equiv.Perm.swap_induction_on with
  | one =>
    change permuteHom n 1 ∈ _
    rw [map_one]
    exact (pairing n).weylGroupToPerm.range.one_mem
  | swap_mul e i j hij ih =>
    change permuteHom n (Equiv.swap i j * e) ∈ _
    rw [map_mul]
    apply (pairing n).weylGroupToPerm.range.mul_mem _ ih
    rw [(pairing n).range_weylGroupToPerm]
    exact Subgroup.subset_closure ⟨⟨(i, j), hij⟩, rfl⟩

def coordinateWeylHom (n : ℕ) :
    Equiv.Perm (Fin n) →* (pairing n).weylGroupToPerm.range where
  toFun e := ⟨permute e, permute_mem_weylImage n e⟩
  map_one' := Subtype.ext ((permuteHom n).map_one)
  map_mul' e f := Subtype.ext ((permuteHom n).map_mul e f)

theorem coordinateWeylHom_bijective (n : ℕ) :
    Function.Bijective (coordinateWeylHom n) := by
  constructor
  · intro e f h
    exact permute_injective n (congrArg Subtype.val h)
  · rintro ⟨w, hw⟩
    have hle : (pairing n).weylGroupToPerm.range ≤ (permuteHom n).range := by
      rw [(pairing n).range_weylGroupToPerm]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨a, rfl⟩
      exact ⟨Equiv.swap a.val.1 a.val.2, rfl⟩
    obtain ⟨e, he⟩ := hle hw
    exact ⟨e, Subtype.ext he⟩

/-- Coordinate permutations and the actual Weyl image, with multiplication preserved. -/
def coordinateWeylEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃* (pairing n).weylGroupToPerm.range :=
  MulEquiv.ofBijective (coordinateWeylHom n) (coordinateWeylHom_bijective n)

@[simp] theorem coordinateWeylEquiv_apply (n : ℕ) (e : Equiv.Perm (Fin n))
    (a : Root n) :
    ((coordinateWeylEquiv n e).val a).val = (e a.val.1, e a.val.2) := rfl

end Atlas.Chevalley.TypeAData
