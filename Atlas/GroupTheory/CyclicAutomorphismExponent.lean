import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace Atlas.GroupTheory

/-- The standard cyclic automorphism equivalence records the exponent on every
 element, and hence on every possible choice of generator. -/
theorem cyclic_automorphism_exponent {C : Type*} [Group C] [Finite C] [IsCyclic C]
    [NeZero (Nat.card C)] (f : MulAut C) (x : C) :
    f x = x ^ ((IsCyclic.mulAutMulEquiv C f : (ZMod (Nat.card C))ˣ) :
      ZMod (Nat.card C)).val := by
  let e := zmodCyclicMulEquiv (inferInstance : IsCyclic C)
  let a : AddAut (ZMod (Nat.card C)) :=
    (MulAutMultiplicative (ZMod (Nat.card C)) ((MulAut.congr e).symm f)).toAdd
  let z : ZMod (Nat.card C) := (e.symm x).toAdd
  have hu : (((IsCyclic.mulAutMulEquiv C f : (ZMod (Nat.card C))ˣ) :
      ZMod (Nat.card C))) = a 1 := rfl
  rw [hu]
  apply e.symm.injective
  have ha : Multiplicative.ofAdd (a z) = e.symm (f x) := by
    change e.symm (f (e (e.symm x))) = e.symm (f x)
    rw [e.apply_symm_apply]
  rw [← ha]
  rw [map_pow]
  change a z = (a 1).val • z
  calc
    a z = z.val • a 1 := by
      rw [← map_nsmul]
      congr 1
      simp [nsmul_eq_mul]
    _ = (a 1).val • z := by
      simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]
      exact mul_comm _ _

end Atlas.GroupTheory
