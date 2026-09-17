import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Removing the zero vector from a finite quadratic zero locus -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [CommRing F] [AddCommGroup V] [Module F V]

/-- The nonzero singular locus removes exactly one vector. -/
theorem card_nonzero_singular [Finite V] (Q : QuadraticForm F V) :
    Nat.card {x : {v : V // Q v=0} // x.val≠0} = Nat.card {v : V // Q v=0}-1 := by
  classical
  letI := Fintype.ofFinite V
  letI : Unique {x : {v : V // Q v=0} // x.val=0} :=
    { default := ⟨⟨0,Q.map_zero⟩,rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext x.prop) }
  have hz : Fintype.card {x : {v : V // Q v=0} // x.val=0} = 1 := Fintype.card_unique
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hz,
    ← Nat.card_eq_fintype_card]

end Atlas.Quadratic
