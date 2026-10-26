import Atlas.LinearGroups.SuzukiFamily.CellClosure
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Exhaustive, unique two-cell parameterization of the actual generated group. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem generated_hasForm (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    {g : Atlas.Symplectic.Sp 2 F} (hg : g ∈ generated m) : HasForm m g := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact hasForm_one m
  | mul_left x hx y hy ih =>
    rcases hx with ((⟨⟨a,b⟩,rfl⟩ | ⟨t,rfl⟩) | hw)
    · exact hasForm_root_left m hcard a b ih
    · exact hasForm_torus_left m hcard t ih
    · have he : x=weylElement := Set.mem_singleton_iff.mp hw
      subst x
      exact hasForm_weyl_left m hcard ih
  | inv_mul_cancel x hx y hy ih =>
    rcases hx with ((⟨⟨a,b⟩,rfl⟩ | ⟨t,rfl⟩) | hw)
    · rw [rootElement_inv m hcard]
      exact hasForm_root_left m hcard _ _ ih
    · rw [← torusElement_inv]
      exact hasForm_torus_left m hcard _ ih
    · have he : x=weylElement := Set.mem_singleton_iff.mp hw
      subst x
      rw [weylElement_inv]
      exact hasForm_weyl_left m hcard ih

theorem shortForm_mem (m : ℕ) (a b : F) (t : Fˣ) : shortForm m a b t ∈ generated m :=
  (generated m).mul_mem (rootElement_mem m a b) (torusElement_mem m t)

theorem longForm_mem (m : ℕ) (a b : F) (t : Fˣ) (c d : F) :
    longForm m a b t c d ∈ generated m :=
  (generated m).mul_mem ((generated m).mul_mem
    ((generated m).mul_mem (rootElement_mem m a b) (weylElement_mem m))
    (torusElement_mem m t)) (rootElement_mem m c d)

abbrev CellParameters (F : Type*) [Field F] :=
  (F × F × Fˣ) ⊕ ((F × F) × (Fˣ × F × F))

def cellMap (m : ℕ) : CellParameters F → Group F m
  | .inl (a,b,t) => ⟨shortForm m a b t,shortForm_mem m a b t⟩
  | .inr ((a,b),(t,c,d)) => ⟨longForm m a b t c d,longForm_mem m a b t c d⟩

theorem cellMap_bijective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Bijective (cellMap (F := F) m) := by
  constructor
  · intro p q he
    have hv := congrArg Subtype.val he
    cases p with
    | inl p =>
      cases q with
      | inl q => exact congrArg Sum.inl (shortForm_injective m hv)
      | inr q => exact False.elim (short_ne_long m hcard _ _ _ _ _ _ _ _ hv)
    | inr p =>
      cases q with
      | inl q => exact False.elim (short_ne_long m hcard _ _ _ _ _ _ _ _ hv.symm)
      | inr q => exact congrArg Sum.inr (longForm_injective m hcard hv)
  · intro g
    rcases generated_hasForm m hcard g.property with ⟨a,b,t,he⟩ | ⟨a,b,t,c,d,he⟩
    · exact ⟨.inl (a,b,t),Subtype.ext he.symm⟩
    · exact ⟨.inr ((a,b),(t,c,d)),Subtype.ext he.symm⟩

def cellEquiv (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) : CellParameters F ≃ Group F m :=
  Equiv.ofBijective (cellMap m) (cellMap_bijective m hcard)
end Atlas.SuzukiFamily
