import Mathlib.LinearAlgebra.Projectivization.Basic

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.LinearAlgebra
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Inclusion of a genuine linear subspace identifies exactly its projective points. -/
def projectiveSubmoduleEquiv (W : Submodule F V) :
    (ℙ F W) ≃ {p : ℙ F V // p.rep ∈ W} := by
  let m := Projectivization.map W.subtype W.subtype_injective
  have hm (p : ℙ F W) : (m p).rep ∈ W := by
    induction p using Projectivization.ind with
    | h v hv =>
      change (Projectivization.mk F v.val (W.subtype_injective.ne hv)).rep ∈ W
      obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v.val (W.subtype_injective.ne hv)
      rw [← ha]
      exact W.smul_mem a.val v.prop
  refine Equiv.ofBijective (fun p => ⟨m p,hm p⟩) ⟨?_,?_⟩
  · intro p q h
    exact Projectivization.map_injective W.subtype W.subtype_injective (congrArg Subtype.val h)
  · intro p
    let v : W := ⟨p.val.rep,p.prop⟩
    have hv : v ≠ 0 := by intro h; exact p.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk F v hv,?_⟩
    apply Subtype.ext
    change Projectivization.mk F p.val.rep _ = p.val
    exact Projectivization.mk_rep p.val

end Atlas.LinearAlgebra
