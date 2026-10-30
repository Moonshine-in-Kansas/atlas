import Atlas.GroupTheory.TailNormalizerLemmas
import Atlas.LinearGroups.ReeF4.TailRhoRootConjugation
import Atlas.LinearGroups.ReeF4.TailRootMembership

/-!
Source-only adapters from the existing actual root identities to subgroup bounds.
No coordinate formula, root operator, tail subgroup or parameter range is changed.
The proofs use explicit generic applications rather than concrete range elimination,
list-equality case splitting, or group normalization in Model.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem rho_alternatingLongRange_le_tail_comap {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) :
    (alternatingLongRootHom hcard k).range ≤
      (positiveRootTailSubgroup hcard).comap (MulAut.conj (weylRhoModel m)).toMonoidHom :=
  TailNormalizer.range_le_conj_comap_of_surjective_parameters
    (positiveRootTailSubgroup hcard) (weylRhoModel m)
    (alternatingLongRootHom hcard k)
    (Multiplicative.ofAdd : F → Multiplicative F)
    (fun u => ⟨u.toAdd, rfl⟩)
    (positiveLongFactor hcard (Fin.rev k))
    (rho_positiveLong_conjugate hcard k)
    (positiveLongFactor_mem_tail hcard (Fin.rev k))

theorem rho_alternatingShortRange_le_tail_comap {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 3) :
    (alternatingShortRootHom hcard k.succ).range ≤
      (positiveRootTailSubgroup hcard).comap (MulAut.conj (weylRhoModel m)).toMonoidHom :=
  TailNormalizer.range_le_conj_comap_of_surjective_parameters
    (positiveRootTailSubgroup hcard) (weylRhoModel m)
    (alternatingShortRootHom hcard k.succ)
    (shortRootParameters m hcard) (shortRootParameters m hcard).surjective
    (fun p : F × F => positiveShortFactor hcard (Fin.rev k).succ p.1 p.2)
    (fun p => rho_positiveTailShort_conjugate hcard k p.1 p.2)
    (fun p => positiveShortFactor_succ_mem_tail hcard (Fin.rev k) p.1 p.2)

/-- The literal seven-factor tail, in its unchanged collection order. The only
conversion here unfolds the tail/list wrappers, leaving each root homomorphism intact. -/
theorem positiveRootTail_le_rho_comap {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ≤
      (positiveRootTailSubgroup hcard).comap (MulAut.conj (weylRhoModel m)).toMonoidHom :=
  TailNormalizer.subgroupListJoin_seven_le
    (alternatingLongRootHom hcard 0).range
    (alternatingShortRootHom hcard 1).range
    (alternatingLongRootHom hcard 1).range
    (alternatingShortRootHom hcard 2).range
    (alternatingLongRootHom hcard 2).range
    (alternatingShortRootHom hcard 3).range
    (alternatingLongRootHom hcard 3).range
    ((positiveRootTailSubgroup hcard).comap (MulAut.conj (weylRhoModel m)).toMonoidHom)
    (rho_alternatingLongRange_le_tail_comap hcard 0)
    (rho_alternatingShortRange_le_tail_comap hcard 0)
    (rho_alternatingLongRange_le_tail_comap hcard 1)
    (rho_alternatingShortRange_le_tail_comap hcard 1)
    (rho_alternatingLongRange_le_tail_comap hcard 2)
    (rho_alternatingShortRange_le_tail_comap hcard 2)
    (rho_alternatingLongRange_le_tail_comap hcard 3)

end Atlas.ReeF4
