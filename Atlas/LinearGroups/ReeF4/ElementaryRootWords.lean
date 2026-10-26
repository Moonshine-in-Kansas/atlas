import Atlas.LinearGroups.ReeF4.ElementaryDerived
import Atlas.LinearGroups.ReeF4.PositiveRootSubgroup

/-! Actual word membership in the locally generated subgroup.
No equality between elementarySubgroup and Model is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem alternatingWeylHom_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (d : DihedralGroup 8) :
    alternatingWeylHom (F := F) m d ∈ elementarySubgroup hcard := by
  have hr (i : ZMod 8) : alternatingWeylHom (F := F) m (.r i) =
      (weylRhoModel m * weylSigmaModel m)^i.val := by
    apply Subtype.ext
    rfl
  have hs (i : ZMod 8) : alternatingWeylHom (F := F) m (.sr i) =
      weylRhoModel m * (weylRhoModel m * weylSigmaModel m)^i.val := by
    apply Subtype.ext
    rfl
  have hp (n : ℕ) : (weylRhoModel m * weylSigmaModel m)^n ∈ elementarySubgroup hcard :=
    (elementarySubgroup hcard).pow_mem
      ((elementarySubgroup hcard).mul_mem (weylRho_mem_elementary hcard)
        (weylSigma_mem_elementary hcard)) n
  cases d with
  | r i => rw [hr]; exact hp _
  | sr i =>
    rw [hs]
    exact (elementarySubgroup hcard).mul_mem (weylRho_mem_elementary hcard) (hp _)

theorem modelWeylEmbedding_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : weylSubgroup (F := F)) :
    modelWeylEmbedding m w ∈ elementarySubgroup hcard := by
  obtain ⟨d,rfl⟩ := (weylDihedralEquiv (F := F)).surjective w
  exact alternatingWeylHom_mem_elementary hcard d

theorem alternatingShortPrefix_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    alternatingShortPrefix (F := F) m k ∈ elementarySubgroup hcard :=
  alternatingWeylHom_mem_elementary hcard _

theorem alternatingLongPrefix_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    alternatingLongPrefix (F := F) m k ∈ elementarySubgroup hcard :=
  (elementarySubgroup hcard).mul_mem (alternatingShortPrefix_mem_elementary hcard k)
    (alternatingWeylHom_mem_elementary hcard _)

theorem alternatingShortRoot_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) (g : shortRootSubgroup m hcard) :
    alternatingShortRootHom hcard k g ∈ elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem
    ((elementarySubgroup hcard).mul_mem (alternatingShortPrefix_mem_elementary hcard k)
      (shortRoot_range_le_elementary hcard ⟨g,rfl⟩))
    ((elementarySubgroup hcard).inv_mem (alternatingShortPrefix_mem_elementary hcard k))

theorem alternatingLongRoot_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) (u : Multiplicative F) :
    alternatingLongRootHom hcard k u ∈ elementarySubgroup hcard := by
  exact (elementarySubgroup hcard).mul_mem
    ((elementarySubgroup hcard).mul_mem (alternatingLongPrefix_mem_elementary hcard k)
      (longRoot_range_le_elementary hcard ⟨u,rfl⟩))
    ((elementarySubgroup hcard).inv_mem (alternatingLongPrefix_mem_elementary hcard k))

theorem positiveRootSubgroup_le_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    positiveRootSubgroup hcard ≤ elementarySubgroup hcard := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨k,u,rfl⟩ | ⟨k,u,rfl⟩)
  · exact alternatingShortRoot_mem_elementary hcard k u
  · exact alternatingLongRoot_mem_elementary hcard k u

theorem alternatingRootWord_mem_elementary {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fin 4 → F) (v : Fin 4 → F × F) :
    alternatingRootWord hcard u v ∈ elementarySubgroup hcard :=
  positiveRootSubgroup_le_elementary hcard
    (alternatingRootWord_mem_positiveRootSubgroup hcard u v)

/-- Use this lifted word when proving transitivity of the elementary action. -/
def elementaryAlternatingRootWord {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fin 4 → F) (v : Fin 4 → F × F) :
    elementarySubgroup hcard :=
  ⟨alternatingRootWord hcard u v, alternatingRootWord_mem_elementary hcard u v⟩

end Atlas.ReeF4
