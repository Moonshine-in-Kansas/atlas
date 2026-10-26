import Atlas.LinearGroups.ReeF4.WeylModel
import Atlas.LinearGroups.ReeF4.RootGroupDerived
import Atlas.LinearGroups.ReeF4.LongRootDerived

/-! Concrete conjugate root factors for the alternating length-eight Weyl word.
The factors are actual subgroups of the intrinsic model, with faithful root
parameters. This file does not assert positivity, collection, or uniqueness
of the resulting twelve-parameter product. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def alternatingWeylHom (m : ℕ) : DihedralGroup 8 →* Model F m :=
  (modelWeylEmbedding m).comp (weylDihedralEquiv (F := F)).toMonoidHom

/-- Prefix (rho sigma)^k preceding the next short-root reflection. -/
def alternatingShortPrefix (m : ℕ) (k : Fin 4) : Model F m :=
  alternatingWeylHom m (.r (k.val : ZMod 8))

/-- Prefix (rho sigma)^k rho preceding the next long-root reflection. -/
def alternatingLongPrefix (m : ℕ) (k : Fin 4) : Model F m :=
  alternatingShortPrefix m k * alternatingWeylHom m (.sr 0)

def alternatingShortRootHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    shortRootSubgroup m hcard →* Model F m :=
  (MulAut.conj (alternatingShortPrefix m k)).toMonoidHom.comp
    (shortRootModelEmbedding hcard)

def alternatingLongRootHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    Multiplicative F →* Model F m :=
  (MulAut.conj (alternatingLongPrefix m k)).toMonoidHom.comp
    (modelLongSL2RootHom hcard)

theorem alternatingShortRootHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    Function.Injective (alternatingShortRootHom hcard k) :=
  (MulAut.conj (alternatingShortPrefix m k)).injective.comp
    (shortRootModelEmbedding_injective hcard)

theorem alternatingLongRootHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    Function.Injective (alternatingLongRootHom hcard k) :=
  (MulAut.conj (alternatingLongPrefix m k)).injective.comp
    (modelLongSL2RootHom_injective hcard)

def alternatingShortRootParameters {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    (F × F) ≃ (alternatingShortRootHom hcard k).range :=
  (shortRootParameters m hcard).trans
    (MonoidHom.ofInjective (alternatingShortRootHom_injective hcard k)).toEquiv

def alternatingLongRootEquiv {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    Multiplicative F ≃* (alternatingLongRootHom hcard k).range :=
  MonoidHom.ofInjective (alternatingLongRootHom_injective hcard k)

theorem card_alternatingShortRoot {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    Nat.card (alternatingShortRootHom hcard k).range = (Nat.card F)^2 := by
  rw [← Nat.card_congr (alternatingShortRootParameters hcard k), Nat.card_prod, pow_two]

theorem card_alternatingLongRoot {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) :
    Nat.card (alternatingLongRootHom hcard k).range = Nat.card F := by
  rw [← Nat.card_congr (alternatingLongRootEquiv hcard k).toEquiv]
  rfl

theorem alternatingShortRoot_mem_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) (k : Fin 4)
    (g : shortRootSubgroup m hcard) :
    alternatingShortRootHom hcard k g ∈ commutator (Model F m) := by
  exact (inferInstance : (commutator (Model F m)).Normal).conj_mem _
    (shortRootModelEmbedding_range_le_commutator hcard hm ⟨g,rfl⟩)
    (alternatingShortPrefix m k)

theorem alternatingLongRoot_mem_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) (k : Fin 4) (u : Multiplicative F) :
    alternatingLongRootHom hcard k u ∈ commutator (Model F m) := by
  exact (inferInstance : (commutator (Model F m)).Normal).conj_mem _
    (modelLongSL2RootHom_range_le_commutator hcard hm ⟨u,rfl⟩)
    (alternatingLongPrefix m k)

/-- An ordered product with four scalar and four paired-field inputs.
Injectivity and closure of this map are separate remaining obligations. -/
def alternatingRootWord {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : Fin 4 → F) (v : Fin 4 → F × F) : Model F m :=
  (List.ofFn (fun k : Fin 4 =>
    alternatingShortRootHom hcard k (shortRootParameters m hcard (v k)) *
      alternatingLongRootHom hcard k (Multiplicative.ofAdd (u k)))).prod

end Atlas.ReeF4
