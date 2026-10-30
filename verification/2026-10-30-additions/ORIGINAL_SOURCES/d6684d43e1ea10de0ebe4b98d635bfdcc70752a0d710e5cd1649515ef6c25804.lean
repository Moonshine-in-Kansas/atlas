import F4Work.PositiveLineKernelCoordinates

/-!
Source-only, uncompiled. The eleven-parameter subgroup N inside U embeds into
the actual full marked-line kernel K. The exact missing surjectivity statement
is K <= U (on the underlying Model elements). Neither this inclusion nor the
order, solvability, or a root filtration of the full K is assumed or proved.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem alternatingShortRoot_mem_positiveLineKernel {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4)
    (u : shortRootSubgroup m hcard) :
    (⟨alternatingShortRootHom hcard k u,
      alternatingShortRoot_mem_positiveRootSubgroup hcard k u⟩ : positiveRootSubgroup hcard)
        ∈ positiveLineKernel hcard := by
  apply (mem_positiveLineKernel_iff hcard _).mpr
  obtain ⟨⟨a,b⟩, rfl⟩ := (shortRootParameters m hcard).surjective u
  exact positiveShortFactor_markedLine_second hcard k a b

theorem alternatingLongRoot_mem_positiveLineKernel {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 3) (u : Multiplicative F) :
    (⟨alternatingLongRootHom hcard k.castSucc u,
      alternatingLongRoot_mem_positiveRootSubgroup hcard k.castSucc u⟩ : positiveRootSubgroup hcard)
        ∈ positiveLineKernel hcard := by
  apply (mem_positiveLineKernel_iff hcard _).mpr
  have hk : (k.castSucc : Fin 4) ≠ 3 := by
    intro he
    have hv := congrArg Fin.val he
    have ht := k.isLt
    change k.val = 3 at hv
    omega
  simpa only [positiveLongFactor, ofAdd_toAdd, if_neg hk, zero_smul, zero_add] using
    positiveLongFactor_markedLine_second hcard k.castSucc u.toAdd

/-- Solvability of the actual subgroup inside U; this is not a solvability theorem for full K. -/
theorem positiveLineKernel_isSolvable {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Group.IsSolvable (positiveLineKernel hcard) := by
  letI := positiveRootSubgroup_isSolvable hcard
  exact Group.isSolvable_of_isSolvable_injective
    (show Function.Injective (positiveLineKernel hcard).subtype from Subtype.val_injective)

/-- Actual inclusion N -> K, retaining the underlying intrinsic Model operator. -/
def positiveLineKernelEmbedding {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveLineKernel hcard →* markedLineRestrictionKernel (F := F) m where
  toFun g := ⟨positiveRootMarkedLineHom hcard g.val, g.property⟩
  map_one' := by
    apply Subtype.ext
    exact (positiveRootMarkedLineHom hcard).map_one
  map_mul' g h := by
    apply Subtype.ext
    exact (positiveRootMarkedLineHom hcard).map_mul g.val h.val

theorem positiveLineKernelEmbedding_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : positiveLineKernel hcard) :
    (positiveLineKernelEmbedding hcard g).val.val = g.val.val := rfl

theorem positiveLineKernelEmbedding_injective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Injective (positiveLineKernelEmbedding hcard) := by
  intro g h he
  apply Subtype.ext
  apply positiveRootMarkedLineHom_injective hcard
  exact congrArg Subtype.val he

theorem mem_positiveLineKernelEmbedding_range_iff {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : markedLineRestrictionKernel (F := F) m) :
    g ∈ (positiveLineKernelEmbedding hcard).range ↔
      g.val.val ∈ positiveRootSubgroup hcard := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.val.property
  · intro hg
    let u : positiveRootSubgroup hcard := ⟨g.val.val, hg⟩
    have hu : positiveRootMarkedLineHom hcard u = g.val := Subtype.ext rfl
    have hk : u ∈ positiveLineKernel hcard := by
      change positiveRootMarkedLineHom hcard u ∈ markedLineRestrictionKernel m
      rw [hu]
      exact g.property
    refine ⟨⟨u,hk⟩, ?_⟩
    apply Subtype.ext
    exact hu

/-- This equivalence exposes the missing full-kernel containment, without assuming it. -/
theorem positiveLineKernelEmbedding_surjective_iff {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Surjective (positiveLineKernelEmbedding hcard) ↔
      ∀ g : markedLineRestrictionKernel (F := F) m,
        g.val.val ∈ positiveRootSubgroup hcard := by
  constructor
  · intro hs g
    exact (mem_positiveLineKernelEmbedding_range_iff hcard g).mp (hs g)
  · intro h g
    exact (mem_positiveLineKernelEmbedding_range_iff hcard g).mpr (h g)

/-- Eleven explicit root parameters give distinct elements of the actual full kernel. -/
def positiveLineKernelFullParam {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    ((Fin 3 → F) × (Fin 4 → F × F)) → markedLineRestrictionKernel (F := F) m :=
  (positiveLineKernelEmbedding hcard) ∘ positiveLineKernelParam hcard

theorem positiveLineKernelFullParam_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p : (Fin 3 → F) × (Fin 4 → F × F)) :
    (positiveLineKernelFullParam hcard p).val.val = positiveLineKernelWord hcard p.1 p.2 := rfl

theorem positiveLineKernelFullParam_injective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Injective (positiveLineKernelFullParam hcard) :=
  (positiveLineKernelEmbedding_injective hcard).comp (positiveLineKernelParam_injective hcard)

/-- Only the lower bound for the full kernel follows before K <= U is established. -/
theorem card_markedLineRestrictionKernel_lower_bound {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    (Nat.card F) ^ 11 ≤ Nat.card (markedLineRestrictionKernel (F := F) m) := by
  rw [← card_positiveLineKernel hcard]
  exact Nat.card_le_card_of_injective _ (positiveLineKernelEmbedding_injective hcard)

end Atlas.ReeF4
