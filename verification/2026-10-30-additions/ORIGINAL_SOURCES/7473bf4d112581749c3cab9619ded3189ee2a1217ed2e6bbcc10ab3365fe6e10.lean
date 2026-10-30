import F4Work.PositiveMarkedLineAction
import Atlas.LinearGroups.ReeF4.PositiveRootOrder

/-!
Source-only, uncompiled. This identifies the pointwise marked-line kernel INSIDE
U with eleven parameters, without identifying it with the full line kernel.
The condition is u 3 = 0 in the established unique twelve-parameter U word.
The other three long and four paired short parameters remain unrestricted.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual pointwise-line kernel inside U, defined by restriction, not by its order. -/
def positiveLineKernel {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Subgroup (positiveRootSubgroup hcard) :=
  ((markedLineRestriction m).comp (positiveRootMarkedLineHom hcard)).ker

theorem positiveLineKernel_normal {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    (positiveLineKernel hcard).Normal :=
  inferInstanceAs (((markedLineRestriction m).comp (positiveRootMarkedLineHom hcard)).ker.Normal)

/-- U already fixes the first marked root; the second root detects the remaining restriction. -/
theorem mem_positiveLineKernel_iff {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : positiveRootSubgroup hcard) :
    g ∈ positiveLineKernel hcard ↔
      g.val.val (rootVector (F := F) (2,0)) = rootVector (2,0) := by
  change positiveRootMarkedLineHom hcard g ∈ markedLineRestrictionKernel m ↔ _
  rw [mem_markedLineRestrictionKernel_iff]
  constructor
  · intro hg
    exact hg (rootVector (2,0)) (Submodule.subset_span (by simp))
  · intro h2 w hw
    change g.val.val w = w
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hw
    rw [← he, _root_.map_add, _root_.map_smul, _root_.map_smul,
      positiveRootSubgroup_fixes_lowestRoot hcard g, h2]

theorem alternatingRootWord_mem_positiveLineKernel_iff {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (u : Fin 4 → F) (v : Fin 4 → F × F) :
    (⟨alternatingRootWord hcard u v,
      alternatingRootWord_mem_positiveRootSubgroup hcard u v⟩ : positiveRootSubgroup hcard)
        ∈ positiveLineKernel hcard ↔ u 3 = 0 := by
  rw [mem_positiveLineKernel_iff]
  change (alternatingRootWord hcard u v).val (rootVector (F := F) (2,0)) =
    rootVector (2,0) ↔ u 3 = 0
  rw [alternatingRootWord_markedLine_second]
  constructor
  · intro he
    have hc := congrArg (fun w : TraceZero F => w.val.2 0 0) he
    simpa [rootVector, Pi.single_apply, smul_eq_mul] using hc
  · intro hu
    simp only [hu, zero_smul, zero_add]

/-- The retained word with precisely the last long parameter set to zero. -/
def positiveLineKernelWord {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (u : Fin 3 → F) (v : Fin 4 → F × F) : Model F m :=
  alternatingRootWord hcard (Fin.snoc u 0) v

theorem positiveLineKernelWord_eq_sevenFactors {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (u : Fin 3 → F) (v : Fin 4 → F × F) :
    positiveLineKernelWord hcard u v =
      positiveShortFactor hcard 0 (v 0).1 (v 0).2 *
      (positiveLongFactor hcard 0 (u 0) *
      (positiveShortFactor hcard 1 (v 1).1 (v 1).2 *
      (positiveLongFactor hcard 1 (u 1) *
      (positiveShortFactor hcard 2 (v 2).1 (v 2).2 *
      (positiveLongFactor hcard 2 (u 2) *
        positiveShortFactor hcard 3 (v 3).1 (v 3).2))))) := by
  rw [positiveLineKernelWord, positiveRootWord_expand]
  have hzero : positiveLongFactor hcard 3 (0 : F) = 1 :=
    (alternatingLongRootHom hcard 3).map_one
  change positiveShortFactor hcard 0 (v 0).1 (v 0).2 *
      (positiveLongFactor hcard 0 (u 0) *
      (positiveShortFactor hcard 1 (v 1).1 (v 1).2 *
      (positiveLongFactor hcard 1 (u 1) *
      (positiveShortFactor hcard 2 (v 2).1 (v 2).2 *
      (positiveLongFactor hcard 2 (u 2) *
      (positiveShortFactor hcard 3 (v 3).1 (v 3).2 * positiveLongFactor hcard 3 0)))))) = _
  rw [hzero, mul_one]

/-- An actual subgroup-valued parametrization, rather than a word-image cardinality alone. -/
def positiveLineKernelParam {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    ((Fin 3 → F) × (Fin 4 → F × F)) → positiveLineKernel hcard := fun p =>
  ⟨⟨positiveLineKernelWord hcard p.1 p.2,
    alternatingRootWord_mem_positiveRootSubgroup hcard (Fin.snoc p.1 0) p.2⟩,
    (alternatingRootWord_mem_positiveLineKernel_iff hcard (Fin.snoc p.1 0) p.2).mpr
      (Fin.snoc_last _ _)⟩

theorem positiveLineKernelParam_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p : (Fin 3 → F) × (Fin 4 → F × F)) :
    (positiveLineKernelParam hcard p).val.val = positiveLineKernelWord hcard p.1 p.2 := rfl

theorem positiveLineKernelParam_injective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Injective (positiveLineKernelParam hcard) := by
  intro p q hpq
  have he := congrArg (fun g : positiveLineKernel hcard => g.val.val) hpq
  have hi := alternatingRootWord_parameters_injective hcard
    (Fin.snoc p.1 0) (Fin.snoc q.1 0) p.2 q.2 he
  apply Prod.ext
  · have ht := congrArg Fin.init hi.1
    simpa only [Fin.init_snoc] using ht
  · exact hi.2

/-- Surjectivity is onto U's pointwise-line kernel only, not onto the full line kernel. -/
theorem positiveLineKernelParam_surjective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Surjective (positiveLineKernelParam hcard) := by
  intro g
  obtain ⟨⟨u,v⟩, huv⟩ := (positiveRootParameters hcard).surjective g.val
  have he : alternatingRootWord hcard u v = g.val.val := congrArg Subtype.val huv
  have hu : u 3 = 0 :=
    (alternatingRootWord_mem_positiveLineKernel_iff hcard u v).mp (by
      have hsub : (⟨alternatingRootWord hcard u v,
        alternatingRootWord_mem_positiveRootSubgroup hcard u v⟩ : positiveRootSubgroup hcard) =
          g.val := Subtype.ext he
      rw [hsub]
      exact g.property)
  refine ⟨(Fin.init u,v), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change alternatingRootWord hcard (Fin.snoc (Fin.init u) 0) v = g.val.val
  have hs : Fin.snoc (Fin.init u) (u 3) = u := Fin.snoc_init_self u
  rw [← hu, hs]
  exact he

def positiveLineKernelParameters {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    ((Fin 3 → F) × (Fin 4 → F × F)) ≃ positiveLineKernel hcard :=
  Equiv.ofBijective (positiveLineKernelParam hcard)
    ⟨positiveLineKernelParam_injective hcard, positiveLineKernelParam_surjective hcard⟩

/-- q^11 is established for the actual subgroup inside U; no full line-kernel count is asserted. -/
theorem card_positiveLineKernel {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (positiveLineKernel hcard) = (Nat.card F) ^ 11 := by
  rw [← Nat.card_congr (positiveLineKernelParameters hcard)]
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

end Atlas.ReeF4
