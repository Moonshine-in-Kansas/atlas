import Atlas.LinearGroups.F4.LongSeedCommutator
import Atlas.LinearGroups.G2.LongRootNormalGeneration

/-! Three genuine long-root seeds, one for each orbit under the short-root
Weyl subgroup. All are commutators, including in characteristics two and three. -/
noncomputable section
namespace Atlas.F4
open scoped commutatorElement
variable {F : Type*} [Field F]

def longRootSeedB (t : F) : Model F := g2Embedding (Atlas.G2.rootB t)
def longRootSeedE (t : F) : Model F := g2Embedding (Atlas.G2.rootE t)

theorem embedded_weylR_longRootSeed (t : F) :
    g2Embedding Atlas.G2.weylR * longRootSeed t * (g2Embedding Atlas.G2.weylR)⁻¹ =
      longRootSeedB t := by
  simpa only [longRootSeed,longRootSeedB,map_mul,map_inv] using
    congrArg g2Embedding (Atlas.G2.weylR_rootA t)

theorem embedded_weylS_longRootSeedB (t : F) :
    g2Embedding Atlas.G2.weylS * longRootSeedB t * (g2Embedding Atlas.G2.weylS)⁻¹ =
      longRootSeedE t := by
  simpa only [longRootSeedB,longRootSeedE,map_mul,map_inv] using
    congrArg g2Embedding (Atlas.G2.weylS_rootB t)

/-- A, B and E, with their original octonion root parameters. -/
def longRootSeeds (seed : Fin 3) (t : F) : Model F :=
  ![longRootSeed t,longRootSeedB t,longRootSeedE t] seed

def longRootSeedConjugator (seed : Fin 3) : Model F :=
  ![1,g2Embedding Atlas.G2.weylR,
    g2Embedding Atlas.G2.weylS * g2Embedding Atlas.G2.weylR] seed

theorem longRootSeedConjugator_conjugate (seed : Fin 3) (t : F) :
    longRootSeedConjugator seed * longRootSeed t * (longRootSeedConjugator seed)⁻¹ =
      longRootSeeds seed t := by
  fin_cases seed
  · simp [longRootSeedConjugator,longRootSeeds]
  · exact embedded_weylR_longRootSeed t
  · change (g2Embedding Atlas.G2.weylS * g2Embedding Atlas.G2.weylR) * longRootSeed t *
      (g2Embedding Atlas.G2.weylS * g2Embedding Atlas.G2.weylR)⁻¹ = longRootSeedE t
    calc
      _ = g2Embedding Atlas.G2.weylS *
          (g2Embedding Atlas.G2.weylR * longRootSeed t * (g2Embedding Atlas.G2.weylR)⁻¹) *
          (g2Embedding Atlas.G2.weylS)⁻¹ := by group
      _ = _ := by rw [embedded_weylR_longRootSeed,embedded_weylS_longRootSeedB]

/-- Explicit commutator expressions inherited from the embedded long A₂. -/
theorem longRootSeeds_commutator (seed : Fin 3) (t : F) :
    ⁅longRootSeedConjugator seed * g2Embedding (Atlas.G2.rootB t) *
        (longRootSeedConjugator seed)⁻¹,
      longRootSeedConjugator seed * g2Embedding (Atlas.G2.rootE 1) *
        (longRootSeedConjugator seed)⁻¹⁆ = longRootSeeds seed t := by
  rw [←conjugate_commutatorElement,longRootSeed_commutator,
    longRootSeedConjugator_conjugate]

theorem longRootSeeds_mem_commutator (seed : Fin 3) (t : F) :
    longRootSeeds seed t ∈ commutator (Model F) := by
  rw [←longRootSeeds_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem longRootSeedB_mem_commutator (t : F) :
    longRootSeedB t ∈ commutator (Model F) := longRootSeeds_mem_commutator 1 t

theorem longRootSeedE_mem_commutator (t : F) :
    longRootSeedE t ∈ commutator (Model F) := longRootSeeds_mem_commutator 2 t

theorem longRootSeeds_add (seed : Fin 3) (s t : F) :
    longRootSeeds seed s * longRootSeeds seed t = longRootSeeds seed (s+t) := by
  rw [←longRootSeedConjugator_conjugate,←longRootSeedConjugator_conjugate,
    ←longRootSeedConjugator_conjugate,←longRootSeed_add]
  group

theorem longRootSeeds_injective (seed : Fin 3) : Function.Injective (longRootSeeds (F := F) seed) := by
  intro s t h
  rw [←longRootSeedConjugator_conjugate,←longRootSeedConjugator_conjugate] at h
  exact longRootSeed_injective (mul_left_cancel (mul_right_cancel h))

end Atlas.F4
