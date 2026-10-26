import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalDichotomy
import Atlas.LinearGroups.Chevalley.RootData.CartanConnectivity
import Atlas.LinearGroups.Chevalley.ModelFlagAction
import Atlas.LinearGroups.Chevalley.ModelBorelSolvable
import Atlas.LinearGroups.Chevalley.ModelPerfectnessGood
import Atlas.GroupTheory.PerfectSolvableSupplement

/-! Simplicity of the literal uniform adjoint model in the existing Good
range. The proof uses actual B-overgroup cells, Cartan connectivity, the
proved core-free Model Borel, its solvability, and independently proved
good-range perfectness. There is no group-order or old-model recognition. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_normal_eq_bot_or_borel_sup_eq_top
    (Φ : RootType) (K : Type*) [Field K] [Finite K]
    (A : Subgroup (Model Φ K)) [A.Normal] :
    A = ⊥ ∨ A ⊔ modelBorel Φ K = ⊤ := by
  let f := selectedWeightCompanionRho Φ K
  let B := positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K
  let C := A.comap f
  letI : C.Normal := (inferInstance : A.Normal).comap f
  have hf : Function.Surjective f := selectedWeightCompanionRho_surjective Φ K
  have hmap : C.map f = A := Subgroup.map_comap_eq_self_of_surjective hf A
  rcases normal_sup_positiveWitnessedTorusJoin_eq_self_or_top
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ) (rootDatum_cartan_connected Φ) C with h | h
  · left
    have hCB : C ≤ B := (show C ≤ C ⊔ B from le_sup_left).trans h.le
    have hAB : A ≤ modelBorel Φ K := by
      change A ≤ B.map f
      rw [← hmap]
      exact Subgroup.map_mono hCB
    have hcore : A ≤ (modelBorel Φ K).normalCore := Subgroup.normal_le_normalCore.mpr hAB
    rw [modelBorel_normalCore_eq_bot Φ K] at hcore
    exact le_antisymm hcore bot_le
  · right
    have he := congrArg (fun H : Subgroup (SelectedWeightCompanion Φ K) => H.map f) h
    rw [Subgroup.map_sup, hmap, Subgroup.map_top_of_surjective f hf] at he
    exact he

/-- The original Good predicate, with all its characteristic-two and
characteristic-three exceptions, suffices for simplicity of the actual Model. -/
theorem model_isSimpleGroup_of_good
    (Φ : RootType) (K : Type*) [Field K] [Fintype K]
    (hgood : Φ.Good (Fintype.card K)) : IsSimpleGroup (Model Φ K) := by
  letI : Nontrivial (Model Φ K) :=
    (modelX_injective Φ K ⟨0, Φ.rank_pos⟩).nontrivial
  letI := model_isPerfect_of_good Φ K hgood
  letI := modelBorel_isSolvable Φ K
  apply Atlas.GroupTheory.simple_of_perfect_solvable_normal_supplement (modelBorel Φ K)
  intro A hA hne
  letI : A.Normal := hA
  rcases model_normal_eq_bot_or_borel_sup_eq_top Φ K A with h | h
  · exact False.elim (hne h)
  · exact h

end Atlas.Chevalley
