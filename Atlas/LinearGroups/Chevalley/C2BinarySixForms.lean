import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2MinusculeCorrespondence
import Atlas.LinearGroups.Chevalley.WeightCompanionLeftInduction
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Sign

/-! Six quadratic refinements in the actual four-coordinate C2 weight
module over F2. Only the six forms and four root-generator matrices are
checked finitely; no whole group is enumerated or recognized from its order. -/
noncomputable section
namespace Atlas.Chevalley.C2Binary
open Classical Integral.RankTwo.C2Minuscule
open scoped Matrix

abbrev K := ZMod 2
abbrev V := Fin 4 → K
abbrev G := Companion K

def parameter : Fin 6 → V :=
  ![![1,0,1,0], ![1,1,1,0], ![1,0,1,1],
    ![0,1,0,1], ![1,1,0,1], ![0,1,1,1]]

def form (i : Fin 6) (v : V) : K :=
  v 0 * v 2 + v 1 * v 3 +
    parameter i 0 * v 2 + parameter i 1 * v 3 +
    parameter i 2 * v 0 + parameter i 3 * v 1

theorem form_injective : Function.Injective form := by decide +kernel

def Preserves (A : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∀ i : Fin 6, ∃ j : Fin 6, (fun v => form i (A *ᵥ v)) = form j

theorem preserves_one : Preserves 1 := by
  intro i
  exact ⟨i, by funext v; simp only [Matrix.one_mulVec]⟩

theorem preserves_mul {A B : Matrix (Fin 4) (Fin 4) K}
    (hA : Preserves A) (hB : Preserves B) : Preserves (A * B) := by
  intro i
  obtain ⟨j, hj⟩ := hA i
  obtain ⟨k, hk⟩ := hB j
  refine ⟨k, ?_⟩
  funext v
  rw [← Matrix.mulVec_mulVec]
  exact (congrFun hj (B *ᵥ v)).trans (congrFun hk v)

theorem preserves_X (k : Fin 2) (t : K) :
    Preserves (1 + t • (![ea, eb] k).map (Int.castRingHom K)) := by
  exact (show ∀ k : Fin 2, ∀ t : K,
    Preserves (1 + t • (![ea, eb] k).map (Int.castRingHom K)) by
      unfold Preserves
      decide +kernel) k t

theorem preserves_Y (k : Fin 2) (t : K) :
    Preserves (1 + t • (![fa, fb] k).map (Int.castRingHom K)) := by
  exact (show ∀ k : Fin 2, ∀ t : K,
    Preserves (1 + t • (![fa, fb] k).map (Int.castRingHom K)) by
      unfold Preserves
      decide +kernel) k t

theorem preserves_weight (g : G) : Preserves (weightMatrixHom K g) := by
  apply weightCompanion_induction_left (rootDatum C2).pairing (rootDatum C2).base
    (selectedWeightOrbits C2) (selectedWeightOrbits_closed C2)
    (selectedWeightOrbits_minuscule C2) K ?_ ?_ ?_ g
  · simpa only [map_one] using preserves_one
  · intro i t h hh
    obtain ⟨k, rfl⟩ := (rootDatum C2).indexEquiv.surjective i
    change Preserves (weightMatrixHom K (selectedWeightCompanionX C2 K k t * h))
    rw [map_mul, matrix_X (R := K) k t]
    exact preserves_mul (preserves_X k t) hh
  · intro i t h hh
    obtain ⟨k, rfl⟩ := (rootDatum C2).indexEquiv.surjective i
    change Preserves (weightMatrixHom K (selectedWeightCompanionY C2 K k t * h))
    rw [map_mul, matrix_Y (R := K) k t]
    exact preserves_mul (preserves_Y k t) hh

theorem long_root_swaps (i : Fin 6) :
    (fun v : V => form i (XB (1 : K) *ᵥ v)) = form (Equiv.swap 0 1 i) := by
  exact (show ∀ i : Fin 6,
    (fun v : V => form i (XB (1 : K) *ᵥ v)) = form (Equiv.swap 0 1 i) by
      decide +kernel) i

end Atlas.Chevalley.C2Binary
