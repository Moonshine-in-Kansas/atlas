import Atlas.LinearGroups.ReeF4.WeylSL2Weyl
import Atlas.LinearGroups.ReeF4.WeylSL2Membership
import Atlas.LinearGroups.ReeF4.WeylModel

/-! The faithful fundamental SL₂ representation belongs to the actual Ree model.
Membership follows from actual root elements and the source Weyl involution,
using ordinary two-dimensional transvection generation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem longSL2Representation_mem_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (A : LongSL2 (F := F)) :
    longSL2Representation (theta F m).toRingHom A ∈ modelSubgroup F m := by
  apply Matrix.SL2.transvection_induction
    (fun A => longSL2Representation (theta F m).toRingHom A ∈ modelSubgroup F m)
    ?_ ?_ A
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change longSL2Representation (theta F m).toRingHom (longSL2Upper c) ∈ _
      rw [longSL2Representation_upper]
      exact longSL2Parameter_mem_modelSubgroup hcard c
    · rw [longSL2_lower, map_mul, map_mul, longSL2Representation_weyl,
        longSL2Representation_upper]
      exact (modelSubgroup F m).mul_mem
        ((modelSubgroup F m).mul_mem (weylOperator_mem_modelSubgroup m 1)
          (longSL2Parameter_mem_modelSubgroup hcard c))
        (weylOperator_mem_modelSubgroup m 1)
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact (modelSubgroup F m).mul_mem hA hB

def modelLongSL2Hom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    LongSL2 (F := F) →* Model F m where
  toFun A := ⟨longSL2Representation (theta F m).toRingHom A,
    longSL2Representation_mem_modelSubgroup hcard A⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (longSL2Representation (theta F m).toRingHom)
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul (longSL2Representation (theta F m).toRingHom) A B

theorem modelLongSL2Hom_injective {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (modelLongSL2Hom hcard) := by
  intro A B h
  exact longSL2Representation_injective (theta F m).toRingHom
    (congrArg (fun g : Model F m => g.val) h)

def modelLongSL2Subgroup {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Subgroup (Model F m) := (modelLongSL2Hom hcard).range

def modelLongSL2Equiv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    LongSL2 (F := F) ≃* modelLongSL2Subgroup hcard :=
  MonoidHom.ofInjective (modelLongSL2Hom_injective hcard)

end Atlas.ReeF4
