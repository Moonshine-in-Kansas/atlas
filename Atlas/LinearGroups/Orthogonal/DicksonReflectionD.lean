import Atlas.LinearGroups.Orthogonal.DicksonInvariant
import Atlas.LinearGroups.Orthogonal.EvenDExchange
import Atlas.LinearAlgebra.QuadraticDicksonMultiplicative

/-! # Residual parity on the reflection subgroup of actual split D

These statements do not identify the reflection subgroup with the full group,
or identify the kernel with the elementary subgroup.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F] {n : ℕ}

def splitDExchangeElement (i : Fin n) : O_DPlus n F :=
  (isometryCarrierEquiv _).symm (splitDExchange i)

theorem splitDExchangeElement_mem_reflections (i : Fin n) :
    splitDExchangeElement (F := F) i ∈ reflectionSubgroup (formD n F) := by
  apply Subgroup.subset_closure
  exact ⟨e i - f i, exchange_direction_nonzero _ _ _ (formD_e i) (formD_f i)
    (polarD_ef i), rfl⟩

theorem dicksonValue_splitDExchange (i : Fin n) :
    dicksonValue (formD n F) (splitDExchangeElement i) = 1 := by
  change (Module.finrank F (residual (formD n F) (splitDExchange i)) : ZMod 2) = 1
  rw [splitDExchange_residual_finrank, Nat.cast_one]

def splitDReflectionCharacter : reflectionSubgroup (formD n F) →* Multiplicative (ZMod 2) :=
  reflectionDicksonCharacter _ polarD_nondegenerate

theorem splitDReflectionCharacter_value (g : reflectionSubgroup (formD n F)) :
    (splitDReflectionCharacter g).toAdd = dicksonValue (formD n F) g.val := rfl

theorem splitDReflectionCharacter_surjective (hn : 0 < n) :
    Function.Surjective (splitDReflectionCharacter (n := n) (F := F)) := by
  intro x
  have hx : x.toAdd = 0 ∨ x.toAdd = 1 := by
    have h := ZMod.val_lt x.toAdd
    have he := ZMod.natCast_zmod_val x.toAdd
    interval_cases hval : x.toAdd.val <;> simp_all
  rcases hx with hx | hx
  · refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hx.symm
  · let i : Fin n := ⟨0, hn⟩
    refine ⟨⟨splitDExchangeElement i, splitDExchangeElement_mem_reflections i⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [splitDReflectionCharacter_value, dicksonValue_splitDExchange, hx]
end Atlas.Orthogonal
