import Mathlib.Data.Subtype
import Atlas.Fischer.CommutingExtensionCounts
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
namespace Atlas.Fischer

abbrev OrderedCommutingTuple (s : ℕ) :=
  {t : Fin s ↪ rootGeneratedRayGroup // (∀ k, t k ∈ Set.range distinguishedRootElement) ∧
    ∀ k l, Commute (t k) (t l)}

def orderedCommutingInit {s : ℕ} (t : OrderedCommutingTuple (s+1)) : OrderedCommutingTuple s :=
  ⟨⟨fun k => t.val k.castSucc,fun k l h => Fin.castSucc_injective s (t.val.injective h)⟩,
    fun k => t.property.1 k.castSucc,fun k l => t.property.2 k.castSucc l.castSucc⟩

def orderedCommutingLast {s : ℕ} (t : OrderedCommutingTuple (s+1)) :
    CommutingExtension (orderedCommutingInit t).val :=
  ⟨t.val (Fin.last s), t.property.1 _, fun k =>
    ⟨fun h => by have hh := congrArg Fin.val (t.val.injective h); simp only [Fin.val_last, Fin.val_castSucc] at hh; omega,t.property.2 _ _⟩⟩

def orderedCommutingSnoc {s : ℕ} (t : OrderedCommutingTuple s)
    (x : CommutingExtension t.val) : OrderedCommutingTuple (s+1) := by
  have hn : x.val ∉ Set.range t.val := by
    rintro ⟨k,hk⟩; exact (x.property.2 k).1 hk.symm
  refine ⟨⟨Fin.snoc t.val x.val,Fin.snoc_injective_of_injective t.val.injective hn⟩,?_,?_⟩
  · intro k
    induction k using Fin.lastCases with
    | last => simpa using x.property.1
    | cast k => simpa using t.property.1 k
  · intro k l
    induction k using Fin.lastCases with
    | last =>
      induction l using Fin.lastCases with
      | last => simp only [Function.Embedding.coeFn_mk,Fin.snoc_last]; exact Commute.refl _
      | cast l => simpa using (x.property.2 l).2.symm
    | cast k =>
      induction l using Fin.lastCases with
      | last => simpa using (x.property.2 k).2
      | cast l => simpa using t.property.2 k l

/-- Appending the last distinguished element is an exact dependent-sum
parametrization, not a numerical recurrence assumed from transitivity. -/
def orderedCommutingSuccEquiv (s : ℕ) : OrderedCommutingTuple (s+1) ≃
    Σ t : OrderedCommutingTuple s, CommutingExtension t.val where
  toFun t := ⟨orderedCommutingInit t,orderedCommutingLast t⟩
  invFun t := orderedCommutingSnoc t.1 t.2
  left_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    induction k using Fin.lastCases with
    | last => simp [orderedCommutingSnoc,orderedCommutingLast]
    | cast k => simp [orderedCommutingSnoc,orderedCommutingInit]; rfl
  right_inv t := by
    rcases t with ⟨t,x⟩
    have hi : orderedCommutingInit (orderedCommutingSnoc t x)=t := by
      apply Subtype.ext
      apply Function.Embedding.ext
      intro k
      simp [orderedCommutingInit,orderedCommutingSnoc]
    apply Sigma.ext hi
    apply (Subtype.heq_iff_coe_eq (by intro y; dsimp only; rw [hi])).mpr
    simp [orderedCommutingLast,orderedCommutingSnoc]

end Atlas.Fischer
