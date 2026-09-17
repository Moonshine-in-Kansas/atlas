import Atlas.Codes.TernaryGolayTriads
import Atlas.Codes.TernarySyndromeSupports

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Atlas.Codes
open scoped BigOperators

def ternaryOrientedTriads : Finset (Finset (Fin 12) × Fin 12) :=
  ternaryTriads.biUnion (fun s => s.image (fun i => (s,i)))

abbrev TernaryOrientedTriad := ↥ternaryOrientedTriads

theorem mem_ternaryOrientedTriads (p : Finset (Fin 12) × Fin 12) :
    p ∈ ternaryOrientedTriads ↔ p.1.card=3 ∧ p.2 ∈ p.1 := by
  rcases p with ⟨s,i⟩
  simp [ternaryOrientedTriads, ternaryTriads, Finset.mem_powersetCard, Prod.mk.injEq]

theorem ternaryOrientedTriads_card : ternaryOrientedTriads.card = 660 := by
  rw [ternaryOrientedTriads, Finset.card_biUnion]
  · have he : ∀ s ∈ ternaryTriads, (s.image (fun i => (s,i))).card = 3 := by
      intro s hs
      rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
      exact (Finset.mem_powersetCard.mp hs).2
    rw [Finset.sum_congr rfl he]
    simp [ternaryTriads_card]
  · intro s hs t ht hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq
    exact hne (congrArg Prod.fst (hi.trans hj.symm))

def ternaryOrientedWord (p : Finset (Fin 12) × Fin 12) : TernaryWord :=
  ternaryTriadWord p.1 + Pi.single p.2 1

theorem ternaryOrientedWord_support (p : TernaryOrientedTriad) :
    ternarySupport (ternaryOrientedWord p.val) = p.val.1 := by
  have hp := (mem_ternaryOrientedTriads p.val).mp p.property
  ext i
  by_cases hi : i=p.val.2
  · subst i
    simp [ternarySupport, ternaryOrientedWord, ternaryTriadWord, hp.2]
    decide
  · simp [ternarySupport, ternaryOrientedWord, ternaryTriadWord, Pi.single_apply, hi]

theorem ternaryOrientedWord_sum (p : TernaryOrientedTriad) :
    ternaryWordSum (ternaryOrientedWord p.val) = 1 := by
  have hp := (mem_ternaryOrientedTriads p.val).mp p.property
  simp [ternaryWordSum, ternaryOrientedWord, ternaryTriadWord, Finset.sum_add_distrib, hp.1]
  decide

def ternaryOrientedRelated (p q : Finset (Fin 12) × Fin 12) : Prop :=
  ternaryEncoder (ternaryDecoder (ternaryOrientedWord p-ternaryOrientedWord q)) =
    ternaryOrientedWord p-ternaryOrientedWord q

instance (p q : Finset (Fin 12) × Fin 12) : Decidable (ternaryOrientedRelated p q) :=
  inferInstanceAs (Decidable (_ = _))

theorem ternaryOrientedRelated_iff (p q : Finset (Fin 12) × Fin 12) :
    ternaryOrientedRelated p q ↔
      ternarySyndromeClass (ternaryOrientedWord p) = ternarySyndromeClass (ternaryOrientedWord q) := by
  rw [ternarySyndromeClass_eq_iff, ternaryGolay_mem_iff_decode]
  rfl

def ternaryOrientedPartners (p : Finset (Fin 12) × Fin 12) :=
  ternaryOrientedTriads.filter (ternaryOrientedRelated p)

def ternaryOrientedBase : Finset (Fin 12) × Fin 12 := ({0,1,2},2)


end Atlas.Codes
