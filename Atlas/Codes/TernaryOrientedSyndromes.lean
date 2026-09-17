import Atlas.Codes.TernaryOrientedAction
import Atlas.Combinatorics.FiniteImageCapacity

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 10000
-- Quotient representatives require additional elaboration through the pinned interfaces.
set_option maxHeartbeats 100000
noncomputable section
namespace Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ternaryOrientedWord_injective :
    Function.Injective (fun p : TernaryOrientedTriad => ternaryOrientedWord p.val) := by
  intro p q he
  have hs : p.val.1 = q.val.1 := by
    simpa only [ternaryOrientedWord_support] using congrArg ternarySupport he
  have hi : p.val.2 = q.val.2 := by
    by_contra hn
    have hp := ((mem_ternaryOrientedTriads _).mp p.property).2
    have hq : p.val.2 ∈ q.val.1 := hs ▸ hp
    have hh := congrFun he p.val.2
    simp [ternaryOrientedWord, ternaryTriadWord, Pi.single_apply, hp, hq, hn] at hh
  exact Subtype.ext (Prod.ext hs hi)

def ternaryOrientedSyndrome (p : TernaryOrientedTriad) : TernaryAffineSyndrome :=
  ⟨ternarySyndromeClass (ternaryOrientedWord p.val), ternaryOrientedWord_sum p⟩

theorem ternaryOrientedSyndrome_disjoint_supports (p q : TernaryOrientedTriad)
    (hne : p ≠ q) (he : ternaryOrientedSyndrome p = ternaryOrientedSyndrome q) :
    Disjoint p.val.1 q.val.1 := by
  by_contra hd
  obtain ⟨i, hi, hj⟩ := Finset.not_disjoint_iff.mp hd
  have hp := ((mem_ternaryOrientedTriads _).mp p.property).1
  have hq := ((mem_ternaryOrientedTriads _).mp q.property).1
  have hc := Finset.card_union_add_card_inter p.val.1 q.val.1
  have hm : 0 < (p.val.1 ∩ q.val.1).card := Finset.card_pos.mpr
    ⟨i, Finset.mem_inter.mpr ⟨hi,hj⟩⟩
  have hu : (ternarySupport (ternaryOrientedWord p.val) ∪
      ternarySupport (ternaryOrientedWord q.val)).card < 6 := by
    rw [ternaryOrientedWord_support, ternaryOrientedWord_support]
    omega
  exact hne (ternaryOrientedWord_injective
    (ternarySyndrome_union_support _ _ hu (congrArg Subtype.val he)))

/-- A class contains at most four oriented triads: their disjoint three-element
supports must fit inside the twelve actual coordinates. -/
theorem ternaryOrientedSyndrome_fiber_le (c : TernaryAffineSyndrome) :
    Nat.card {p : TernaryOrientedTriad // ternaryOrientedSyndrome p=c} ≤ 4 := by
  rw [Atlas.Combinatorics.fiber_card_filter]
  let s := Finset.univ.filter (fun p : TernaryOrientedTriad => ternaryOrientedSyndrome p=c)
  have hd : (↑s : Set TernaryOrientedTriad).Pairwise (fun p q => Disjoint p.val.1 q.val.1) := by
    intro p hp q hq hne
    exact ternaryOrientedSyndrome_disjoint_supports p q hne
      ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  have hc : (s.biUnion (fun p => p.val.1)).card = s.card*3 := by
    rw [Finset.card_biUnion hd]
    have he : ∀ p ∈ s, p.val.1.card = 3 := fun p _ =>
      ((mem_ternaryOrientedTriads _).mp p.property).1
    rw [Finset.sum_congr rfl he]
    simp
  have hb := Finset.card_le_univ (s.biUnion (fun p => p.val.1))
  rw [hc, Fintype.card_fin] at hb
  change s.card ≤ 4
  omega

def ternaryOrientedSyndromes : Finset TernaryAffineSyndrome := Finset.univ.image ternaryOrientedSyndrome

theorem ternarySingleton_oriented_disjoint :
    Disjoint ternarySingletonSyndromes ternaryOrientedSyndromes := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hd
  have hpc := ((mem_ternaryOrientedTriads _).mp p.property).1
  have he := ternarySyndrome_small_support (ternaryOrientedWord p.val) (Pi.single i 1)
    (by rw [ternaryOrientedWord_support, hpc, ternarySupport_singleton]; simp)
    (congrArg Subtype.val hp)
  have hh := congrArg (fun w => (ternarySupport w).card) he
  rw [ternaryOrientedWord_support, hpc, ternarySupport_singleton] at hh
  simpa using hh

theorem ternaryOrientedSyndrome_ne_pair (p : TernaryOrientedTriad) (s : TernaryPair) :
    ternaryOrientedSyndrome p ≠ ternaryPairSyndrome s := by
  intro hp
  have hsc : s.val.card = 2 := (Finset.mem_powersetCard.mp s.property).2
  have hpc : p.val.1.card = 3 := ((mem_ternaryOrientedTriads _).mp p.property).1
  have hs : (ternarySupport (ternaryOrientedWord p.val)).card +
      (ternarySupport (ternaryPairWord s.val)).card < 6 := by
    rw [ternaryOrientedWord_support, hpc, ternaryPairWord_support, hsc]
    decide
  have heq : ternarySyndromeClass (ternaryOrientedWord p.val) =
      ternarySyndromeClass (ternaryPairWord s.val) := congrArg Subtype.val hp
  have he := ternarySyndrome_small_support _ _ hs heq
  have hh := congrArg (fun w : TernaryWord => (ternarySupport w).card) he
  rw [ternaryOrientedWord_support, hpc, ternaryPairWord_support, hsc] at hh
  contradiction

theorem ternaryPair_oriented_disjoint :
    Disjoint ternaryPairSyndromes ternaryOrientedSyndromes := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  change c ∈ Finset.univ.image ternaryPairSyndrome at hc
  change c ∈ Finset.univ.image ternaryOrientedSyndrome at hd
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hc
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hd
  exact ternaryOrientedSyndrome_ne_pair p s (hp.trans hs.symm)

end Atlas.Codes
