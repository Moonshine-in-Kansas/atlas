import Atlas.Rudvalis.ReferenceQuartetExhaustion
import Atlas.Combinatorics.PairwiseIncidence
import Mathlib.Data.Subtype

namespace Atlas.Rudvalis
open scoped BigOperators
open Classical

abbrev IntrinsicCouples := {c : Set MinimalCross // IsCouple c}
abbrev IntrinsicQuartets := {Q : Set MinimalCross // IsQuartet Q}

noncomputable def orthogonalPairCouple (z : OrthogonalPairs) : IntrinsicCouples :=
  ⟨{z.val.1,z.val.2},Set.ncard_pair (fun h=>crossOrthogonal_irrefl _ (h ▸ (show CrossOrthogonal z.val.1 z.val.2 from z.prop))),by
    intro a ha b hb hab
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · exact (hab rfl).elim
    · exact z.prop
    · exact (crossOrthogonal_symm _ _).mp z.prop
    · exact (hab rfl).elim⟩

noncomputable def orderedPairCouplePointEquiv : OrthogonalPairs ≃ Σc : IntrinsicCouples,c.val :=
  Equiv.ofBijective (fun z=>⟨orthogonalPairCouple z,⟨z.val.1,by change z.val.1∈({z.val.1,z.val.2} : Set MinimalCross); exact Or.inl rfl⟩⟩) (by
    constructor
    · rintro ⟨⟨a,b⟩,hab⟩ ⟨⟨c,d⟩,hcd⟩ h
      have hx : a=c := congrArg (fun z : Σc : IntrinsicCouples,c.val=>z.2.val) h
      subst c
      have he : ({a,b} : Set MinimalCross)={a,d} :=
        congrArg (fun z : Σc : IntrinsicCouples,c.val=>z.1.val) h
      have hb : b∈({a,d} : Set MinimalCross) := he ▸ (show b∈({a,b} : Set MinimalCross) from Or.inr rfl)
      have hbd : b=d := by
        rcases hb with hb|hb
        · exact False.elim (crossOrthogonal_irrefl _ (hb ▸ hab))
        · exact hb
      subst d
      rfl
    · rintro ⟨⟨s,hs⟩,x,hx⟩
      obtain ⟨a,b,hab,rfl⟩ := Set.ncard_eq_two.mp hs.1
      have ho : CrossOrthogonal a b := hs.2 (Or.inl rfl) (Or.inr rfl) hab
      rcases hx with hx|hx
      · subst x
        exact ⟨⟨(a,b),ho⟩,rfl⟩
      · subst x
        refine ⟨⟨(b,a),(crossOrthogonal_symm _ _).mp ho⟩,?_⟩
        have he : ({b,a} : Set MinimalCross)={a,b} := Set.pair_comm _ _
        apply Sigma.ext
        · exact Subtype.ext he
        · change (⟨b,Or.inl rfl⟩ : ({b,a} : Set MinimalCross)) ≍
            (⟨b,Or.inr rfl⟩ : ({a,b} : Set MinimalCross))
          exact (Subtype.heq_iff_coe_eq (fun z=>by rw [he])).mpr rfl)

theorem intrinsicCouples_card : Nat.card IntrinsicCouples=3562650 := by
  let : Fintype IntrinsicCouples := Fintype.ofFinite _
  have h := Nat.card_congr orderedPairCouplePointEquiv
  rw [rudvalis_ordered_orthogonal_pairs_card,Nat.card_sigma] at h
  have hc (c : IntrinsicCouples) : Nat.card c.val=2 := c.prop.1
  simp_rw [hc] at h
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  rw [←Nat.card_eq_fintype_card] at h
  omega

noncomputable def couplesWithinEquiv (s : Set MinimalCross) :
    {c : IntrinsicCouples // c.val⊆s} ≃
      {c : Set MinimalCross // c⊆s ∧ c.ncard=2 ∧ c.Pairwise CrossOrthogonal} :=
  {toFun := fun c=>⟨c.val.val,c.prop,c.val.prop⟩
   invFun := fun c=>⟨⟨c.val,c.prop.2⟩,c.prop.1⟩
   left_inv := fun _=>rfl
   right_inv := fun _=>rfl}

theorem couplesWithin_card (s : Set MinimalCross) (hs : s.Finite) (hp : s.Pairwise CrossOrthogonal) :
    Nat.card {c : IntrinsicCouples // c.val⊆s}=s.ncard.choose 2 := by
  rw [Nat.card_congr (couplesWithinEquiv s)]
  exact Atlas.Combinatorics.pairwise_subsets_card CrossOrthogonal s hs hp 2

noncomputable def coupleQuartetIncidenceEquiv :
    (Σc : IntrinsicCouples,QuartetsThrough c.val) ≃
      ΣQ : IntrinsicQuartets,{c : IntrinsicCouples // c.val⊆Q.val} :=
  {toFun := fun z=>⟨⟨z.2.val,z.2.prop.1⟩,z.1,z.2.prop.2⟩
   invFun := fun z=>⟨z.2.val,⟨z.1.val,z.1.prop,z.2.prop⟩⟩
   left_inv := fun _=>rfl
   right_inv := fun _=>rfl}

theorem intrinsicQuartets_card : Nat.card IntrinsicQuartets=2968875 := by
  let : Fintype IntrinsicCouples := Fintype.ofFinite _
  let : Fintype IntrinsicQuartets := Fintype.ofFinite _
  have h := Nat.card_congr coupleQuartetIncidenceEquiv
  rw [Nat.card_sigma,Nat.card_sigma] at h
  have hc (c : IntrinsicCouples) : Nat.card (QuartetsThrough c.val)=5 := quartetsThrough_couple_card c.val c.prop
  have hQ (Q : IntrinsicQuartets) : Nat.card {c : IntrinsicCouples // c.val⊆Q.val}=6 := by
    rw [couplesWithin_card Q.val (isQuartet_finite Q.prop) Q.prop.2.1,Q.prop.1]
    rfl
  simp_rw [hc,hQ] at h
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,intrinsicCouples_card] at h
  omega

end Atlas.Rudvalis
