import Atlas.Codes.TernaryGolayTriads
import Atlas.Codes.TernaryGolaySupports

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Codes
open scoped BigOperators

def ternaryPositiveSupport (w : TernaryWord) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => w i=1)

def ternaryNegativeSupport (w : TernaryWord) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => w i=2)

def TernaryBalancedHexad (w : TernaryWord) : Prop :=
  (ternaryPositiveSupport w).card=3 ∧ (ternaryNegativeSupport w).card=3

instance (w : TernaryWord) : Decidable (TernaryBalancedHexad w) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev TernaryBalancedWords := {w : ternaryGolay // TernaryBalancedHexad w.val}

theorem ternaryBalanced_parameter_count :
    (Finset.univ.filter (fun p : TernaryParameters => TernaryBalancedHexad (ternaryEncoder p))).card=220 := by
  decide +kernel

theorem ternaryBalancedWords_card : Nat.card TernaryBalancedWords=220 := by
  classical
  let e : {p : TernaryParameters // TernaryBalancedHexad (ternaryEncoder p)} ≃ TernaryBalancedWords :=
    ternaryGolayEquiv.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact ternaryBalanced_parameter_count

theorem ternaryBalanced_weight (w : TernaryWord) (hw : TernaryBalancedHexad w) :
    ternaryWeight w=6 := by
  have he : ternarySupport w=ternaryPositiveSupport w ∪ ternaryNegativeSupport w := by
    ext i
    simp only [ternarySupport,ternaryPositiveSupport,ternaryNegativeSupport,
      Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    have hc : ∀ a : ZMod 3,a≠0 ↔ a=1 ∨ a=2 := by decide
    exact hc (w i)
  have hd : Disjoint (ternaryPositiveSupport w) (ternaryNegativeSupport w) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    exact (by decide : (1 : ZMod 3)≠2) (h1.symm.trans h2)
  rw [← ternarySupport_card,he,Finset.card_union_of_disjoint hd,hw.1,hw.2]

def ternaryBalancedSixWord (c : TernaryBalancedWords) : TernarySixWords :=
  ⟨c.val,ternaryBalanced_weight c.val.val c.prop⟩

def ternarySignedLift (a : ZMod 3) : ℤ := if a=1 then 1 else if a=2 then -1 else 0

theorem ternaryBalanced_signed_sum (w : TernaryWord) (hw : TernaryBalancedHexad w) :
    ∑ i,ternarySignedLift (w i)=0 := by
  have he (i : Fin 12) : ternarySignedLift (w i)=
      (if w i=1 then (1 : ℤ) else 0)-(if w i=2 then 1 else 0) := by
    have hc : ∀ a : ZMod 3,ternarySignedLift a=
        (if a=1 then (1 : ℤ) else 0)-(if a=2 then 1 else 0) := by decide
    exact hc (w i)
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  have hp : (Finset.univ.filter (fun i => w i=1)).card=3 := hw.1
  have hn : (Finset.univ.filter (fun i => w i=2)).card=3 := hw.2
  simp [← Finset.sum_filter,hp,hn]

theorem ternaryBalanced_constant_shift (w : TernaryWord) (hw : TernaryBalancedHexad w)
    (a : ZMod 3) (ha : TernaryBalancedHexad (fun i => w i+a)) : a=0 := by
  by_contra hn
  have hh : a=1 ∨ a=2 := by
    have h : ∀ b : ZMod 3,b≠0 → b=1 ∨ b=2 := by decide
    exact h a hn
  rcases hh with rfl | rfl
  · have he : ternaryPositiveSupport (fun i => w i+1) = (ternarySupport w)ᶜ := by
      ext i
      simp [ternaryPositiveSupport,ternarySupport]
    have hc := ha.1
    rw [he,Finset.card_compl,Fintype.card_fin,ternarySupport_card,ternaryBalanced_weight w hw] at hc
    omega
  · have he : ternaryNegativeSupport (fun i => w i+2) = (ternarySupport w)ᶜ := by
      ext i
      simp [ternaryNegativeSupport,ternarySupport]
    have hc := ha.2
    rw [he,Finset.card_compl,Fintype.card_fin,ternarySupport_card,ternaryBalanced_weight w hw] at hc
    omega

theorem ternaryPositiveSupport_permute (σ : Equiv.Perm (Fin 12)) (w : TernaryWord) :
    ternaryPositiveSupport (fun i => w (σ.symm i)) = (ternaryPositiveSupport w).map σ.toEmbedding := by
  ext i
  simp [ternaryPositiveSupport,Finset.mem_map_equiv]

theorem ternaryNegativeSupport_permute (σ : Equiv.Perm (Fin 12)) (w : TernaryWord) :
    ternaryNegativeSupport (fun i => w (σ.symm i)) = (ternaryNegativeSupport w).map σ.toEmbedding := by
  ext i
  simp [ternaryNegativeSupport,Finset.mem_map_equiv]

theorem ternaryBalanced_permute (σ : Equiv.Perm (Fin 12)) (w : TernaryWord)
    (hw : TernaryBalancedHexad w) : TernaryBalancedHexad (fun i => w (σ.symm i)) := by
  simpa [TernaryBalancedHexad,ternaryPositiveSupport_permute,ternaryNegativeSupport_permute] using hw

def ternaryBalancedBase : TernaryWord :=
  ternaryTriadWord ternaryBaseTriad-ternaryTriadWord {7,9,10}

theorem ternaryBalanced_base_unique : ∀ p : TernaryParameters,
    TernaryBalancedHexad (ternaryEncoder p) →
    ternaryPositiveSupport (ternaryEncoder p)=ternaryBaseTriad →
    ternaryEncoder p=ternaryBalancedBase := by decide +kernel

/-- A balanced hexad word is determined by its positive triad, uniformly by
transport of the one marked base calculation through the actual M11. -/
theorem ternaryBalanced_positive_unique (u v : ternaryGolay)
    (hu : TernaryBalancedHexad u.val) (hv : TernaryBalancedHexad v.val)
    (hpos : ternaryPositiveSupport u.val=ternaryPositiveSupport v.val) : u=v := by
  obtain ⟨g,hg⟩ := ternaryTriads_transitive (ternaryPositiveSupport u.val) ternaryBaseTriad
    hu.1 (by decide)
  have hbase (w : ternaryGolay) (hw : TernaryBalancedHexad w.val)
      (hp : ternaryPositiveSupport w.val=ternaryPositiveSupport u.val) :
      (fun i => w.val (g.val.symm i))=ternaryBalancedBase := by
    obtain ⟨p,hpenc⟩ := g.prop w.val w.prop
    apply hpenc ▸ ternaryBalanced_base_unique p ?_ ?_
    · rw [hpenc]
      exact ternaryBalanced_permute g.val w.val hw
    · rw [hpenc,ternaryPositiveSupport_permute,hp,hg]
  have he := (hbase u hu rfl).trans (hbase v hv hpos.symm).symm
  apply Subtype.ext
  funext i
  have hh := congrFun he (g.val i)
  simpa only [Equiv.symm_apply_apply] using hh

theorem ternaryBalanced_neg (w : TernaryWord) (hw : TernaryBalancedHexad w) :
    TernaryBalancedHexad (-w) := by
  have hp : ternaryPositiveSupport (-w)=ternaryNegativeSupport w := by
    ext i
    simp only [ternaryPositiveSupport,ternaryNegativeSupport,Finset.mem_filter,
      Finset.mem_univ,true_and,Pi.neg_apply]
    have h : ∀ x : ZMod 3,-x=1 ↔ x=2 := by decide
    exact h _
  have hn : ternaryNegativeSupport (-w)=ternaryPositiveSupport w := by
    ext i
    simp only [ternaryPositiveSupport,ternaryNegativeSupport,Finset.mem_filter,
      Finset.mem_univ,true_and,Pi.neg_apply]
    have h : ∀ x : ZMod 3,-x=2 ↔ x=1 := by decide
    exact h _
  exact ⟨hp ▸ hw.2,hn ▸ hw.1⟩

def ternaryBalancedNeg (c : TernaryBalancedWords) : TernaryBalancedWords :=
  ⟨-c.val,ternaryBalanced_neg c.val.val c.prop⟩

theorem ternarySignedLift_neg (a : ZMod 3) : ternarySignedLift (-a)= -ternarySignedLift a := by
  revert a; decide +kernel

end Atlas.Codes
