import Atlas.Rudvalis.CodeGroupOrder
import Atlas.Rudvalis.MinimumSupportObstructions

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

theorem quaternary_minimum_not_constant_rows (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) : ¬constantOnRows (reduce w) := by
  classical
  intro h
  obtain ⟨s,hs⟩ := (constantOnRows_iff _).mp h
  have hn := quaternary_minimum_residue_weight w hw hweight
  rw [hs,rowSubsetWord_weight] at hn
  have hc : s.card=2 := by omega
  obtain ⟨p,q,hpq,rfl⟩ := Finset.card_eq_two.mp hc
  have he : rowSubsetWord {p,q}=rowWord p+rowWord q := by
    funext z
    by_cases hp : z.1=p <;> by_cases hq : z.1=q <;>
      simp_all [rowSubsetWord,rowWord]
  exact quaternary_minimum_not_two_rows p q hpq w hw hweight (hs.trans he)

/-- Necessary four-block support data, independently of signed lift existence. -/
def admissibleFourSupport (d : BinaryWord) : Prop :=
  ∃ (a : Point) (ε : Point → Bit),
    d=binaryNormalMap (ε,outerMatrix a.val a.val,0) ∧
    (∀ p : Point,dot a.val p.val=0 → ε p=0) ∧ (∑ p : Point,ε p)=1

theorem quaternary_minimum_support_cases (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) :
    admissibleFourSupport (reduce w) ∨ hasNonzeroQuadraticPart (reduce w) := by
  have hd : reduce w∈binaryResidue := (quaternaryCode_residue _).mpr ⟨w,hw,rfl⟩
  have hn := quaternary_minimum_residue_weight w hw hweight
  rcases (binaryResidue_three_strata _ hd).1 with hc | hb | hq
  · exact False.elim (quaternary_minimum_not_constant_rows w hw hweight hc)
  · obtain ⟨ε,M,hM,he⟩ := hb
    have htype := (binaryNormalMap_bilinear_weight_sixteen ε M hM).mp (he ▸ hn)
    obtain ⟨b,a,hba⟩ := htype.1
    subst M
    obtain ⟨hab,hε⟩ := quaternary_four_active_support_constraint w hw hweight ε a b he.symm
    subst b
    refine Or.inl ⟨a,ε,he.symm,?_,hε⟩
    intro p hp
    exact htype.2 p (by rw [matrixAt_outer,hp,zero_smul])
  · exact Or.inr hq

end Atlas.Rudvalis
