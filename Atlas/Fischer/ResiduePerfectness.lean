import Atlas.GroupTheory.ConjugateOddRelation
import Atlas.Fischer.ResidueOctadRelation
import Atlas.Fischer.ResidueQuotientGeometry
import Atlas.Fischer.WittDuads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem residueDistinguishedElement_covariance (S : Finset Omega)
    (g : ResidueGroup S) (x : ResiduePoint S) :
    g*residueDistinguishedElement S x*g⁻¹=residueDistinguishedElement S (g • x) := by
  obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective g
  let q := QuotientGroup.mk' (residueCentralElementary S)
  change q a * q (residuePointCentralizer S x) * (q a)⁻¹ =
    q (residuePointCentralizer S ((QuotientGroup.mk a : ResidueGroup S) • x))
  rw [← map_inv,← map_mul,← map_mul]
  apply congrArg (QuotientGroup.mk' (residueCentralElementary S))
  apply Subtype.ext
  exact (residueGroup_mk_smul_val S a x).symm

theorem residueDistinguishedElement_conjugate (S : Finset Omega) (hS : S.card ≤ 4)
    (x y : ResiduePoint S) :
    ∃ g : ResidueGroup S, g*residueDistinguishedElement S x*g⁻¹=residueDistinguishedElement S y := by
  haveI := residueGroup_transitive S hS
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ResidueGroup S) x y
  exact ⟨g,(residueDistinguishedElement_covariance S g x).trans (congrArg _ hg)⟩

theorem residueDistinguishedElement_square (S : Finset Omega) (x : ResiduePoint S) :
    residueDistinguishedElement S x ^ 2=1 := by
  have hx : (residuePointCentralizer S x)^2=1 := by
    apply Subtype.ext
    obtain ⟨i,hi⟩ := x.prop.1
    change x.val^2=1
    rw [← hi,← distinguishedRootElement_order i]
    exact pow_orderOf_eq_one _
  rw [residueDistinguishedElement,← map_pow,hx,map_one]

/-- The actual octad relation and the transitive original-point action prove
perfectness; quotient-image injectivity is not used. -/
theorem residueGroup_perfect_of_octad (S : Finset Omega) (hS : S.card ≤ 2)
    (O : Octad) (hO : (O.val ∩ S).card=1) : Group.IsPerfect (ResidueGroup S) :=
  Atlas.GroupTheory.perfect_of_conjugate_seven_relation
    (residueDistinguishedElement S) (residueDistinguishedElement_generates S hS)
    (residueDistinguishedElement_conjugate S (by omega))
    (residueDistinguishedElement_square S) (residueOctadList S O)
    (residueOctadList_length S O hO) (residueOctadList_relation S O)

theorem residue_octad_meets_once (S : Finset Omega) (hpos : 0<S.card) (hS : S.card≤2) :
    ∃ O : Octad, (O.val ∩ S).card=1 := by
  classical
  interval_cases hc : S.card
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    have hn : (octads.filter (fun O => i ∈ O)).Nonempty :=
      Finset.card_pos.mp (by rw [octads_through_point_card]; decide)
    obtain ⟨O,hO⟩ := hn
    obtain ⟨hO,hi⟩ := Finset.mem_filter.mp hO
    exact ⟨⟨O,hO⟩,by simp [hi]⟩
  · have hn : (octads.filter (fun O => ∅ ⊆ O ∧ (O ∩ S).card=1)).Nonempty := by
      apply Finset.card_pos.mp
      have h := (octad_duad_distribution S hc).2.1
      change (octads.filter (fun O => ∅ ⊆ O ∧ (O ∩ S).card=1)).card=352 at h
      omega
    obtain ⟨O,hO⟩ := hn
    obtain ⟨hO,_,hi⟩ := Finset.mem_filter.mp hO
    exact ⟨⟨O,hO⟩,hi⟩

/-- Both nonempty residues are perfect, by the actual seven-factor octad relation. -/
theorem residueGroup_perfect (S : Finset Omega) (hpos : 0<S.card) (hS : S.card≤2) :
    Group.IsPerfect (ResidueGroup S) := by
  obtain ⟨O,hO⟩ := residue_octad_meets_once S hpos hS
  exact residueGroup_perfect_of_octad S hS O hO

end Atlas.Fischer
