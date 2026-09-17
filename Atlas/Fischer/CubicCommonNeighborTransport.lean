import Atlas.Fischer.MathieuOctadStabilizer
import Atlas.Mathieu.OctadPairNormalization

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual common neighbors, refined by their triple intersection. -/
abbrev CubicCommonNeighbors (D F : Octad) (u : ℕ) :=
  {G : Octad // (D.val ∩ G.val).card=4 ∧ (F.val ∩ G.val).card=4 ∧
    ((D.val ∩ F.val) ∩ G.val).card=u}

def cubicCommonNeighborCount (D F : Octad) (u : ℕ) : ℕ := Nat.card (CubicCommonNeighbors D F u)

theorem cubicCommonNeighbor_permute_inter (g : Mathieu24CodeModel) (A B : Finset Omega) :
    permuteBlock g.val (A ∩ B)=permuteBlock g.val A ∩ permuteBlock g.val B :=
  Finset.image_inter A B g.val.injective

theorem cubicCommonNeighbor_pair_card (g : Mathieu24CodeModel) (D G : Octad) :
    ((g • D).val ∩ (g • G).val).card=(D.val ∩ G.val).card := by
  rw [mathieuOctadAction_val,mathieuOctadAction_val,← cubicCommonNeighbor_permute_inter,
    permuteBlock_card]

theorem cubicCommonNeighbor_triple_card (g : Mathieu24CodeModel) (D F G : Octad) :
    (((g • D).val ∩ (g • F).val) ∩ (g • G).val).card=((D.val ∩ F.val) ∩ G.val).card := by
  rw [mathieuOctadAction_val,mathieuOctadAction_val,mathieuOctadAction_val,
    ← cubicCommonNeighbor_permute_inter,← cubicCommonNeighbor_permute_inter,permuteBlock_card]

def cubicCommonNeighborEquiv (g : Mathieu24CodeModel) (D F : Octad) (u : ℕ) :
    CubicCommonNeighbors D F u ≃ CubicCommonNeighbors (g • D) (g • F) u where
  toFun G := ⟨g • G.val,by
    simpa only [cubicCommonNeighbor_pair_card,cubicCommonNeighbor_triple_card] using G.property⟩
  invFun G := ⟨g⁻¹ • G.val,by
    have h := G.property
    have hp := cubicCommonNeighbor_pair_card g⁻¹ (g • D) G.val
    have hq := cubicCommonNeighbor_pair_card g⁻¹ (g • F) G.val
    have ht := cubicCommonNeighbor_triple_card g⁻¹ (g • D) (g • F) G.val
    simp only [inv_smul_smul] at hp hq ht
    exact ⟨hp.trans h.1,hq.trans h.2.1,ht.trans h.2.2⟩⟩
  left_inv G := by apply Subtype.ext; exact inv_smul_smul g G.val
  right_inv G := by apply Subtype.ext; exact smul_inv_smul g G.val

theorem cubicCommonNeighborCount_invariant (g : Mathieu24CodeModel) (D F : Octad) (u : ℕ) :
    cubicCommonNeighborCount D F u=cubicCommonNeighborCount (g • D) (g • F) u :=
  Nat.card_congr (cubicCommonNeighborEquiv g D F u)

/-- Every actual pair meeting in a tetrad is carried to two unions of columns
sharing exactly one column of the retained sextet. -/
theorem cubicCommonNeighbor_pair_normalize (D F : Octad) (hDF : (D.val ∩ F.val).card=4) :
    ∃ g : Mathieu24CodeModel,∃ i j k : HexIndex,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (g • D).val=tetrad i ∪ tetrad j ∧ (g • F).val=tetrad i ∪ tetrad k := by
  let T : FourSet := ⟨D.val ∩ F.val,hDF⟩
  let S := sextetCompletion T
  have hT : T.val ∈ S.val := tetrad_mem_completion T
  have hD : D.val \ T.val ∈ S.val := by
    apply Finset.mem_insert_of_mem
    exact (companion_mem T _).mpr ⟨D.val,D.property,Finset.inter_subset_left,rfl⟩
  have hF : F.val \ T.val ∈ S.val := by
    apply Finset.mem_insert_of_mem
    exact (companion_mem T _).mpr ⟨F.val,F.property,Finset.inter_subset_right,rfl⟩
  obtain ⟨g,hg⟩ := sextet_equivalent_distinguished S
  obtain ⟨i,hi⟩ := sextet_image_part_tetrad S g hg T.val hT
  obtain ⟨j,hj⟩ := sextet_image_part_tetrad S g hg (D.val \ T.val) hD
  obtain ⟨k,hk⟩ := sextet_image_part_tetrad S g hg (F.val \ T.val) hF
  have heD : (g • D).val=tetrad i ∪ tetrad j := by
    rw [mathieuOctadAction_val,← Finset.union_sdiff_of_subset (show T.val ⊆ D.val from Finset.inter_subset_left)]
    change (T.val ∪ (D.val \ T.val)).image g.val=_
    rw [Finset.image_union]
    exact congrArg₂ (· ∪ ·) hi hj
  have heF : (g • F).val=tetrad i ∪ tetrad k := by
    rw [mathieuOctadAction_val,← Finset.union_sdiff_of_subset (show T.val ⊆ F.val from Finset.inter_subset_right)]
    change (T.val ∪ (F.val \ T.val)).image g.val=_
    rw [Finset.image_union]
    exact congrArg₂ (· ∪ ·) hi hk
  have hij : i ≠ j := by
    intro h
    have hc := octad_size (g • D).val (g • D).property
    rw [heD,h,Finset.union_self,tetrad_card] at hc
    omega
  have hik : i ≠ k := by
    intro h
    have hc := octad_size (g • F).val (g • F).property
    rw [heF,h,Finset.union_self,tetrad_card] at hc
    omega
  have hjk : j ≠ k := by
    intro h
    have he : g • D=g • F := Subtype.ext (by rw [heD,heF,h])
    have hh : D=F := (MulAction.injective g) he
    have hc := hDF
    rw [hh,Finset.inter_self,octad_size F.val F.property] at hc
    omega
  exact ⟨g,i,j,k,hij,hik,hjk,heD,heF⟩

end Atlas.Fischer
