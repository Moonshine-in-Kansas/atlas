import Atlas.Fischer.WittMarkedPointRefinements
import Atlas.Fischer.DuadWeightCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev OctadSeparatingVertex (i j : Omega) := {D : Octad // i ∈ D.val ∧ j ∉ D.val}

private theorem octad_filter_split (P Q : Finset Omega → Prop) :
    (octads.filter (fun D => P D ∧ Q D)).card +
      (octads.filter (fun D => P D ∧ ¬ Q D)).card = (octads.filter P).card := by
  classical
  simpa only [Finset.filter_filter] using (octads.filter P).card_filter_add_card_filter_not Q

theorem octadSeparatingVertex_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (OctadSeparatingVertex i j) = 176 := by
  classical
  unfold OctadSeparatingVertex
  rw [octad_predicate_card (fun D : Finset Omega => i ∈ D ∧ j ∉ D)]
  have hi := octadReplication_one ({i} : Finset Omega) (by simp)
  have hijc := octadReplication_two ({i, j} : Finset Omega) (by simp [hij])
  have h := octad_filter_split (fun D => i ∈ D) (fun D => j ∈ D)
  simp only [octadReplication, Finset.singleton_subset_iff, Finset.insert_subset_iff] at hi hijc
  have h' : 77 + (octads.filter (fun D => i ∈ D ∧ j ∉ D)).card = 253 := by
    convert h using 2
    · symm
      convert hijc using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
    · congr 1
      ext B
      simp only [Finset.mem_filter]
    · symm
      convert hi using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
  have ans : (octads.filter (fun D => i ∈ D ∧ j ∉ D)).card = 176 := by omega
  convert ans using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]

theorem octadSeparating_neighbor_count (i j : Omega) (D : OctadSeparatingVertex i j) :
    (octads.filter (fun B => i ∈ B ∧ j ∉ B ∧ (B ∩ D.val.val).card = 4)).card = 105 := by
  classical
  have h140 := octad_inside_point_four D.val i D.property.1
  have h35 := octad_inside_outside_pair_four D.val i j D.property.1 D.property.2
  have h := octad_filter_split (fun B => i ∈ B ∧ (B ∩ D.val.val).card = 4) (fun B => j ∈ B)
  simp only [octadIntersectionCount, Finset.singleton_subset_iff, Finset.insert_subset_iff] at h140 h35
  have ha : (octads.filter (fun B => (i ∈ B ∧ (B ∩ D.val.val).card = 4) ∧ j ∈ B)).card = 35 := by
    convert h35 using 1
    congr 1
    ext B
    simp only [Finset.mem_filter]
    tauto
  have hb : (octads.filter (fun B => (i ∈ B ∧ (B ∩ D.val.val).card = 4) ∧ ¬ j ∈ B)).card =
      (octads.filter (fun B => i ∈ B ∧ j ∉ B ∧ (B ∩ D.val.val).card = 4)).card := by
    congr 1
    ext B
    simp only [Finset.mem_filter]
    tauto
  have hbase : (octads.filter (fun B => i ∈ B ∧ (B ∩ D.val.val).card = 4)).card = 140 := by
    convert h140 using 1
  have h' : 35 + (octads.filter (fun B => i ∈ B ∧ j ∉ B ∧ (B ∩ D.val.val).card = 4)).card = 140 := by
    convert h using 2
    · symm
      convert ha using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
    · symm
      convert hb using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
    · symm
      convert hbase using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
  omega

theorem octadSeparating_cross_count (i j : Omega) (D : OctadSeparatingVertex i j) :
    (octads.filter (fun B => j ∈ B ∧ i ∉ B ∧ (B ∩ D.val.val).card = 4)).card = 35 := by
  classical
  have h70 := (octad_outside_point_distribution D.val.val {j} D.val.property
    (by simpa using D.property.2) (by simp)).2.2
  have h35 := octad_inside_outside_pair_four D.val i j D.property.1 D.property.2
  have h := octad_filter_split (fun B => j ∈ B ∧ (B ∩ D.val.val).card = 4) (fun B => i ∈ B)
  simp only [octadIntersectionCount, Finset.singleton_subset_iff, Finset.insert_subset_iff] at h70 h35
  have ha : (octads.filter (fun B => (j ∈ B ∧ (B ∩ D.val.val).card = 4) ∧ i ∈ B)).card = 35 := by
    convert h35 using 1
    congr 1
    ext B
    simp only [Finset.mem_filter]
    tauto
  have hb : (octads.filter (fun B => (j ∈ B ∧ (B ∩ D.val.val).card = 4) ∧ ¬ i ∈ B)).card =
      (octads.filter (fun B => j ∈ B ∧ i ∉ B ∧ (B ∩ D.val.val).card = 4)).card := by
    congr 1
    ext B
    simp only [Finset.mem_filter]
    tauto
  have hbase : (octads.filter (fun B => j ∈ B ∧ (B ∩ D.val.val).card = 4)).card = 70 := by
    convert h70 using 1
  have h' : 35 + (octads.filter (fun B => j ∈ B ∧ i ∉ B ∧ (B ∩ D.val.val).card = 4)).card = 70 := by
    convert h using 2
    · symm
      convert ha using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
    · symm
      convert hb using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
    · symm
      convert hbase using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]
  omega

end Atlas.Fischer
