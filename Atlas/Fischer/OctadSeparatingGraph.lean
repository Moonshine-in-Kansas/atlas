import Atlas.Fischer.OctadSeparatingCounts
import Atlas.Graphs.DenseConnected

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

instance octadSeparatingVertex_fintype (i j : Omega) : Fintype (OctadSeparatingVertex i j) :=
  Fintype.ofFinite _

/-- The actual176-vertex octad graph used in the pointwise-U stabilizer proof. -/
def octadSeparatingGraph (i j : Omega) : SimpleGraph (OctadSeparatingVertex i j) where
  Adj D E := (E.val.val ∩ D.val.val).card = 4
  symm := ⟨fun D E h => by simpa only [Finset.inter_comm] using h⟩
  loopless := ⟨fun D h => by
    have hc := octad_size D.val.val D.val.property
    rw [Finset.inter_self, hc] at h
    omega⟩

theorem octadSeparatingGraph_degree (i j : Omega) (D : OctadSeparatingVertex i j) :
    (octadSeparatingGraph i j).degree D = 105 := by
  let e : (octadSeparatingGraph i j).neighborSet D ≃
      {B : Octad // i ∈ B.val ∧ j ∉ B.val ∧ (B.val ∩ D.val.val).card = 4} :=
    { toFun := fun B => ⟨B.val.val, B.val.property.1, B.val.property.2, B.property⟩
      invFun := fun B => ⟨⟨B.val, B.property.1, B.property.2.1⟩, B.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
  rw [octad_predicate_card (fun B : Finset Omega => i ∈ B ∧ j ∉ B ∧ (B ∩ D.val.val).card = 4)]
  convert octadSeparating_neighbor_count i j D using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]

theorem octadSeparatingGraph_connected (i j : Omega) (hij : i ≠ j) :
    (octadSeparatingGraph i j).Connected := by
  have hc : Fintype.card (OctadSeparatingVertex i j) = 176 := by
    rw [← Nat.card_eq_fintype_card, octadSeparatingVertex_card i j hij]
  letI : Nonempty (OctadSeparatingVertex i j) :=
    Fintype.card_pos_iff.mp (by rw [hc]; norm_num)
  apply Atlas.Graphs.connected_of_half_lt_degree
  intro D
  rw [hc, octadSeparatingGraph_degree]
  norm_num

/-- The35 cross incidences counted as actual opposite-side vertices. -/
theorem octadSeparating_cross_vertex_card (i j : Omega) (D : OctadSeparatingVertex i j) :
    Nat.card {E : OctadSeparatingVertex j i // (E.val.val ∩ D.val.val).card = 4} = 35 := by
  let e : {E : OctadSeparatingVertex j i // (E.val.val ∩ D.val.val).card = 4} ≃
      {B : Octad // j ∈ B.val ∧ i ∉ B.val ∧ (B.val ∩ D.val.val).card = 4} :=
    { toFun := fun B => ⟨B.val.val, B.val.property.1, B.val.property.2, B.property⟩
      invFun := fun B => ⟨⟨B.val, B.property.1, B.property.2.1⟩, B.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, octad_predicate_card (fun B : Finset Omega => j ∈ B ∧ i ∉ B ∧ (B ∩ D.val.val).card = 4)]
  convert octadSeparating_cross_count i j D using 1 <;> congr 1 <;> ext B <;> simp only [Finset.mem_filter]

end Atlas.Fischer
