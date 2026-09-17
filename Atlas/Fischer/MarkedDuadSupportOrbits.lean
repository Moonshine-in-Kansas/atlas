import Atlas.Fischer.RootFamilyParameters
import Atlas.Mathieu.GolaySmallSetFixing

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual Mathieu transport of duads, fixing their prescribed common markings
and an exterior point; this is derived from retained five-transitivity. -/
theorem mathieu_marked_duad_transitive (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (p q : RootDuad) (hSp : S ⊆ p.val) (hSq : S ⊆ q.val)
    (hxp : x∉p.val) (hxq : x∉q.val) :
    ∃ g : Mathieu24CodeModel,permuteBlock g.val p.val=q.val ∧
      (∀ i∈S,g.val i=i) ∧ g.val x=x := by
  classical
  have hd (p : RootDuad) (hSp : S ⊆ p.val) (hxp : x∉p.val) :
      Disjoint (insert x S) (p.val \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨hip,hiS⟩ := Finset.mem_sdiff.mp hj
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hxp hip
    · exact hiS hi
  have hxS : x∉S := fun hi => hxp (hSp hi)
  obtain ⟨g,hfix,hmap⟩ := mathieu24_fixing_small_set_transitive (insert x S)
    (p.val \ S) (q.val \ S) (2-S.card) (hd p hSp hxp) (hd q hSq hxq)
    (by rw [Finset.card_sdiff_of_subset hSp,p.prop])
    (by rw [Finset.card_sdiff_of_subset hSq,q.prop])
    (by rw [Finset.card_insert_of_notMem hxS];omega)
  have hgS : S.image g.val=S := by
    calc
      S.image g.val=S.image id := Finset.image_congr (fun i hi => hfix i (Finset.mem_insert_of_mem hi))
      _ = S := Finset.image_id
  refine ⟨g,?_,fun i hi => hfix i (Finset.mem_insert_of_mem hi),hfix x (Finset.mem_insert_self _ _)⟩
  change p.val.image g.val=q.val
  calc
    _ = (S ∪ (p.val \ S)).image g.val := by rw [Finset.union_sdiff_of_subset hSp]
    _ = S ∪ (q.val \ S) := by rw [Finset.image_union,hgS];exact congrArg (S ∪ ·) hmap
    _ = q.val := Finset.union_sdiff_of_subset hSq

end Atlas.Fischer
