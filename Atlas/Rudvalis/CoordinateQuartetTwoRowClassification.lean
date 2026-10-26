import Atlas.Rudvalis.CoordinateTwoRowRigidity

namespace Atlas.Rudvalis

/-- A quartet in the (2,2) row pattern belongs to the constructed affine-plane family. -/
theorem coordinateQuartet_two_row_constructed (p q : Point) (hpq : p≠q) (x y z t : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y))
    (hzt : coordinateCross (q,z)≠coordinateCross (q,t))
    (hQ : IsQuartet {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (q,t)}) :
    {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (q,t)}∈
      Set.range coordinatePlaneQuartetFromParameters := by
  classical
  let s : CoordinateRowPair := ⟨{p,q},by simp [hpq]⟩
  let a := coordinateRowPairNormal s
  have hap : dot a.val p.val=0 := coordinateRowPairNormal_spec s p (by simp [s])
  have haq : dot a.val q.val=0 := coordinateRowPairNormal_spec s q (by simp [s])
  obtain ⟨hd,he⟩ := coordinateQuartet_two_row_rigidity p q hpq x y z t hxy hzt hQ
  have hh : ∀a b : Bit,a+b=0 → a=b := by decide +kernel
  have hxy' : dot a.val y=dot a.val x := by
    apply hh
    rw [←dot_add_right]
    rcases hd with hd|hd <;> rw [hd] <;> simp [dot_add_right,hap,haq]
  have hzt' : dot a.val t=dot a.val z := by
    apply hh
    rw [←dot_add_right]
    rcases he with he|he <;> rw [he] <;> simp [dot_add_right,hap,haq]
  let f : s.val→Bit := fun r => if r.val=p then dot a.val x else dot a.val z
  let v : CoordinatePlaneQuartetParameters := ⟨s,f⟩
  have hv : coordinatePlaneQuartetFromParameters v=
      coordinatePlaneQuartet p q a (dot a.val x) (dot a.val z) := by
    rw [coordinatePlaneQuartetFromParameters_eq v p q hpq rfl]
    simp only [v,f,ite_true,Ne.symm hpq,ite_false]
    rfl
  refine ⟨v,?_⟩
  apply Eq.symm
  apply Set.eq_of_subset_of_ncard_le
  · intro c hc
    rw [hv]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
    rcases hc with rfl|rfl|rfl|rfl
    · exact Or.inl ⟨x,rfl,rfl⟩
    · exact Or.inl ⟨y,hxy',rfl⟩
    · exact Or.inr ⟨z,rfl,rfl⟩
    · exact Or.inr ⟨t,hzt',rfl⟩
  · rw [(coordinatePlaneQuartetFromParameters_isQuartet v).1,hQ.1]
  · exact isQuartet_finite (coordinatePlaneQuartetFromParameters_isQuartet v)

end Atlas.Rudvalis
