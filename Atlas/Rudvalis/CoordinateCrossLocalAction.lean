import Atlas.Rudvalis.CoordinateCrossAction

namespace Atlas.Rudvalis

theorem binaryCoordinate_same_row (p d e : Point) (hpd : p≠d) (hpe : p≠e) (x : E) :
    ∃g : binaryPermutationGroup,g.val (p,x)=(p,x) ∧
      g.val (p,x+d.val)=(p,x+e.val) := by
  obtain ⟨A,hAp,hAd⟩ := point_pair_linearEquiv p d p e hpd hpe
  choose t ht using section_difference_origin A
  let g := binarySectionGroupLift A t ht
  have hr : linearPointEquiv A p=p := Subtype.ext hAp
  obtain ⟨k,hk⟩ := point_has_one p
  let u := (basisPoint k).val
  have hu : dot u p.val=1 := by rw [dot_basisPoint]; exact hk
  let B := outerMatrix (x+A (x+t p)) u
  have hB : matrixAt B p.val=x+A (x+t p) := by rw [matrixAt_outer,hu,one_smul]
  refine ⟨⟨coordinateTranslation B,coordinateTranslation_mem B⟩*g,?_,?_⟩
  · change (linearPointEquiv A p,A (x+t p)+matrixAt B (linearPointEquiv A p).val)=(p,x)
    rw [hr,hB]
    congr 1
    calc A (x+t p)+(x+A (x+t p))=x+(A (x+t p)+A (x+t p)) := by abel
         _=x := by rw [vector_add_self,add_zero]
  · change (linearPointEquiv A p,A (x+d.val+t p)+matrixAt B (linearPointEquiv A p).val)=(p,x+e.val)
    rw [hr,hB,show x+d.val+t p=(x+t p)+d.val by abel,map_add,hAd]
    congr 1
    calc A (x+t p)+e.val+(x+A (x+t p))=(x+e.val)+(A (x+t p)+A (x+t p)) := by abel
         _=x+e.val := by rw [vector_add_self,add_zero]

theorem coordinateCross_same_row_transitive (p : Point) (x y z : E)
    (hy : coordinateCross (p,y)≠coordinateCross (p,x))
    (hz : coordinateCross (p,z)≠coordinateCross (p,x)) :
    ∃g : MulAction.stabilizer codeGroup (coordinateCross (p,x)),
      g.val • coordinateCross (p,y)=coordinateCross (p,z) := by
  have diff (y : E) (h : coordinateCross (p,y)≠coordinateCross (p,x)) :
      y+x≠0 ∧ y+x≠p.val := by
    constructor
    · intro he
      have hyx : y=x := by
        calc y=(y+x)+x := by simp [add_assoc,vector_add_self]
             _=x := by rw [he,zero_add]
      exact h (by rw [hyx])
    · intro he
      have hyx : y=x+p.val := by
        calc y=(y+x)+x := by simp [add_assoc,vector_add_self]
             _=x+p.val := by rw [he,add_comm]
      apply h
      rw [hyx]
      simpa only [codeI_coordinate] using coordinateCross_I (p,x)
  obtain ⟨hy0,hyp⟩ := diff y hy
  obtain ⟨hz0,hzp⟩ := diff z hz
  let d : Point := ⟨y+x,hy0⟩
  let e : Point := ⟨z+x,hz0⟩
  have hpd : p≠d := by intro h; exact hyp (congrArg Subtype.val h).symm
  have hpe : p≠e := by intro h; exact hzp (congrArg Subtype.val h).symm
  obtain ⟨b,hb,hc⟩ := binaryCoordinate_same_row p d e hpd hpe x
  have hyx : x+d.val=y := by change x+(y+x)=y; rw [add_comm y x,←add_assoc,vector_add_self,zero_add]
  have hzx : x+e.val=z := by change x+(z+x)=z; rw [add_comm z x,←add_assoc,vector_add_self,zero_add]
  rw [hyx,hzx] at hc
  obtain ⟨g,hg⟩ := codePermutationHom_surjective b
  have he : g.val.right=b.val := congrArg Subtype.val hg
  have hfix : g∈MulAction.stabilizer codeGroup (coordinateCross (p,x)) := by
    change g • coordinateCross (p,x)=coordinateCross (p,x)
    rw [coordinateCross_action,he,hb]
  refine ⟨⟨g,hfix⟩,?_⟩
  rw [coordinateCross_action,he,hc]

end Atlas.Rudvalis
