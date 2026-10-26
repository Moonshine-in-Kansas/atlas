import Atlas.Rudvalis.FourRowKernelOrbit

namespace Atlas.Rudvalis

 theorem coordinateCross_stabilizer_linear_lift (p : Point) (A : E≃ₗ[Bit]E)
    (hA : A p.val=p.val) :
    ∃g : MulAction.stabilizer codeGroup (coordinateCross (p,0)),codeBlockLinearHom g.val=A := by
  obtain ⟨g,hg⟩ := codeBlockLinearHom_surjective A
  have hr : (g.val.right (p,0)).1=p := by
    apply Subtype.ext
    rw [←codeBlockLinear_coordinates,hg,hA]
  let y := (g.val.right (p,0)).2
  have hy : g.val.right (p,0)=(p,y) := Prod.ext hr rfl
  obtain ⟨i,hi⟩ := point_has_one p
  have hu : dot (basisPoint i).val p.val=1 := by rw [dot_basisPoint]; exact hi
  let B := outerMatrix y (basisPoint i).val
  have hB : matrixAt B p.val=y := by rw [matrixAt_outer,hu,one_smul]
  obtain ⟨t,ht⟩ := codeRowKernel_translation_lift B
  have hf : t.val*g∈MulAction.stabilizer codeGroup (coordinateCross (p,0)) := by
    change (t.val*g) • coordinateCross (p,0)=coordinateCross (p,0)
    rw [mul_smul,coordinateCross_action,hy,coordinateCross_action,ht]
    change coordinateCross (p,y+matrixAt B p.val)=coordinateCross (p,0)
    rw [hB,vector_add_self]
  refine ⟨⟨t.val*g,hf⟩,?_⟩
  rw [map_mul,show codeBlockLinearHom t.val=1 from t.prop,hg,one_mul]

 theorem codeReferenceStabilizer_linear_lift (A : E≃ₗ[Bit]E)
    (hA : A (rowLabel 0).val=(rowLabel 0).val) :
    ∃g : codeReferenceStabilizer,codeBlockLinearHom g.val=A := by
  obtain ⟨g,hg⟩ := coordinateCross_stabilizer_linear_lift (rowLabel 0) A hA
  refine ⟨⟨g.val,?_⟩,hg⟩
  change g.val • localReferenceCross=localReferenceCross
  rw [localReferenceCross_eq]
  exact g.prop

/-- A transvection fixing p transports any two forms taking value one at p. -/
noncomputable def activeFormTransvection (p a b : Point)
    (ha : dot a.val p.val=1) (hb : dot b.val p.val=1) : E≃ₗ[Bit]E where
  toFun v := v+dot (a.val+b.val) v • p.val
  invFun v := v+dot (a.val+b.val) v • p.val
  left_inv v := by
    have hz : dot (a.val+b.val) p.val=0 := by rw [dot_add_left,ha,hb]; decide
    simp only [dot_add_right,dot_smul_right,hz,mul_zero,add_zero]
    rw [add_assoc,←add_smul]
    have hh (k : Bit) : k+k=0 := by exact Atlas.Codes.bit_self_add k
    rw [hh,zero_smul,add_zero]
  right_inv v := by
    have hz : dot (a.val+b.val) p.val=0 := by rw [dot_add_left,ha,hb]; decide
    simp only [dot_add_right,dot_smul_right,hz,mul_zero,add_zero]
    rw [add_assoc,←add_smul]
    have hh (k : Bit) : k+k=0 := by exact Atlas.Codes.bit_self_add k
    rw [hh,zero_smul,add_zero]
  map_add' v w := by rw [dot_add_right,add_smul]; abel
  map_smul' k v := by
    simp only [dot_smul_right,smul_add,smul_smul,RingHom.id_apply]

 theorem activeFormTransvection_fixed (p a b : Point) (ha : dot a.val p.val=1)
    (hb : dot b.val p.val=1) : activeFormTransvection p a b ha hb p.val=p.val := by
  change p.val+dot (a.val+b.val) p.val • p.val=p.val
  rw [dot_add_left,ha,hb,show (1:Bit)+1=0 from by decide,zero_smul,add_zero]

 theorem activeFormTransvection_dual (p a b : Point) (ha : dot a.val p.val=1)
    (hb : dot b.val p.val=1) (v : E) :
    dot b.val (activeFormTransvection p a b ha hb v)=dot a.val v := by
  change dot b.val (v+dot (a.val+b.val) v • p.val)=_
  rw [dot_add_right,dot_smul_right,hb,mul_one,dot_add_left]
  rw [add_comm (dot a.val v),←add_assoc,Atlas.Codes.bit_self_add,zero_add]

end Atlas.Rudvalis
