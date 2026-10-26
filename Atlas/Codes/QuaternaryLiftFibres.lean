import Atlas.Codes.QuaternaryWeightSplit

/-! Signed lifts of one residue form a torsor over the shortened torsion code. -/
namespace Atlas.Codes.Quaternary
variable {ι : Type*}

def supportedCode (T : Submodule Binary (ι → Binary)) (d : ι → Binary) :
    Submodule Binary (ι → Binary) where
  carrier := {s | s∈T ∧ ∀ i,d i=0 → s i=0}
  zero_mem' := ⟨T.zero_mem,by simp⟩
  add_mem' := by
    rintro a b ⟨ha,ha0⟩ ⟨hb,hb0⟩
    exact ⟨T.add_mem ha hb,fun i hi => by simp [ha0 i hi,hb0 i hi]⟩
  smul_mem' := by
    rintro a b ⟨hb,hb0⟩
    exact ⟨T.smul_mem a hb,fun i hi => by simp [hb0 i hi]⟩

abbrev SignedLift (Q : Submodule Quat (ι → Quat)) (d : ι → Binary) :=
  {w : Q // reduce w.val=d ∧ ∀ i,w.val i≠2}

theorem reduced_zero_no_two (a : Quat) (hr : reduceScalar a=0) (h : a≠2) : a=0 := by
  decide +kernel +revert

theorem signed_lift_add_double (w : ι → Quat) (s : ι → Binary)
    (hw : ∀ i,w i≠2) (hs : ∀ i,reduce w i=0 → s i=0) :
    ∀ i,(w+double s) i≠2 := by
  have h : ∀ a : Quat,∀ b : Binary,a≠2 → (reduceScalar a=0 → b=0) → a+doubleScalar b≠2 := by
    decide +kernel
  intro i
  exact h _ _ (hw i) (hs i)

noncomputable def signedLiftMap (Q : Submodule Quat (ι → Quat))
    (T : Submodule Binary (ι → Binary)) (ht : ∀ s,double s∈Q ↔ s∈T)
    (d : ι → Binary) (w : SignedLift Q d) : supportedCode T d → SignedLift Q d := fun s =>
  ⟨⟨w.val.val+double s.val,Q.add_mem w.val.prop ((ht s.val).mpr s.prop.1)⟩,
    by rw [map_add,reduce_double,add_zero]; exact w.prop.1,
    signed_lift_add_double w.val.val s.val w.prop.2 (fun i hi =>
      s.prop.2 i (by rwa [← w.prop.1]))⟩

theorem signedLiftMap_bijective (Q : Submodule Quat (ι → Quat))
    (T : Submodule Binary (ι → Binary)) (ht : ∀ s,double s∈Q ↔ s∈T)
    (d : ι → Binary) (w : SignedLift Q d) : Function.Bijective (signedLiftMap Q T ht d w) := by
  constructor
  · intro a b h
    apply Subtype.ext
    have he := congrArg (fun v : SignedLift Q d => v.val.val) h
    change w.val.val+double a.val=w.val.val+double b.val at he
    exact double_injective (add_left_cancel he)
  · intro v
    have hz : reduce (v.val.val-w.val.val)=0 := by rw [map_sub,v.prop.1,w.prop.1,sub_self]
    obtain ⟨s,hs⟩ := (reduce_eq_zero _).mp hz
    have hT : s∈T := (ht s).mp (by rw [hs]; exact Q.sub_mem v.val.prop w.val.prop)
    have h0 (i : ι) (hi : d i=0) : s i=0 := by
      have hv : v.val.val i=0 := reduced_zero_no_two _
        (by change reduce v.val.val i=0; rw [v.prop.1,hi]) (v.prop.2 i)
      have hw : w.val.val i=0 := reduced_zero_no_two _
        (by change reduce w.val.val i=0; rw [w.prop.1,hi]) (w.prop.2 i)
      have he := congrFun hs i
      change doubleScalar (s i)=v.val.val i-w.val.val i at he
      rw [hv,hw,sub_self] at he
      exact doubleScalar_injective (by simpa using he)
    refine ⟨⟨s,hT,h0⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change w.val.val+double s=v.val.val
    rw [hs]
    abel

noncomputable def signedLiftEquiv (Q : Submodule Quat (ι → Quat))
    (T : Submodule Binary (ι → Binary)) (ht : ∀ s,double s∈Q ↔ s∈T)
    (d : ι → Binary) (w : SignedLift Q d) : supportedCode T d ≃ SignedLift Q d :=
  Equiv.ofBijective (signedLiftMap Q T ht d w) (signedLiftMap_bijective Q T ht d w)

end Atlas.Codes.Quaternary
