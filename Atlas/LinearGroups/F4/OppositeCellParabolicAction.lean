import Atlas.Algebra.Albert.OppositeChart
import Atlas.LinearGroups.F4.ParabolicMarkedPoint

/-! The actual C₀ line stabilizer acts on the normalized opposite affine cell.
The normalization uses its genuine line character, not an assumed parabolic model. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def parabolicLineScale (g : parabolicPointStabilizer (F:=F)) : Fˣ :=
  Classical.choose ((mem_parabolicPointStabilizer_iff g.val).mp g.prop)

theorem parabolicLineScale_action (g : parabolicPointStabilizer (F:=F)) :
    g.val.val parabolicVector=(parabolicLineScale g).val • parabolicVector :=
  Classical.choose_spec ((mem_parabolicPointStabilizer_iff g.val).mp g.prop)

def parabolicLineCharacter : parabolicPointStabilizer (F:=F) →* Fˣ where
  toFun := parabolicLineScale
  map_one' := by
    apply Units.ext
    have h := congrArg (fun x : Carrier F=>x.2 2 0)
      (parabolicLineScale_action (1 : parabolicPointStabilizer (F:=F)))
    simpa [parabolicVector] using h.symm
  map_mul' g h := by
    apply Units.ext
    have he := parabolicLineScale_action (g*h)
    change g.val.val (h.val.val parabolicVector)=_ at he
    rw [parabolicLineScale_action h,map_smul,parabolicLineScale_action g,smul_smul] at he
    have hc := congrArg (fun x : Carrier F=>x.2 2 0) he
    simpa [parabolicVector,mul_comm] using hc.symm

theorem parabolicLineCharacter_action (g : parabolicPointStabilizer (F:=F)) :
    g.val.val parabolicVector=(parabolicLineCharacter g).val • parabolicVector :=
  parabolicLineScale_action g

theorem parabolicPairing_C7 (x : Carrier F) :
    tracePairing (parabolicVector (F:=F)) x=x.2 2 7 := by
  rw [tracePairing_coordinates]
  simp [parabolicVector,Fin.sum_univ_succ]

theorem parabolicLineCharacter_C7 (g : parabolicPointStabilizer (F:=F))
    (x : Carrier F) :
    (parabolicLineCharacter g).val*(g.val.val x).2 2 7=x.2 2 7 := by
  have h := stabilizer_tracePairing g.val parabolicVector x
  rw [parabolicLineCharacter_action,tracePairing_smul_left,
    parabolicPairing_C7,parabolicPairing_C7] at h
  exact h

def normalizedParabolicCell (g : parabolicPointStabilizer (F:=F))
    (x : OppositeCell F) : OppositeCell F :=
  ⟨(parabolicLineCharacter g).val • g.val.val x.val,by
    refine ⟨?_,?_,?_⟩
    · rw [adjoint_smul,stabilizer_adjoint,x.prop.1,map_zero,smul_zero]
    · change parabolicTrace ((parabolicLineCharacter g).val • g.val.val x.val)=0
      rw [map_smul]
      change (parabolicLineCharacter g).val*trace (g.val.val x.val)=0
      rw [stabilizer_trace,x.prop.2.1,mul_zero]
    · exact (parabolicLineCharacter_C7 g x.val).trans x.prop.2.2⟩

instance oppositeCellParabolicAction : MulAction (parabolicPointStabilizer (F:=F)) (OppositeCell F) where
  smul := normalizedParabolicCell
  one_smul x := by
    apply Subtype.ext
    change (parabolicLineCharacter (1 : parabolicPointStabilizer (F:=F))).val •
      (1 : parabolicPointStabilizer (F:=F)).val.val x.val=x.val
    rw [map_one]
    simp
  mul_smul g h x := by
    apply Subtype.ext
    change (parabolicLineCharacter (g*h)).val • (g*h).val.val x.val =
      (parabolicLineCharacter g).val • g.val.val
        ((parabolicLineCharacter h).val • h.val.val x.val)
    rw [map_mul,Units.val_mul,map_smul,smul_smul]
    rfl

theorem oppositeCellParabolicAction_val (g : parabolicPointStabilizer (F:=F))
    (x : OppositeCell F) :
    (g • x).val=(parabolicLineCharacter g).val • g.val.val x.val := rfl

theorem parabolicLineCharacter_eq_one_of_vector_fixed
    (g : parabolicPointStabilizer (F:=F))
    (hg : g.val.val parabolicVector=parabolicVector) : parabolicLineCharacter g=1 := by
  apply Units.ext
  have h := parabolicLineCharacter_action g
  rw [hg] at h
  have hc := congrArg (fun x : Carrier F=>x.2 2 0) h
  simpa [parabolicVector] using hc.symm

end Atlas.F4
