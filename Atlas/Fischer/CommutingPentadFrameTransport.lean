import Atlas.Fischer.MarkedPentadCentralizerOrder

noncomputable section
namespace Atlas.Fischer

/-- Actual maximal frames containing every entry of an ordered commuting pentad. -/
abbrev CommutingPentadFrame (t : OrderedCommutingTuple 5) :=
  {F : FischerFrame // ∀ k : Fin 5,t.val k ∈ F.val}

def commutingPentadFrameTransport (g : rootGeneratedRayGroup)
    (t u : OrderedCommutingTuple 5) (h : g • t=u) :
    CommutingPentadFrame t ≃ CommutingPentadFrame u where
  toFun F := ⟨g • F.val,by
    intro k
    have hk := congrArg (fun t : OrderedCommutingTuple 5 => t.val k) h
    rw [← hk]
    exact ⟨t.val k,F.prop k,rfl⟩⟩
  invFun F := ⟨g⁻¹ • F.val,by
    intro k
    have hk := congrArg (fun t : OrderedCommutingTuple 5 => t.val k) h
    refine ⟨u.val k,F.prop k,?_⟩
    change g⁻¹*u.val k*(g⁻¹)⁻¹=t.val k
    rw [← hk,orderedCommutingTuple_smul_apply]
    group⟩
  left_inv F := by apply Subtype.ext; exact inv_smul_smul g F.val
  right_inv F := by apply Subtype.ext; exact smul_inv_smul g F.val

@[simp] theorem commutingPentadFrameTransport_val (g : rootGeneratedRayGroup)
    (t u : OrderedCommutingTuple 5) (h : g • t=u) (F : CommutingPentadFrame t) :
    (commutingPentadFrameTransport g t u h F).val=g • F.val := rfl

def commutingPentadFrameConjugate (t : OrderedCommutingTuple 5)
    (g : MulAction.stabilizer rootGeneratedRayGroup t) (F : CommutingPentadFrame t) :
    CommutingPentadFrame t :=
  commutingPentadFrameTransport g.val t t (MulAction.mem_stabilizer_iff.mp g.prop) F

instance commutingPentadFrameMulAction (t : OrderedCommutingTuple 5) :
    MulAction (MulAction.stabilizer rootGeneratedRayGroup t) (CommutingPentadFrame t) where
  smul := commutingPentadFrameConjugate t
  one_smul F := by apply Subtype.ext; exact one_smul rootGeneratedRayGroup F.val
  mul_smul g h F := by apply Subtype.ext; exact mul_smul g.val h.val F.val

@[simp] theorem commutingPentadFrame_smul_val (t : OrderedCommutingTuple 5)
    (g : MulAction.stabilizer rootGeneratedRayGroup t) (F : CommutingPentadFrame t) :
    (g • F).val=g.val • F.val := rfl

end Atlas.Fischer
