import Atlas.Lattices.EisensteinNormPatterns
import Atlas.Conway.EisensteinFrameOrder
import Atlas.Conway.EisensteinFrameAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinMonomialIntegral_coordinate (p : EisensteinMonomialParameters)
    (x : EisensteinLattice) (i : Fin 12) :
    (eisensteinIntegralAction (eisensteinMonomialParameterIsometry p) x).val i =
      eisensteinSignedPhase p.1 (p.2.1.val i)*x.val (p.2.2.val.symm i) := by
  apply eisensteinToRational_injective
  have h := congrFun (eisensteinIntegralAction_agrees (eisensteinMonomialParameterIsometry p) x) i
  rw [eisensteinMonomialParameterIsometry_apply] at h
  exact h.trans (map_mul eisensteinToRational _ _).symm

theorem eisensteinMonomialNormCount (p : EisensteinMonomialParameters)
    (x : EisensteinShell 6) (n : ℤ) :
    eisensteinNormCount (eisensteinShellAction (eisensteinMonomialParameterIsometry p) 6 x) n =
      eisensteinNormCount x n := by
  classical
  have hc (i : Fin 12) :
      ((eisensteinIntegralAction (eisensteinMonomialParameterIsometry p) x.val).val i).norm =
        (x.val.val (p.2.2.val.symm i)).norm := by
    rw [eisensteinMonomialIntegral_coordinate,map_mul]
    have hp : ∀ b : Bool,∀ a : ZMod 3,(eisensteinSignedPhase b a).norm=1 := by decide +kernel
    rw [hp,one_mul]
  change (Finset.univ.filter (fun i =>
    ((eisensteinIntegralAction (eisensteinMonomialParameterIsometry p) x.val).val i).norm=n)).card = _
  simp_rw [hc]
  have he : Finset.univ.filter (fun i => (x.val.val (p.2.2.val.symm i)).norm=n) =
      (Finset.univ.filter (fun i => (x.val.val i).norm=n)).map p.2.2.val.toEmbedding := by
    ext i
    simp [Finset.mem_map_equiv]
  rw [he,Finset.card_map]
  rfl

theorem eisensteinLocalNormCount (g : eisensteinCoordinateFrameStabilizer)
    (x : EisensteinShell 6) (n : ℤ) :
    eisensteinNormCount (eisensteinShellAction g.val 6 x) n=eisensteinNormCount x n := by
  obtain ⟨p,rfl⟩ := eisensteinFrameFromParameters_surjective g
  exact eisensteinMonomialNormCount p x n

end Atlas.Conway
