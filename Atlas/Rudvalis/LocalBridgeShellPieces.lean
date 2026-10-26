import Atlas.Rudvalis.LocalBridgeDoubles
import Atlas.Rudvalis.HeavyCommonPerpendicular

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 6000

theorem halfCoordinates_signedSeed (z : SeedCoordinate→ℤ) :
    halfCoordinates (signedSeedTransport z)=(1/2:ℚ) • seedIntegerRational z := by
  funext i
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective i
  change ((signedSeedTransport z (seedCoordinateEquiv (r,k)):ℤ):ℚ)/2=_
  rw [signedSeedTransport_apply]
  change _=(1/2:ℚ)*seedTransportLinear (fun i=>(z i:ℚ)) (seedCoordinateEquiv (r,k))
  rw [seedTransportLinear_apply]
  simp only [signedPositionSign]
  split_ifs <;> push_cast <;> ring

noncomputable def localBridgeShell (c : Fin 3) : MinimalShell :=
  ![localFusionT • coordinateShellLift (localOutsideCoordinate,true),
    shiftedSeedShell,localFusionT • shiftedSeedShell] c

theorem localBridgeShell_val (c : Fin 3) :
    (localBridgeShell c).val.val=halfCoordinates (localBridgeDouble c) := by
  rw [localBridgeDouble,halfCoordinates_signedSeed]
  fin_cases c
  · change (localFusionT • coordinateShellLift (localOutsideCoordinate,true)).val.val=_
    rw [local_gaussian_shell_val,local_axis_shell_val]
    have hi : originalFrame (1,1)=coordinateMinimum localOutsideCoordinate := by
      rw [originalFrame_signed_axis];rfl
    rw [←hi]
    have h := localFusionT_extra_vectors 0
    rw [localExtraVector_axis 0 (by decide)] at h
    change localFusionT.val (originalFrame (1,1))=_ at h
    rw [h,localExtraVector,funext localBridgeDouble_first,seedIntegerRational_int_mul,smul_smul]
    norm_num
  · change shiftedSeedShell.val.val=_
    rw [shiftedSeedShell_val,shiftedSeedA,funext localBridgeDouble_middle]
    rfl
  · change (localFusionT • shiftedSeedShell).val.val=_
    rw [local_gaussian_shell_val,shiftedSeedShell_val,shiftedSeedA,←localExtraVector_seed,map_smul,
      localFusionT_extra_vectors,localExtraVector,funext localBridgeDouble_last,
      seedIntegerRational_int_mul,smul_smul,smul_smul]
    norm_num
    rfl

theorem localBridgeWord_mem (c : Fin 3) : localBridgeWord c∈quaternaryCode := by
  obtain ⟨z,hz,he⟩ := (rudvalisLattice_mem _).mp (localBridgeShell c).val.prop
  rw [localBridgeShell_val] at he
  have h := halfCoordinates_injective he
  subst z
  exact hz

noncomputable def localBridgeMinimumWord (c : Fin 3) : MinimumWords :=
  ⟨⟨localBridgeWord c,localBridgeWord_mem c⟩,localBridgeWord_weight c⟩

theorem localBridgeMinimumWord_shell (c : Fin 3) :
    minimumWordShellLift (localBridgeMinimumWord c)=localBridgeShell c := by
  apply Subtype.ext
  apply Subtype.ext
  change halfCoordinates (integerLift (localBridgeWord c))=_
  rw [localBridgeWord_balanced,localBridgeShell_val]

theorem localBridgeWord_four (c : Fin 2) :
    admissibleFourSupport (reduce (localBridgeWord c.castSucc)) := by
  rcases quaternary_minimum_support_cases _ (localBridgeWord_mem c.castSucc)
    (localBridgeWord_weight c.castSucc) with h|⟨a,ha,he⟩
  · exact h
  · have h := binaryNormalMap_injective (he.trans (localBridgeWord_residue c.castSucc))
    have hz : (seedEncodedParameters (localBridgeParameterCode c.castSucc)).2.2=0 := by
      have hh : ∀c : Fin 2,∀i : Fin 3,
          (seedEncodedParameters (localBridgeParameterCode c.castSucc)).2.2 i=0 := by decide +kernel
      exact funext (hh c)
    exact False.elim (ha ((congrArg (fun a : BinaryParameters => a.2.2) h).trans hz))

theorem localBridgeWord_heavy : hasNonzeroQuadraticPart (reduce (localBridgeWord 2)) := by
  refine ⟨seedEncodedParameters (localBridgeParameterCode 2),?_,(localBridgeWord_residue 2).symm⟩
  intro h
  have hi := congrFun h 1
  have hn : (seedEncodedParameters (localBridgeParameterCode 2)).2.2 (1:Fin 3)≠0 := by decide +kernel
  exact hn hi

theorem localBridgeShell_four (c : Fin 2) : localBridgeShell c.castSucc∈fourShellPiece := by
  refine ⟨⟨⟨localBridgeWord c.castSucc,localBridgeWord_mem _⟩,
    localBridgeWord_weight _,localBridgeWord_four c⟩,?_⟩
  exact localBridgeMinimumWord_shell c.castSucc

theorem localBridgeShell_heavy : localBridgeShell 2∈heavyShellPiece := by
  refine ⟨⟨⟨localBridgeWord 2,localBridgeWord_mem _⟩,
    localBridgeWord_weight _,localBridgeWord_heavy⟩,?_⟩
  exact localBridgeMinimumWord_shell 2

theorem localFourBridgeCross_four :
    ∃c : FourBlockCrosses,shellPieceCrossMap fourShellPiece c=localFourBridgeCross :=
  ⟨Quotient.mk _ ⟨localBridgeShell 0,localBridgeShell_four 0⟩,rfl⟩

theorem shiftedSeedCross_four :
    ∃c : FourBlockCrosses,shellPieceCrossMap fourShellPiece c=shiftedSeedCross :=
  ⟨Quotient.mk _ ⟨localBridgeShell 1,localBridgeShell_four 1⟩,rfl⟩

theorem localHeavyBridgeCross_heavy :
    ∃c : HeavyCrosses,shellPieceCrossMap heavyShellPiece c=localHeavyBridgeCross :=
  ⟨Quotient.mk _ ⟨localBridgeShell 2,localBridgeShell_heavy⟩,rfl⟩

end Atlas.Rudvalis
