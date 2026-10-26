import Atlas.Rudvalis.LocalFusionBridgeEnergy
import Atlas.Rudvalis.CoordinateQuartetCompletion

namespace Atlas.Rudvalis
set_option maxRecDepth 6000

noncomputable def localTripleSourceCoordinate (i : Fin 3) : Coordinate :=
  let j : SeedCoordinate := ![(0,1),(4,4),(1,2)] i
  seedCoordinateEquiv (j.1,signedPositionIndex j.2)

theorem localTripleSource_axis (i : Fin 3) :
    originalFrame (![(0,1),(4,4),(1,2)] i)=coordinateMinimum (localTripleSourceCoordinate i) := by
  rw [originalFrame_signed_axis]
  have hn : (![ (0,1),(4,4),(1,2)] i : SeedCoordinate).2≠0 := by decide +kernel +revert
  rw [ite_eq_right hn]
  rfl

theorem minimalCross_I_smul (v : MinimalShell) : minimalCross (codeI • v)=minimalCross v := by
  apply (minimalCross_eq_iff _ _).mpr
  exact ⟨⟨codeI,Subgroup.mem_zpowers codeI⟩,rfl⟩

theorem minimalCross_negI_eq (v w : MinimalShell)
    (h : v.val.val= -rationalI w.val.val) : minimalCross v=minimalCross w := by
  apply (minimalCross_eq_iff _ _).mpr
  refine ⟨⟨codeI^3,Subgroup.pow_mem _ (Subgroup.mem_zpowers codeI) 3⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change rationalMonomialHom (codeI.val^3) w.val.val=v.val.val
  rw [h,map_pow]
  change (rationalI^3) w.val.val= -rationalI w.val.val
  rw [show (3:ℕ)=2+1 from rfl,pow_add,pow_two,pow_one]
  change rationalI (rationalI (rationalI w.val.val))= -rationalI w.val.val
  exact rationalI_square _

theorem local_gaussian_shell_val (g : gaussianLatticeGroup) (v : MinimalShell) :
    (g • v).val.val=g.val v.val.val := rfl

theorem local_code_shell_val (g : codeGroup) (v : MinimalShell) :
    (g • v).val.val=rationalMonomialHom g.val v.val.val := rfl

theorem local_axis_shell_val (i : Coordinate) :
    (coordinateShellLift (i,true)).val.val=coordinateMinimum i := rfl

noncomputable def shiftedSeedShell : MinimalShell :=
  codeI • (localTripleTransport • coordinateShellLift (localTripleSourceCoordinate 2,true))

noncomputable def shiftedSeedCross : MinimalCross := minimalCross shiftedSeedShell

theorem shiftedSeedShell_val : shiftedSeedShell.val.val=shiftedSeedA := by
  rw [shiftedSeedShell,local_code_shell_val,local_gaussian_shell_val,local_axis_shell_val]
  change rationalI (localTripleTransport.val (coordinateMinimum (localTripleSourceCoordinate 2)))=_
  rw [←localTripleSource_axis]
  change rationalI (localTripleTransport.val (originalFrame (1,2)))=_
  rw [localTripleTransport_third,map_neg,rationalI_square,neg_neg]

theorem localTripleTransport_first_cross :
    localTripleTransport • coordinateCross (localTripleSourceCoordinate 0)=localReferenceCross := by
  apply gaussian_coordinateCross_of_negative
  rw [←localTripleSource_axis]
  change localTripleTransport.val (originalFrame (0,1))= -coordinateMinimum (localFusionSourceCoordinate 0)
  rw [localTripleTransport_first,←localFusionSource_axis]
  rfl

theorem localTripleTransport_second_cross :
    localTripleTransport • coordinateCross (localTripleSourceCoordinate 1)=referenceSecondCross := by
  apply minimalCross_negI_eq
  rw [local_gaussian_shell_val,local_axis_shell_val,local_axis_shell_val]
  change localTripleTransport.val (coordinateMinimum (localTripleSourceCoordinate 1))=
    -rationalI (coordinateMinimum (localFusionSourceCoordinate 1))
  rw [←localTripleSource_axis,←localFusionSource_axis]
  exact localTripleTransport_second

theorem localTripleTransport_third_cross :
    localTripleTransport • coordinateCross (localTripleSourceCoordinate 2)=shiftedSeedCross := by
  exact (minimalCross_I_smul _).symm

theorem shiftedSeedCross_no_quartet :
    ¬∃Q : Set MinimalCross,IsQuartet Q ∧ referenceCouple⊆Q ∧ shiftedSeedCross∈Q := by
  rintro ⟨Q,hQ,hc,hs⟩
  apply no_quartet_through_three_coordinate_rows
    (localTripleSourceCoordinate 0) (localTripleSourceCoordinate 1) (localTripleSourceCoordinate 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨gaussianImage localTripleTransport⁻¹ Q,
    (isQuartet_gaussianImage _ _).mpr hQ,?_,?_,?_⟩
  · have h := Set.mem_image_of_mem (fun c : MinimalCross => localTripleTransport⁻¹ • c)
      (hc (Or.inl rfl))
    change localTripleTransport⁻¹ • localReferenceCross∈gaussianImage localTripleTransport⁻¹ Q at h
    rw [←localTripleTransport_first_cross,inv_smul_smul] at h
    exact h
  · have h := Set.mem_image_of_mem (fun c : MinimalCross => localTripleTransport⁻¹ • c)
      (hc (Or.inr rfl))
    change localTripleTransport⁻¹ • referenceSecondCross∈gaussianImage localTripleTransport⁻¹ Q at h
    rw [←localTripleTransport_second_cross,inv_smul_smul] at h
    exact h
  · have h := Set.mem_image_of_mem (fun c : MinimalCross => localTripleTransport⁻¹ • c) hs
    change localTripleTransport⁻¹ • shiftedSeedCross∈gaussianImage localTripleTransport⁻¹ Q at h
    rw [←localTripleTransport_third_cross,inv_smul_smul] at h
    exact h

end Atlas.Rudvalis
