import Atlas.LinearGroups.F4.TorusLongRootMaps

noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

private theorem coordinateEquiv_basis (c d : Atlas.Albert.Coordinate) :
    Atlas.Albert.coordinateEquiv (Atlas.Albert.basisVector c : Atlas.Albert.Carrier F) d =
      (Pi.single c (1 : F) : Atlas.Albert.Coordinate → F) d := by
  cases d <;> rfl

private theorem coordinateEquiv_basis_fin (j l : Fin 27) :
    Atlas.Albert.coordinateEquiv (Atlas.Albert.basisVector (albertCoordinateOfFin j) :
      Atlas.Albert.Carrier F) (albertCoordinateOfFin l) = if l=j then 1 else 0 := by
  have hi : Function.Injective albertCoordinateOfFin := albertCoordinateFinEquiv.symm.injective
  simp only [coordinateEquiv_basis,Pi.single_apply,hi.eq_iff]

theorem longRoot_torusLongApply (k : Fin 4) (t : F) (x : Atlas.Albert.Carrier F) :
    (longRoot (torusLongLabel k) t).val x=torusLongApply k t x := by
  let w : Model F := longRootWordElement (longRootWitness (torusLongLabel k))
  have he : (longRoot (torusLongLabel k) t).val.toLinearMap.comp w.val.toLinearMap =
      (torusLongLinear k t).comp w.val.toLinearMap := by
    apply Atlas.Albert.linearMap_ext_basis
    intro c
    obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
    change albertCoordinateOfFin j=c at hj
    rw [←hj]
    change (longRoot (torusLongLabel k) t).val
      (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
        torusLongApply k t
          (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)))
    have h1 : torusLongApply k (1 : F)
        (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
          w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) +
            torusLongSeedColumn k j := by
      dsimp only [w]
      rw [longRootWordElement_basis]
      exact torusLong_columns k j
    have h2 : (longRoot (torusLongLabel k) t).val
        (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
          w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) +
            t • torusLongSeedColumn k j := by
      dsimp only [w]
      rw [longRoot_conjugated_apply]
      apply congrArg (fun v : Atlas.Albert.Carrier F =>
        w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) + t • v)
      unfold torusLongSeedColumn
      apply Finset.sum_congr rfl
      intro l _
      rw [coordinateEquiv_basis_fin]
      split_ifs <;> simp [smul_smul]
    rw [h2,torusLongApply_parameter,h1]
    simp only [add_sub_cancel_left]
  obtain ⟨y,rfl⟩ := w.val.surjective x
  exact congrArg (fun f : Atlas.Albert.Carrier F →ₗ[F] Atlas.Albert.Carrier F => f y) he

end Atlas.F4
