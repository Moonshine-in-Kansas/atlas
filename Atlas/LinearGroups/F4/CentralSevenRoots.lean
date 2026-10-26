import Atlas.LinearGroups.F4.CentralSevenCoefficients

/-! Identification of the seven independent translations with the constructed roots. -/
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

theorem centralSeven_single_long (k : Fin 6) (t : F) :
    (longRoot (centralSevenLongLabel k) t).val =
      centralSevenEquiv (Pi.single k.castSucc t) := by
  let w : Model F := longRootWordElement (longRootWitness (centralSevenLongLabel k))
  have he : (longRoot (centralSevenLongLabel k) t).val.toLinearMap.comp w.val.toLinearMap =
      (centralSevenEquiv (Pi.single k.castSucc t)).toLinearMap.comp w.val.toLinearMap := by
    apply Atlas.Albert.linearMap_ext_basis
    intro c
    obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
    change albertCoordinateOfFin j=c at hj
    rw [←hj]
    change (longRoot (centralSevenLongLabel k) t).val
      (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
        centralSevenApply (Pi.single k.castSucc t)
          (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)))
    have h1 : centralSevenApply (Pi.single k.castSucc (1 : F))
        (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
          w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) +
            centralSevenSeedLinearColumn k j := by
      dsimp only [w]
      rw [longRootWordElement_basis]
      exact centralSeven_coefficients k j
    have h2 : (longRoot (centralSevenLongLabel k) t).val
        (w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
          w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) +
            t • centralSevenSeedLinearColumn k j := by
      dsimp only [w]
      rw [longRoot_conjugated_apply]
      apply congrArg (fun v : Atlas.Albert.Carrier F =>
        w.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) + t • v)
      unfold centralSevenSeedLinearColumn
      apply Finset.sum_congr rfl
      intro l _
      rw [coordinateEquiv_basis_fin]
      split_ifs <;> simp [smul_smul]
    rw [h2,centralSevenApply_single_long,h1]
    simp only [add_sub_cancel_left]
  apply LinearEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := w.val.surjective x
  exact congrArg (fun f : Atlas.Albert.Carrier F →ₗ[F] Atlas.Albert.Carrier F => f y) he

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem centralSeven_single_short (t : F) :
    (shortRoot 0 0 t).val = centralSevenEquiv (Pi.single 6 t) := by
  apply LinearEquiv.ext
  intro x
  change Atlas.Albert.shortRootLinear 0 t x=centralSevenApply (Pi.single 6 t) x
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Atlas.SplitOctonion.conjugate,
        Atlas.SplitOctonion.trace,Atlas.SplitOctonion.mul,Atlas.SplitOctonion.unit,
        centralSevenApply,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Atlas.SplitOctonion.conjugate,
        Atlas.SplitOctonion.trace,Atlas.SplitOctonion.mul,Atlas.SplitOctonion.unit,
        centralSevenApply,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring

end Atlas.F4
