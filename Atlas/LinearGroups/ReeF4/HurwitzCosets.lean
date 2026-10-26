import Atlas.LinearGroups.ReeF4.HurwitzRoots

/-! Identification of the three root blocks with Q8, omega Q8 and omega-bar Q8.
The division by two below takes place only in integer root-label arithmetic. -/
namespace Atlas.ReeF4

def hurwitzLeftOmega (x : ScaledHurwitz) : ScaledHurwitz :=
  ![(-x 0-x 1-x 2-x 3)/2, (x 0-x 1-x 2+x 3)/2,
    (x 0+x 1-x 2-x 3)/2, (x 0-x 1+x 2-x 3)/2]

def hurwitzLeftOmegaBar (x : ScaledHurwitz) : ScaledHurwitz :=
  ![(-x 0+x 1+x 2+x 3)/2, (-x 0-x 1+x 2-x 3)/2,
    (-x 0-x 1-x 2+x 3)/2, (-x 0+x 1-x 2-x 3)/2]

theorem omega_division_exact : ∀ r : ShortRootLabel,
    let x := scaledShortRoot r
    2 • hurwitzLeftOmega x =
      ![-x 0-x 1-x 2-x 3, x 0-x 1-x 2+x 3,
        x 0+x 1-x 2-x 3, x 0-x 1+x 2-x 3] := by decide

theorem omegaBar_division_exact : ∀ r : ShortRootLabel,
    let x := scaledShortRoot r
    2 • hurwitzLeftOmegaBar x =
      ![-x 0+x 1+x 2+x 3, -x 0-x 1+x 2-x 3,
        -x 0-x 1-x 2+x 3, -x 0+x 1-x 2-x 3] := by decide

theorem firstBlock_omegaCoset : ∀ j : Fin 8, ∃ k : Fin 8,
    scaledShortRoot (1,j) = hurwitzLeftOmega (scaledShortRoot (0,k)) := by decide

theorem secondBlock_omegaBarCoset : ∀ j : Fin 8, ∃ k : Fin 8,
    scaledShortRoot (2,j) = hurwitzLeftOmegaBar (scaledShortRoot (0,k)) := by decide

theorem omegaCoset_firstBlock : ∀ k : Fin 8, ∃ j : Fin 8,
    hurwitzLeftOmega (scaledShortRoot (0,k)) = scaledShortRoot (1,j) := by decide

theorem omegaBarCoset_secondBlock : ∀ k : Fin 8, ∃ j : Fin 8,
    hurwitzLeftOmegaBar (scaledShortRoot (0,k)) = scaledShortRoot (2,j) := by decide

end Atlas.ReeF4
