import Atlas.LinearGroups.F4.ShortWeylData

noncomputable section
namespace Atlas.F4

section Scalars
variable {R S : Type*} [CommRing R] [CommRing S]

theorem shortWeyl_map_smul (φ : R →+* S) (t : R) (x : Atlas.Albert.Carrier R) :
    Atlas.Albert.map φ (t • x) = φ t • Atlas.Albert.map φ x := by
  apply Prod.ext
  · funext i; exact φ.map_mul _ _
  · funext i j; exact φ.map_mul _ _

theorem shortWeylApply_map (φ : R →+* S) (i : Fin 8) (x : Atlas.Albert.Carrier R) :
    shortWeylApply i (Atlas.Albert.map φ x) = Atlas.Albert.map φ (shortWeylApply i x) := by
  simp only [shortWeylApply, ← Atlas.Albert.shortRootLinear_map, map_one]

theorem shortWeylApply_basis (i : Fin 8) (j : Fin 27) :
    shortWeylApply i (Atlas.Albert.basisVector (albertCoordinateOfFin j) : Atlas.Albert.Carrier R) =
      (shortWeylSign i j : R) • Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i j)) := by
  have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (shortWeyl_integral_basis i j)
  rw [← shortWeylApply_map, Atlas.Albert.map_basisVector, shortWeyl_map_smul,
    Atlas.Albert.map_basisVector] at h
  exact h

end Scalars

variable {F : Type*} [Field F]

/-- Opposite Wilson parameters have the same sign in this Weyl word. -/
def shortWeylFirstPair (i : Fin 8) : Model F :=
  shortRootFirstPair i 1 * shortRootFirstPair (7-i) 1 * shortRootFirstPair i 1

theorem shortWeylFirstPair_apply (i : Fin 8) (x : Atlas.Albert.Carrier F) :
    (shortWeylFirstPair i).val x = shortWeylApply i x := rfl

theorem shortWeylFirstPair_basis (i : Fin 8) (j : Fin 27) :
    (shortWeylFirstPair (F := F) i).val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) =
      (shortWeylSign i j : F) • Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i j)) :=
  shortWeylApply_basis i j

theorem shortWeylFirstPair_opposite (i : Fin 8) :
    shortWeylFirstPair (F := F) (7-i) = shortWeylFirstPair i := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.Albert.linearMap_ext_basis
  intro c
  obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
  change albertCoordinateOfFin j = c at hj
  rw [← hj]
  change (shortWeylFirstPair (7-i)).val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) =
    (shortWeylFirstPair i).val (Atlas.Albert.basisVector (albertCoordinateOfFin j))
  rw [shortWeylFirstPair_basis, shortWeylFirstPair_basis]
  have hd : ∀ i : Fin 8, shortWeylAxis (7-i) = shortWeylAxis i := by decide +kernel
  simp only [shortWeylSign, shortWeylDestination, hd]

set_option maxHeartbeats 400000 in
theorem shortWeyl_pow_four_of_basis (g : Model F) (i : Fin 8)
    (hg : ∀ j : Fin 27, g.val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) =
      (shortWeylSign i j : F) • Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i j))) : g ^ 4 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.Albert.linearMap_ext_basis
  intro c
  obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
  change albertCoordinateOfFin j = c at hj
  rw [← hj]
  change g.val (g.val
    (g.val (g.val
      (Atlas.Albert.basisVector (albertCoordinateOfFin j))))) =
        Atlas.Albert.basisVector (albertCoordinateOfFin j)
  simp only [hg, map_smul, smul_smul,
    shortWeylDestination_involutive i j,
    shortWeylDestination_involutive i (shortWeylDestination i j)]
  have hs : (shortWeylSign i j : F) * (shortWeylSign i (shortWeylDestination i j) : F) *
      (shortWeylSign i j : F) * (shortWeylSign i (shortWeylDestination i j) : F) = 1 := by
    have hz : ∀ (i : Fin 8) (j : Fin 27), shortWeylSign i j *
        shortWeylSign i (shortWeylDestination i j) * shortWeylSign i j *
        shortWeylSign i (shortWeylDestination i j) = 1 := by decide +kernel
    have hc := congrArg (fun n : ℤ => (n : F)) (hz i j)
    simpa only [Int.cast_mul, Int.cast_one] using hc
  rw [hs, one_smul]

theorem shortWeylFirstPair_pow_four (i : Fin 8) : (shortWeylFirstPair (F := F) i)^4 = 1 :=
  shortWeyl_pow_four_of_basis _ i (shortWeylFirstPair_basis i)

end Atlas.F4
