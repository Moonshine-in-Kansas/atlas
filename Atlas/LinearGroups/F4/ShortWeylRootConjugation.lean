import Atlas.LinearGroups.F4.ShortWeylRootTables

noncomputable section
namespace Atlas.F4
variable {R : Type*} [CommRing R]

def shortWeylLinear (i : Fin 8) : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R :=
  (Atlas.Albert.shortRootLinear i 1).comp ((Atlas.Albert.shortRootLinear (7-i) 1).comp
    (Atlas.Albert.shortRootLinear i 1))

theorem shortWeylLinear_basis (i : Fin 8) (j : Fin 27) :
    shortWeylLinear i (Atlas.Albert.basisVector (albertCoordinateOfFin j) : Atlas.Albert.Carrier R) =
      (shortWeylSign i j : R) • Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i j)) := shortWeylApply_basis i j

theorem shortWeylLinear_map {S : Type*} [CommRing S] (φ : R →+* S)
    (i : Fin 8) (x : Atlas.Albert.Carrier R) :
    shortWeylLinear i (Atlas.Albert.map φ x) = Atlas.Albert.map φ (shortWeylLinear i x) :=
  shortWeylApply_map φ i x

theorem shortWeylLinear_L_column (i : Fin 8) (r : Fin 24) (j : Fin 27) :
    shortWeylLinear i (shortRootLinearColumn r j) = shortWeylLColumn i r j := by
  unfold shortRootLinearColumn shortWeylLColumn
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · rw [map_smul, shortWeylLinear_basis, smul_smul] <;> rfl
  · exact map_zero _

theorem shortWeylLinear_Q_column (i : Fin 8) (r : Fin 24) (j : Fin 27) :
    shortWeylLinear i (shortRootQuadraticColumn r j) = shortWeylQColumn i r j := by
  unfold shortRootQuadraticColumn shortWeylQColumn
  split_ifs
  · rw [map_smul, shortWeylLinear_basis, smul_smul] <;> rfl
  · exact map_zero _

theorem shortWeyl_L_integral_basis (i : Fin 8) (r : Fin 24) (j : Fin 27) :
    shortWeylLinear i (shortRootL r (Atlas.Albert.basisVector (albertCoordinateOfFin j) :
      Atlas.Albert.Carrier ℤ)) = shortWeylRootSign i r • shortRootL (shortWeylRootDestination i r)
        (shortWeylLinear i (Atlas.Albert.basisVector (albertCoordinateOfFin j))) := by
  rw [shortRootL_integral_column, shortWeylLinear_L_column, shortWeyl_L_column_identity,
    shortWeylLinear_basis, map_smul, shortRootL_integral_column, smul_smul] <;> rfl

theorem shortWeyl_Q_integral_basis (i : Fin 8) (r : Fin 24) (j : Fin 27) :
    shortWeylLinear i (shortRootQ r (Atlas.Albert.basisVector (albertCoordinateOfFin j) :
      Atlas.Albert.Carrier ℤ)) = shortRootQ (shortWeylRootDestination i r)
        (shortWeylLinear i (Atlas.Albert.basisVector (albertCoordinateOfFin j))) := by
  rw [shortRootQ_integral_column, shortWeylLinear_Q_column, shortWeyl_Q_column_identity,
    shortWeylLinear_basis, map_smul, shortRootQ_integral_column] <;> rfl

theorem shortWeyl_L_commute (i : Fin 8) (r : Fin 24) (x : Atlas.Albert.Carrier R) :
    shortWeylLinear i (shortRootL r x) = (shortWeylRootSign i r : R) •
      shortRootL (shortWeylRootDestination i r) (shortWeylLinear i x) := by
  have he : (shortWeylLinear (R := R) i).comp (shortRootL r) =
      (shortWeylRootSign i r : R) • (shortRootL (shortWeylRootDestination i r)).comp
        (shortWeylLinear i) := by
    apply Atlas.Albert.linearMap_ext_basis
    intro c
    obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
    change albertCoordinateOfFin j = c at hj
    rw [← hj]
    have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (shortWeyl_L_integral_basis i r j)
    rw [← shortWeylLinear_map, ← shortRootL_map, Atlas.Albert.map_basisVector,
      shortWeyl_map_smul, ← shortRootL_map, ← shortWeylLinear_map,
      Atlas.Albert.map_basisVector] at h
    exact h
  exact congrArg (fun f : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R => f x) he

theorem shortWeyl_Q_commute (i : Fin 8) (r : Fin 24) (x : Atlas.Albert.Carrier R) :
    shortWeylLinear i (shortRootQ r x) =
      shortRootQ (shortWeylRootDestination i r) (shortWeylLinear i x) := by
  have he : (shortWeylLinear (R := R) i).comp (shortRootQ r) =
      (shortRootQ (shortWeylRootDestination i r)).comp (shortWeylLinear i) := by
    apply Atlas.Albert.linearMap_ext_basis
    intro c
    obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
    change albertCoordinateOfFin j = c at hj
    rw [← hj]
    have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (shortWeyl_Q_integral_basis i r j)
    rw [← shortWeylLinear_map, ← shortRootQ_map, Atlas.Albert.map_basisVector,
      ← shortRootQ_map, ← shortWeylLinear_map, Atlas.Albert.map_basisVector] at h
    exact h
  exact congrArg (fun f : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R => f x) he

variable {F : Type*} [Field F]

theorem shortWeyl_shortRoot_intertwine (i : Fin 8) (r : Fin 24) (t : F) :
    shortWeylFirstPair i * shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t =
      shortRoot (shortRootPosition (shortWeylRootDestination i r)).1
        (shortRootPosition (shortWeylRootDestination i r)).2 ((shortWeylRootSign i r : F) * t) *
          shortWeylFirstPair i := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change shortWeylLinear i ((shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t).val x) =
    (shortRoot (shortRootPosition (shortWeylRootDestination i r)).1
      (shortRootPosition (shortWeylRootDestination i r)).2 ((shortWeylRootSign i r : F) * t)).val
        (shortWeylLinear i x)
  rw [shortRoot_polynomial_all, shortRoot_polynomial_all, map_add, map_add, map_smul,
    map_smul, shortWeyl_L_commute, shortWeyl_Q_commute, smul_smul, mul_pow]
  have hs : (shortWeylRootSign i r : F)^2 = 1 := by
    have hc := congrArg (fun n : ℤ => (n : F)) (shortWeylRootSign_sq i r)
    simpa only [Int.cast_pow, Int.cast_one] using hc
  rw [hs, one_mul, mul_comm t (shortWeylRootSign i r : F)]

theorem shortWeyl_shortRoot_conjugate (i : Fin 8) (r : Fin 24) (t : F) :
    shortWeylFirstPair i * shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t *
      (shortWeylFirstPair i)⁻¹ =
      shortRoot (shortRootPosition (shortWeylRootDestination i r)).1
        (shortRootPosition (shortWeylRootDestination i r)).2 ((shortWeylRootSign i r : F) * t) := by
  rw [shortWeyl_shortRoot_intertwine]
  simp [mul_assoc]

end Atlas.F4
