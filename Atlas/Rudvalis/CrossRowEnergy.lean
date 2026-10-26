import Atlas.Rudvalis.CoordinateRowProjection

namespace Atlas.Rudvalis
open Classical

theorem coordinateRowEnergy_I (s : Set Point) (v : RationalSpace) :
    coordinateRowEnergy s (rationalI v)=coordinateRowEnergy s v := by
  unfold coordinateRowEnergy
  rw [coordinateRowProjection_gaussian,rationalI_pairing]

theorem coordinateRowEnergy_I_pow (s : Set Point) (n : ℕ) (v : RationalSpace) :
    coordinateRowEnergy s (rationalMonomialHom (codeI.val^n) v)=coordinateRowEnergy s v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',map_mul]
    change coordinateRowEnergy s (rationalI (rationalMonomialHom (codeI.val^n) v))=_
    rw [coordinateRowEnergy_I,ih]

theorem coordinateRowEnergy_units (s : Set Point) (u : GaussianUnits) (v : MinimalShell) :
    coordinateRowEnergy s (u • v).val.val=coordinateRowEnergy s v.val.val := by
  classical
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp u.prop)
  change coordinateRowEnergy s (rationalMonomialHom u.val.val v.val.val)=_
  rw [←he]
  exact coordinateRowEnergy_I_pow s n v.val.val

/-- Squared length of the projection of a minimal cross to selected coordinate rows.
It is independent of its four Gaussian-unit representatives. -/
noncomputable def crossRowEnergy (s : Set Point) : MinimalCross→ℚ :=
  Quotient.lift (fun v : MinimalShell => coordinateRowEnergy s v.val.val) (by
    intro v w h
    obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp h
    rw [←hu]
    exact coordinateRowEnergy_units s u w)

theorem crossRowEnergy_mk (s : Set Point) (v : MinimalShell) :
    crossRowEnergy s (minimalCross v)=coordinateRowEnergy s v.val.val := rfl

theorem crossRowEnergy_complement (s : Set Point) (c : MinimalCross) :
    crossRowEnergy s c+crossRowEnergy sᶜ c=4 := by
  induction c using Quotient.inductionOn with
  | h v =>
    change coordinateRowEnergy s v.val.val+coordinateRowEnergy sᶜ v.val.val=4
    rw [coordinateRowEnergy_complement]
    exact v.prop

theorem coordinateRowProjection_coordinateMinimum (s : Set Point) (i : Coordinate) :
    coordinateRowProjection s (coordinateMinimum i)=
      if i.1∈s then coordinateMinimum i else 0 := by
  classical
  ext j
  by_cases hji : j=i
  · subst j
    simp only [coordinateRowProjection_apply]
    split_ifs <;> rfl
  · by_cases hi : i.1∈s <;> simp [coordinateRowProjection_apply,coordinateMinimum,hi,hji]

theorem crossRowEnergy_coordinateCross (s : Set Point) (i : Coordinate) :
    crossRowEnergy s (coordinateCross i)=if i.1∈s then 4 else 0 := by
  classical
  change coordinateRowEnergy s (coordinateMinimum i)=_
  unfold coordinateRowEnergy
  rw [coordinateRowProjection_coordinateMinimum]
  split_ifs
  · exact coordinateMinimum_norm i
  · simp [rationalDot]

theorem crossRowEnergy_nonneg (s : Set Point) (c : MinimalCross) : 0≤crossRowEnergy s c := by
  induction c using Quotient.inductionOn with
  | h v => exact rationalDot_self_nonneg _

theorem crossRowEnergy_le_four (s : Set Point) (c : MinimalCross) : crossRowEnergy s c≤4 := by
  have h := crossRowEnergy_complement s c
  have hn := crossRowEnergy_nonneg sᶜ c
  linarith

end Atlas.Rudvalis

