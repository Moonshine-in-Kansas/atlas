import Atlas.LinearGroups.Triality.InversionSubgroup

/-! The independent parameter count for each inversion-root subgroup. -/
noncomputable section
namespace Atlas.Triality
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def inversionCoordinates (w : Fin 12) :
    {p : PositiveParameters F K // InversionParameters F K w p} ≃
      AllowedCoordinate K (!rootSurvives w 0) × AllowedCoordinate F (!rootSurvives w 1) ×
      AllowedCoordinate K (!rootSurvives w 2) × AllowedCoordinate K (!rootSurvives w 3) ×
      AllowedCoordinate F (!rootSurvives w 4) × AllowedCoordinate F (!rootSurvives w 5) where
  toFun p := (⟨p.val.a,fun h => p.property.1 (by simpa using h)⟩,
    ⟨p.val.b,fun h => p.property.2.1 (by simpa using h)⟩,
    ⟨p.val.c,fun h => p.property.2.2.1 (by simpa using h)⟩,
    ⟨p.val.d,fun h => p.property.2.2.2.1 (by simpa using h)⟩,
    ⟨p.val.u,fun h => p.property.2.2.2.2.1 (by simpa using h)⟩,
    ⟨p.val.v,fun h => p.property.2.2.2.2.2 (by simpa using h)⟩)
  invFun p := ⟨⟨p.1.val,p.2.1.val,p.2.2.1.val,p.2.2.2.1.val,p.2.2.2.2.1.val,p.2.2.2.2.2.val⟩,
    ⟨fun h => p.1.property (by simpa using h),fun h => p.2.1.property (by simpa using h),
     fun h => p.2.2.1.property (by simpa using h),fun h => p.2.2.2.1.property (by simpa using h),
     fun h => p.2.2.2.2.1.property (by simpa using h),fun h => p.2.2.2.2.2.property (by simpa using h)⟩⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

theorem card_inversionParameters (hdeg : Module.finrank F K = 3) (w : Fin 12) :
    Nat.card {p : PositiveParameters F K // InversionParameters F K w p} =
      Nat.card F ^ weightedLength w := by
  rw [Nat.card_congr (inversionCoordinates F K w)]
  simp only [Nat.card_prod,card_allowedCoordinate]
  rw [FiniteCubic.card_extension hdeg,rootSurvives_table,weightedLength_table]
  fin_cases w
  · change 1 * (1 * (1 * (1 * (1 * (1))))) = Nat.card F^0
    ring
  · change Nat.card F^3 * (1 * (1 * (1 * (1 * (1))))) = Nat.card F^3
    ring
  · change 1 * (Nat.card F * (1 * (1 * (1 * (1))))) = Nat.card F^1
    ring
  · change Nat.card F^3 * (1 * (1 * (1 * (Nat.card F * (1))))) = Nat.card F^4
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (1 * (1 * (1))))) = Nat.card F^4
    ring
  · change Nat.card F^3 * (1 * (1 * (Nat.card F^3 * (Nat.card F * (1))))) = Nat.card F^7
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (1 * (1 * (Nat.card F))))) = Nat.card F^5
    ring
  · change Nat.card F^3 * (1 * (1 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^8
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (Nat.card F^3 * (1 * (Nat.card F))))) = Nat.card F^8
    ring
  · change Nat.card F^3 * (1 * (Nat.card F^3 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^11
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^9
    ring
  · change Nat.card F^3 * (Nat.card F * (Nat.card F^3 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^12
    ring

end Atlas.Triality
