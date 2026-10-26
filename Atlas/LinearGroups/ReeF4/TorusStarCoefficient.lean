import Atlas.LinearGroups.ReeF4.TorusFieldWeights
import Atlas.LinearGroups.ReeF4.TorusScalar
import Atlas.LinearGroups.ReeF4.PartialStabilizer

/-! Exact source-torus compatibility for every coefficient of the candidate
exterior extension, using the actual inverse-Tits field automorphism. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def markedTorusWeight (m : ℕ) (a b : Fˣ) : TraceZeroCoordinate → F
  | .inl _ => 1
  | .inr r => (torusWeight (G := Fˣ) m a b r : F)

theorem torusEquiv_marked (m : ℕ) (a b : Fˣ) (i : TraceZeroCoordinate) :
    torusEquiv m a b (markedBasis i) = markedTorusWeight m a b i • markedBasis i := by
  cases i with
  | inl i => simp [markedBasis_diagonal, markedTorusWeight]
  | inr r => simp [markedBasis_root, markedTorusWeight]

theorem torusEquiv_oppositeValue (m : ℕ) (a b : Fˣ) (r : ShortRootLabel) :
    torusEquiv m a b (oppositeLabelValue r) = oppositeLabelValue r := by
  unfold oppositeLabelValue
  split_ifs <;> simp

theorem torusStarCoefficient {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a b : Fˣ) (i j : TraceZeroCoordinate) :
    thetaInv F m (markedTorusWeight m a b i * markedTorusWeight m a b j) •
      extensionCoefficient i j = torusEquiv m a b (extensionCoefficient i j) := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [markedTorusWeight, one_mul, map_one, one_smul, extensionCoefficient]
      split_ifs <;> simp
    | inr s => simp [extensionCoefficient]
  | inr r =>
    cases j with
    | inl j => simp [extensionCoefficient]
    | inr s =>
      by_cases ho : s = (r.1, Fin.rev r.2)
      · subst s
        have hw : (torusWeight (G := Fˣ) m a b r : F) *
            (torusWeight (G := Fˣ) m a b (r.1,Fin.rev r.2) : F) = 1 := by
          rw [torusWeight_opposite m a b r]
          simp
        simp only [extensionCoefficient, if_pos rfl, markedTorusWeight, hw,
          map_one, one_smul]
        exact (torusEquiv_oppositeValue m a b r).symm
      · by_cases hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0
        · simp only [extensionCoefficient, if_neg ho, if_pos hp, markedTorusWeight]
          rw [torusWeight_star_thetaInv hcard a b r s hp, torusEquiv_root]
        · simp [extensionCoefficient, ho, hp]

end Atlas.ReeF4
