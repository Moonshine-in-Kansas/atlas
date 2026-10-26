import Atlas.LinearGroups.ReeF4.HurwitzRoots

/-! Wilson R1 §4's two-parameter diagonal weights. This is a table of integer
characters, independent of any finite-field identity. The exponent t is
2^(m+1), the existing theta convention; its square identity is only available
later under the finite-field cardinality hypothesis. Diagonal labels are fixed.
The printed positive label w₁″ has weight α^(2−t) β^(1−t). -/
namespace Atlas.ReeF4

/-- The powers of the two nonzero torus parameters on the 24 marked roots. -/
def torusWeightExponents (m : ℕ) (r : ShortRootLabel) : ℤ × ℤ :=
  let t : ℤ := (2 ^ (m + 1) : ℕ)
  (![![(1,0), (t-1,0), (-1,t), (1-t,2-t),
        (t-1,t-2), (1,-t), (1-t,0), (-1,0)],
     ![(t-1,t-1), (1,1-t), (1-t,1), (1,-1),
        (-1,1), (t-1,-1), (-1,t-1), (1-t,1-t)],
     ![(0,1), (t,-1), (0,t-1), (t-2,t-1),
        (2-t,1-t), (0,1-t), (-t,1), (0,-1)]]) r.1 r.2

theorem torusWeightExponents_opposite (m : ℕ) (r : ShortRootLabel) :
    torusWeightExponents m (r.1, Fin.rev r.2) = -torusWeightExponents m r := by
  rcases r with ⟨b,j⟩
  fin_cases b <;> fin_cases j <;> ext <;>
    simp [torusWeightExponents, Fin.rev] <;> ring

variable {G : Type*} [CommGroup G]

def torusWeight (m : ℕ) (a b : G) (r : ShortRootLabel) : G :=
  a ^ (torusWeightExponents m r).1 * b ^ (torusWeightExponents m r).2

@[simp] theorem torusWeight_one (m : ℕ) (r : ShortRootLabel) :
    torusWeight m (1 : G) 1 r = 1 := by simp [torusWeight]

theorem torusWeight_mul (m : ℕ) (a b c d : G) (r : ShortRootLabel) :
    torusWeight m (a*c) (b*d) r = torusWeight m a b r * torusWeight m c d r := by
  simp only [torusWeight, mul_zpow]
  ac_rfl

theorem torusWeight_opposite (m : ℕ) (a b : G) (r : ShortRootLabel) :
    torusWeight m a b (r.1, Fin.rev r.2) = (torusWeight m a b r)⁻¹ := by
  simp [torusWeight, torusWeightExponents_opposite, mul_comm]

@[simp] theorem torusWeight_parameter_left (m : ℕ) (a b : G) :
    torusWeight m a b (0,0) = a := by simp [torusWeight, torusWeightExponents]

@[simp] theorem torusWeight_parameter_right (m : ℕ) (a b : G) :
    torusWeight m a b (2,0) = b := by simp [torusWeight, torusWeightExponents]

def torusWeightHom (m : ℕ) : G × G →* (ShortRootLabel → G) where
  toFun p := torusWeight m p.1 p.2
  map_one' := by funext r; exact torusWeight_one m r
  map_mul' p q := by funext r; exact torusWeight_mul m p.1 p.2 q.1 q.2 r

theorem torusWeightHom_injective (m : ℕ) :
    Function.Injective (torusWeightHom (G := G) m) := by
  intro p q h
  apply Prod.ext
  · have h0 := congrFun h (0,0)
    change torusWeight m p.1 p.2 (0,0) = torusWeight m q.1 q.2 (0,0) at h0
    simpa using h0
  · have h0 := congrFun h (2,0)
    change torusWeight m p.1 p.2 (2,0) = torusWeight m q.1 q.2 (2,0) at h0
    simpa using h0

end Atlas.ReeF4
