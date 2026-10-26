import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinGamma
import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinSimpleOperators
import Atlas.LinearAlgebra.BooleanSpinGammaConjugation

/-! Explicit local action on the original odd quadratic coordinates.
These are conjugation identities for actual simple-root spin matrices, not a
constructed global spin-to-orthogonal homomorphism. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule Atlas.BooleanSpin

variable (r : ℕ) (R : Type*) [CommRing R]

/-- x_i ↦ x_i+t*x_j and y_j ↦ y_j-t*y_i; all other coordinates are fixed. -/
def longCoordinates (i j : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    Atlas.Orthogonal.VectorB r R :=
  v + (Pi.single (.inl i) (t*v.1 (.inl j)),0) -
    (Pi.single (.inr j) (t*v.1 (.inr i)),0)

/-- x_i ↦ x_i+2tz-t²y_i, z ↦ z-ty_i; other coordinates are fixed. -/
def shortUpperCoordinates (i : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    Atlas.Orthogonal.VectorB r R :=
  v + (Pi.single (.inl i) (2*t*v.2-t^2*v.1 (.inr i) : R),0) -
    (0,t*v.1 (.inr i))

/-- y_i ↦ y_i-2tz-t²x_i, z ↦ z+tx_i; other coordinates are fixed. -/
def shortLowerCoordinates (i : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    Atlas.Orthogonal.VectorB r R :=
  v - (Pi.single (.inr i) (2*t*v.2+t^2*v.1 (.inl i) : R),0) +
    (0,t*v.1 (.inl i))

theorem spinGamma_long (i j : Fin r) (hij : i ≠ j) (t : R)
    (v : Atlas.Orthogonal.VectorB r R) :
    (1+t • (creation R i*annihilation R j))*spinGamma r R v*
      (1-t • (creation R i*annihilation R j)) =
      spinGamma r R (longCoordinates r R i j t v) := by
  rw [longCoordinates, map_sub, map_add, spinGamma_e, spinGamma_f]
  exact long_gamma R i j hij t (fun k => v.1 (.inl k)) (fun k => v.1 (.inr k)) v.2

theorem spinGamma_shortUpper (i : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    (1+t • (creation R i*parity R))*spinGamma r R v*
      (1-t • (creation R i*parity R)) =
      spinGamma r R (shortUpperCoordinates r R i t v) := by
  rw [shortUpperCoordinates, map_sub, map_add, spinGamma_e, spinGamma_z]
  exact short_upper_gamma R i t (fun k => v.1 (.inl k)) (fun k => v.1 (.inr k)) v.2

theorem spinGamma_shortLower (i : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    (1+t • (parity R*annihilation R i))*spinGamma r R v*
      (1-t • (parity R*annihilation R i)) =
      spinGamma r R (shortLowerCoordinates r R i t v) := by
  rw [shortLowerCoordinates, map_add, map_sub, spinGamma_f, spinGamma_z]
  exact short_lower_gamma R i t (fun k => v.1 (.inl k)) (fun k => v.1 (.inr k)) v.2

private theorem end_apply_sub (N : Module.End R (Space (I := Fin r) R))
    (v w : Space (I := Fin r) R) : N (v-w) = N v-N w := N.map_sub v w

private theorem factor_neg (N : Module.End R (Space (I := Fin r) R)) (t : R) :
    (1 + (-t) • N) = 1-t • N := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul]
  ring

private theorem factor_sub_neg (N : Module.End R (Space (I := Fin r) R)) (t : R) :
    (1 - (-t) • N) = 1+t • N := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul]
  ring

private theorem unit_factors (N : Module.End R (Space (I := Fin r) R))
    (hN : N*N=0) (t : R) : (1+t • N)*(1-t • N)=1 := by
  apply LinearMap.ext
  intro v
  have hv : N (N v) = 0 := by
    change (N*N) v = 0
    rw [hN]
    rfl
  apply Finsupp.ext
  intro sigma
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, end_apply_sub r R,
    LinearMap.map_smul, hv, smul_zero, sub_zero, Finsupp.zero_apply, Finsupp.add_apply,
    Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- Compare scalar diagonal entries after a genuine invertible conjugation;
nondegeneracy of the polar form is not required. -/
theorem spinGamma_conjugation_form
    (S T : Module.End R (Space (I := Fin r) R)) (hST : S*T=1) (hTS : T*S=1)
    (v w : Atlas.Orthogonal.VectorB r R)
    (h : S*spinGamma r R v*T=spinGamma r R w) :
    Atlas.Orthogonal.formB r R w = Atlas.Orthogonal.formB r R v := by
  have hs : Atlas.Orthogonal.formB r R w • (1 : Module.End R (Space (I := Fin r) R)) =
      Atlas.Orthogonal.formB r R v • 1 := by
    calc
      _ = spinGamma r R w * spinGamma r R w := (spinGamma_square r R w).symm
      _ = (S*spinGamma r R v*T)*(S*spinGamma r R v*T) := by rw [h]
      _ = S*(spinGamma r R v*(T*S)*spinGamma r R v)*T := by noncomm_ring
      _ = S*(spinGamma r R v*spinGamma r R v)*T := by rw [hTS, mul_one]
      _ = _ := by rw [spinGamma_square, mul_smul_comm, mul_one,
        smul_mul_assoc, hST]
  have he := congrArg (fun f : Module.End R (Space (I := Fin r) R) =>
    f (Finsupp.single vacuum 1) vacuum) hs
  simpa using he

private theorem form_of_squareZero
    (N : Module.End R (Space (I := Fin r) R)) (hN : N*N=0)
    (t : R) (v w : Atlas.Orthogonal.VectorB r R)
    (h : (1+t • N)*spinGamma r R v*(1-t • N)=spinGamma r R w) :
    Atlas.Orthogonal.formB r R w = Atlas.Orthogonal.formB r R v := by
  apply spinGamma_conjugation_form r R _ _ (unit_factors r R N hN t) _ v w h
  simpa only [factor_neg r R, factor_sub_neg r R] using unit_factors r R N hN (-t)

theorem longCoordinates_form (i j : Fin r) (hij : i ≠ j) (t : R)
    (v : Atlas.Orthogonal.VectorB r R) :
    Atlas.Orthogonal.formB r R (longCoordinates r R i j t v) =
      Atlas.Orthogonal.formB r R v :=
  form_of_squareZero r R _ (long_square R i j hij) t v _ (spinGamma_long r R i j hij t v)

theorem shortUpperCoordinates_form (i : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    Atlas.Orthogonal.formB r R (shortUpperCoordinates r R i t v) =
      Atlas.Orthogonal.formB r R v :=
  form_of_squareZero r R _ (short_upper_square R i) t v _ (spinGamma_shortUpper r R i t v)

theorem shortLowerCoordinates_form (i : Fin r) (t : R) (v : Atlas.Orthogonal.VectorB r R) :
    Atlas.Orthogonal.formB r R (shortLowerCoordinates r R i t v) =
      Atlas.Orthogonal.formB r R v :=
  form_of_squareZero r R _ (short_lower_square R i) t v _ (spinGamma_shortLower r R i t v)

private theorem rootMatrix_operator (n : ℕ) (R : Type*) [CommRing R]
    (i : Fin (n+1)) (ε : ℤ) (N : Module.End R (Space (I := Fin (n+1)) R))
    (hN : spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n i) ε) = matrix R N) (t : R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (simpleB n i) ε t) = matrix R (1+t • N) := by
  simp only [Strings.rootMatrix, map_add, map_one, map_smul, hN]

/-- The actual positive long simple-root spin matrix conjugates gamma by the displayed coordinates. -/
theorem spin_X_simple_long_gamma (n : ℕ) (R : Type*) [CommRing R] (i : Fin n)
    (t : R) (v : Atlas.Orthogonal.VectorB (n+1) R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (simpleB n i.castSucc) (-1) t) * matrix R (spinGamma (n+1) R v) *
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n i.castSucc) (-1) (-t)) =
      matrix R (spinGamma (n+1) R (longCoordinates (n+1) R i.castSucc i.succ t v)) := by
  have hs : spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n i.castSucc) (-1)) = matrix R (creation R i.castSucc*annihilation R i.succ) := by
    rw [spin_raising_simple_long, map_mul]
  rw [rootMatrix_operator n R _ _ _ hs t, rootMatrix_operator n R _ _ _ hs (-t)]
  simpa only [map_mul, factor_neg] using congrArg (matrix R)
    (spinGamma_long (n+1) R i.castSucc i.succ (ne_of_lt i.castSucc_lt_succ) t v)

theorem spin_Y_simple_long_gamma (n : ℕ) (R : Type*) [CommRing R] (i : Fin n)
    (t : R) (v : Atlas.Orthogonal.VectorB (n+1) R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (simpleB n i.castSucc) 1 t) * matrix R (spinGamma (n+1) R v) *
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n i.castSucc) 1 (-t)) =
      matrix R (spinGamma (n+1) R (longCoordinates (n+1) R i.succ i.castSucc t v)) := by
  have hs : spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n i.castSucc) 1) = matrix R (creation R i.succ*annihilation R i.castSucc) := by
    rw [spin_lowering_simple_long, map_mul]
  rw [rootMatrix_operator n R _ _ _ hs t, rootMatrix_operator n R _ _ _ hs (-t)]
  simpa only [map_mul, factor_neg] using congrArg (matrix R)
    (spinGamma_long (n+1) R i.succ i.castSucc (Ne.symm (ne_of_lt i.castSucc_lt_succ)) t v)

theorem spin_X_simple_short_gamma (n : ℕ) (R : Type*) [CommRing R]
    (t : R) (v : Atlas.Orthogonal.VectorB (n+1) R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (simpleB n (Fin.last n)) (-1) t) * matrix R (spinGamma (n+1) R v) *
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n (Fin.last n)) (-1) (-t)) =
      matrix R (spinGamma (n+1) R (shortUpperCoordinates (n+1) R (Fin.last n) t v)) := by
  have hs : spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n (Fin.last n)) (-1)) = matrix R (creation R (Fin.last n)*parity R) := by
    rw [spin_raising_simple_last, map_mul]
  rw [rootMatrix_operator n R _ _ _ hs t, rootMatrix_operator n R _ _ _ hs (-t)]
  simpa only [map_mul, factor_neg] using congrArg (matrix R)
    (spinGamma_shortUpper (n+1) R (Fin.last n) t v)

theorem spin_Y_simple_short_gamma (n : ℕ) (R : Type*) [CommRing R]
    (t : R) (v : Atlas.Orthogonal.VectorB (n+1) R) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (simpleB n (Fin.last n)) 1 t) * matrix R (spinGamma (n+1) R v) *
      spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
        (simpleB n (Fin.last n)) 1 (-t)) =
      matrix R (spinGamma (n+1) R (shortLowerCoordinates (n+1) R (Fin.last n) t v)) := by
  have hs : spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (simpleB n (Fin.last n)) 1) = matrix R (parity R*annihilation R (Fin.last n)) := by
    rw [spin_lowering_simple_last, map_mul]
  rw [rootMatrix_operator n R _ _ _ hs t, rootMatrix_operator n R _ _ _ hs (-t)]
  simpa only [map_mul, factor_neg] using congrArg (matrix R)
    (spinGamma_shortLower (n+1) R (Fin.last n) t v)

end Atlas.Chevalley.Comparison.TypeB
