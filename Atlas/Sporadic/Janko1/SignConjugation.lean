import Atlas.Sporadic.Janko1.SignGroup

/-!
Source-only continuation of the preserved sign-conjugation draft.

The public declarations and the actual octonion/sign models are unchanged.
The two finite matrix products are reduced to scalar entry identities before
decision, avoiding repeated eight-term matrix sums. No generated-group search
is used. This candidate has not been elaborated or kernel-checked.
-/
namespace Atlas.Janko1

theorem coordinateRepresentation_signElement (a : SignParameters) :
    coordinateRepresentation (signElement a) = Matrix.diagonal (signFactor a) := by
  have hc : wilsonEquiv.symm.conjRingEquiv (signLinear a) = signCoordinates a :=
    LinearEquiv.conj_symm_conj wilsonEquiv (signCoordinates a)
  change LinearMap.toMatrix' (wilsonEquiv.symm.conjRingEquiv (signLinear a)) = _
  rw [hc]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply]
  funext i
  exact (Matrix.mulVec_diagonal (signFactor a) x i).symm

def signShift (a : SignParameters) : SignParameters := ![a 2, a 0, a 1 + a 2]
def signDouble (a : SignParameters) : SignParameters := ![a 0+a 2, a 2, a 1+a 2]

set_option maxRecDepth 8192 in
private theorem signShift_entry : ∀ (a : SignParameters) (i j : Fin 8),
    generatorMatrix 0 i j * signFactor a j =
      signFactor (signShift a) i * generatorMatrix 0 i j := by decide

set_option maxRecDepth 8192 in
private theorem signDouble_entry : ∀ (a : SignParameters) (i j : Fin 8),
    generatorMatrix 1 i j * signFactor a j =
      signFactor (signDouble a) i * generatorMatrix 1 i j := by decide

private theorem signShift_matrix : ∀ a : SignParameters,
    generatorMatrix 0 * Matrix.diagonal (signFactor a) =
      Matrix.diagonal (signFactor (signShift a)) * generatorMatrix 0 := by
  intro a
  ext i j
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using signShift_entry a i j

private theorem signDouble_matrix : ∀ a : SignParameters,
    generatorMatrix 1 * Matrix.diagonal (signFactor a) =
      Matrix.diagonal (signFactor (signDouble a)) * generatorMatrix 1 := by
  intro a
  ext i j
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using signDouble_entry a i j

theorem P_signElement (a : SignParameters) :
    P * signElement a = signElement (signShift a) * P := by
  apply coordinateRepresentation_injective
  simp only [map_mul, coordinateRepresentation_P, coordinateRepresentation_signElement]
  exact signShift_matrix a

theorem Q_signElement (a : SignParameters) :
    Q * signElement a = signElement (signDouble a) * Q := by
  apply coordinateRepresentation_injective
  simp only [map_mul, coordinateRepresentation_Q, coordinateRepresentation_signElement]
  exact signDouble_matrix a

theorem P_conjugates_sign (a : SignParameters) :
    P * signElement a * P⁻¹ = signElement (signShift a) := by
  rw [P_signElement, mul_assoc, mul_inv_cancel, mul_one]

theorem Q_conjugates_sign (a : SignParameters) :
    Q * signElement a * Q⁻¹ = signElement (signDouble a) := by
  rw [Q_signElement, mul_assoc, mul_inv_cancel, mul_one]

theorem signElement_basis_zero : signElement ![1,0,0] = R := by
  apply coordinateRepresentation_injective
  rw [coordinateRepresentation_signElement, coordinateRepresentation_R]
  decide

end Atlas.Janko1
