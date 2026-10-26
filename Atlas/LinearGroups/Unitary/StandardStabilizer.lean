import Atlas.LinearGroups.Unitary.StandardComplement
import Atlas.LinearGroups.Unitary.VectorAction

/-! The full norm-one vector stabilizer, by actual block restriction and extension. -/
noncomputable section
namespace Atlas.Unitary
open Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The actual stabilizer of the first coordinate unit vector. -/
abbrev firstStabilizer (hdeg : Module.finrank F K = 2) :=
  MulAction.stabilizer (U F K (n + 1) hdeg) (coordinateUnit (F := F) (K := K) (0 : Fin (n+1)))

private theorem hermitian_cons (a b : K) (x y : Fin n → K) :
    hermitian F K (Fin.cons a x) (Fin.cons b y) =
      a * Atlas.FiniteQuadratic.conjugation F K b + hermitian F K x y := by
  simp [hermitian, Fin.sum_univ_succ]

/-- Extend a matrix by the identity on the first coordinate. -/
def extendMatrix (g : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => g i' j') j) i

omit [Finite K] in
@[simp] theorem extendMatrix_mulVec (g : Matrix (Fin n) (Fin n) K)
    (x : Fin (n+1) → K) : extendMatrix g *ᵥ x = Fin.cons (x 0) (g *ᵥ Fin.tail x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [mulVec, dotProduct, extendMatrix, Fin.sum_univ_succ, Fin.tail]

/-- Actual unitary block extension into the norm-one vector stabilizer. -/
def extendUnitary (hdeg : Module.finrank F K = 2) (g : U F K n hdeg) :
    firstStabilizer (n := n) hdeg := by
  have hmem : (letI := conjugationStarRing F K hdeg
      extendMatrix g.val ∈ Matrix.unitaryGroup (Fin (n+1)) K) := by
    apply (mem_u_iff_preserves_hermitian hdeg _).mpr
    intro x y
    rw [extendMatrix_mulVec, extendMatrix_mulVec, hermitian_cons,
      u_preserves_hermitian hdeg]
    conv_rhs => rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y]
    exact (hermitian_cons _ _ _ _).symm
  refine ⟨⟨extendMatrix g.val, hmem⟩, ?_⟩
  change _ • coordinateUnit (F := F) (K := K) (0 : Fin (n+1)) = _
  apply Subtype.ext
  change extendMatrix g.val *ᵥ Pi.single 0 1 = Pi.single 0 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [extendMatrix, mulVec, dotProduct, Pi.single_apply]

private theorem firstStabilizer_fixes (hdeg : Module.finrank F K = 2)
    (g : firstStabilizer (n := n) hdeg) :
    g.val.val *ᵥ firstVector K n = firstVector K n :=
  congrArg Subtype.val (show g.val • coordinateUnit (F := F) (K := K) (0 : Fin (n+1)) = _ from g.property)

private theorem firstStabilizer_first_coord (hdeg : Module.finrank F K = 2)
    (g : firstStabilizer (n := n) hdeg) (x : Fin (n+1) → K) :
    (g.val.val *ᵥ x) 0 = x 0 := by
  rw [← hermitian_firstVector F K (g.val.val *ᵥ x), ← firstStabilizer_fixes hdeg g,
    u_preserves_hermitian hdeg, hermitian_firstVector]

/-- Restriction to the actual standard orthogonal complement. -/
def restrictMatrix (g : Matrix (Fin (n+1)) (Fin (n+1)) K) : Matrix (Fin n) (Fin n) K :=
  g.submatrix Fin.succ Fin.succ

private theorem restrict_mulVec (hdeg : Module.finrank F K = 2)
    (g : firstStabilizer (n := n) hdeg) (x : Fin n → K) :
    g.val.val *ᵥ Fin.cons 0 x = Fin.cons 0 (restrictMatrix g.val.val *ᵥ x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using firstStabilizer_first_coord hdeg g (Fin.cons 0 x)
  · simp [mulVec, dotProduct, restrictMatrix, Fin.sum_univ_succ]

/-- Full restriction, retaining the matrix group carrier. -/
def restrictUnitary (hdeg : Module.finrank F K = 2)
    (g : firstStabilizer (n := n) hdeg) : U F K n hdeg := by
  refine ⟨restrictMatrix g.val.val, (mem_u_iff_preserves_hermitian hdeg _).mpr ?_⟩
  intro x y
  have h := u_preserves_hermitian hdeg g.val (Fin.cons 0 x) (Fin.cons 0 y)
  rw [restrict_mulVec, restrict_mulVec, hermitian_cons, hermitian_cons] at h
  simpa using h

@[simp] theorem restrict_extend (hdeg : Module.finrank F K = 2) (g : U F K n hdeg) :
    restrictUnitary hdeg (extendUnitary hdeg g) = g := by
  apply Subtype.ext
  ext i j
  rfl

@[simp] theorem extend_restrict (hdeg : Module.finrank F K = 2)
    (g : firstStabilizer (n := n) hdeg) :
    extendUnitary hdeg (restrictUnitary hdeg g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · have h := firstStabilizer_first_coord hdeg g (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at h
    change Fin.cases 1 (fun _ => 0) j = g.val.val 0 j
    change g.val.val 0 j = (Pi.single j 1 : Fin (n+1) → K) 0 at h
    rw [h]
    refine Fin.cases ?_ (fun j' => ?_) j <;> simp
  · refine Fin.cases ?_ (fun j' => ?_) j
    · change (0 : K) = g.val.val i'.succ 0
      have h := congrFun (firstStabilizer_fixes hdeg g) i'.succ
      simpa [firstVector, Matrix.mulVec_single_one, Pi.single_apply] using h.symm
    · rfl

/-- The full stabilizer is multiplicatively equivalent to the lower-dimensional
unitary group, with proved inverse restriction and extension. -/
def firstStabilizerEquiv (hdeg : Module.finrank F K = 2) :
    firstStabilizer (n := n) hdeg ≃* U F K n hdeg where
  toFun := restrictUnitary hdeg
  invFun := extendUnitary hdeg
  left_inv := extend_restrict hdeg
  right_inv := restrict_extend hdeg
  map_mul' g k := by
    apply Subtype.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    have h := congrArg Fin.tail (congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K =>
      A *ᵥ Fin.cons 0 (Pi.single i 1)) (show (g * k).val.val = g.val.val * k.val.val from rfl))
    rw [← Matrix.mulVec_mulVec, restrict_mulVec, restrict_mulVec, restrict_mulVec] at h
    change restrictMatrix (g * k).val.val *ᵥ Pi.single i 1 =
      (restrictMatrix g.val.val * restrictMatrix k.val.val) *ᵥ Pi.single i 1
    simpa only [Fin.tail_cons, Matrix.mulVec_mulVec] using h
end Atlas.Unitary
