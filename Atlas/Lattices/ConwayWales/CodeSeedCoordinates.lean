import Atlas.Lattices.ConwayWales.FrameCode

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

/-- The integer coordinates of the two unscaled quaternion seeds in the real basis. -/
def integerA : IntegerCoordinates := fun p =>
  (![ ![![1,0],![1,0],![1,0],![1,0]],
      ![![0,0],![0,0],![0,0],![0,0]],
      ![![0,0],![0,0],![0,0],![0,0]],
      ![![0,1],![1,0],![0,1],![-1,0]],
      ![![0,0],![0,0],![0,0],![0,0]],
      ![![0,1],![0,1],![-1,0],![1,0]],
      ![![0,1],![-1,0],![1,0],![0,1]]] p.1) p.2.1 p.2.2

def integerB : IntegerCoordinates := fun p =>
  (![ ![![0,1],![1,0],![1,0],![1,0]],
      ![![0,1],![0,0],![0,0],![-1,0]],
      ![![0,1],![-1,0],![0,0],![0,0]],
      ![![0,0],![0,0],![-1,0],![1,0]],
      ![![0,1],![0,0],![-1,0],![0,0]],
      ![![0,0],![-1,0],![1,0],![0,0]],
      ![![0,0],![1,0],![0,0],![-1,0]]] p.1) p.2.1 p.2.2

theorem integerEmbedding_A : integerEmbedding integerA = A := by
  funext r
  fin_cases r <;> apply Quaternion.ext
  all_goals simp only [integerEmbedding,gaussian_coordinate_formula]
  all_goals norm_num [integerA,A,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]


theorem integerEmbedding_B : integerEmbedding integerB = B := by
  funext r
  fin_cases r <;> apply Quaternion.ext
  all_goals simp only [integerEmbedding,gaussian_coordinate_formula]
  all_goals norm_num [integerB,B,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]


def integerCentralI (z : IntegerCoordinates) : IntegerCoordinates := fun p =>
  ![-z (p.1,p.2.1,1), z (p.1,p.2.1,0)] p.2.2

/-- Integral signed coordinate permutations for right multiplication by 1,j,k,l. -/
def integerRight (u : Fin 4) (z : IntegerCoordinates) : IntegerCoordinates := fun p =>
  (![ ![z (p.1,0,p.2.2),z (p.1,1,p.2.2),z (p.1,2,p.2.2),z (p.1,3,p.2.2)],
      ![-z (p.1,1,p.2.2),z (p.1,0,p.2.2),z (p.1,3,p.2.2),-z (p.1,2,p.2.2)],
      ![-z (p.1,2,p.2.2),-z (p.1,3,p.2.2),z (p.1,0,p.2.2),z (p.1,1,p.2.2)],
      ![-z (p.1,3,p.2.2),z (p.1,2,p.2.2),-z (p.1,1,p.2.2),z (p.1,0,p.2.2)]] u) p.2.1

theorem integerEmbedding_centralI (z : IntegerCoordinates) :
    integerEmbedding (integerCentralI z) = Complex.I • integerEmbedding z := by
  funext r
  apply Quaternion.ext <;>
    simp [integerEmbedding, integerCentralI, gaussian_coordinate_formula,
      Complex.I_mul_I, mul_add, mul_assoc, mul_comm] <;> ring_nf <;> norm_num

theorem integerEmbedding_right (u : Fin 4) (z : IntegerCoordinates) :
    integerEmbedding (integerRight u z) = fun r => integerEmbedding z r * quaternionBasis u := by
  funext r
  fin_cases u <;> apply Quaternion.ext <;>
    simp [integerEmbedding, integerRight, quaternionBasis, j,k,l,gaussian_coordinate_formula] <;> ring

/-- The sixteen actual seed rows: A or B, times a central phase, times a quaternion unit. -/
def integerCodeSeed (t : Fin 2) (u : Fin 4) (e : Fin 2) : IntegerCoordinates :=
  integerRight u (if e = 0 then (if t = 0 then integerA else integerB)
    else integerCentralI (if t = 0 then integerA else integerB))

theorem integerCodeSeed_mem (t : Fin 2) (u : Fin 4) (e : Fin 2) :
    modFour (integerCodeSeed t u e) ∈ frameCode := by
  apply (halfEmbedding_mem_iff_code _).mp
  have ha := seedLattice_right_order a a_mem_seedLattice (quaternionBasis u) (basis_mem_gaussianOrder u)
  have hb := seedLattice_right_order b b_mem_seedLattice (quaternionBasis u) (basis_mem_gaussianOrder u)
  fin_cases t <;> fin_cases e
  all_goals norm_num only [integerCodeSeed, Fin.ext_iff, Fin.val_zero, Fin.val_one, ite_true, ite_false]
  all_goals simp only [halfEmbedding,
    integerEmbedding_right, integerEmbedding_centralI, integerEmbedding_A, integerEmbedding_B]
  · convert ha using 1
    funext r
    ext <;> simp [a,b] <;> ring
  · convert gaussian_smul_mem_seedLattice gaussian_I ha using 1
    funext r
    change (1/2 : ℂ) • ((Complex.I • A r) * quaternionBasis u) =
      Complex.I • (((1/2 : ℂ) • A r) * quaternionBasis u)
    ext <;> simp <;> ring
  · convert hb using 1
    funext r
    ext <;> simp [a,b] <;> ring
  · convert gaussian_smul_mem_seedLattice gaussian_I hb using 1
    funext r
    change (1/2 : ℂ) • ((Complex.I • B r) * quaternionBasis u) =
      Complex.I • (((1/2 : ℂ) • B r) * quaternionBasis u)
    ext <;> simp <;> ring

end Atlas.ConwayWales
