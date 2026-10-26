import Atlas.Rudvalis.TorsionMinimum
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Actual coordinate translations of the binary Hamming weave. -/
namespace Atlas.Rudvalis
open scoped BigOperators

abbrev BinaryMatrix := Matrix (Fin 3) (Fin 3) Bit

theorem vector_add_self (x : E) : x+x = 0 := by
  ext i
  exact Atlas.Codes.bit_self_add (x i)

theorem matrixAt_add (A B : BinaryMatrix) (p : E) :
    matrixAt (A+B) p = matrixAt A p + matrixAt B p := by
  ext j
  simp [matrixAt,add_mul,Finset.sum_add_distrib]

def coordinateTranslation (A : BinaryMatrix) : Equiv.Perm Coordinate where
  toFun z := (z.1,z.2+matrixAt A z.1.val)
  invFun z := (z.1,z.2+matrixAt A z.1.val)
  left_inv z := by simp [add_assoc,vector_add_self]
  right_inv z := by simp [add_assoc,vector_add_self]

theorem coordinateTranslation_mul (A B : BinaryMatrix) :
    coordinateTranslation (A+B) = coordinateTranslation A * coordinateTranslation B := by
  apply Equiv.ext
  intro z
  change (z.1, z.2 + matrixAt (A+B) z.1.val) =
    (z.1, (z.2 + matrixAt B z.1.val) + matrixAt A z.1.val)
  congr 1
  rw [matrixAt_add]
  abel

theorem coordinateTranslation_injective : Function.Injective coordinateTranslation := by
  intro A B h
  have he (p : Point) : matrixAt A p.val = matrixAt B p.val := by
    have hh := congrArg Prod.snd (Equiv.congr_fun h (p,0))
    simpa [coordinateTranslation] using hh
  ext j i
  have hi := congrFun (he (basisPoint i)) j
  fin_cases i <;> simpa [basisPoint,binaryLabel,matrixAt,Fin.sum_univ_succ] using hi

def crossMatrix (c : E) : BinaryMatrix :=
  ![![0,c 2,c 1], ![c 2,0,c 0], ![c 1,c 0,0]]

theorem crossMatrix_pair (c : E) (A : BinaryMatrix) (p x : E) :
    dot (matrixAt (crossMatrix c * A) p) x = polar c (matrixAt A p) x := by
  change (∑ j, (∑ i, (∑ k, crossMatrix c j k * A k i) * p i) * x j) =
    polar c (matrixAt A p) x
  simp [matrixAt,crossMatrix,polar,Fin.sum_univ_succ]
  ring

theorem polar_comm (c x y : E) : polar c x y = polar c y x := by
  simp [polar]
  ring

theorem theta_translate (p : Point) (c x t : E) :
    theta p c (x+t) = theta p c x + theta p c t + polar c t x := by
  have h : ∀ a b c d : Bit, a+b+c=d → a=b+c+d := by decide
  simpa only [polar_comm c x t] using
    h _ _ _ _ (theta_polarization p c x t)

/-- The full coordinate automorphism group of the actual binary residue code. -/
def binaryPermutationGroup : Subgroup (Equiv.Perm Coordinate) where
  carrier := {g | ∀ w : BinaryWord, w ∈ binaryResidue ↔ (w ∘ g) ∈ binaryResidue}
  one_mem' := by intro w; rfl
  mul_mem' := by
    intro g h hg hh w
    exact (hg w).trans (hh (w ∘ g))
  inv_mem' := by
    intro g hg w
    simpa [Function.comp_def] using (hg (w ∘ (g⁻¹ : Equiv.Perm Coordinate))).symm

/-- The explicit parameter update under a block translation. -/
def translatedParameters (A : BinaryMatrix) (a : BinaryParameters) : BinaryParameters :=
  (fun p => a.1 p + dot (matrixAt a.2.1 p.val) (matrixAt A p.val) +
    theta p a.2.2 (matrixAt A p.val), a.2.1+crossMatrix a.2.2*A, a.2.2)

theorem binaryNormalMap_translation (A : BinaryMatrix) (a : BinaryParameters) :
    binaryNormalMap (translatedParameters A a) = binaryNormalMap a ∘ coordinateTranslation A := by
  funext z
  change (a.1 z.1 + dot (matrixAt a.2.1 z.1.val) (matrixAt A z.1.val) +
      theta z.1 a.2.2 (matrixAt A z.1.val)) +
      dot (matrixAt (a.2.1+crossMatrix a.2.2*A) z.1.val) z.2 + theta z.1 a.2.2 z.2 =
    a.1 z.1 + dot (matrixAt a.2.1 z.1.val) (z.2+matrixAt A z.1.val) +
      theta z.1 a.2.2 (z.2+matrixAt A z.1.val)
  rw [matrixAt_add,dot_add_left,crossMatrix_pair,dot_add_right,theta_translate]
  ring

theorem coordinateTranslation_preserves (A : BinaryMatrix) (w : BinaryWord)
    (hw : w ∈ binaryResidue) : w ∘ coordinateTranslation A ∈ binaryResidue := by
  obtain ⟨a,rfl⟩ := hw
  exact ⟨translatedParameters A a, binaryNormalMap_translation A a⟩

theorem coordinateTranslation_mem (A : BinaryMatrix) :
    coordinateTranslation A ∈ binaryPermutationGroup := by
  intro w
  constructor
  · exact coordinateTranslation_preserves A w
  · intro hw
    have h := coordinateTranslation_preserves A (w ∘ coordinateTranslation A) hw
    simpa [Function.comp_def,coordinateTranslation,add_assoc,vector_add_self] using h

/-- The faithful elementary abelian translation group inside the actual code group. -/
def coordinateTranslationHom : Multiplicative BinaryMatrix →* binaryPermutationGroup where
  toFun A := ⟨coordinateTranslation A.toAdd, coordinateTranslation_mem A.toAdd⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    change (z.1,z.2+matrixAt 0 z.1.val) = z
    have h : matrixAt 0 z.1.val = 0 := by ext j; simp [matrixAt]
    simp [h]
  map_mul' A B := Subtype.ext (coordinateTranslation_mul A.toAdd B.toAdd)

theorem coordinateTranslationHom_injective : Function.Injective coordinateTranslationHom := by
  intro A B h
  have he := coordinateTranslation_injective (congrArg Subtype.val h)
  exact he

def binaryTranslationSubgroup : Subgroup binaryPermutationGroup := coordinateTranslationHom.range

noncomputable def binaryTranslationEquiv :
    Multiplicative BinaryMatrix ≃* binaryTranslationSubgroup :=
  MonoidHom.ofInjective coordinateTranslationHom_injective

theorem binaryTranslationSubgroup_order : Nat.card binaryTranslationSubgroup = 512 := by
  rw [← Nat.card_congr binaryTranslationEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card, BinaryMatrix, Matrix, Bit, ZMod.card]

end Atlas.Rudvalis

