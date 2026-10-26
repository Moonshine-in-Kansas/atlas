import Atlas.Lattices.ConwayWales.GaussianCoordinates
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

/-- Row, quaternion coordinate, and real/imaginary coordinate, respectively. -/
abbrev RealIndex := Row × Fin 4 × Fin 2
abbrev IntegerCoordinates := RealIndex → ℤ
abbrev FrameCodeSpace := RealIndex → ZMod 4

theorem realIndex_card : Fintype.card RealIndex = 56 := by decide

def integerEmbedding (z : IntegerCoordinates) : Space := fun r =>
  ⟨GaussianInt.toComplex ⟨z (r,0,0), z (r,0,1)⟩,
   GaussianInt.toComplex ⟨z (r,1,0), z (r,1,1)⟩,
   GaussianInt.toComplex ⟨z (r,2,0), z (r,2,1)⟩,
   GaussianInt.toComplex ⟨z (r,3,0), z (r,3,1)⟩⟩

theorem integerEmbedding_order (z : IntegerCoordinates) (r : Row) :
    integerEmbedding z r ∈ gaussianOrder :=
  ⟨⟨_,rfl⟩,⟨_,rfl⟩,⟨_,rfl⟩,⟨_,rfl⟩⟩

theorem integerEmbedding_surjective_order (v : Space) (hv : ∀ r, v r ∈ gaussianOrder) :
    ∃ z, integerEmbedding z = v := by
  have h : ∀ r, ∃ w : Fin 4 → GaussianInt,
      GaussianInt.toComplex (w 0) = (v r).re ∧
      GaussianInt.toComplex (w 1) = (v r).imI ∧
      GaussianInt.toComplex (w 2) = (v r).imJ ∧
      GaussianInt.toComplex (w 3) = (v r).imK := by
    intro r
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := hv r
    exact ⟨![a,b,c,d],ha,hb,hc,hd⟩
  choose w hw using h
  refine ⟨fun p => ![(w p.1 p.2.1).re, (w p.1 p.2.1).im] p.2.2, ?_⟩
  funext r
  apply Quaternion.ext <;> simp only [integerEmbedding, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> aesop

def halfEmbedding (z : IntegerCoordinates) : Space := (1 / 2 : ℂ) • integerEmbedding z

def modFour (z : IntegerCoordinates) : FrameCodeSpace := fun i => (z i : ZMod 4)

/-- The actual doubled seed lattice reduced in the specified real basis. -/
def frameCode : Set FrameCodeSpace :=
  {c | ∃ z : IntegerCoordinates, halfEmbedding z ∈ seedLattice ∧ modFour z = c}

theorem gaussian_coordinate_formula (a b : ℤ) :
    GaussianInt.toComplex ⟨a,b⟩ = (a : ℂ) + (b : ℂ) * Complex.I := rfl

theorem integerEmbedding_add (z w : IntegerCoordinates) :
    integerEmbedding (z + w) = integerEmbedding z + integerEmbedding w := by
  funext r
  apply Quaternion.ext <;>
    simp only [integerEmbedding, Pi.add_apply, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add]
  all_goals simp only [gaussian_coordinate_formula, Int.cast_add]; ring

theorem integerEmbedding_four (z : IntegerCoordinates) :
    integerEmbedding (fun i => 4 * z i) = (4 : ℂ) • integerEmbedding z := by
  funext r
  apply Quaternion.ext <;>
    simp only [Pi.smul_apply, integerEmbedding, Quaternion.re_smul, Quaternion.imI_smul,
      Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul]
  all_goals simp only [gaussian_coordinate_formula, Int.cast_mul, Int.cast_ofNat]; ring

theorem halfEmbedding_add (z w : IntegerCoordinates) :
    halfEmbedding (z+w) = halfEmbedding z + halfEmbedding w := by
  simp only [halfEmbedding, integerEmbedding_add, smul_add]

theorem halfEmbedding_four_mem (z : IntegerCoordinates) :
    halfEmbedding (fun i => 4 * z i) ∈ seedLattice := by
  simpa only [halfEmbedding, integerEmbedding_four, smul_smul,
    show (1/2 : ℂ)*4=2 by norm_num] using
    doubled_order_vectors_mem (integerEmbedding z) (integerEmbedding_order z)

theorem modFour_equal (z w : IntegerCoordinates) (h : modFour z = modFour w) :
    ∃ k : IntegerCoordinates, w = z + fun i => 4 * k i := by
  have hdiv : ∀ i, (4 : ℤ) ∣ w i - z i := by
    intro i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (z i) (w i) 4).mp (congrFun h i)
  choose k hk using hdiv
  refine ⟨k, ?_⟩
  funext i
  have := hk i
  dsimp only [Pi.add_apply]
  omega

theorem halfEmbedding_mem_iff_code (z : IntegerCoordinates) :
    halfEmbedding z ∈ seedLattice ↔ modFour z ∈ frameCode := by
  constructor
  · intro hz; exact ⟨z,hz,rfl⟩
  · rintro ⟨w,hw,heq⟩
    obtain ⟨k,hk⟩ := modFour_equal w z heq
    rw [hk,halfEmbedding_add]
    exact seedLattice.add_mem hw (halfEmbedding_four_mem k)

/-- Construction A recovers the given seed lattice, rather than defining a substitute. -/
theorem seedLattice_constructionA (v : Space) :
    v ∈ seedLattice ↔ ∃ z : IntegerCoordinates,
      modFour z ∈ frameCode ∧ halfEmbedding z = v := by
  constructor
  · intro hv
    obtain ⟨z,hz⟩ := integerEmbedding_surjective_order ((2 : ℂ) • v)
      (seedLattice_le_halfIntegral hv)
    have hh : halfEmbedding z = v := by
      rw [halfEmbedding,hz,smul_smul]
      norm_num
    exact ⟨z,(halfEmbedding_mem_iff_code z).mp (hh ▸ hv),hh⟩
  · rintro ⟨z,hz,rfl⟩
    exact (halfEmbedding_mem_iff_code z).mpr hz

theorem integerEmbedding_zero : integerEmbedding 0 = 0 := by
  have h := integerEmbedding_add 0 0
  simpa using h

theorem halfEmbedding_zero : halfEmbedding 0 = 0 := by
  rw [halfEmbedding, integerEmbedding_zero, smul_zero]

def halfEmbeddingHom : IntegerCoordinates →+ Space where
  toFun := halfEmbedding
  map_zero' := halfEmbedding_zero
  map_add' := halfEmbedding_add

def modFourHom : IntegerCoordinates →+ FrameCodeSpace where
  toFun := modFour
  map_zero' := by ext i; exact Int.cast_zero
  map_add' := by intros; ext i; exact Int.cast_add _ _

/-- The frame code as an additive subgroup, with its actual lattice preimage. -/
def frameCodeGroup : AddSubgroup FrameCodeSpace :=
  (seedLattice.toAddSubgroup.comap halfEmbeddingHom).map modFourHom

theorem frameCodeGroup_carrier : (frameCodeGroup : Set FrameCodeSpace) = frameCode := rfl

/-- Additivity over Z/4 is the linear-code structure over that ring. -/
def frameCodeModule : Submodule (ZMod 4) FrameCodeSpace where
  carrier := frameCode
  zero_mem' := frameCodeGroup.zero_mem
  add_mem' := frameCodeGroup.add_mem
  smul_mem' := by
    intro a c hc
    have h := frameCodeGroup.nsmul_mem hc a.val
    change a • c ∈ frameCodeGroup
    convert h using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem frameCodeModule_carrier : (frameCodeModule : Set FrameCodeSpace) = frameCode := rfl

theorem integerEmbedding_injective : Function.Injective integerEmbedding := by
  intro z w h
  funext ⟨r,u,b⟩
  have hh := congrFun h r
  have h0 := GaussianInt.toComplex_injective (congrArg (fun q : Q => q.re) hh)
  have h1 := GaussianInt.toComplex_injective (congrArg (fun q : Q => q.imI) hh)
  have h2 := GaussianInt.toComplex_injective (congrArg (fun q : Q => q.imJ) hh)
  have h3 := GaussianInt.toComplex_injective (congrArg (fun q : Q => q.imK) hh)
  fin_cases u <;> fin_cases b
  · exact congrArg Zsqrtd.re h0
  · exact congrArg Zsqrtd.im h0
  · exact congrArg Zsqrtd.re h1
  · exact congrArg Zsqrtd.im h1
  · exact congrArg Zsqrtd.re h2
  · exact congrArg Zsqrtd.im h2
  · exact congrArg Zsqrtd.re h3
  · exact congrArg Zsqrtd.im h3

/-- Cyclic shift of the seven blocks, preserving the eight real positions per block. -/
def shiftCoordinates {R : Type*} (d : Row) (z : RealIndex → R) : RealIndex → R :=
  fun p => z (p.1-d,p.2)

theorem halfEmbedding_shift (d : Row) (z : IntegerCoordinates) :
    halfEmbedding (shiftCoordinates d z) = translate d (halfEmbedding z) := rfl

theorem frameCode_shift (d : Row) {c : FrameCodeSpace} (hc : c ∈ frameCode) :
    shiftCoordinates d c ∈ frameCode := by
  obtain ⟨z,hz,rfl⟩ := hc
  refine ⟨shiftCoordinates d z, ?_, rfl⟩
  rw [halfEmbedding_shift]
  exact translate_mem_seedLattice d _ hz

end Atlas.ConwayWales




