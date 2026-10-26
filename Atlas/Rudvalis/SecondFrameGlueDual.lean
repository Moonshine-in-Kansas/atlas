import Atlas.Rudvalis.SecondFrameBasis
import Atlas.Rudvalis.FrameGlueHexad
import Atlas.Rudvalis.CodeProjectionCoordinates
import Atlas.Lattices.BinaryGlueDual

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def frameGlueSeedCoordinate (z : FrameGlueCoordinate) : SeedCoordinate :=
  originalCoordinateEquiv.symm (frameGluePoint z.1,z.2)

theorem frameGlueSeedCoordinate_injective : Function.Injective frameGlueSeedCoordinate := by
  intro a b h
  have he := originalCoordinateEquiv.symm.injective h
  exact Prod.ext (frameGluePoint_injective (congrArg Prod.fst he)) (congrArg (fun z : Point × E => z.2) he)

/-- The selected twenty-four orthonormal vectors are the actual second-frame b_i/2. -/
noncomputable def frameGlueEmbedding : (FrameGlueCoordinate→ℚ) →ₗ[ℚ] RationalSpace where
  toFun y := ∑i,(y i/2) • secondFrame (frameGlueSeedCoordinate i)
  map_add' y z := by simp [add_div,add_smul,Finset.sum_add_distrib]
  map_smul' a y := by simp [Finset.smul_sum,smul_smul,mul_div_assoc]

private theorem pairing_comm (v w : RationalSpace) : rationalDot v w=rationalDot w v := by
  simp [rationalDot,mul_comm]

theorem frameGlueEmbedding_basis_pairing (y : FrameGlueCoordinate→ℚ) (j : FrameGlueCoordinate) :
    rationalDot (frameGlueEmbedding y) (secondFrame (frameGlueSeedCoordinate j))=2*y j := by
  change rationalDot (∑i,(y i/2) • secondFrame (frameGlueSeedCoordinate i)) _=_
  rw [rationalDot_finset_sum_smul]
  simp only [secondFrame_pairing,frameGlueSeedCoordinate_injective.eq_iff]
  simp [mul_ite]
  ring

theorem frameGlueEmbedding_pairing (y z : FrameGlueCoordinate→ℚ) :
    rationalDot (frameGlueEmbedding y) (frameGlueEmbedding z)=∑i,y i*z i := by
  rw [pairing_comm]
  change rationalDot (∑i,(z i/2) • secondFrame (frameGlueSeedCoordinate i)) _=_
  rw [rationalDot_finset_sum_smul]
  simp_rw [pairing_comm (secondFrame _) _,frameGlueEmbedding_basis_pairing]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem frameGlueEmbedding_injective : Function.Injective frameGlueEmbedding := by
  intro y z h
  funext i
  have he := congrArg (fun v => rationalDot v (secondFrame (frameGlueSeedCoordinate i))) h
  rw [frameGlueEmbedding_basis_pairing,frameGlueEmbedding_basis_pairing] at he
  linarith

/-- Actual local second-frame glue, before proving its inclusion in the global lattice. -/
def MemSecondFrameGlue (v : RationalSpace) : Prop :=
  ∃z : FrameGlueCoordinate→ℤ,Atlas.Lattices.BinaryGlue.residue z∈frameGlueCode ∧ frameGlueEmbedding (Atlas.Lattices.BinaryGlue.integerCast z)=v

/-- Integral pairing dual inside the selected rational twenty-four-space. -/
def MemSecondFrameGlueDual (v : RationalSpace) : Prop :=
  v∈frameGlueEmbedding.range ∧ ∀w : RationalSpace,MemSecondFrameGlue w →
    ∃k : ℤ,rationalDot v w=k

theorem frameGlue_binary_self_dual : Atlas.Lattices.BinaryGlue.dualCode frameGlueCode=frameGlueCode :=
  frameGlueCode_self_dual

theorem frameGlueEmbedding_mem_dual_iff (y : FrameGlueCoordinate→ℚ) :
    MemSecondFrameGlueDual (frameGlueEmbedding y) ↔ Atlas.Lattices.BinaryGlue.MemDual frameGlueCode y := by
  constructor
  · rintro ⟨_,hy⟩ z hz
    obtain ⟨k,hk⟩ := hy (frameGlueEmbedding (Atlas.Lattices.BinaryGlue.integerCast z)) ⟨z,hz,rfl⟩
    rw [frameGlueEmbedding_pairing] at hk
    exact ⟨k,hk⟩
  · intro hy
    refine ⟨⟨y,rfl⟩,?_⟩
    rintro w ⟨z,hz,rfl⟩
    rw [frameGlueEmbedding_pairing]
    exact hy z hz

/-- The local glue is 2-modular: its integral dual is exactly one half of itself. -/
theorem secondFrameGlue_dual_iff_twice_mem (v : RationalSpace) :
    MemSecondFrameGlueDual v ↔ MemSecondFrameGlue ((2 : ℚ) • v) := by
  constructor
  · rintro ⟨⟨y,rfl⟩,hy⟩
    have hd := (frameGlueEmbedding_mem_dual_iff y).mp ⟨⟨y,rfl⟩,hy⟩
    obtain ⟨z,hz,he⟩ := (Atlas.Lattices.BinaryGlue.selfDual_mem_dual_iff_twice_mem frameGlueCode frameGlue_binary_self_dual y).mp hd
    refine ⟨z,hz,?_⟩
    rw [he]
    exact frameGlueEmbedding.map_smul (2 : ℚ) y
  · rintro ⟨z,hz,he⟩
    let y : FrameGlueCoordinate→ℚ := Atlas.Lattices.BinaryGlue.half z
    have hv : frameGlueEmbedding y=v := by
      have hy : (2 : ℚ) • y=Atlas.Lattices.BinaryGlue.integerCast z := by
        ext i
        change 2*((z i : ℚ)/2)=(z i : ℚ)
        ring
      have hh : (2 : ℚ) • frameGlueEmbedding y=(2 : ℚ) • v := by
        rw [←map_smul,hy,he]
      ext i
      have hi := congrFun hh i
      change 2*frameGlueEmbedding y i=2*v i at hi
      linarith
    rw [←hv,frameGlueEmbedding_mem_dual_iff]
    apply (Atlas.Lattices.BinaryGlue.half_mem_dual_iff frameGlueCode z).mpr
    rw [frameGlue_binary_self_dual]
    exact hz

end Atlas.Rudvalis
