import Atlas.Fischer.ParkerElementarySubcodes
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

/-- The sign coordinate of an actual multiplicative section of a Parker preimage. -/
@[ext] structure ParkerSection (K : ParkerElementarySubcode) where
  sign : K.code → Bit
  zero : sign 0 = 0
  correction : ∀ a b, sign (a+b)+sign a+sign b = parkerGolayFactorSet a.val b.val

namespace ParkerSection
variable {K : ParkerElementarySubcode}

theorem exists_section (K : ParkerElementarySubcode) : Nonempty (ParkerSection K) := by
  obtain ⟨η,hη,hadd⟩ := K.cocycle.exists_correction
  exact ⟨⟨η,hη,hadd⟩⟩

noncomputable def chosen (K : ParkerElementarySubcode) : ParkerSection K :=
  Classical.choice (exists_section K)

/-- This section takes its values in the actual Parker loop. -/
def lift (q : ParkerSection K) (a : K.code) : ParkerLoop := (a.val,q.sign a)

@[simp] theorem lift_code (q : ParkerSection K) (a : K.code) : (q.lift a).1 = a.val := rfl
@[simp] theorem lift_zero (q : ParkerSection K) : q.lift 0 = (0,0) := by
  simp [lift,q.zero]

theorem lift_multiply (q : ParkerSection K) (a b : K.code) :
    q.lift (a+b) = parkerLoopMultiply (q.lift a) (q.lift b) := by
  have hs : q.sign (a+b) = q.sign a+q.sign b+parkerGolayFactorSet a.val b.val := by
    rw [← q.correction]
    have h := CharTwo.add_self_eq_zero (q.sign a+q.sign b)
    calc
      _ = q.sign (a+b)+((q.sign a+q.sign b)+(q.sign a+q.sign b)) := by rw [h,add_zero]
      _ = _ := by abel
  exact Prod.ext rfl hs

/-- The section is an actual group embedding into the retained preimage. -/
def embedding (q : ParkerSection K) : Multiplicative K.code →* K.Preimage where
  toFun a := ⟨q.lift a.toAdd, a.toAdd.property⟩
  map_one' := Subtype.ext q.lift_zero
  map_mul' a b := Subtype.ext (q.lift_multiply a.toAdd b.toAdd)

theorem embedding_injective (q : ParkerSection K) : Function.Injective q.embedding := by
  intro a b h
  have he := congrArg (fun d : K.Preimage => d.val.1) h
  exact Multiplicative.toAdd.injective (Subtype.ext he)

/-- Character translation is the precise freedom in choosing a section. -/
def translate (q : ParkerSection K) (l : Module.Dual Bit K.code) : ParkerSection K where
  sign a := q.sign a+l a
  zero := by simp [q.zero]
  correction := (Atlas.Algebra.binary_correction_add_linear
    (fun a b : K.code => parkerGolayFactorSet a.val b.val) q.sign q.zero q.correction l).2

@[simp] theorem translate_sign (q : ParkerSection K) (l : Module.Dual Bit K.code)
    (a : K.code) : (q.translate l).sign a = q.sign a+l a := rfl

theorem translate_lift (q : ParkerSection K) (l : Module.Dual Bit K.code) (a : K.code) :
    (q.translate l).lift a = parkerSign (l a) (q.lift a) := rfl

noncomputable def difference (q r : ParkerSection K) : Module.Dual Bit K.code :=
  Classical.choose (Atlas.Algebra.binary_corrections_differ_by_linear
    (fun a b : K.code => parkerGolayFactorSet a.val b.val)
    q.sign r.sign q.zero r.zero q.correction r.correction)

theorem difference_apply (q r : ParkerSection K) (a : K.code) :
    q.difference r a = q.sign a+r.sign a :=
  Classical.choose_spec (Atlas.Algebra.binary_corrections_differ_by_linear
    (fun a b : K.code => parkerGolayFactorSet a.val b.val)
    q.sign r.sign q.zero r.zero q.correction r.correction) a

theorem translate_difference (q r : ParkerSection K) : q.translate (q.difference r) = r := by
  apply ParkerSection.ext
  funext a
  change q.sign a+q.difference r a=r.sign a
  rw [difference_apply,← add_assoc,CharTwo.add_self_eq_zero,zero_add]

/-- An actual equivalence, recording the character-torsor statement without
choosing a preferred splitting in the theorem. -/
noncomputable def characterEquiv (q : ParkerSection K) :
    Module.Dual Bit K.code ≃ ParkerSection K where
  toFun := q.translate
  invFun := q.difference
  right_inv := q.translate_difference
  left_inv l := by
    ext a
    rw [difference_apply,translate_sign,← add_assoc,CharTwo.add_self_eq_zero,zero_add]

/-- Every prescribed sign over a nonzero codeword is attained by a section. -/
theorem exists_sign (a : K.code) (ha : a ≠ 0) (s : Bit) :
    ∃ q : ParkerSection K, q.sign a = s := by
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one Bit ha
  let q := chosen K
  refine ⟨q.translate ((s+q.sign a) • l), ?_⟩
  change q.sign a+(s+q.sign a)*l a=s
  rw [hl,mul_one]
  calc
    _ = s+(q.sign a+q.sign a) := by abel
    _ = s := by rw [CharTwo.add_self_eq_zero,add_zero]

/-- Calibration refers to a prescribed actual Parker element, not an abstract
isomorphic sign choice. -/
theorem exists_lift (a : K.code) (ha : a ≠ 0) (d : ParkerLoop) (hd : d.1=a.val) :
    ∃ q : ParkerSection K, q.lift a = d := by
  obtain ⟨q,hq⟩ := exists_sign a ha d.2
  exact ⟨q,Prod.ext hd.symm hq⟩

end ParkerSection
end Atlas.Fischer
