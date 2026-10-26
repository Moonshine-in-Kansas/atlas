import Atlas.Rudvalis.SecondFrameBasis
import Atlas.Lattices.ModularReflection

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def secondFrameProjection (s : Finset SeedCoordinate) : RationalSpace →ₗ[ℚ] RationalSpace :=
  secondFrameBasis.constr ℚ (fun i => if i∈s then secondFrameBasis i else 0)

theorem secondFrameProjection_basis (s : Finset SeedCoordinate) (i : SeedCoordinate) :
    secondFrameProjection s (secondFrameBasis i)=if i∈s then secondFrameBasis i else 0 :=
  secondFrameBasis.constr_basis ℚ _ i

theorem secondFrameProjection_idempotent (s : Finset SeedCoordinate) (v : RationalSpace) :
    secondFrameProjection s (secondFrameProjection s v)=secondFrameProjection s v := by
  have he : (secondFrameProjection s).comp (secondFrameProjection s)=secondFrameProjection s := by
    apply secondFrameBasis.ext
    intro i
    simp only [LinearMap.comp_apply,secondFrameProjection_basis]
    by_cases hi : i∈s <;> simp [hi,secondFrameProjection_basis]
  exact congrArg (fun f : RationalSpace →ₗ[ℚ] RationalSpace => f v) he

theorem secondFrame_pairing_repr (v : RationalSpace) (i : SeedCoordinate) :
    rationalDot v (secondFrameBasis i)=4*secondFrameBasis.repr v i := by
  calc
    _=rationalDot (∑j,secondFrameBasis.repr v j • secondFrameBasis j) (secondFrameBasis i) := by rw [secondFrameBasis.sum_repr]
    _=_ := by
      rw [rationalDot_finset_sum_smul]
      simp [secondFrameBasis_apply,secondFrame_pairing]
      ring

noncomputable def secondFrameReflection (s : Finset SeedCoordinate) : RationalSpace ≃ₗ[ℚ] RationalSpace :=
  Atlas.Lattices.reflectionEquiv (secondFrameProjection s) (secondFrameProjection_idempotent s)

theorem secondFrameReflection_basis (s : Finset SeedCoordinate) (i : SeedCoordinate) :
    secondFrameReflection s (secondFrameBasis i)=if i∈s then secondFrameBasis i else -secondFrameBasis i := by
  change (2 : ℚ) • secondFrameProjection s (secondFrameBasis i)-secondFrameBasis i=_
  rw [secondFrameProjection_basis]
  by_cases hi : i∈s <;> simp [hi,two_smul]

def rationalForm : LinearMap.BilinForm ℚ RationalSpace := dotProductBilin ℚ ℚ

theorem rationalForm_apply (v w : RationalSpace) : rationalForm v w=rationalDot v w := rfl

theorem rationalDot_symmetric (v w : RationalSpace) : rationalDot v w=rationalDot w v := by
  simp [rationalDot,mul_comm]

theorem secondFrame_dot_repr (v w : RationalSpace) :
    rationalDot v w=∑ i,4*secondFrameBasis.repr v i*secondFrameBasis.repr w i := by
  calc
    _=rationalDot (∑j,secondFrameBasis.repr v j • secondFrameBasis j) w := by rw [secondFrameBasis.sum_repr]
    _=∑i,secondFrameBasis.repr v i*rationalDot (secondFrameBasis i) w := rationalDot_finset_sum_smul _ _ _ _
    _=_ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rationalDot_symmetric,secondFrame_pairing_repr]
      ring

theorem secondFrameProjection_repr (s : Finset SeedCoordinate) (v : RationalSpace) (i : SeedCoordinate) :
    secondFrameBasis.repr (secondFrameProjection s v) i=
      if i∈s then secondFrameBasis.repr v i else 0 := by
  classical
  by_cases hi : i∈s <;> simp [hi,secondFrameProjection,Module.Basis.constr_apply_fintype,map_sum,map_smul,
    apply_ite,Finsupp.single_apply,eq_comm]

theorem secondFrameProjection_selfadjoint (s : Finset SeedCoordinate) (v w : RationalSpace) :
    rationalDot (secondFrameProjection s v) w=rationalDot v (secondFrameProjection s w) := by
  rw [secondFrame_dot_repr,secondFrame_dot_repr]
  simp_rw [secondFrameProjection_repr]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈s <;> simp [hi]

theorem secondFrameReflection_pairing (s : Finset SeedCoordinate) (v w : RationalSpace) :
    rationalDot (secondFrameReflection s v) (secondFrameReflection s w)=rationalDot v w :=
  Atlas.Lattices.reflectionMap_pairing rationalForm (secondFrameProjection s)
    (secondFrameProjection_idempotent s) (secondFrameProjection_selfadjoint s) v w

theorem secondFrameProjection_eq_self_iff (s : Finset SeedCoordinate) (v : RationalSpace) :
    secondFrameProjection s v=v ↔ ∀i,i∉s → secondFrameBasis.repr v i=0 := by
  constructor
  · intro h i hi
    have he := congrArg (fun w => secondFrameBasis.repr w i) h
    rw [secondFrameProjection_repr,if_neg hi] at he
    exact he.symm
  · intro h
    apply secondFrameBasis.repr.injective
    ext i
    rw [secondFrameProjection_repr]
    by_cases hi : i∈s <;> simp [hi,h i]

theorem secondFrameProjection_range (s : Finset SeedCoordinate) (v : RationalSpace) :
    v∈LinearMap.range (secondFrameProjection s) ↔ ∀i,i∉s → secondFrameBasis.repr v i=0 := by
  rw [←secondFrameProjection_eq_self_iff]
  constructor
  · rintro ⟨w,rfl⟩
    exact secondFrameProjection_idempotent s w
  · intro h
    exact ⟨v,h⟩

theorem secondFrameReflection_involutive (s : Finset SeedCoordinate) :
    Function.Involutive (secondFrameReflection s) :=
  Atlas.Lattices.reflectionMap_involutive (secondFrameProjection s) (secondFrameProjection_idempotent s)

end Atlas.Rudvalis


