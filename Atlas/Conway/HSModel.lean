import Atlas.Sporadic.Conway3Construction
import Atlas.Conway.LeechTriangleSlice

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem minimumPairMinus_dot (i j : Omega) (u : IntegerCoordinates) :
    integerDot (minimumPairMinus i j).val u = 4*(u i-u j) := by
  simp [minimumPairMinus,integerDot,coordinateVector,Pi.single_apply,sub_mul,ite_mul,
    Finset.sum_sub_distrib,mul_sub]

def hsEndpoint : leech := minimumPairMinus co3MarkedCoordinate co3BasePoint.val

theorem hs_endpoint_norm : integerDot hsEndpoint.val hsEndpoint.val = 32 :=
  minimumPairMinus_norm _ _ (Ne.symm co3BasePoint.prop)

theorem hs_normSix_endpoint_dot :
    integerDot (normSixVector co3MarkedCoordinate).val hsEndpoint.val = 16 := by
  rw [integerDot_comm]
  change integerDot (minimumPairMinus _ _).val _ = 16
  rw [minimumPairMinus_dot]
  norm_num [normSixVector_apply,co3MarkedCoordinate,co3BasePoint]

abbrev HSModel := LeechTriangleStabilizer (normSixVector co3MarkedCoordinate) hsEndpoint

/-- The intrinsic possible norm-four sides of the 2-3-3 triangle. -/
abbrev HSSides := {u : leech // integerDot u.val u.val = 32 ∧
  integerDot (normSixVector co3MarkedCoordinate).val u.val = 16}

instance hsSidesAction : MulAction Atlas.Sporadic.Conway3.Model HSSides where
  smul g u := ⟨g.val.val u.val,g.val.prop u.val u.val |>.trans u.prop.1,by
    have he := g.val.prop (normSixVector co3MarkedCoordinate) u.val
    rw [show g.val.val (normSixVector co3MarkedCoordinate) = normSixVector co3MarkedCoordinate from g.prop] at he
    exact he.trans u.prop.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def hsBaseSide : HSSides := ⟨hsEndpoint,hs_endpoint_norm,hs_normSix_endpoint_dot⟩

abbrev HSGraphPoints := LeechTriangleSlice (normSixVector co3MarkedCoordinate) hsEndpoint 32 24 16

instance hsGraphAction : MulAction HSModel HSGraphPoints := leechTriangleSliceAction _ _ _ _ _

theorem hs_side_distance (u : HSSides) :
    integerDot ((normSixVector co3MarkedCoordinate)-u.val).val
      ((normSixVector co3MarkedCoordinate)-u.val).val = 48 := by
  rw [leech_norm_sub,normSixVector_norm,u.prop.1,u.prop.2]
  norm_num

end Atlas.Conway
