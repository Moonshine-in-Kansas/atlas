import Atlas.Conway.OrthogonalMinimumLines

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

instance vectorStabilizerLineAction (v : leech) :
    MulAction (fullVectorStabilizer v) LeechAntipodalLine :=
  MulAction.compHom _ (quotientAntipodalLineRepresentation.comp (vectorStabilizerProjection v))

def orthogonalLineStabilizer (i j : Omega) : Subgroup (fullVectorStabilizer (minimumPairPlus i j)) :=
  MulAction.stabilizer _ (antipodalLine (minimumPairMinus i j))

theorem orthogonalLineStabilizer_eq_monomial (i j : Omega) (hij : i ≠ j) :
    orthogonalLineStabilizer i j = monomialSubgroup.comap
      (fullVectorStabilizer (minimumPairPlus i j)).subtype := by
  ext g
  change leechCentralProjection g.val • antipodalLine (minimumPairMinus i j) =
    antipodalLine (minimumPairMinus i j) ↔ g.val ∈ monomialSubgroup
  rw [projection_antipodalLine,antipodalLine_eq_iff]
  constructor
  · rintro (hg | hg)
    · exact minimumPair_fixer_mem_monomial g.val i j g.prop hg
    · obtain ⟨s,hs⟩ := monomial_pair_sign_swap i j hij
      have hp : (s.val.val*g.val).val (minimumPairPlus i j) = minimumPairPlus i j := by
        change s.val.val.val (g.val.val _) = _
        rw [show g.val.val (minimumPairPlus i j) = minimumPairPlus i j from g.prop,
          leechVectorStabilizer_fixes]
      have hm : (s.val.val*g.val).val (minimumPairMinus i j) = minimumPairMinus i j := by
        change s.val.val.val (g.val.val _) = _
        rw [hg,map_neg,hs,neg_neg]
      have hh := monomialSubgroup.mul_mem (monomialSubgroup.inv_mem s.val.prop)
        (minimumPair_fixer_mem_monomial _ i j hp hm)
      simpa only [inv_mul_cancel_left] using hh
  · intro hg
    let r : leechVectorStabilizer firstShapeStabilizer (minimumPairPlus i j) :=
      ⟨⟨g.val,monomial_le_firstShapeStabilizer hg⟩,g.prop⟩
    have hx := firstShape_point_orbit_mem i j hij _ (MulAction.mem_orbit _ r)
    rcases four_orthogonal_partition i j hij _ hx.1 hx.2 with hp | hz
    · exact hp
    · exact (firstShape_no_disjoint_fusion i j hij r hz).elim

def orthogonalLineMonomialEquiv (i j : Omega) (hij : i ≠ j) :
    orthogonalLineStabilizer i j ≃* leechVectorStabilizer monomialSubgroup (minimumPairPlus i j) where
  toFun g := ⟨⟨g.val.val,by
    exact (le_of_eq (orthogonalLineStabilizer_eq_monomial i j hij)) g.prop⟩,g.val.prop⟩
  invFun g := ⟨⟨g.val.val,g.prop⟩,by
    rw [orthogonalLineStabilizer_eq_monomial i j hij]
    exact g.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Atlas.Conway
