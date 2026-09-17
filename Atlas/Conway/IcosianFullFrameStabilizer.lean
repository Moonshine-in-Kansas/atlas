import Atlas.Conway.IcosianFrameMonomial

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Pointwise

theorem icosianMonomialToHermitian_apply (g : icosianLiftedMonomial)
    (x : IcosianRationalCoordinates) (j : Fin 3) :
    (icosianMonomialToHermitian g • x) j=
      (icosianMonomialUnits (g.val.left j) : IcosianQuaternion)*x (g.val.right.symm j) := rfl

theorem icosianMonomial_axis (g : icosianLiftedMonomial) (i : Fin 3) :
    icosianMonomialToHermitian g • icosianAxisPoint i=icosianAxisPoint (g.val.right i) := by
  simp only [icosianAxisPoint,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (icosianMonomialUnits (g.val.left (g.val.right i)) : IcosianQuaternion),?_⟩
  funext j
  rw [icosianMonomialToHermitian_apply]
  by_cases hj : j=g.val.right i
  · subst j; simp [Pi.single_apply,MulOpposite.smul_eq_mul_unop]
  · have hj' : g.val.right.symm j≠i := by
      intro h; apply hj; simpa using congrArg g.val.right h
    simp [Pi.single_apply,hj,hj',MulOpposite.smul_eq_mul_unop]

theorem icosianMonomial_mem_frameStabilizer (g : icosianLiftedMonomial) :
    icosianMonomialToHermitian g∈icosianCoordinateFrameStabilizer := by
  change icosianMonomialToHermitian g • icosianCoordinateFrame=icosianCoordinateFrame
  apply Set.Subset.antisymm
  · rintro x ⟨y,⟨i,rfl⟩,rfl⟩
    change icosianMonomialToHermitian g • icosianAxisPoint i∈icosianCoordinateFrame
    rw [icosianMonomial_axis]
    exact ⟨_,rfl⟩
  · rintro x ⟨i,rfl⟩
    refine ⟨icosianAxisPoint (g.val.right.symm i),⟨_,rfl⟩,?_⟩
    simp [icosianMonomial_axis]

/-- Every isometry preserving the actual three quaternionic axes is one of the
integral unit monomial lifts of the full finite gluing stabilizer. -/
theorem icosianMonomial_range_eq_frameStabilizer :
    icosianMonomialToHermitian.range=icosianCoordinateFrameStabilizer := by
  apply le_antisymm
  · rintro f ⟨g,rfl⟩
    exact icosianMonomial_mem_frameStabilizer g
  · intro f hf
    refine ⟨⟨icosianFrameMonomial ⟨f,hf⟩,icosianFrameMonomial_mem ⟨f,hf⟩⟩,?_⟩
    apply Subtype.ext
    exact icosianFrameMonomial_representation ⟨f,hf⟩

theorem icosianCoordinateFrameStabilizer_card :
    Nat.card icosianCoordinateFrameStabilizer=2304 := by
  rw [← icosianMonomial_range_eq_frameStabilizer]
  exact icosianMonomialToHermitian_range_card

end Atlas.Conway
