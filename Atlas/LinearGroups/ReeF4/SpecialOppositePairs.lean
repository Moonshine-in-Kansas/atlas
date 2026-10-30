import Atlas.LinearGroups.ReeF4.SpecialOppositeAction

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem first_opposite_specialOpposite (m : ℕ) :
    SpecialOpposite m (firstSpecialPoint (F := F) m) (oppositeSpecialPoint m) := by
  apply (specialOpposite_mk_iff m _ _ (isSpecialVector_firstRoot m) (isSpecialVector_oppositeRoot m)).mpr
  rw [first_opposite_polar]
  exact one_ne_zero

/-- An actual ordered opposite pair, with the inherited intrinsic Model action. -/
abbrev SpecialOppositePairs (m : ℕ) :=
  {pq : SpecialPoints (F := F) m × SpecialPoints (F := F) m // SpecialOpposite m pq.1 pq.2}

instance specialOppositePairsAction (m : ℕ) :
    MulAction (Model F m) (SpecialOppositePairs (F := F) m) where
  smul g p := ⟨(g • p.val.1,g • p.val.2),
    (specialOpposite_model_iff m g p.val.1 p.val.2).mpr p.property⟩
  one_smul p := by apply Subtype.ext; exact Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul g h p := by apply Subtype.ext; exact Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)

def baseSpecialOppositePair (m : ℕ) : SpecialOppositePairs (F := F) m :=
  ⟨(firstSpecialPoint m,oppositeSpecialPoint m),first_opposite_specialOpposite m⟩

end Atlas.ReeF4
