import Atlas.LinearGroups.ReeF4.SpecialOppositePairs
import Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity
import Atlas.LinearGroups.ReeF4.PositiveRootPointAction
import Atlas.LinearGroups.ReeF4.SpecialOppositeAction
import Atlas.LinearGroups.ReeF4.SpecialPointTransitivity

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The existing U action restricted to the actual projective opposite-point set. -/
instance positiveRootOppositeAction {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    MulAction (positiveRootSubgroup hcard) (OppositeSpecialPoints (F := F) m) where
  smul g p := ⟨g.val • p.val,by
    have h := (specialOpposite_model_iff m g.val (firstSpecialPoint m) p.val).mpr p.property
    simpa only [positiveRootSubgroup_fixes_firstSpecialPoint hcard g] using h⟩
  one_smul p := by apply Subtype.ext; exact one_smul (Model F m) p.val
  mul_smul g h p := by apply Subtype.ext; exact mul_smul g.val h.val p.val

@[simp] theorem positiveRootOppositeAction_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (g : positiveRootSubgroup hcard) (p : OppositeSpecialPoints (F := F) m) :
    (g • p).val=g.val • p.val := rfl

theorem chart9ToOpposite_equivariant {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (g : positiveRootSubgroup hcard) (z : NormalizedSpecialChart (F := F) m 9) :
    chart9ToOpposite m (g • z)=g • chart9ToOpposite m z := by
  apply Subtype.ext
  exact (specialPointMk_smul m g.val z.val z.property.1).symm

theorem positiveRoot_oppositePoint_transitive {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (p q : OppositeSpecialPoints (F := F) m) :
    ∃ g : positiveRootSubgroup hcard, g • p=q := by
  obtain ⟨u,rfl⟩ := chart9ToOpposite_surjective m p
  obtain ⟨v,rfl⟩ := chart9ToOpposite_surjective m q
  obtain ⟨g,hg⟩ := positiveRoot_chart9_transitive hcard u v
  have he : g • u=v := Subtype.ext hg
  refine ⟨g,?_⟩
  rw [←chart9ToOpposite_equivariant hcard,he]

theorem positiveRoot_oppositePoint_pretransitive {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    MulAction.IsPretransitive (positiveRootSubgroup hcard) (OppositeSpecialPoints (F := F) m) where
  exists_smul_eq := positiveRoot_oppositePoint_transitive hcard

theorem elementary_oppositePair_to_base {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : SpecialOppositePairs (F := F) m) :
    ∃ g : elementarySubgroup hcard, g.val • p=baseSpecialOppositePair m := by
  obtain ⟨a,ha⟩ := elementary_specialPoint_transitive hcard p.val.1 (firstSpecialPoint m)
  have hb : SpecialOpposite m (firstSpecialPoint m) (a.val • p.val.2) := by
    have h := (specialOpposite_model_iff m a.val p.val.1 p.val.2).mpr p.property
    simpa only [ha] using h
  obtain ⟨u,hu⟩ := positiveRoot_oppositePoint_transitive hcard
    ⟨a.val • p.val.2,hb⟩ ⟨oppositeSpecialPoint m,first_opposite_specialOpposite m⟩
  refine ⟨⟨u.val*a.val,(elementarySubgroup hcard).mul_mem
    (positiveRootSubgroup_le_elementary hcard u.property) a.property⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (u.val*a.val) • p.val.1=firstSpecialPoint m
    rw [mul_smul,ha]
    exact positiveRootSubgroup_fixes_firstSpecialPoint hcard u
  · change (u.val*a.val) • p.val.2=oppositeSpecialPoint m
    rw [mul_smul]
    exact congrArg Subtype.val hu


theorem model_oppositePair_to_base {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : SpecialOppositePairs (F := F) m) :
    ∃ g : Model F m, g • p=baseSpecialOppositePair m := by
  obtain ⟨g,hg⟩ := elementary_oppositePair_to_base hcard p
  exact ⟨g.val,hg⟩

theorem elementary_specialOppositePair_transitive {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (p q : SpecialOppositePairs (F := F) m) :
    ∃ g : elementarySubgroup hcard, g.val • p=q := by
  obtain ⟨a,ha⟩ := elementary_oppositePair_to_base hcard p
  obtain ⟨b,hb⟩ := elementary_oppositePair_to_base hcard q
  refine ⟨b⁻¹*a,?_⟩
  change (b.val⁻¹*a.val) • p=q
  rw [mul_smul,ha,←hb,inv_smul_smul]

/-- Ordered opposite-pair transitivity, independently of any group-order premise. -/
theorem model_specialOppositePairs_pretransitive {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    MulAction.IsPretransitive (Model F m) (SpecialOppositePairs (F := F) m) where
  exists_smul_eq p q := by
    obtain ⟨a,ha⟩ := model_oppositePair_to_base hcard p
    obtain ⟨b,hb⟩ := model_oppositePair_to_base hcard q
    refine ⟨b⁻¹*a,?_⟩
    rw [mul_smul,ha,←hb,inv_smul_smul]

end Atlas.ReeF4
