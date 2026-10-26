import Atlas.LinearGroups.Chevalley.RootData.ParabolicLengthAdditivity
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! Restricting an actual standard parabolic to an embedded root system.
The root embedding and its simple-reflection covariance are explicit inputs;
faithfulness follows from actual parabolic length, not a presentation or order. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N ι' M' N' : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
  (Q : RootPairing ι' ℤ M' N') [Q.IsCrystallographic] [Q.IsReduced] (c : Q.Base)

/-- An actual parabolic element fixing its selected simple roots is the identity. -/
theorem rootParabolic_eq_one_of_fixes_simple (J : Finset b.support)
    (w : P.weylGroupToPerm.range) (hw : w ∈ rootParabolicSubgroup P b J)
    (hfix : ∀ i ∈ J, w.val i.val = i.val) : w = 1 := by
  have hp : ∀ i ∈ J, b.IsPos (w.val i.val) := by
    intro i hi
    rw [hfix i hi]
    exact b.isPos_of_mem_support i.property
  have hl := rootWeylLength_mul_parabolic_of_simple_positive P b J w hp w⁻¹
    ((rootParabolicSubgroup P b J).inv_mem hw)
  simp only [mul_inv_cancel, rootWeylLength_one, rootWeylLength_inv] at hl
  apply (rootWeylLength_eq_zero_iff P b w).mp
  omega

variable (e : ι ↪ ι') (k : b.support → c.support) (J : Finset c.support)
  (hJ : ∀ j, j ∈ J ↔ ∃ i, k i = j)
  (hreflect : ∀ i : b.support, ∀ β : ι,
    e (P.reflectionPerm i.val β) = Q.reflectionPerm (k i).val (e β))

include hJ hreflect in
private theorem exists_root_restriction (w : Q.weylGroupToPerm.range)
    (hw : w ∈ rootParabolicSubgroup Q c J) :
    ∃ v : P.weylGroupToPerm.range, ∀ β, e (v.val β) = w.val (e β) := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, rfl⟩ := hg
    obtain ⟨i, rfl⟩ := (hJ j).mp hj
    exact ⟨simpleWeylReflection P b i, hreflect i⟩
  | one => exact ⟨1, fun _ => rfl⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨u, hu⟩ := ihg
    obtain ⟨v, hv⟩ := ihh
    refine ⟨u * v, ?_⟩
    intro β
    change e (u.val (v.val β)) = g.val (h.val (e β))
    rw [hu, hv]
  | inv g hg ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨v⁻¹, ?_⟩
    intro β
    apply g.val.injective
    change g.val (e (v.val.symm β)) = g.val (g.val.symm (e β))
    rw [← hv]
    simp only [Equiv.apply_symm_apply]

private def rootRestrictionValue (w : rootParabolicSubgroup Q c J) :
    P.weylGroupToPerm.range :=
  Classical.choose (exists_root_restriction P b Q c e k J hJ hreflect w.val w.property)

private theorem rootRestrictionValue_spec (w : rootParabolicSubgroup Q c J) (β : ι) :
    e ((rootRestrictionValue P b Q c e k J hJ hreflect w).val β) =
      w.val.val (e β) :=
  Classical.choose_spec
    (exists_root_restriction P b Q c e k J hJ hreflect w.val w.property) β

/-- The literal ambient parabolic acts on the embedded actual roots. -/
def rootParabolicRestriction : rootParabolicSubgroup Q c J →* P.weylGroupToPerm.range where
  toFun := rootRestrictionValue P b Q c e k J hJ hreflect
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro β
    apply e.injective
    exact rootRestrictionValue_spec P b Q c e k J hJ hreflect 1 β
  map_mul' x y := by
    apply Subtype.ext
    apply Equiv.ext
    intro β
    apply e.injective
    change e ((rootRestrictionValue P b Q c e k J hJ hreflect (x * y)).val β) =
      e ((rootRestrictionValue P b Q c e k J hJ hreflect x).val
        ((rootRestrictionValue P b Q c e k J hJ hreflect y).val β))
    rw [rootRestrictionValue_spec, rootRestrictionValue_spec, rootRestrictionValue_spec]
    rfl

theorem rootParabolicRestriction_apply (w : rootParabolicSubgroup Q c J) (β : ι) :
    e ((rootParabolicRestriction P b Q c e k J hJ hreflect w).val β) =
      w.val.val (e β) :=
  rootRestrictionValue_spec P b Q c e k J hJ hreflect w β

theorem rootParabolicRestriction_simple (i : b.support) :
    rootParabolicRestriction P b Q c e k J hJ hreflect
        ⟨simpleWeylReflection Q c (k i),
          Subgroup.subset_closure ⟨k i, (hJ (k i)).mpr ⟨i, rfl⟩, rfl⟩⟩ =
      simpleWeylReflection P b i := by
  apply Subtype.ext
  apply Equiv.ext
  intro β
  apply e.injective
  rw [rootParabolicRestriction_apply]
  exact (hreflect i β).symm

theorem rootParabolicRestriction_injective
    (hsimple : ∀ i : b.support, e i.val = (k i).val) :
    Function.Injective (rootParabolicRestriction P b Q c e k J hJ hreflect) := by
  intro x y h
  have hxy (i : b.support) : x.val.val (k i).val = y.val.val (k i).val := by
    have hi := congrArg (fun v : P.weylGroupToPerm.range => e (v.val i.val)) h
    simpa only [rootParabolicRestriction_apply, hsimple] using hi
  have hz : x.val⁻¹ * y.val = 1 := by
    apply rootParabolic_eq_one_of_fixes_simple Q c J _
      ((rootParabolicSubgroup Q c J).mul_mem
        ((rootParabolicSubgroup Q c J).inv_mem x.property) y.property)
    intro j hj
    obtain ⟨i, rfl⟩ := (hJ j).mp hj
    change x.val.val.symm (y.val.val (k i).val) = (k i).val
    rw [← hxy i]
    exact x.val.val.symm_apply_apply _
  apply Subtype.ext
  exact inv_mul_eq_one.mp hz

theorem rootParabolicRestriction_surjective :
    Function.Surjective (rootParabolicRestriction P b Q c e k J hJ hreflect) := by
  let f := rootParabolicRestriction P b Q c e k J hJ hreflect
  have hs (i : b.support) : simpleWeylReflection P b i ∈ f.range :=
    ⟨⟨simpleWeylReflection Q c (k i),
      Subgroup.subset_closure ⟨k i, (hJ (k i)).mpr ⟨i, rfl⟩, rfl⟩⟩,
      rootParabolicRestriction_simple P b Q c e k J hJ hreflect i⟩
  have hl (l : List b.support) : rootWeylWord P b l ∈ f.range := by
    induction l with
    | nil => exact f.range.one_mem
    | cons i l ih => exact f.range.mul_mem (hs i) ih
  intro v
  obtain ⟨l, _, he⟩ := rootWeylLength_spec P b v
  have he' : rootWeylWord P b l = v := by
    apply Subtype.ext
    simpa only [rootWeylWord_val] using he
  exact he' ▸ hl l

/-- An actual embedded root system identifies the selected ambient parabolic. -/
def rootParabolicRestrictionEquiv
    (hsimple : ∀ i : b.support, e i.val = (k i).val) :
    rootParabolicSubgroup Q c J ≃* P.weylGroupToPerm.range :=
  MulEquiv.ofBijective (rootParabolicRestriction P b Q c e k J hJ hreflect)
    ⟨rootParabolicRestriction_injective P b Q c e k J hJ hreflect hsimple,
      rootParabolicRestriction_surjective P b Q c e k J hJ hreflect⟩

end Atlas.Chevalley.RootData
