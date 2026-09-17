import Atlas.Fischer.DoubleCentralizerModels

set_option maxHeartbeats 800000
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def doubleCoverSecondPoint (i j : Omega) (hij : i ≠ j) : ResiduePoint {i} :=
  residueBasicPoint {i} j (by simpa using hij.symm)

def doubleCoverCentralizerTarget (i j : Omega) (hij : i ≠ j) : Subgroup (ResidueGroup {i}) :=
  Subgroup.centralizer {residueDistinguishedElement {i} (doubleCoverSecondPoint i j hij)}

/-- Injectivity of the original distinguished class supplies the exact lift of a centralizer. -/
theorem doubleCentralizer_lift_iff (i j : Omega) (hij : i ≠ j)
    (a : residueCentralizer {i}) :
    QuotientGroup.mk' (residueCentralElementary {i}) a ∈ doubleCoverCentralizerTarget i j hij ↔
      a.val ∈ residueCentralizer {i,j} := by
  let x := doubleCoverSecondPoint i j hij
  let q := QuotientGroup.mk' (residueCentralElementary {i})
  constructor
  · intro ha
    have he : q a * residueDistinguishedElement {i} x * (q a)⁻¹ =
        residueDistinguishedElement {i} x := by
      have hc := ha _ (Set.mem_singleton _)
      change residueDistinguishedElement {i} x * q a = q a * residueDistinguishedElement {i} x at hc
      rw [← hc]
      group
    have hx : q a • x=x := residueDistinguished_injective {i} (by simp)
      ((residueDistinguishedElement_covariance {i} (q a) x).symm.trans he)
    have hj : a.val * distinguishedRootElement (.inl j) * a.val⁻¹ = distinguishedRootElement (.inl j) := by
      have h := congrArg Subtype.val hx
      exact (residueGroup_mk_smul_val {i} a x).symm.trans h
    apply (mem_markedPentadPointwise_iff _ _).mpr
    intro k hk
    rcases Finset.mem_insert.mp hk with hki | hk
    · subst k
      exact (mem_markedPentadPointwise_iff _ _).mp a.prop i (by simp)
    · have hk := Finset.mem_singleton.mp hk
      simpa only [hk] using hj
  · intro ha
    rintro z (rfl : z=residueDistinguishedElement {i} x)
    have hc := ha _ (show distinguishedRootElement (.inl j) ∈ residueBasicSet {i,j} from ⟨j,by simp,rfl⟩)
    have he : residuePointCentralizer {i} x * a = a * residuePointCentralizer {i} x := Subtype.ext hc
    exact congrArg q he

/-- Projection of the actual double centralizer onto the full quotient centralizer. -/
def doubleCentralizerTargetHom (i j : Omega) (hij : i ≠ j) :
    residueCentralizer {i,j} →* doubleCoverCentralizerTarget i j hij :=
  ((QuotientGroup.mk' (residueCentralElementary {i})).comp
    (doubleCentralizerInclusion i j)).codRestrict _ (fun a =>
      (doubleCentralizer_lift_iff i j hij _).mpr a.prop)

theorem doubleCentralizerTargetHom_surjective (i j : Omega) (hij : i ≠ j) :
    Function.Surjective (doubleCentralizerTargetHom i j hij) := by
  intro y
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (residueCentralElementary {i}) y.val
  have hm : a.val ∈ residueCentralizer {i,j} :=
    (doubleCentralizer_lift_iff i j hij a).mp (ha ▸ y.prop)
  exact ⟨⟨a.val,hm⟩,Subtype.ext ha⟩

theorem doubleCentralizerTargetHom_kernel (i j : Omega) (hij : i ≠ j) :
    (doubleCentralizerTargetHom i j hij).ker=doubleCentralizerFirstKernel i j := by
  ext a
  change (doubleCentralizerTargetHom i j hij a=1) ↔ a.val∈residueElementary {i}
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff (doubleCentralizerInclusion i j a)).mp
      (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (doubleCentralizerInclusion i j a)).mpr h

/-- The double cover is the actual full centralizer of the second residue involution. -/
def doubleCoverCentralizerEquiv (i j : Omega) (hij : i ≠ j) :
    FischerDoubleCover i j ≃* doubleCoverCentralizerTarget i j hij :=
  (QuotientGroup.quotientMulEquivOfEq (doubleCentralizerTargetHom_kernel i j hij).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (doubleCentralizerTargetHom_surjective i j hij))

end Atlas.Fischer
