import Atlas.Conway.EisensteinFrameScalarQuotient

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

abbrev EisensteinScalarParameters := Multiplicative (ZMod 2) × Multiplicative (ZMod 3)

def eisensteinConstantCodeHom : Multiplicative (ZMod 3) →* Multiplicative ternaryGolay where
  toFun a := Multiplicative.ofAdd (a.toAdd • ternaryOne)
  map_one' := congrArg Multiplicative.ofAdd (zero_smul _ _)
  map_mul' a b := congrArg Multiplicative.ofAdd (add_smul a.toAdd b.toAdd ternaryOne)

def eisensteinScalarAbstractHom : EisensteinScalarParameters →* EisensteinFrameAbstractGroup :=
  (MonoidHom.id _).prodMap (SemidirectProduct.inl.comp eisensteinConstantCodeHom)

def eisensteinScalarFrameHom : EisensteinScalarParameters →* eisensteinCoordinateFrameStabilizer :=
  eisensteinFrameGroupHom.comp eisensteinScalarAbstractHom

/-- The six scalar isometries, before passing to the centralizer in Co0. -/
def eisensteinScalarHom : EisensteinScalarParameters →* eisensteinHermitianGroup :=
  eisensteinFrameAbstractHom.comp eisensteinScalarAbstractHom

theorem eisensteinScalarAbstractHom_injective : Function.Injective eisensteinScalarAbstractHom := by
  intro a b h
  refine Prod.ext (show a.1 = b.1 from congrArg (fun x : EisensteinFrameAbstractGroup => x.1) h) ?_
  apply Multiplicative.toAdd.injective
  have he := congrArg (fun x : EisensteinFrameAbstractGroup => x.2.left.toAdd.val 0) h
  simpa [eisensteinScalarAbstractHom,eisensteinConstantCodeHom,ternaryOne] using he

theorem eisensteinScalarFrameHom_injective : Function.Injective eisensteinScalarFrameHom :=
  eisensteinFrameGroupHom_bijective.1.comp eisensteinScalarAbstractHom_injective

theorem eisensteinScalarHom_injective : Function.Injective eisensteinScalarHom := by
  intro a b h
  apply eisensteinScalarFrameHom_injective
  exact Subtype.ext h

def eisensteinScalarSubgroup : Subgroup eisensteinHermitianGroup := eisensteinScalarHom.range

def eisensteinFrameScalarSubgroup : Subgroup eisensteinCoordinateFrameStabilizer := eisensteinScalarFrameHom.range

theorem eisensteinScalarSubgroup_order : Nat.card eisensteinScalarSubgroup = 6 := by
  rw [show Nat.card eisensteinScalarSubgroup = Nat.card EisensteinScalarParameters from
    Nat.card_congr (MonoidHom.ofInjective eisensteinScalarHom_injective).toEquiv.symm]
  rw [Nat.card_prod]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),Nat.card_zmod]
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),Nat.card_zmod]
  rw [h2,h3]

theorem eisensteinFrameScalarSubgroup_order : Nat.card eisensteinFrameScalarSubgroup = 6 := by
  rw [show Nat.card eisensteinFrameScalarSubgroup = Nat.card EisensteinScalarParameters from
    Nat.card_congr (MonoidHom.ofInjective eisensteinScalarFrameHom_injective).toEquiv.symm]
  exact (Nat.card_congr (MonoidHom.ofInjective eisensteinScalarHom_injective).toEquiv).trans
    eisensteinScalarSubgroup_order

theorem eisensteinFramePhaseQuotient_ker : eisensteinFramePhaseQuotient.ker = eisensteinFrameScalarSubgroup := by
  ext x
  let a := eisensteinFullFrameGroupEquiv.symm x
  have ha : eisensteinFrameGroupHom a = x := eisensteinFullFrameGroupEquiv.apply_symm_apply x
  change eisensteinAbstractPhaseQuotient a = 1 ↔ ∃ b, eisensteinScalarFrameHom b = x
  rw [← MonoidHom.mem_ker,eisensteinAbstractPhaseQuotient_kernel]
  constructor
  · rintro ⟨ht,hg⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp ht
    refine ⟨(a.1,Multiplicative.ofAdd c),?_⟩
    change eisensteinFrameGroupHom (eisensteinScalarAbstractHom (a.1,Multiplicative.ofAdd c)) = x
    rw [← ha]
    congr 1
    refine Prod.ext rfl (SemidirectProduct.ext ?_ hg.symm)
    exact congrArg Multiplicative.ofAdd hc
  · rintro ⟨b,hb⟩
    have hab : eisensteinScalarAbstractHom b = a :=
      eisensteinFrameGroupHom_bijective.1 (hb.trans ha.symm)
    rw [← hab]
    exact ⟨Submodule.mem_span_singleton.mpr ⟨b.2.toAdd,rfl⟩,rfl⟩


def eisensteinScalarCoefficient (a : EisensteinScalarParameters) : Eisenstein :=
  eisensteinSignedPhase (decide (a.1.toAdd ≠ 0)) a.2.toAdd

theorem eisensteinScalarHom_apply (a : EisensteinScalarParameters)
    (z : EisensteinRationalCoordinates) :
    (eisensteinScalarHom a).val z = eisensteinToRational (eisensteinScalarCoefficient a) • z := by
  change (eisensteinFrameAbstractHom (eisensteinScalarAbstractHom a)).val z = _
  rw [eisensteinFrameAbstractHom_parameters]
  funext i
  rw [eisensteinMonomialParameterIsometry_apply]
  simp [eisensteinAbstractParameters,eisensteinScalarAbstractHom,eisensteinConstantCodeHom,
    eisensteinScalarCoefficient,ternaryOne, Equiv.Perm.one_def]

theorem eisensteinScalarHom_commutes (a : EisensteinScalarParameters) (f : eisensteinHermitianGroup) :
    eisensteinScalarHom a * f = f * eisensteinScalarHom a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change (eisensteinScalarHom a).val (f.val z) = f.val ((eisensteinScalarHom a).val z)
  rw [eisensteinScalarHom_apply,eisensteinScalarHom_apply]
  exact (f.prop.1 _ _).symm

theorem eisensteinScalarSubgroup_le_center : eisensteinScalarSubgroup ≤ Subgroup.center eisensteinHermitianGroup := by
  rintro x ⟨a,rfl⟩
  exact Subgroup.mem_center_iff.mpr (fun f => (eisensteinScalarHom_commutes a f).symm)

instance eisensteinScalarSubgroup_normal : eisensteinScalarSubgroup.Normal :=
  ⟨fun x hx g => by
    rw [(Subgroup.mem_center_iff.mp (eisensteinScalarSubgroup_le_center hx)) g]
    simpa [mul_assoc] using hx⟩

instance eisensteinFrameScalarSubgroup_normal : eisensteinFrameScalarSubgroup.Normal := by
  rw [← eisensteinFramePhaseQuotient_ker]
  infer_instance

/-- The full frame stabilizer modulo its six actual scalar isometries is
precisely the previously constructed five-dimensional phase semidirect product. -/
def eisensteinFrameModuloScalarsEquiv :
    eisensteinCoordinateFrameStabilizer ⧸ eisensteinFrameScalarSubgroup ≃* TernaryLocalPhaseGroup :=
  (QuotientGroup.quotientMulEquivOfEq eisensteinFramePhaseQuotient_ker.symm).trans
    eisensteinFramePhaseQuotientEquiv

theorem eisensteinFrameModuloScalars_order :
    Nat.card (eisensteinCoordinateFrameStabilizer ⧸ eisensteinFrameScalarSubgroup) = 1924560 :=
  (Nat.card_congr eisensteinFrameModuloScalarsEquiv.toEquiv).trans ternaryLocalPhaseGroup_order


def eisensteinScalarUnitHom : EisensteinScalarParameters →* Eisensteinˣ where
  toFun a := eisensteinSignedPhaseUnit (decide (a.1.toAdd ≠ 0)) a.2.toAdd
  map_one' := by apply Units.ext; rfl
  map_mul' := by
    intro a b
    apply Units.ext
    have h : ∀ a b : EisensteinScalarParameters,
        eisensteinScalarCoefficient (a*b) = eisensteinScalarCoefficient a * eisensteinScalarCoefficient b := by
      decide +kernel
    simpa only [Units.val_mul,eisensteinSignedPhaseUnit_val,eisensteinScalarCoefficient] using h a b

theorem eisensteinScalarUnitHom_injective : Function.Injective eisensteinScalarUnitHom := by
  intro a b h
  have hc : eisensteinScalarCoefficient a = eisensteinScalarCoefficient b := by
    simpa only [eisensteinScalarUnitHom,MonoidHom.coe_mk,OneHom.coe_mk,eisensteinSignedPhaseUnit_val,eisensteinScalarCoefficient] using congrArg Units.val h
  have he := eisensteinSignedPhase_injective (a₁ := (decide (a.1.toAdd ≠ 0),a.2.toAdd))
    (a₂ := (decide (b.1.toAdd ≠ 0),b.2.toAdd)) hc
  have h2 : Function.Injective (fun x : ZMod 2 => decide (x≠0)) := by decide
  refine Prod.ext ?_ ?_
  · exact Multiplicative.toAdd.injective (h2 (congrArg (fun x : Bool × ZMod 3 => x.1) he))
  · exact Multiplicative.toAdd.injective (congrArg (fun x : Bool × ZMod 3 => x.2) he)

theorem eisensteinScalarUnitHom_surjective : Function.Surjective eisensteinScalarUnitHom := by
  letI : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; decide)
  have hc : Nat.card EisensteinScalarParameters = Nat.card Eisensteinˣ := by
    rw [eisenstein_units_card]
    exact (Nat.card_congr (MonoidHom.ofInjective eisensteinScalarHom_injective).toEquiv).trans
      eisensteinScalarSubgroup_order
  exact (Nat.bijective_iff_injective_and_card eisensteinScalarUnitHom).mpr
    ⟨eisensteinScalarUnitHom_injective,hc⟩ |>.2

/-- All Eisenstein units, with their multiplication, are the six scalar parameters. -/
def eisensteinScalarUnitEquiv : EisensteinScalarParameters ≃* Eisensteinˣ :=
  MulEquiv.ofBijective eisensteinScalarUnitHom
    ⟨eisensteinScalarUnitHom_injective,eisensteinScalarUnitHom_surjective⟩

/-- The full scalar-unit hom into the actual Hermitian lattice isometry group. -/
def eisensteinUnitIsometries : Eisensteinˣ →* eisensteinHermitianGroup :=
  eisensteinScalarHom.comp eisensteinScalarUnitEquiv.symm.toMonoidHom

theorem eisensteinUnitIsometries_apply (u : Eisensteinˣ) (z : EisensteinRationalCoordinates) :
    (eisensteinUnitIsometries u).val z = eisensteinToRational (u : Eisenstein) • z := by
  rw [show eisensteinUnitIsometries u = eisensteinScalarHom (eisensteinScalarUnitEquiv.symm u) from rfl,
    eisensteinScalarHom_apply]
  have hu := congrArg Units.val (eisensteinScalarUnitEquiv.apply_symm_apply u)
  have hu' : eisensteinScalarCoefficient (eisensteinScalarUnitEquiv.symm u) = (u : Eisenstein) := by
    simpa only [eisensteinScalarUnitEquiv,MulEquiv.ofBijective_apply,eisensteinScalarUnitHom,MonoidHom.coe_mk,OneHom.coe_mk,eisensteinSignedPhaseUnit_val,eisensteinScalarCoefficient] using hu
  exact congrArg (fun c => eisensteinToRational c • z) hu'

theorem eisensteinFrameModuloScalars_perfect :
    Group.IsPerfect (eisensteinCoordinateFrameStabilizer ⧸ eisensteinFrameScalarSubgroup) := by
  letI := ternaryLocalPhaseGroup_perfect
  exact Group.IsPerfect.ofSurjective (f := eisensteinFrameModuloScalarsEquiv.symm.toMonoidHom) eisensteinFrameModuloScalarsEquiv.symm.surjective

/-- The same scalar subgroup in the actual Co0 centralizer. -/
def eisensteinCentralizerScalars : Subgroup eisensteinCentralizer :=
  eisensteinScalarSubgroup.map eisensteinCentralizerEquiv.toMonoidHom


theorem eisensteinCentralizerScalars_order : Nat.card eisensteinCentralizerScalars = 6 :=
  (Nat.card_congr (eisensteinScalarSubgroup.equivMapOfInjective
    eisensteinCentralizerEquiv.toMonoidHom eisensteinCentralizerEquiv.injective).toEquiv.symm).trans
      eisensteinScalarSubgroup_order

theorem eisensteinCentralizerScalars_le_center :
    eisensteinCentralizerScalars ≤ Subgroup.center eisensteinCentralizer := by
  rintro x ⟨y,hy,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨f,rfl⟩ := eisensteinCentralizerEquiv.surjective g
  change eisensteinCentralizerEquiv f * eisensteinCentralizerEquiv y =
    eisensteinCentralizerEquiv y * eisensteinCentralizerEquiv f
  rw [← map_mul,← map_mul]
  exact congrArg eisensteinCentralizerEquiv (Subgroup.mem_center_iff.mp (eisensteinScalarSubgroup_le_center hy) f)

instance eisensteinCentralizerScalars_normal : eisensteinCentralizerScalars.Normal :=
  ⟨fun x hx g => by
    rw [(Subgroup.mem_center_iff.mp (eisensteinCentralizerScalars_le_center hx)) g]
    simpa [mul_assoc] using hx⟩

theorem eisensteinUnitIsometries_Co0_agrees (u : Eisensteinˣ) (z : EisensteinRationalCoordinates) :
    (fullIsometryEquiv (eisensteinCentralizerEquiv (eisensteinUnitIsometries u)).val).val
      (eisensteinComparison z) = eisensteinComparison (eisensteinToRational (u : Eisenstein) • z) := by
  rw [eisensteinCentralizerEquiv_agrees,eisensteinUnitIsometries_apply]


theorem eisensteinUnitIsometries_range : eisensteinUnitIsometries.range = eisensteinScalarSubgroup := by
  ext f
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨eisensteinScalarUnitEquiv.symm u,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨eisensteinScalarUnitEquiv a,?_⟩
    change eisensteinScalarHom (eisensteinScalarUnitEquiv.symm (eisensteinScalarUnitEquiv a)) = _
    rw [MulEquiv.symm_apply_apply]

theorem eisensteinFrameScalarSubgroup_comap :
    eisensteinScalarSubgroup.comap eisensteinCoordinateFrameStabilizer.subtype =
      eisensteinFrameScalarSubgroup := by
  ext x
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a,rfl⟩

end Atlas.Conway
