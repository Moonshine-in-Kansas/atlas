import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Group

/-! Transporting a subgroup normalized by a point stabilizer. These constructions
use only transitivity and local normality, independently of any group family. -/
noncomputable section
namespace Atlas.GroupTheory.LocalTransport
open scoped Pointwise
variable {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
variable (a : X) (R : Subgroup G)

def transporter (x : X) : G := (MulAction.exists_smul_eq G a x).choose

theorem transporter_action (x : X) : transporter (G:=G) a x • a=x :=
  (MulAction.exists_smul_eq G a x).choose_spec

def localAt (x : X) : Subgroup G := MulAut.conj (transporter (G:=G) a x) • R

def localEquiv (x : X) : R ≃* localAt a R x :=
  R.equivMapOfInjective (MulAut.conj (transporter (G:=G) a x)).toMonoidHom
    (MulAut.conj (transporter (G:=G) a x)).injective

theorem card_localAt (x : X) : Nat.card (localAt a R x)=Nat.card R :=
  (Nat.card_congr (localEquiv a R x).toEquiv).symm

theorem localAt_solvable [Group.IsSolvable R] (x : X) :
    Group.IsSolvable (localAt a R x) :=
  Group.isSolvable_of_surjective (f := (localEquiv a R x).toMonoidHom) (localEquiv a R x).surjective

variable (hN : MulAction.stabilizer G a ≤ Subgroup.normalizer (R : Set G))

include hN in
theorem conjugate_eq {g h : G} (he : g • a=h • a) :
    MulAut.conj g • R=MulAut.conj h • R := by
  have hk : h⁻¹*g∈MulAction.stabilizer G a := by
    change (h⁻¹*g) • a=a
    rw [mul_smul,he,inv_smul_smul]
  have hn : MulAut.conj (h⁻¹*g) • R=R := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hN hk) b).mp hb
    · intro hx
      refine ⟨(h⁻¹*g)⁻¹*x*(h⁻¹*g),?_,?_⟩
      · exact (Subgroup.mem_normalizer_iff''.mp (hN hk) x).mp hx
      · change (h⁻¹*g)*((h⁻¹*g)⁻¹*x*(h⁻¹*g))*(h⁻¹*g)⁻¹=x
        group
  have heq : g=h*(h⁻¹*g) := by group
  rw [heq,map_mul,mul_smul,hn]

include hN in
theorem localAt_eq_of_transport (x : X) (g : G) (hg : g • a=x) :
    localAt a R x=MulAut.conj g • R :=
  conjugate_eq a R hN ((transporter_action a x).trans hg.symm)

include hN in
theorem localAt_base : localAt a R a=R := by
  rw [localAt_eq_of_transport a R hN a 1 (one_smul _ _)]
  simp

include hN in
theorem localAt_conj (g : G) (x : X) :
    localAt a R (g • x)=MulAut.conj g • localAt a R x := by
  rw [localAt_eq_of_transport a R hN (g • x) (g*transporter (G:=G) a x)
    (by rw [mul_smul,transporter_action]),map_mul,mul_smul]
  rfl

variable (hR : R ≤ MulAction.stabilizer G a)

include hR in
theorem localAt_le_stabilizer (x : X) : localAt a R x ≤ MulAction.stabilizer G x := by
  rintro g ⟨b,hb,rfl⟩
  change (transporter (G:=G) a x*b*(transporter (G:=G) a x)⁻¹) • x=x
  have he : (transporter (G:=G) a x*b*(transporter (G:=G) a x)⁻¹) • (transporter (G:=G) a x • a)=
      transporter (G:=G) a x • a := by
    rw [mul_smul,mul_smul,inv_smul_smul]
    rw [show b • a=a from hR hb]
  simpa only [transporter_action] using he

include hN hR in
theorem localAt_normal (x : X) :
    ((localAt a R x).subgroupOf (MulAction.stabilizer G x)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (localAt_le_stabilizer a R hR x)).mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg b hb
  have hc : MulAut.conj g • localAt a R x=localAt a R x := by
    rw [←localAt_conj a R hN,MulAction.mem_stabilizer_iff.mp hg]
  rw [←hc]
  exact ⟨b,hb,rfl⟩

include hN in
theorem localAt_iSup_eq_normalClosure :
    (⨆x : X,localAt a R x)=Subgroup.normalClosure (R : Set G) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    rintro g ⟨b,hb,rfl⟩
    exact (inferInstance : (Subgroup.normalClosure (R : Set G)).Normal).conj_mem b
      (Subgroup.subset_normalClosure hb) (transporter (G:=G) a x)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨b,hb,hbg⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨k,rfl⟩ := isConj_iff.mp hbg
    apply le_iSup (localAt a R) (k • a)
    rw [localAt_eq_of_transport a R hN (k • a) k rfl]
    exact ⟨b,hb,rfl⟩

end Atlas.GroupTheory.LocalTransport
