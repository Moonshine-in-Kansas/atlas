import Atlas.GroupTheory.IwasawaStabilizer
import Mathlib.GroupTheory.Abelianization.Defs

namespace Atlas.GroupTheory
open scoped commutatorElement
open scoped IsMulCommutative

/-- The local Iwasawa argument also applies when the conjugates generate only
 a perfect normal subgroup, rather than the entire ambient group. -/
theorem normalClosure_le_normal_sup_local {G X : Type*} [Group G] [MulAction G X]
    (a : X) (A : Subgroup G) (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal)
    (L : Subgroup G) [L.Normal] [MulAction.IsPretransitive L X] :
    Subgroup.normalClosure (A : Set G) ≤ L ⊔ A := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨b,hb,hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g,rfl⟩ := isConj_iff.mp hbx
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq L a (g • a)
  let s : MulAction.stabilizer G a := ⟨n.val⁻¹*g,by
    change (n.val⁻¹*g) • a = a
    rw [mul_smul,← hn]
    exact inv_smul_smul n.val a⟩
  let b' : MulAction.stabilizer G a := ⟨b,hA hb⟩
  have hs : s*b'*s⁻¹ ∈ A.subgroupOf (MulAction.stabilizer G a) :=
    hAn.conj_mem b' hb s
  have hsa : s.val*b*s.val⁻¹ ∈ A := hs
  have he : g*b*g⁻¹ = n.val * (s.val*b*s.val⁻¹) * n.val⁻¹ := by
    dsimp [s]; group
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.prop)
    (Subgroup.mem_sup_right hsa)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left n.prop))

/-- An abelian local subgroup contributes nothing to the derived quotient. -/
theorem commutator_normal_sup_abelian_le {G : Type*} [Group G]
    (L A : Subgroup G) [L.Normal] (hAc : IsMulCommutative A) : ⁅L ⊔ A,L ⊔ A⁆ ≤ L := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨n,hn,a,ha,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨m,hm,b,hb,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  let q := QuotientGroup.mk' L
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅n*a,m*b⁆ = 1
  rw [map_commutatorElement, map_mul, map_mul,
    show q n = 1 from (QuotientGroup.eq_one_iff _).mpr hn,
    show q m = 1 from (QuotientGroup.eq_one_iff _).mpr hm, one_mul, one_mul]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  rw [← map_mul, ← map_mul]
  congr 1
  letI := hAc
  exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) ⟨b,hb⟩)

/-- In a faithful primitive action, a perfect normal closure of an abelian
normal subgroup of a point stabilizer is contained in every nontrivial normal subgroup. -/
theorem perfect_normalClosure_minimal {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X]
    (a : X) (A : Subgroup G) (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal)
    (hAc : IsMulCommutative A)
    [Group.IsPerfect (Subgroup.normalClosure (A : Set G))]
    (L : Subgroup G) [L.Normal] (hne : L ≠ ⊥) :
    Subgroup.normalClosure (A : Set G) ≤ L := by
  letI := normal_pretransitive (X := X) L hne
  have h := normalClosure_le_normal_sup_local a A hA hAn L
  rw [← Subgroup.commutator_eq_self (H := Subgroup.normalClosure (A : Set G))]
  exact (Subgroup.commutator_mono h h).trans (commutator_normal_sup_abelian_le L A hAc)

end Atlas.GroupTheory
