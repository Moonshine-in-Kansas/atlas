import Atlas.LinearGroups.F4.ScalarRadicalNormalization
import Atlas.LinearGroups.F4.ParabolicKernelFactorization
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Normality of the actual radical in the full parabolic. Inside the normal
seven-dimensional action kernel it is a normal Sylow subgroup, hence characteristic.
Only the independent radical and scalar-kernel cardinalities are used. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def parabolicRadical : Subgroup (parabolicPointStabilizer (F:=F)) :=
  (radicalParabolicHom (F:=F)).range

theorem radicalParabolicHom_injective : Function.Injective (radicalParabolicHom (F:=F)) := by
  intro p q h
  apply radicalElement_injective
  exact congrArg (fun g : parabolicPointStabilizer (F:=F)=>g.val) h

theorem parabolicRadical_mem_iff (g : parabolicPointStabilizer (F:=F)) :
    g∈parabolicRadical ↔ g.val∈radicalSubgroup := by
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p,rfl⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

theorem parabolicRadical_le_kernel : parabolicRadical (F:=F) ≤ parabolicOrthogonalHom.ker := by
  rintro _ ⟨p,rfl⟩
  exact radicalParabolic_orthogonal p

theorem scalarParabolic_normalizes (a : Fˣ) :
    scalarParabolic a∈(Subgroup.normalizer (parabolicRadical (F:=F) : Set (parabolicPointStabilizer (F:=F)))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [parabolicRadical_mem_iff,parabolicRadical_mem_iff]
  exact (Subgroup.mem_normalizer_iff.mp (scalarTorus_normalizes_radical a)) g.val

theorem parabolicKernel_le_radical_normalizer :
    (parabolicOrthogonalHom (F:=F)).ker ≤ Subgroup.normalizer (parabolicRadical (F:=F) : Set (parabolicPointStabilizer (F:=F))) := by
  intro g hg
  obtain ⟨⟨p,a⟩,he⟩ := parabolicKernelFactorEquiv.surjective ⟨g,hg⟩
  have hh := congrArg Subtype.val he
  change radicalParabolicHom p*scalarParabolic a=g at hh
  rw [←hh]
  exact (Subgroup.normalizer (parabolicRadical (F:=F) : Set (parabolicPointStabilizer (F:=F)))).mul_mem
    (parabolicRadical.le_normalizer ⟨p,rfl⟩) (scalarParabolic_normalizes a)

theorem parabolicRadical_normal_in_kernel :
    ((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer parabolicRadical_le_kernel).mpr
    parabolicKernel_le_radical_normalizer

theorem parabolicRadical_card [Finite F] : Nat.card (parabolicRadical (F:=F))=Nat.card F^15 := by
  change Nat.card (Set.range (radicalParabolicHom (F:=F)))=_
  rw [Nat.card_range_of_injective radicalParabolicHom_injective]
  change Nat.card (Atlas.GroupTheory.BilinearExtension (radicalCocycle (F:=F)))=_
  rw [Atlas.GroupTheory.BilinearExtension.card]
  simp only [Nat.card_fun,Nat.card_fin]
  ring

theorem parabolicRadical_kernel_card [Finite F] :
    Nat.card ((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker)=Nat.card F^15 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe parabolicRadical_le_kernel).toEquiv,
    parabolicRadical_card]

theorem parabolicRadical_kernel_index [Finite F] :
    ((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker).index=Nat.card F-1 := by
  have h := ((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker).card_mul_index
  rw [parabolicRadical_kernel_card,card_parabolicOrthogonalHom_kernel] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 15) h

theorem parabolicRadical_characteristic_in_kernel [Finite F] :
    ((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker).Characteristic := by
  letI := Fintype.ofFinite F
  obtain ⟨p,hchar,n,hprime,hq⟩ := FiniteField.card' F
  letI : Fact p.Prime := ⟨hprime⟩
  have hq' : Nat.card F=p^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hq
  let S := (parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker
  have hS : Nat.card S=p^((n:ℕ)*15) := by
    change Nat.card ((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker)=_
    rw [parabolicRadical_kernel_card,hq',pow_mul]
  have hpS : IsPGroup p S := IsPGroup.of_card hS
  have hnot : ¬p∣S.index := by
    rw [show S.index=Nat.card F-1 from parabolicRadical_kernel_index]
    intro hbad
    have hdq : p∣Nat.card F := by
      rw [hq']
      exact dvd_pow_self p (by exact n.ne_zero)
    have hd : p∣1 := by
      have hh := Nat.dvd_sub hdq hbad
      have he : Nat.card F-(Nat.card F-1)=1 := by have := Nat.card_pos (α:=F); omega
      simpa only [he] using hh
    exact hprime.not_dvd_one hd
  let P : Sylow p ((parabolicOrthogonalHom (F:=F)).ker) := hpS.toSylow hnot
  have hnormal : P.Normal := parabolicRadical_normal_in_kernel
  exact Sylow.characteristic_of_normal P hnormal

theorem parabolicRadical_normal [Finite F] : (parabolicRadical (F:=F)).Normal := by
  letI := parabolicRadical_characteristic_in_kernel (F:=F)
  have h : (((parabolicRadical (F:=F)).subgroupOf parabolicOrthogonalHom.ker).map
      (parabolicOrthogonalHom (F:=F)).ker.subtype).Normal := inferInstance
  simpa only [Subgroup.map_subgroupOf_eq_of_le parabolicRadical_le_kernel] using h

end Atlas.F4
