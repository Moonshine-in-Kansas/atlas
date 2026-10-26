import Atlas.LinearGroups.Triality.SurvivingParameterCard

/-! Actual subgroups consisting of the ordered inversion-root coordinates. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def InversionParameters (w : Fin 12) (p : PositiveParameters F K) : Prop :=
  (rootSurvives w 0 = true → p.a=0) ∧
  (rootSurvives w 1 = true → p.b=0) ∧
  (rootSurvives w 2 = true → p.c=0) ∧
  (rootSurvives w 3 = true → p.d=0) ∧
  (rootSurvives w 4 = true → p.u=0) ∧
  (rootSurvives w 5 = true → p.v=0)

theorem inversionParameters_collect (w : Fin 12) (p r : PositiveParameters F K)
    (hp : InversionParameters F K w p) (hr : InversionParameters F K w r) :
    InversionParameters F K w (positiveCollect F K p r) := by
  fin_cases w
  · have hpa := hp.1 (by decide)
    have hra := hr.1 (by decide)
    have hpb := hp.2.1 (by decide)
    have hrb := hr.2.1 (by decide)
    have hpc := hp.2.2.1 (by decide)
    have hrc := hr.2.2.1 (by decide)
    have hpd := hp.2.2.2.1 (by decide)
    have hrd := hr.2.2.2.1 (by decide)
    have hpu := hp.2.2.2.2.1 (by decide)
    have hru := hr.2.2.2.2.1 (by decide)
    have hpv := hp.2.2.2.2.2 (by decide)
    have hrv := hr.2.2.2.2.2 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro _
      simp [positiveCollect,hpa,hra,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
  · have hpb := hp.2.1 (by decide)
    have hrb := hr.2.1 (by decide)
    have hpc := hp.2.2.1 (by decide)
    have hrc := hr.2.2.1 (by decide)
    have hpd := hp.2.2.2.1 (by decide)
    have hrd := hr.2.2.2.1 (by decide)
    have hpu := hp.2.2.2.2.1 (by decide)
    have hru := hr.2.2.2.2.1 (by decide)
    have hpv := hp.2.2.2.2.2 (by decide)
    have hrv := hr.2.2.2.2.2 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
  · have hpa := hp.1 (by decide)
    have hra := hr.1 (by decide)
    have hpc := hp.2.2.1 (by decide)
    have hrc := hr.2.2.1 (by decide)
    have hpd := hp.2.2.2.1 (by decide)
    have hrd := hr.2.2.2.1 (by decide)
    have hpu := hp.2.2.2.2.1 (by decide)
    have hru := hr.2.2.2.2.1 (by decide)
    have hpv := hp.2.2.2.2.2 (by decide)
    have hrv := hr.2.2.2.2.2 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro _
      simp [positiveCollect,hpa,hra,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpa,hra,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpc,hrc,hpd,hrd,hpu,hru,hpv,hrv]
  · have hpb := hp.2.1 (by decide)
    have hrb := hr.2.1 (by decide)
    have hpc := hp.2.2.1 (by decide)
    have hrc := hr.2.2.1 (by decide)
    have hpd := hp.2.2.2.1 (by decide)
    have hrd := hr.2.2.2.1 (by decide)
    have hpv := hp.2.2.2.2.2 (by decide)
    have hrv := hr.2.2.2.2.2 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpv,hrv]
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpd,hrd,hpv,hrv]
  · have hpa := hp.1 (by decide)
    have hra := hr.1 (by decide)
    have hpd := hp.2.2.2.1 (by decide)
    have hrd := hr.2.2.2.1 (by decide)
    have hpu := hp.2.2.2.2.1 (by decide)
    have hru := hr.2.2.2.2.1 (by decide)
    have hpv := hp.2.2.2.2.2 (by decide)
    have hrv := hr.2.2.2.2.2 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru,hpv,hrv]
    · intro h
      cases h
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru,hpv,hrv]
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru,hpv,hrv]
  · have hpb := hp.2.1 (by decide)
    have hrb := hr.2.1 (by decide)
    have hpc := hp.2.2.1 (by decide)
    have hrc := hr.2.2.1 (by decide)
    have hpv := hp.2.2.2.2.2 (by decide)
    have hrv := hr.2.2.2.2.2 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpv,hrv]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpv,hrv]
    · intro h
      cases h
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc,hpv,hrv]
  · have hpa := hp.1 (by decide)
    have hra := hr.1 (by decide)
    have hpd := hp.2.2.2.1 (by decide)
    have hrd := hr.2.2.2.1 (by decide)
    have hpu := hp.2.2.2.2.1 (by decide)
    have hru := hr.2.2.2.2.1 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru]
    · intro h
      cases h
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru]
    · intro _
      simp [positiveCollect,hpa,hra,hpd,hrd,hpu,hru]
    · intro h
      cases h
  · have hpb := hp.2.1 (by decide)
    have hrb := hr.2.1 (by decide)
    have hpc := hp.2.2.1 (by decide)
    have hrc := hr.2.2.1 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc]
    · intro _
      simp [positiveCollect,hpb,hrb,hpc,hrc]
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
  · have hpa := hp.1 (by decide)
    have hra := hr.1 (by decide)
    have hpu := hp.2.2.2.2.1 (by decide)
    have hru := hr.2.2.2.2.1 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro _
      simp [positiveCollect,hpa,hra,hpu,hru]
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpa,hra,hpu,hru]
    · intro h
      cases h
  · have hpb := hp.2.1 (by decide)
    have hrb := hr.2.1 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro h
      cases h
    · intro _
      simp [positiveCollect,hpb,hrb]
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
  · have hpa := hp.1 (by decide)
    have hra := hr.1 (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro _
      simp [positiveCollect,hpa,hra]
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
def inversionMonoid (hdeg : Module.finrank F K = 3) (w : Fin 12) : Submonoid (O_DPlus 4 K) where
  carrier := {g | ∃ p, InversionParameters F K w p ∧ positiveMatrix F K p=g}
  one_mem' := ⟨⟨0,0,0,0,0,0⟩,by simp [InversionParameters],positiveMatrix_zero F K⟩
  mul_mem' := by
    rintro _ _ ⟨p,hp,rfl⟩ ⟨r,hr,rfl⟩
    exact ⟨positiveCollect F K p r,inversionParameters_collect F K w p r hp hr,
      (positiveMatrix_mul F K hdeg p r).symm⟩

theorem inversionMonoid_inv_mem (hdeg : Module.finrank F K = 3) (w : Fin 12)
    (g : O_DPlus 4 K) (hg : g ∈ inversionMonoid F K hdeg w) : g⁻¹ ∈ inversionMonoid F K hdeg w := by
  let S := inversionMonoid F K hdeg w
  let f : S → S := fun x => ⟨g*x.val,S.mul_mem hg x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val he))
  obtain ⟨x,hx⟩ := (Finite.surjective_of_injective hf) (1 : S)
  have he : g*x.val=1 := congrArg Subtype.val hx
  have hx' : x.val=g⁻¹ := by
    calc
      x.val=g⁻¹*(g*x.val) := by group
      _ = g⁻¹ := by rw [he,mul_one]
  exact hx' ▸ x.property

def inversionSubgroup (hdeg : Module.finrank F K = 3) (w : Fin 12) : Subgroup (O_DPlus 4 K) where
  __ := inversionMonoid F K hdeg w
  inv_mem' := inversionMonoid_inv_mem F K hdeg w _

theorem inversion_surviving_zero (w : Fin 12) (p : PositiveParameters F K)
    (hi : InversionParameters F K w p) (hs : SurvivingParameters F K w p) : p=⟨0,0,0,0,0,0⟩ := by
  have ha : p.a=0 := by cases h : rootSurvives w 0; exact hs.1 h; exact hi.1 h
  have hb : p.b=0 := by cases h : rootSurvives w 1; exact hs.2.1 h; exact hi.2.1 h
  have hc : p.c=0 := by cases h : rootSurvives w 2; exact hs.2.2.1 h; exact hi.2.2.1 h
  have hd : p.d=0 := by cases h : rootSurvives w 3; exact hs.2.2.2.1 h; exact hi.2.2.2.1 h
  have hu : p.u=0 := by cases h : rootSurvives w 4; exact hs.2.2.2.2.1 h; exact hi.2.2.2.2.1 h
  have hv : p.v=0 := by cases h : rootSurvives w 5; exact hs.2.2.2.2.2 h; exact hi.2.2.2.2.2 h
  cases p
  simp_all

end Atlas.Triality
