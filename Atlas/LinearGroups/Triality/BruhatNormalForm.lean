import Atlas.LinearGroups.Triality.InversionCard
import Atlas.LinearGroups.Triality.BruhatCard

/-! Unique ordered inversion-root coordinates for each actual Bruhat cell. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def bruhatNormalMap (w : Fin 12)
    (p : {p : PositiveParameters F K // InversionParameters F K w p} × borel F K hdeg) :
    BruhatCell F K hdeg w :=
  ⟨positiveMatrix F K p.1.val * weylLift F K w * p.2.val,
    DoubleCoset.mem_doubleCoset.mpr ⟨_,unipotent_le_borel F K hdeg ⟨p.1.val,rfl⟩,
      _,p.2.property,rfl⟩⟩

theorem bruhatNormalMap_injective (w : Fin 12) : Function.Injective (bruhatNormalMap F K hdeg w) := by
  intro p r he
  have hh : positiveMatrix F K p.1.val * weylLift F K w * p.2.val =
      positiveMatrix F K r.1.val * weylLift F K w * r.2.val := congrArg Subtype.val he
  let I := inversionSubgroup F K hdeg w
  have hp : positiveMatrix F K p.1.val ∈ I := ⟨p.1.val,p.1.property,rfl⟩
  have hr : positiveMatrix F K r.1.val ∈ I := ⟨r.1.val,r.1.property,rfl⟩
  obtain ⟨s,hsi,hse⟩ := I.mul_mem (I.inv_mem hp) hr
  have hc : (weylLift F K w)⁻¹ * positiveMatrix F K s * weylLift F K w = p.2.val*r.2.val⁻¹ := by
    rw [hse]
    calc
      _ = (weylLift F K w)⁻¹ * (positiveMatrix F K p.1.val)⁻¹ *
        (positiveMatrix F K r.1.val * weylLift F K w * r.2.val) * r.2.val⁻¹ := by group
      _ = _ := by rw [← hh]; group
  have hss : SurvivingParameters F K w s := by
    apply survivingParameters_of_conjugate F K hdeg w s
    rw [hc]
    exact Subgroup.mul_mem _ p.2.property (Subgroup.inv_mem _ r.2.property)
  have hs := inversion_surviving_zero F K w s hsi hss
  have hpr : positiveMatrix F K p.1.val=positiveMatrix F K r.1.val := by
    have hz : positiveMatrix F K s=1 := by rw [hs,positiveMatrix_zero]
    have heq : (positiveMatrix F K p.1.val)⁻¹ * positiveMatrix F K r.1.val=1 := hse.symm.trans hz
    exact inv_mul_eq_one.mp heq
  have hpars : p.1=r.1 := Subtype.ext (positiveMatrix_injective F K hpr)
  have hb : p.2=r.2 := by
    apply Subtype.ext
    rw [hpr] at hh
    exact mul_left_cancel hh
  exact Prod.ext hpars hb

theorem bruhatNormalMap_bijective (w : Fin 12) : Function.Bijective (bruhatNormalMap F K hdeg w) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨bruhatNormalMap_injective F K hdeg w,?_⟩
  rw [Nat.card_prod,card_inversionParameters F K hdeg,card_bruhatCell F K hdeg]

def bruhatNormalEquiv (w : Fin 12) :
    ({p : PositiveParameters F K // InversionParameters F K w p} × borel F K hdeg) ≃
      BruhatCell F K hdeg w := Equiv.ofBijective _ (bruhatNormalMap_bijective F K hdeg w)

def CellParameters := Σ w : Fin 12,
  {p : PositiveParameters F K // InversionParameters F K w p} × borel F K hdeg

def cellEquiv : CellParameters F K hdeg ≃ Group F K :=
  (Equiv.sigmaCongrRight (bruhatNormalEquiv F K hdeg)).trans (bruhatCellsEquiv F K hdeg)

end Atlas.Triality
