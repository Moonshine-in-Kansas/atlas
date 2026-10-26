import Atlas.LinearGroups.Orthogonal.DiagonalAction
import Atlas.LinearGroups.Triality.Basic

/-! The faithful diagonal torus of the triality pinning. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def sigmaUnit : Kˣ →* Kˣ := Units.map (FiniteCubic.sigma F K).toMonoidHom
def baseUnit : Fˣ →* Kˣ := Units.map (algebraMap F K).toMonoidHom

/-- Four positive weights; the negative weights are their inverses. -/
def torusWeights : Kˣ × Fˣ →* (Fin 4 → Kˣ) where
  toFun p := ![p.1,baseUnit F K p.2 / p.1,
    sigmaUnit F K p.1 * sigmaUnit F K (sigmaUnit F K p.1) / baseUnit F K p.2,
    sigmaUnit F K (sigmaUnit F K p.1) / sigmaUnit F K p.1]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' p r := by
    ext i; fin_cases i <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

def torusMap : Kˣ × Fˣ →* O_DPlus 4 K := diagonalEmbedding.comp (torusWeights F K)

theorem torusMap_injective : Function.Injective (torusMap F K) := by
  intro p r h
  have hw := diagonalEmbedding_injective h
  have ha : p.1=r.1 := by simpa [torusWeights] using congrFun hw 0
  apply Prod.ext ha
  apply Units.ext
  apply (algebraMap F K).injective
  have hb := congrArg (fun d : Fin 4 → Kˣ => ((d 0 * d 1 : Kˣ) : K)) hw
  simpa [torusWeights, baseUnit, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb

def torus : Subgroup (O_DPlus 4 K) := (torusMap F K).range

def torusParameters : (Kˣ × Fˣ) ≃ torus F K :=
  Equiv.ofBijective (fun p => ⟨torusMap F K p,⟨p,rfl⟩⟩) ⟨
    fun _ _ h => torusMap_injective F K (congrArg Subtype.val h),
    by rintro ⟨g,p,hp⟩; exact ⟨p,Subtype.ext hp⟩⟩

theorem card_torus (hdeg : Module.finrank F K = 3) :
    Nat.card (torus F K) = (Nat.card F ^ 3 - 1)*(Nat.card F - 1) := by
  rw [← Nat.card_congr (torusParameters F K), Nat.card_prod, Nat.card_units,
    Nat.card_units, FiniteCubic.card_extension hdeg]

end Atlas.Triality
