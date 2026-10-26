import Atlas.LinearGroups.Triality.SurvivingParameterCard
import Atlas.GroupTheory.DoubleCosetCard

/-! Cardinalities of the twelve disjoint actual Bruhat cells. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Atlas.GroupTheory
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def BruhatCell (w : Fin 12) :=
  DoubleCoset.doubleCoset (weylLift F K w) (borel F K hdeg : Set (O_DPlus 4 K)) (borel F K hdeg)

theorem weightedLength_le (w : Fin 12) : weightedLength w ≤ 12 := by
  revert w
  decide

theorem card_bruhatCell (w : Fin 12) :
    Nat.card (BruhatCell F K hdeg w) = Nat.card F ^ weightedLength w * Nat.card (borel F K hdeg) := by
  have hc := card_doubleCoset_mul_intersection (borel F K hdeg) (weylLift F K w)
  change Nat.card (BruhatCell F K hdeg w) * Nat.card (borelIntersection F K hdeg w) =
    Nat.card (borel F K hdeg)*Nat.card (borel F K hdeg) at hc
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card (borelIntersection F K hdeg w) from Nat.card_pos)
  rw [hc,card_borelIntersection F K hdeg,card_borel F K hdeg]
  have hp : Nat.card F^weightedLength w * Nat.card F^(12-weightedLength w)=Nat.card F^12 := by
    rw [← pow_add,Nat.add_sub_of_le (weightedLength_le w)]
  calc
    _ = (Nat.card F^12 * Nat.card F^12) * ((Nat.card F^3-1)*(Nat.card F-1))^2 := by ring
    _ = _ := by rw [← hp]; ring

def bruhatCellsMap (p : Σ w : Fin 12, BruhatCell F K hdeg w) : Group F K :=
  ⟨p.2.val,(generated_mem_iff_bruhat F K hdeg _).mpr (by
    obtain ⟨b,hb,c,hc,he⟩ := DoubleCoset.mem_doubleCoset.mp p.2.property
    exact ⟨p.1,b,hb,c,hc,he⟩)⟩

theorem bruhatCellsMap_bijective : Function.Bijective (bruhatCellsMap F K hdeg) := by
  constructor
  · rintro ⟨w,g⟩ ⟨v,h⟩ he
    have hg : g.val=h.val := congrArg Subtype.val he
    obtain ⟨a,ha,b,hb,he₁⟩ := DoubleCoset.mem_doubleCoset.mp g.property
    obtain ⟨c,hc,d,hd,he₂⟩ := DoubleCoset.mem_doubleCoset.mp h.property
    have hw : w=v := bruhat_cells_disjoint F K hdeg w v ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
      (he₁.symm.trans (hg.trans he₂))
    subst v
    exact congrArg (Sigma.mk w) (Subtype.ext hg)
  · intro g
    obtain ⟨w,b,hb,c,hc,he⟩ := bruhat_exhaustion F K hdeg g.val g.property
    exact ⟨⟨w,⟨g.val,DoubleCoset.mem_doubleCoset.mpr ⟨b,hb,c,hc,he⟩⟩⟩,rfl⟩

def bruhatCellsEquiv : (Σ w : Fin 12, BruhatCell F K hdeg w) ≃ Group F K :=
  Equiv.ofBijective _ (bruhatCellsMap_bijective F K hdeg)

theorem card_group_bruhat_sum :
    Nat.card (Group F K) = (∑ w : Fin 12, Nat.card F ^ weightedLength w) * Nat.card (borel F K hdeg) := by
  rw [← Nat.card_congr (bruhatCellsEquiv F K hdeg),Nat.card_sigma]
  simp_rw [card_bruhatCell F K hdeg]
  exact (Finset.sum_mul _ _ _).symm

end Atlas.Triality
