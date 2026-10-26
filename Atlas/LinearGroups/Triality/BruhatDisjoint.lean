import Atlas.LinearGroups.Triality.BorelTriangular
import Atlas.LinearGroups.Triality.BruhatExhaustion

/-! Distinct actual Weyl representatives give disjoint Borel double cells. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem borel_weyl_eq_weyl_borel (w v : Fin 12) (a b : borel F K hdeg)
    (he : a.val * weylLift F K w = weylLift F K v * b.val) : w=v := by
  by_contra hne
  obtain ⟨i,hi⟩ := coordinateWord_height_separates w v hne
  obtain ⟨u,hu⟩ := weylLift_single F K w i
  obtain ⟨z,hz⟩ := weylWord_row F K (weylWord v) i
  have hentry := congrArg (fun g : O_DPlus 4 K =>
    g.val (Pi.single (coordinateWord (weylWord w) i) 1) i) he
  change a.val.val ((weylLift F K w).val _) i =
    (weylLift F K v).val (b.val.val _) i at hentry
  rw [hu,map_smul] at hentry
  rw [show (weylLift F K v).val _ i = _ from hz _] at hentry
  rw [borel_below F K hdeg b _ _ hi,mul_zero] at hentry
  exact (mul_ne_zero u.ne_zero (borel_diagonal_ne_zero F K hdeg a i)) hentry

theorem bruhat_cells_disjoint (w v : Fin 12) (a b c d : borel F K hdeg)
    (he : a.val * weylLift F K w * b.val = c.val * weylLift F K v * d.val) : w=v := by
  apply borel_weyl_eq_weyl_borel F K hdeg w v (c⁻¹*a) (d*b⁻¹)
  change (c.val⁻¹*a.val)*weylLift F K w = weylLift F K v*(d.val*b.val⁻¹)
  calc
    _ = c.val⁻¹*(a.val*weylLift F K w*b.val)*b.val⁻¹ := by group
    _ = _ := by rw [he]; group

theorem bruhat_unique_index (g : O_DPlus 4 K) (hg : g ∈ generated F K) :
    ∃! w : Fin 12, ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg,
      g = b * weylLift F K w * c := by
  obtain ⟨w,b,hb,c,hc,he⟩ := bruhat_exhaustion F K hdeg g hg
  refine ⟨w,⟨b,hb,c,hc,he⟩,?_⟩
  rintro v ⟨d,hd,e,hh,hv⟩
  exact bruhat_cells_disjoint F K hdeg v w ⟨d,hd⟩ ⟨e,hh⟩ ⟨b,hb⟩ ⟨c,hc⟩ (hv.symm.trans he)

end Atlas.Triality
