import Atlas.LinearGroups.Triality.TorusCore
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary

/-! Trivial scalar intersection, independently of the simplicity theorem. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem scalar_commutes (g : O_DPlus 4 K) (c : K)
    (hs : ∀ x, g.val x=c • x) (a : O_DPlus 4 K) : g*a=a*g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (a.val x)=a.val (g.val x)
  rw [hs,hs,map_smul]

theorem scalar_mem_borel (g : O_DPlus 4 K) (hg : g ∈ generated F K)
    (c : K) (hs : ∀ x, g.val x=c • x) : g ∈ borel F K hdeg := by
  obtain ⟨w,b,hb,d,hd,he⟩ := bruhat_exhaustion F K hdeg g hg
  by_cases hw : w=0
  · subst w
    have he' : g=b*d := by simpa [weylLift,weylWord] using he
    rw [he']
    exact Subgroup.mul_mem _ hb hd
  obtain ⟨i,hi⟩ := coordinateWord_height_separates w 0 hw
  change coordinateHeight (coordinateWord (weylWord w) i) < coordinateHeight i at hi
  let a : borel F K hdeg := ⟨b⁻¹*d⁻¹,Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) (Subgroup.inv_mem _ hd)⟩
  have hn : weylLift F K w = b⁻¹*g*d⁻¹ := by rw [he]; group
  obtain ⟨u,hu⟩ := weylWord_row F K (weylWord w) i
  have hh := hu (Pi.single (coordinateWord (weylWord w) i) 1)
  change (weylLift F K w).val _ i=_ at hh
  rw [hn] at hh
  change b⁻¹.val (g.val (d⁻¹.val _)) i=_ at hh
  rw [hs,map_smul] at hh
  have hz := borel_below F K hdeg a i _ hi
  change (b⁻¹).val ((d⁻¹).val (Pi.single (coordinateWord (weylWord w) i) 1)) i=0 at hz
  simp only [Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one] at hh
  change c * ((b⁻¹).val ((d⁻¹).val (Pi.single (coordinateWord (weylWord w) i) 1)) i) = (u : K) at hh
  rw [hz,mul_zero] at hh
  have hh' : (u : K)=0 := hh.symm
  exact False.elim (u.ne_zero hh')

include hdeg in
theorem scalar_eq_one (g : O_DPlus 4 K) (hg : g ∈ generated F K)
    (c : K) (hs : ∀ x, g.val x=c • x) : g=1 := by
  have hb := scalar_mem_borel F K hdeg g hg c hs
  have ht : g ∈ torus F K := by
    apply borel_opposite_intersection_le_torus F K hdeg g hb
    have hc := scalar_commutes K g c hs (weylLift F K 11)
    rw [mul_assoc, hc, inv_mul_cancel_left]
    exact hb
  obtain ⟨h,he⟩ := ht
  have hfixed (p : PositiveParameters F K) : torusScale F K h p=p := by
    have hc := scalar_commutes K g c hs (positiveMatrix F K p)
    rw [← he,torus_positive_intertwine F K hdeg h p] at hc
    exact positiveMatrix_injective F K (mul_right_cancel hc)
  have hh := torusScale_fixed_all F K h hfixed
  rw [← he,hh,map_one]

end Atlas.Triality
