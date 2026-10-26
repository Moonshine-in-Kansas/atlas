import Atlas.LinearGroups.Orthogonal.Minus.RankThreeImage
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeSpanning
import Atlas.LinearGroups.Unitary.Center

/-! Exact full and projective kernels of the actual unitary exterior-square action. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Atlas.Orthogonal.B2Exterior Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankThreeFullHom_scalar_iff (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (c : F) :
    (∀ v, (rankThreeFullHom hdeg g).val v = c • v) ↔
      (∀ w : hodgeFixed hdeg, exteriorMap g.val w.val = c • w.val) := by
  constructor
  · intro h w
    have he := rankThreeFullHom_intertwine hdeg g ((rankThreeHodgeIsometry hdeg).symm w)
    rw [h,map_smul,QuadraticMap.IsometryEquiv.apply_symm_apply] at he
    exact he.symm
  · intro h v
    apply (rankThreeHodgeIsometry hdeg).injective
    apply Subtype.ext
    change (rankThreeHodgeIsometry hdeg ((rankThreeFullHom hdeg g).val v)).val =
      (rankThreeHodgeIsometry hdeg (c • v)).val
    rw [rankThreeFullHom_intertwine,map_smul]
    exact h (rankThreeHodgeIsometry hdeg v)

theorem rankThreeFullHom_eq_one_iff_scalar (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) :
    rankThreeFullHom hdeg g = 1 ↔ ∃ a : K, a^2=1 ∧ g.val=a • 1 := by
  constructor
  · intro hg
    have hs : ∀ v, (rankThreeFullHom hdeg g).val v = (1:F) • v := by
      rw [hg]
      intro v
      exact (one_smul F v).symm
    obtain ⟨a,ha,hga⟩ := matrix_scalar_of_hodgeFixed_scalar hdeg g.val 1 one_ne_zero
      ((rankThreeFullHom_scalar_iff hdeg g 1).mp hs)
    exact ⟨a,by simpa only [map_one] using ha,hga⟩
  · rintro ⟨a,ha,hga⟩
    have hs : ∀ w : hodgeFixed hdeg, exteriorMap g.val w.val = (1:F) • w.val := by
      intro w
      rw [hga,exteriorMap_scalar,LinearMap.smul_apply,LinearMap.id_apply,ha,one_smul,one_smul]
    have hg := (rankThreeFullHom_scalar_iff hdeg g 1).mpr hs
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact (hg v).trans (one_smul F v)

theorem rankThreeProjectiveHom_eq_one_iff_center
 (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) :
    rankThreeProjectiveHom hdeg g = 1 ↔ g ∈ Subgroup.center (Atlas.Unitary.SU F K 4 hdeg) := by
  change (QuotientGroup.mk (rankThreeElementaryHom hdeg g) : ProjectiveElementary (form hdeg 2)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨c,hc,hg⟩
    have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc
    obtain ⟨a,ha,hga⟩ := matrix_scalar_of_hodgeFixed_scalar hdeg g.val c hc0
      ((rankThreeFullHom_scalar_iff hdeg g c).mp hg)
    have hd : g.val = Matrix.diagonal (fun _ => a) := by
      simpa only [Matrix.smul_one_eq_diagonal] using hga
    obtain ⟨p,hp⟩ := Atlas.Unitary.scalar_matrix_parameter hdeg (by decide : 0 < 4) g a hd
    rw [← hp]
    exact Atlas.Unitary.scalarSpecial_mem_center F K hdeg 4 p
  · intro hg
    obtain ⟨a,ha⟩ := Atlas.Unitary.central_matrix_scalar hdeg (by decide : 0 < 4) g hg
    obtain ⟨p,hp⟩ := Atlas.Unitary.scalar_matrix_parameter hdeg (by decide : 0 < 4) g a ha
    subst g
    let b : K := p.val.val.val
    have hb0 : b ≠ 0 := p.val.val.ne_zero
    have hbN : b * conjugation F K b = 1 := (normOne_mem_iff hdeg _).mp p.val.prop
    have hb4 : b^4 = 1 := congrArg (fun u : normOne F K => u.val.val) p.prop
    have hfixed : conjugation F K (b^2) = b^2 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hb0)
      calc
        b^2 * conjugation F K (b^2) = (b*conjugation F K b)^2 := by rw [map_pow,mul_pow]
        _ = 1 := by rw [hbN,one_pow]
        _ = b^2*b^2 := by simpa only [← pow_add] using hb4.symm
    obtain ⟨c,hc⟩ := (conjugation_fixed_iff hdeg (b^2)).mp hfixed
    have hc2 : c^2 = 1 := by
      apply (algebraMap F K).injective
      rw [map_pow,hc,map_one,← pow_mul]
      exact hb4
    refine ⟨c,hc2,?_⟩
    apply (rankThreeFullHom_scalar_iff hdeg _ c).mpr
    intro w
    have hm : (Atlas.Unitary.scalarSpecial F K hdeg p).val = b • (1 : Matrix (Fin 4) (Fin 4) K) := by
      rw [Matrix.smul_one_eq_diagonal]
      rfl
    rw [hm,exteriorMap_scalar,LinearMap.smul_apply,LinearMap.id_apply]
    ext i
    change b^2 * w.val i = c • w.val i
    rw [Algebra.smul_def,hc]

theorem rankThreeProjectiveHom_kernel (hdeg : Module.finrank F K = 2) :
    (rankThreeProjectiveHom hdeg).ker = Subgroup.center (Atlas.Unitary.SU F K 4 hdeg) := by
  ext g
  exact rankThreeProjectiveHom_eq_one_iff_center hdeg g

def rankThreePSUHom (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.PSU F K 4 hdeg →* ProjectiveElementary (form hdeg 2) :=
  QuotientGroup.lift _ (rankThreeProjectiveHom hdeg) (by
    intro g hg
    exact (rankThreeProjectiveHom_eq_one_iff_center hdeg g).mpr hg)

@[simp] theorem rankThreePSUHom_projection (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) :
    rankThreePSUHom hdeg (QuotientGroup.mk g) = rankThreeProjectiveHom hdeg g := rfl

theorem rankThreePSUHom_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (rankThreePSUHom hdeg) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Atlas.Unitary.SU F K 4 hdeg)) x
  change rankThreeProjectiveHom hdeg g = 1 at hx
  change QuotientGroup.mk g = (1 : Atlas.Unitary.PSU F K 4 hdeg)
  exact (QuotientGroup.eq_one_iff g).mpr ((rankThreeProjectiveHom_eq_one_iff_center hdeg g).mp hx)

end Atlas.Orthogonal.Minus
