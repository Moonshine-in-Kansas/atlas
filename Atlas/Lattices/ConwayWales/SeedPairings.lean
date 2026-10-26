import Atlas.Lattices.ConwayWales.QuaternionPairing

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

/-- First column of v15 Table `tab:inner`, with the manuscript's positive-shift convention. -/
def aCorrelation : Row → Q := ![⟨4,-Complex.I,-Complex.I,-Complex.I⟩, l, j, -k, k, -j, -l]

-- Seven explicit four-coordinate identities, without native evaluation.
set_option maxHeartbeats 1600000 in
theorem quaternionPair_a_translate (d : Row) :
    quaternionPair a (translate d a) = aCorrelation (-d) := by
  fin_cases d <;> simp only [quaternionPair, Fin.sum_univ_succ]
  all_goals dsimp [a, A, translate, dagger, aCorrelation, j, k, l]
  all_goals ext <;> norm_num [map_ofNat] <;> ring_nf <;> norm_num [map_ofNat]

theorem aCorrelation_integral (d : Row) : aCorrelation d ∈ gaussianOrder := by
  fin_cases d <;> simp [aCorrelation, gaussianOrder, gaussian_I, j,k,l]


theorem quaternionPair_half_coordinate (v : Space) (hv : v ∈ halfIntegralModule)
    (d : Row) (u : Fin 4) : quaternionPair v (seedGenerator 0 d u) ∈ gaussianOrder := by
  have he : quaternionPair v (seedGenerator 0 d u) =
      dagger ((2 : ℂ) • v d) * quaternionBasis u := by
    simp [quaternionPair, seedGenerator, dagger_smul, mul_ite,
      Finset.sum_ite_eq', mul_smul_comm, smul_mul_assoc]
  rw [he]
  exact gaussianOrder.mul_mem (gaussianOrder_dagger (hv d)) (basis_mem_gaussianOrder u)

theorem translate_f_eq (d : Row) : translate d f = Complex.I • seedGenerator 0 d 0 := by
  funext r
  by_cases h : r = d
  · subst r
    ext <;> norm_num [translate, f, seedGenerator, quaternionBasis, mul_comm]
  · simp [translate, f, seedGenerator, quaternionBasis, sub_eq_zero, h]

theorem f_mem_seedLattice : f ∈ seedLattice := by
  have h := gaussian_smul_mem_seedLattice gaussian_I (seedGenerator_mem 0 0 0)
  rw [← translate_f_eq] at h
  change (fun r => f (r - 0)) ∈ seedLattice at h
  simpa only [sub_zero] using h

theorem c_halfIntegral : c ∈ halfIntegralModule := by
  intro r
  change (2 : ℂ) • ((1 / 2 : ℂ) • C r) ∈ gaussianOrder
  simpa only [smul_smul, mul_one_div_cancel (by norm_num : (2 : ℂ) ≠ 0), one_smul]
    using C_mem_gaussianOrder r

theorem quaternionPair_half_f (v : Space) (hv : v ∈ halfIntegralModule) (d : Row) :
    quaternionPair v (translate d f) ∈ gaussianOrder := by
  rw [translate_f_eq, quaternionPair_smul_right]
  exact gaussianOrder_smul gaussian_I (quaternionPair_half_coordinate v hv d 0)

theorem quaternionPair_a_a_integral (d : Row) :
    quaternionPair a (translate d a) ∈ gaussianOrder := by
  rw [quaternionPair_a_translate]
  exact aCorrelation_integral _

theorem quaternionPair_a_b_integral (d : Row) :
    quaternionPair a (translate d b) ∈ gaussianOrder := by
  rw [← quaternionPair_convolution, convolution_a, convolution_translate, convolution_b]
  exact quaternionPair_half_f c c_halfIntegral (-d)

theorem quaternionPair_b_b_integral (d : Row) :
    quaternionPair b (translate d b) ∈ gaussianOrder := by
  rw [← quaternionPair_convolution, convolution_b, convolution_translate, convolution_b]
  exact quaternionPair_half_f f (seedLattice_le_halfIntegral f_mem_seedLattice) (-d)

theorem translated_right_pair_integral (v w : Space)
    (h : ∀ d, quaternionPair v (translate d w) ∈ gaussianOrder)
    (d e : Row) (u z : Fin 4) :
    quaternionPair (fun r => v (r-d) * quaternionBasis u)
      (fun r => w (r-e) * quaternionBasis z) ∈ gaussianOrder := by
  change quaternionPair (fun r => translate d v r * quaternionBasis u)
    (fun r => translate e w r * quaternionBasis z) ∈ gaussianOrder
  rw [quaternionPair_right_multiples, quaternionPair_translate]
  exact gaussianOrder.mul_mem (gaussianOrder.mul_mem
    (gaussianOrder_dagger (basis_mem_gaussianOrder u)) (h _)) (basis_mem_gaussianOrder z)

theorem quaternionPair_seed_generators (t s : Fin 3) (d e : Row) (u z : Fin 4) :
    quaternionPair (seedGenerator t d u) (seedGenerator s e z) ∈ gaussianOrder := by
  fin_cases t <;> fin_cases s
  · exact quaternionPair_half_coordinate _ (seedGenerator_halfIntegral _ _ _) _ _
  · rw [← quaternionPair_swap]
    exact gaussianOrder_dagger (quaternionPair_half_coordinate _ (seedGenerator_halfIntegral _ _ _) _ _)
  · rw [← quaternionPair_swap]
    exact gaussianOrder_dagger (quaternionPair_half_coordinate _ (seedGenerator_halfIntegral _ _ _) _ _)
  · exact quaternionPair_half_coordinate _ (seedGenerator_halfIntegral _ _ _) _ _
  · exact translated_right_pair_integral a a quaternionPair_a_a_integral d e u z
  · exact translated_right_pair_integral a b quaternionPair_a_b_integral d e u z
  · exact quaternionPair_half_coordinate _ (seedGenerator_halfIntegral _ _ _) _ _
  · rw [← quaternionPair_swap]
    exact gaussianOrder_dagger (translated_right_pair_integral a b quaternionPair_a_b_integral e d z u)
  · exact translated_right_pair_integral b b quaternionPair_b_b_integral d e u z

end Atlas.ConwayWales
