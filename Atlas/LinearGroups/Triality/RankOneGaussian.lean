import Atlas.LinearGroups.SL2Gaussian
import Atlas.LinearGroups.Triality.RankOneBruhat

/-! Gaussian rewrites through the actual short and long SL₂ homomorphisms. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortWeyl_root_gaussian (a : Kˣ) :
    shortWeyl F K * shortRoot F K (a : K) =
      shortRoot F K (↑(-a⁻¹) : K) * torusMap F K (-a⁻¹,1) *
        shortNegativeRoot F K (↑a⁻¹ : K) := by
  have h := congrArg (rankOneShortOrthogonal F K) (Matrix.SL2.weyl_upper_gaussian a)
  have hd := short_diagonal_torus F K (-a⁻¹)
  simp only [diagonalSL] at hd
  simpa only [map_mul, rankOneShortOrthogonal_upper, rankOneShortOrthogonal_lower,
    hd, shortWeyl] using h

theorem longWeyl_root_gaussian (a : Fˣ) :
    longWeyl F K * longRoot F K (a : F) =
      longRoot F K (↑(-a⁻¹) : F) * torusMap F K (1,-a⁻¹) *
        longNegativeRoot F K (↑a⁻¹ : F) := by
  have h := congrArg (rankOneLongOrthogonal F K) (Matrix.SL2.weyl_upper_gaussian a)
  have hd := long_diagonal_torus F K (-a⁻¹)
  simp only [diagonalSL] at hd
  simpa only [map_mul, rankOneLongOrthogonal_upper, rankOneLongOrthogonal_lower,
    hd, longWeyl] using h

end Atlas.Triality
