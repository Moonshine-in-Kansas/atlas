import Atlas.Fischer.CubicTriangleAverages

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def cubicPointDelta (i j k : Omega) : Scalar :=
  (if i=j then 1 else 0)+(if j=k then 1 else 0)+(if k=i then 1 else 0)

def cubicPointDeltaThree (i j k : Omega) : Scalar :=
  (if i=j then 1 else 0)*(if j=k then 1 else 0)

/-- The actual ordered-triangle incidence contraction with the source's
normalization divided by gamma. The coefficient is beta^3/(4 gamma)
for sextets, and -3 beta^3/(4 gamma) for trios. -/
def cubicSextetPointContributionOverGamma (i j k : Omega) : Scalar :=
  (1/16)*cubicSextetIncidenceSum i j k

theorem cubicSextetPointContributionOverGamma_eq (i j k : Omega) :
    cubicSextetPointContributionOverGamma i j k=
      (-665/2)+7840*cubicPointDelta i j k-89600*cubicPointDeltaThree i j k := by
  unfold cubicSextetPointContributionOverGamma cubicPointDelta cubicPointDeltaThree
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k
      rw [cubicSextetIncidenceSum_diagonal]
      norm_num
    · rw [cubicSextetIncidenceSum_two_equal i k hik]
      simp [hik,Ne.symm hik]
      norm_num
  · by_cases hik : i=k
    · subst k
      rw [cubicSextetIncidenceSum_swapLast,cubicSextetIncidenceSum_two_equal i j hij]
      simp [hij,Ne.symm hij]
      norm_num
    · by_cases hjk : j=k
      · subst k
        rw [cubicSextetIncidenceSum_swapFirst,cubicSextetIncidenceSum_swapLast,
          cubicSextetIncidenceSum_two_equal j i (Ne.symm hij)]
        simp [hij,Ne.symm hij]
        norm_num
      · rw [cubicSextetIncidenceSum_distinct i j k hij hik hjk]
        simp [hij,hik,hjk,Ne.symm hik]
        norm_num

/-- The actual ordered-triangle incidence contraction with the source's
normalization divided by gamma. The coefficient is beta^3/(4 gamma)
for sextets, and -3 beta^3/(4 gamma) for trios. -/
def cubicTrioPointContributionOverGamma (i j k : Omega) : Scalar :=
  (-3/16)*cubicTrioIncidenceSum i j k

theorem cubicTrioPointContributionOverGamma_eq (i j k : Omega) :
    cubicTrioPointContributionOverGamma i j k=
      (-4545/8)+3600*cubicPointDelta i j k-23040*cubicPointDeltaThree i j k := by
  unfold cubicTrioPointContributionOverGamma cubicPointDelta cubicPointDeltaThree
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k
      rw [cubicTrioIncidenceSum_diagonal]
      norm_num
    · rw [cubicTrioIncidenceSum_two_equal i k hik]
      simp [hik,Ne.symm hik]
      norm_num
  · by_cases hik : i=k
    · subst k
      rw [cubicTrioIncidenceSum_swapLast,cubicTrioIncidenceSum_two_equal i j hij]
      simp [hij,Ne.symm hij]
      norm_num
    · by_cases hjk : j=k
      · subst k
        rw [cubicTrioIncidenceSum_swapFirst,cubicTrioIncidenceSum_swapLast,
          cubicTrioIncidenceSum_two_equal j i (Ne.symm hij)]
        simp [hij,Ne.symm hij]
        norm_num
      · rw [cubicTrioIncidenceSum_distinct i j k hij hik hjk]
        simp [hij,hik,hjk,Ne.symm hik]
        norm_num

end Atlas.Fischer
