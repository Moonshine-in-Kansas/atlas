import Atlas.LinearGroups.Unitary.PointNormalClosure

/-! The abelian line groups in the actual projective action, including their
normality in the full point stabilizer and their actual normal closures. -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem projectivePointTransvections_le_stabilizer (hdeg : Module.finrank F K = 2)
    (hn : 0 < n) (p : IsotropicPoints F K n) :
    letI := isotropicAction hdeg hn
    projectivePointTransvections hdeg p ≤ MulAction.stabilizer (PSU F K n hdeg) p := by
  letI := isotropicAction hdeg hn
  rintro g ⟨x, hx, rfl⟩
  exact pointTransvections_le_stabilizer hdeg p hx

theorem projectivePointTransvections_normal (hdeg : Module.finrank F K = 2)
    (hn : 0 < n) (p : IsotropicPoints F K n) :
    letI := isotropicAction hdeg hn
    ((projectivePointTransvections hdeg p).subgroupOf
      (MulAction.stabilizer (PSU F K n hdeg) p)).Normal := by
  letI := isotropicAction hdeg hn
  apply (Subgroup.normal_subgroupOf_iff
    (projectivePointTransvections_le_stabilizer hdeg hn p)).mpr
  rintro a g ⟨x, hx, rfl⟩ hg
  obtain ⟨y, rfl⟩ := projection_surjective F K n hdeg g
  have hy : y ∈ MulAction.stabilizer (SU F K n hdeg) p := hg
  have hxy := (Subgroup.normal_subgroupOf_iff
    (pointTransvections_le_stabilizer hdeg p)).mp (pointTransvections_normal hdeg p) x y hx hy
  exact ⟨y * x * y⁻¹, hxy, by simp⟩

theorem normalClosure_projectivePointTransvections (hdeg : Module.finrank F K = 2)
    (p : IsotropicPoints F K n) :
    Subgroup.normalClosure (projectivePointTransvections hdeg p : Set (PSU F K n hdeg)) =
      (transvectionGenerated hdeg).map (projection F K n hdeg) := by
  rw [← normalClosure_pointTransvections hdeg p,
    Subgroup.map_normalClosure _ _ (projection_surjective F K n hdeg)]
  rfl

theorem normalClosure_projectivePointTransvections_eq_top
    (hdeg : Module.finrank F K = 2) (p : IsotropicPoints F K n)
    (hgen : transvectionGenerated hdeg (n := n) = ⊤) :
    Subgroup.normalClosure (projectivePointTransvections hdeg p : Set (PSU F K n hdeg)) = ⊤ := by
  rw [normalClosure_projectivePointTransvections, hgen]
  exact Subgroup.map_top_of_surjective _ (projection_surjective F K n hdeg)
end Atlas.Unitary
