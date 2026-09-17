import Atlas.Codes.HexacodeLocalSimple
import Atlas.GroupTheory.AffineNormal
import Atlas.Mathieu.TetradPointwiseStabilizer

noncomputable section
namespace Atlas.Codes

def tetradAffineTranslations (i : HexIndex) : Subgroup (TetradPointAffine i) :=
  (SemidirectProduct.inl : Multiplicative (hexZeroCoordinate i) →* TetradPointAffine i).range

theorem tetradAffineTranslations_centralizer (i : HexIndex) :
    Subgroup.centralizer (tetradAffineTranslations i : Set (TetradPointAffine i)) =
      tetradAffineTranslations i :=
  Atlas.GroupTheory.affine_centralizer (hexZeroAffineAction i) (hexZeroAffineAction_injective i)

theorem tetradAffine_normal_subgroups (i : HexIndex)
    (W : Subgroup (TetradPointAffine i)) [W.Normal] :
    W = ⊥ ∨ W = tetradAffineTranslations i ∨ W = ⊤ := by
  letI := hexPointKernel_simple i
  exact Atlas.GroupTheory.affine_normal_subgroups (hexZeroAffineAction i)
    (hexZeroAffineAction_injective i) (hexZero_invariant_subgroup i) W

def tetradPointTranslations (i : HexIndex) : Subgroup (TetradPointStabilizer i) :=
  (tetradAffineTranslations i).map (tetradPointStabilizerEquiv i).toMonoidHom

theorem tetradPointTranslations_centralizer (i : HexIndex) :
    Subgroup.centralizer (tetradPointTranslations i : Set (TetradPointStabilizer i)) =
      tetradPointTranslations i := by
  let e := tetradPointStabilizerEquiv i
  ext g
  obtain ⟨x,rfl⟩ := e.surjective g
  constructor
  · intro hx
    have hc : x ∈ Subgroup.centralizer
        (tetradAffineTranslations i : Set (TetradPointAffine i)) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro u hu
      apply e.injective
      simp only [map_mul]
      exact Subgroup.mem_centralizer_iff.mp hx (e u) ⟨u,hu,rfl⟩
    rw [tetradAffineTranslations_centralizer] at hc
    exact ⟨x,hc,rfl⟩
  · rintro ⟨u,hu,he⟩
    have hux : u = x := e.injective he
    subst u
    have hc : x ∈ Subgroup.centralizer
        (tetradAffineTranslations i : Set (TetradPointAffine i)) := by
      rwa [tetradAffineTranslations_centralizer]
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact (map_mul e v x).symm.trans
      ((congrArg e (Subgroup.mem_centralizer_iff.mp hc v hv)).trans (map_mul e x v))

theorem tetradPoint_normal_subgroups (i : HexIndex)
    (W : Subgroup (TetradPointStabilizer i)) [W.Normal] :
    W = ⊥ ∨ W = tetradPointTranslations i ∨ W = ⊤ := by
  have h := tetradAffine_normal_subgroups i
    (W.comap (tetradPointStabilizerEquiv i).toMonoidHom)
  have he := Subgroup.map_comap_eq_self_of_surjective
    (f := (tetradPointStabilizerEquiv i).toMonoidHom)
    (tetradPointStabilizerEquiv i).surjective W
  rcases h with hb | hu | ht
  · left
    rw [← he, hb, Subgroup.map_bot]
  · right; left
    rw [← he, hu]
    rfl
  · right; right
    rw [← he, ht]
    exact Subgroup.map_top_of_surjective _ (tetradPointStabilizerEquiv i).surjective

end Atlas.Codes
