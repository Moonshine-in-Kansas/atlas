import Atlas.LinearGroups.ReeF4.TailRhoNormalization
import Atlas.GroupTheory.TailLeviNormalizerLemmas
import Atlas.LinearGroups.ReeF4.OppositePairStabilizer
import Atlas.LinearGroups.ReeF4.WeylSL2TorusDecomposition
import Atlas.LinearGroups.ReeF4.WeylSigmaDerived

/-!
Source-only repair. Normalization of the existing seven-factor tail by the
actual Suzuki x scalar Levi, including q=2. All 16 original public declaration
headers are retained. Generic normalization hypotheses are discharged below
from actual operators. No point-parabolic decomposition, splitting, or simplicity
is used. No compilation, proof checking, audit, or resource measurement was run.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Atlas.GroupTheory

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem torusModel_range_le_shortRoot_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    (torusModelHom hcard).range ≤
      Subgroup.normalizer (shortRootModelEmbedding hcard).range := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro t ⟨⟨a,b⟩,rfl⟩ x ⟨u,rfl⟩
  have hv : torusEquiv m a b * u.val * (torusEquiv m a b)⁻¹ ∈
      shortRootSubgroup m hcard :=
    (Subgroup.mem_normalizer_iff.mp
      (torusEquiv_mem_shortRoot_normalizer hcard a b) u.val).mp u.property
  exact ⟨⟨_,hv⟩, Subtype.ext rfl⟩

/-- The full two-parameter torus normalizes the actual additive long-root group.
The square-root decomposition of the torus is valid also over the binary field. -/
theorem torusModel_range_le_longRoot_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    (torusModelHom hcard).range ≤
      Subgroup.normalizer (modelLongSL2RootHom hcard).range := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro t ⟨⟨a,b⟩,rfl⟩ x ⟨u,rfl⟩
  obtain ⟨s,c,ha,hb⟩ := exists_longSL2_torus_factors a b
  have ht : torusModelHom hcard (a,b) =
      torusModelHom hcard (s,s⁻¹) * torusModelHom hcard (c,c) := by
    rw [← map_mul]
    congr 1
    exact Prod.ext ha hb
  have hc : Commute (torusModelHom hcard (c,c)) (modelLongSL2RootHom hcard u) := by
    apply Subtype.ext
    change torusEquiv m c c * longSL2Equiv u.toAdd ((theta F m).toRingHom u.toAdd) =
      longSL2Equiv u.toAdd ((theta F m).toRingHom u.toAdd) * torusEquiv m c c
    rw [← longSL2Representation_upper (theta F m).toRingHom u.toAdd]
    exact (torusEquiv_scalar_commutes m c (theta F m).toRingHom
      (longSL2Upper u.toAdd)).eq
  have hscale : torusModelHom hcard (s,s⁻¹) * modelLongSL2RootHom hcard u *
      (torusModelHom hcard (s,s⁻¹))⁻¹ =
      modelLongSL2RootHom hcard (Multiplicative.ofAdd ((s : F)^2 * u.toAdd)) := by
    apply Subtype.ext
    exact longSL2Parameter_torus_conjugate m s u.toAdd
  refine ⟨Multiplicative.ofAdd ((s : F)^2 * u.toAdd), ?_⟩
  symm
  rw [ht]
  exact (TailLeviNormalizer.conjugate_mul_of_commute
    (torusModelHom hcard (s,s⁻¹)) (torusModelHom hcard (c,c))
    (modelLongSL2RootHom hcard u) hc).trans hscale

theorem weylRhoModel_mem_modelTorus_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    weylRhoModel (F := F) m ∈ Subgroup.normalizer (torusModelHom hcard).range := by
  apply TailNormalizer.mem_normalizer_of_inv_eq_self_of_conjugate_mem
    (torusModelHom hcard).range (weylRhoModel m) (weylRhoModel_inv m)
  rintro t ⟨⟨a,b⟩,rfl⟩
  refine ⟨(a, thetaUnits m a * b⁻¹), ?_⟩
  rw [weylRhoModel_inv]
  apply Subtype.ext
  exact (weylRho_torus hcard a b).symm

theorem weylSigmaModel_mem_modelTorus_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    weylSigmaModel (F := F) m ∈ Subgroup.normalizer (torusModelHom hcard).range := by
  apply TailNormalizer.mem_normalizer_of_inv_eq_self_of_conjugate_mem
    (torusModelHom hcard).range (weylSigmaModel m) (weylSigmaModel_inv m)
  rintro t ⟨⟨a,b⟩,rfl⟩
  refine ⟨(b,a), ?_⟩
  rw [weylSigmaModel_inv]
  apply Subtype.ext
  exact (weylSigma_torus m a b).symm

theorem alternatingWeylHom_mem_modelTorus_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (d : DihedralGroup 8) :
    alternatingWeylHom (F := F) m d ∈
      Subgroup.normalizer (torusModelHom hcard).range := by
  let N : Subgroup (Model F m) :=
    Subgroup.normalizer ((torusModelHom hcard).range : Set (Model F m))
  have hp (n : ℕ) : (weylRhoModel m * weylSigmaModel m)^n ∈ N :=
    N.pow_mem (N.mul_mem (weylRhoModel_mem_modelTorus_normalizer hcard)
      (weylSigmaModel_mem_modelTorus_normalizer hcard)) n
  cases d with
  | r i =>
    have he : alternatingWeylHom (F := F) m (.r i) =
        (weylRhoModel m * weylSigmaModel m)^i.val := by apply Subtype.ext; rfl
    rw [he]
    exact hp _
  | sr i =>
    have he : alternatingWeylHom (F := F) m (.sr i) =
        weylRhoModel m * (weylRhoModel m * weylSigmaModel m)^i.val := by
      apply Subtype.ext; rfl
    rw [he]
    exact N.mul_mem (weylRhoModel_mem_modelTorus_normalizer hcard) (hp _)

theorem torusModel_range_le_alternatingShort_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) :
    (torusModelHom hcard).range ≤
      Subgroup.normalizer (alternatingShortRootHom hcard k).range :=
  TailLeviNormalizer.normalizes_conjugated_range (torusModelHom hcard).range
    (shortRootModelEmbedding hcard) (alternatingShortPrefix m k)
    (alternatingWeylHom_mem_modelTorus_normalizer hcard (.r (k.val : ZMod 8)))
    (torusModel_range_le_shortRoot_normalizer hcard)

theorem torusModel_range_le_alternatingLong_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : Fin 4) :
    (torusModelHom hcard).range ≤
      Subgroup.normalizer (alternatingLongRootHom hcard k).range :=
  TailLeviNormalizer.normalizes_conjugated_range (torusModelHom hcard).range
    (modelLongSL2RootHom hcard) (alternatingLongPrefix m k)
    ((Subgroup.normalizer
      ((torusModelHom hcard).range : Set (Model F m))).mul_mem
      (alternatingWeylHom_mem_modelTorus_normalizer hcard (.r (k.val : ZMod 8)))
      (alternatingWeylHom_mem_modelTorus_normalizer hcard (.sr 0)))
    (torusModel_range_le_longRoot_normalizer hcard)

theorem torusModel_range_le_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    (torusModelHom hcard).range ≤ Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  exact TailLeviNormalizer.le_normalizer_subgroupListJoin_seven
    (torusModelHom hcard).range
    (alternatingLongRootHom hcard 0).range
    (alternatingShortRootHom hcard 1).range
    (alternatingLongRootHom hcard 1).range
    (alternatingShortRootHom hcard 2).range
    (alternatingLongRootHom hcard 2).range
    (alternatingShortRootHom hcard 3).range
    (alternatingLongRootHom hcard 3).range
    (torusModel_range_le_alternatingLong_normalizer hcard 0)
    (torusModel_range_le_alternatingShort_normalizer hcard 1)
    (torusModel_range_le_alternatingLong_normalizer hcard 1)
    (torusModel_range_le_alternatingShort_normalizer hcard 2)
    (torusModel_range_le_alternatingLong_normalizer hcard 2)
    (torusModel_range_le_alternatingShort_normalizer hcard 3)
    (torusModel_range_le_alternatingLong_normalizer hcard 3)

theorem alternatingShortRootHom_zero_eq {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : shortRootSubgroup m hcard) :
    alternatingShortRootHom hcard 0 g = shortRootModelEmbedding hcard g := by
  have hp : alternatingShortPrefix (F := F) m 0 = 1 := by
    change alternatingWeylHom m (1 : DihedralGroup 8) = 1
    exact map_one _
  change alternatingShortPrefix m 0 * shortRootModelEmbedding hcard g *
    (alternatingShortPrefix m 0)⁻¹ = _
  rw [hp]
  simp only [one_mul, inv_one, mul_one]

theorem shortRootModelEmbedding_mem_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : shortRootSubgroup m hcard) :
    shortRootModelEmbedding hcard g ∈ Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  rw [← alternatingShortRootHom_zero_eq hcard g]
  exact positiveRoot_head_le_tail_normalizer hcard ⟨g,rfl⟩

/-- Closure of the actual short-root, T(1,b), and rho generators suffices. -/
theorem modelSuzukiEmbedding_mem_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : SuzukiFamily.Group F m) :
    modelSuzukiEmbedding m hcard g ∈ Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  let N : Subgroup (Model F m) :=
    Subgroup.normalizer (positiveRootTailSubgroup hcard : Set (Model F m))
  let H : Subgroup (TraceZero F ≃ₗ[F] TraceZero F) :=
    N.map (modelSubgroup F m).subtype
  have hle : suzukiLeviSubgroup m hcard ≤ H := by
    apply (Subgroup.closure_le H).mpr
    intro x hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨⟨a,b⟩,rfl⟩ := hx
      exact ⟨shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b)),
        shortRootModelEmbedding_mem_tail_normalizer hcard _, rfl⟩
    · obtain ⟨b,rfl⟩ := hx
      exact ⟨torusModelHom hcard (1,b),
        torusModel_range_le_tail_normalizer hcard ⟨(1,b),rfl⟩, rfl⟩
    · rcases hx with rfl
      exact ⟨weylRhoModel m, weylRhoModel_mem_tail_normalizer hcard, rfl⟩
  obtain ⟨x,hx,he⟩ := hle (suzukiLeviEmbedding m hcard g).property
  have hxe : x = modelSuzukiEmbedding m hcard g := Subtype.ext he
  change x ∈ N at hx
  rw [← hxe]
  exact hx

theorem modelSuzukiProduct_le_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    modelSuzukiProductSubgroup hcard ≤ Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  rintro x ⟨⟨g,s⟩,rfl⟩
  change modelSuzukiEmbedding m hcard g * torusModelHom hcard (thetaUnits m s,s) ∈
    Subgroup.normalizer (positiveRootTailSubgroup hcard : Set (Model F m))
  exact (Subgroup.normalizer
    (positiveRootTailSubgroup hcard : Set (Model F m))).mul_mem
    (modelSuzukiEmbedding_mem_tail_normalizer hcard g)
    (torusModel_range_le_tail_normalizer hcard ⟨(thetaUnits m s,s),rfl⟩)

/-- The same normalization statement for the identified full opposite-pair stabilizer. -/
theorem oppositePairStabilizer_le_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    MulAction.stabilizer (Model F m) (baseSpecialOppositePair (F := F) m) ≤
      Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  rw [← oppositePairStabilizer_eq_suzukiProduct hcard]
  exact modelSuzukiProduct_le_tail_normalizer hcard

/-- Only the generated join is used here; it has not been identified with a parabolic. -/
theorem positiveRootTail_normal_in_join_levi {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    ((positiveRootTailSubgroup hcard).subgroupOf
      (positiveRootTailSubgroup hcard ⊔ modelSuzukiProductSubgroup hcard)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le (positiveRootTailSubgroup hcard).le_normalizer
    (modelSuzukiProduct_le_tail_normalizer hcard)

/-- The actual Levi acts by conjugation on the literal tail subgroup. -/
def suzukiProductTailAction {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    modelSuzukiProductSubgroup hcard →* MulAut (positiveRootTailSubgroup hcard) :=
  (positiveRootTailSubgroup hcard).normalizerMonoidHom.comp
    (Subgroup.inclusion (modelSuzukiProduct_le_tail_normalizer hcard))

theorem suzukiProductTailAction_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (l : modelSuzukiProductSubgroup hcard) (r : positiveRootTailSubgroup hcard) :
    (suzukiProductTailAction hcard l r).val = l.val * r.val * l.val⁻¹ := rfl

end Atlas.ReeF4
