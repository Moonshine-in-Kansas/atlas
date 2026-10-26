import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionAdjoinOrbit
import Atlas.LinearGroups.Chevalley.WeightCompanionCentralTorus

/-! An adjoined actual weight orbit in a single root-lattice coset is scalar
on the actual adjoint kernel. This uses torus containment over arbitrary fields,
not finite-group order or an identification of the full center. -/
noncomputable section
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base) (R : Type*) [CommRing R]

/-- A root-trivial character is constant on each literal root-lattice coset. -/
theorem weightTorusCharacter_eq_of_sub_mem_rootLattice
    (t : b.support → Rˣ)
    (ht : ∀ a, weightTorusCharacter P b R t (rootWeight P a)=1)
    (μ ν : WeightLattice P) (h : μ-ν ∈ rootLattice P) :
    weightTorusCharacter P b R t μ=weightTorusCharacter P b R t ν := by
  have hker : rootLattice P ≤ weightTorusCharacterKernel P b R t :=
    Submodule.span_le.mpr (by rintro _ ⟨a,rfl⟩; exact ht a)
  have hdiff : weightTorusCharacter P b R t (μ-ν)=1 := hker h
  have he : weightTorusCharacter P b R t (μ-ν) =
      weightTorusCharacter P b R t μ / weightTorusCharacter P b R t ν := by
    exact
      (weightTorusCharacterHom P b R t).map_div
        (Multiplicative.ofAdd μ) (Multiplicative.ofAdd ν)
  exact div_eq_one.mp (he.symm.trans hdiff)

variable (Φ : RootType) (S : Finset (WeightLattice (rootDatum Φ).pairing))
  (hc : ∀ i μ, μ ∈ S → weightReflection (rootDatum Φ).pairing i μ ∈ S)
  (hm : ∀ μ ∈ S, ∀ i,
    μ (corootElement (rootDatum Φ).pairing i) = -1 ∨
    μ (corootElement (rootDatum Φ).pairing i) = 0 ∨
    μ (corootElement (rootDatum Φ).pairing i) = 1)
  (K : Type*) [Field K]

/-- Adding an orbit preserves the original literal adjoint block map. -/
theorem selectedWeightCompanionAdjoinOrbitEquiv_rho
    (g : WeightCompanion (rootDatum Φ).pairing (rootDatum Φ).base
      (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
      (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K) :
    selectedWeightCompanionRho Φ K (selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K g) =
      weightCompanionRho (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedAdjoinedWeightOrbits Φ S) (selectedAdjoinedWeightOrbits_closed Φ S hc)
        (selectedAdjoinedWeightOrbits_minuscule Φ S hm) K g := rfl

/-- The scalar is a unit, obtained from the actual torus character at μ₀.
The single-coset premise is a lattice statement, not an assumed scalar action. -/
theorem selectedWeightCompanionOrbitRepresentation_scalar_of_rho_eq_one
    (μ₀ : WeightLattice (rootDatum Φ).pairing)
    (hcoset : ∀ μ ∈ S, μ-μ₀ ∈ rootLattice (rootDatum Φ).pairing)
    (g : SelectedWeightCompanion Φ K) (hg : selectedWeightCompanionRho Φ K g=1) :
    ∃ c : Kˣ, (selectedWeightCompanionOrbitRepresentation Φ S hc hm K g).val =
      Matrix.diagonal (fun _ => c.val) := by
  let P := (rootDatum Φ).pairing
  let b := (rootDatum Φ).base
  let O := selectedAdjoinedWeightOrbits Φ S
  let hc' := selectedAdjoinedWeightOrbits_closed Φ S hc
  let hm' := selectedAdjoinedWeightOrbits_minuscule Φ S hm
  let e := selectedWeightCompanionAdjoinOrbitEquiv Φ S hc hm K
  let z := e.symm g
  have hz : weightCompanionRho P b O hc' hm' K z=1 := by
    rw [← selectedWeightCompanionAdjoinOrbitEquiv_rho Φ S hc hm K]
    change selectedWeightCompanionRho Φ K (e (e.symm g))=1
    rw [e.apply_symm_apply]
    exact hg
  have hT := weightCompanion_rhoKernel_le_torus P b O hc' hm' K
    (rootDatum_simpleDiamondProducts Φ) hz
  rw [weightCompanionTorusSubgroup_eq_range] at hT
  obtain ⟨t,ht⟩ := hT
  have htker : adjointTorusParameters P b K t=1 := by
    rw [← weightCompanionRho_torusParameters P b O hc' hm' K,ht]
    exact hz
  have hroot : ∀ a, weightTorusCharacter P b K t (rootWeight P a)=1 :=
    (adjointTorusParameters_eq_one_iff_character P K b t).mp htker
  have hconst (μ : WeightOrbit P S) :
      weightTorusCharacter P b K t μ.val=weightTorusCharacter P b K t μ₀ :=
    weightTorusCharacter_eq_of_sub_mem_rootLattice P b K t hroot μ.val μ₀
      (hcoset μ.val μ.property)
  refine ⟨weightTorusCharacter P b K t μ₀, ?_⟩
  change (z.val.2 none).val = _
  rw [← ht]
  change ((weightCompanionTorusProduct P b O hc' hm' K Finset.univ t).val.2 none).val = _
  rw [weightCompanionTorusProduct_minuscule]
  congr 1
  funext μ
  have hbase (i : b.support) : corootBasis P b i=corootElement P i.val := by
    apply Subtype.ext
    exact b.flip.coe_toWeightBasisInt_apply (⟨i.val,i.property⟩ : b.flip.support)
  have he := congrArg (fun c : Kˣ => c.val) (hconst μ)
  simpa [weightTorusCharacter,hbase,map_prod] using he

end Atlas.Chevalley
