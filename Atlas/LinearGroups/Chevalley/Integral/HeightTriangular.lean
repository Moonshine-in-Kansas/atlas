import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Atlas.LinearGroups.Chevalley.Integral.GradedMatrix
import Atlas.LinearAlgebra.HeightUnitriangular

/-! Exact integral height degrees for the actual Geck raising matrices and
their divided powers. Unitriangularity is then reduced to any coefficient
ring; no factorial is divided out in that ring. -/

noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual adjoint basis height: Cartan coordinates have height zero and
root coordinates have the height of that root in the chosen base. -/
def geckHeight : b.support ⊕ ι → ℤ := Sum.elim (fun _ => 0) b.height

/-- A nonzero entry of the actual simple raising operator increases height
by exactly one. This includes both Cartan/root transition blocks. -/
theorem raising_height_weightedSupport (i : b.support) :
    WeightedSupport (geckHeight P b) 1 (raising P b i) := by
  let := P.indexNeg
  have hi : b.height i.val = 1 :=
    RootPairing.Base.height_one_of_mem_support i.property
  intro row col hne
  rcases row with a | a <;> rcases col with c | c
  · simp [raising, RootPairing.GeckConstruction.e] at hne
  · have hc : c = -i.val := by
      by_contra hc
      simp [raising, RootPairing.GeckConstruction.e, -RootPairing.indexNeg_neg, hc] at hne
    subst c
    simp [geckHeight, b.height_reflectionPerm_self, -RootPairing.indexNeg_neg, hi]
  · have ha : a = i.val := by
      by_contra ha
      simp [raising, RootPairing.GeckConstruction.e, ha] at hne
    subst a
    simp [geckHeight, hi]
  · have hac : P.root a = P.root i + P.root c := by
      by_contra hac
      simp [raising, RootPairing.GeckConstruction.e, hac] at hne
    simpa [geckHeight, hi, add_comm] using
      b.height_add hac

/-- Degree n is proved before reduction, using cancellation only in the
integer divided-power equation. -/
theorem raisingDividedPower_height_weightedSupport (i : b.support) (n : ℕ) :
    WeightedSupport (geckHeight P b) (n : ℤ) (raisingDividedPower P b i n) := by
  simpa using (raising_height_weightedSupport P b i).divided n
    (factorial_smul_raisingDividedPower P b i n)

variable (R : Type*) [CommRing R]

/-- Positive divided powers vanish where row height is at most column height, over
every commutative ring, including characteristics two and three. -/
theorem raisingDividedOver_eq_zero_of_height_le (i : b.support) (n : ℕ)
    (hn : 0 < n) (row col : b.support ⊕ ι)
    (hheight : geckHeight P b row ≤ geckHeight P b col) :
    raisingDividedOver P b R i n row col = 0 := by
  have hz : raisingDividedPower P b i n row col = 0 := by
    by_contra hne
    have he := raisingDividedPower_height_weightedSupport P b i n row col hne
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    omega
  simp [raisingDividedOver, Matrix.map_apply, hz]

/-- The actual positive root element is unitriangular for the integer height
filtration, with no hypothesis on characteristic or field size. -/
theorem raisingExponential_heightUnitriangular (i : b.support) (t : R) :
    Atlas.Matrix.HeightUnitriangular (geckHeight P b)
      (raisingExponential P b R i t) := by
  intro row col hheight
  have h1 := raisingDividedOver_eq_zero_of_height_le P b R i 1 (by decide)
    row col hheight
  have h2 := raisingDividedOver_eq_zero_of_height_le P b R i 2 (by decide)
    row col hheight
  have h3 := raisingDividedOver_eq_zero_of_height_le P b R i 3 (by decide)
    row col hheight
  rw [raisingDividedOver_one] at h1
  simp [raisingExponential_expansion, Matrix.add_apply, Matrix.smul_apply,
    h1, h2, h3]

theorem raisingRootElement_mem_heightUnitriangular (i : b.support) (t : R) :
    raisingRootElement P b R i t ∈
      Atlas.Matrix.heightUnitriangularSubgroup (geckHeight P b) := by
  exact ⟨raisingExponential_heightUnitriangular P b R i t,
    raisingExponential_heightUnitriangular P b R i (-t)⟩

end Atlas.Chevalley.Integral
