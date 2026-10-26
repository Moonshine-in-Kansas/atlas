import Atlas.LinearGroups.Chevalley.Integral.WeightedSupportNilpotent
import Atlas.LinearGroups.Chevalley.Integral.GradedAdjoint

/-! UNCHECKED actual Geck application. A single-edge raising bracket has
positive degree for the sum of its two coroot weights. This does not use
simple-diamond arithmetic, Serre identities, or a root-group commutator. -/
noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual integral bracket has degree two for the sum of the two
simple-coroot weight functions. Only the two Cartan equations are needed. -/
theorem raising_a2_bracket_weightedSupport (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    WeightedSupport (fun a => geckWeight P b i a + geckWeight P b j a) 2
      (raising P b i * raising P b j - raising P b j * raising P b i) := by
  have hi : WeightedSupport (fun a => geckWeight P b i a + geckWeight P b j a) 1
      (raising P b i) := by
    intro a c hac
    have hself := raising_weightedSupport P b i i a c hac
    have hcross := raising_weightedSupport P b j i a c hac
    rw [b.cartanMatrix_apply_same] at hself
    rw [hij] at hcross
    dsimp only at *
    omega
  have hj : WeightedSupport (fun a => geckWeight P b i a + geckWeight P b j a) 1
      (raising P b j) := by
    intro a c hac
    have hcross := raising_weightedSupport P b i j a c hac
    have hself := raising_weightedSupport P b j j a c hac
    rw [hji] at hcross
    rw [b.cartanMatrix_apply_same] at hself
    dsimp only at *
    omega
  have hprod : WeightedSupport (fun a => geckWeight P b i a + geckWeight P b j a) 2
      (raising P b i * raising P b j) := by simpa using hi.mul hj
  have hrev : WeightedSupport (fun a => geckWeight P b i a + geckWeight P b j a) 2
      (raising P b j * raising P b i) := by simpa using hj.mul hi
  intro a c hac
  by_cases hp : (raising P b i * raising P b j) a c = 0
  · have hr : (raising P b j * raising P b i) a c ≠ 0 := by
      intro hr
      apply hac
      simp only [Matrix.sub_apply, hp, hr, sub_self]
    exact hrev a c hr
  · exact hprod a c hp

/-- Nilpotence is proved over the integers before any coefficient reduction. -/
theorem raising_a2_bracket_isNilpotent (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    IsNilpotent (raising P b i * raising P b j - raising P b j * raising P b i) :=
  (raising_a2_bracket_weightedSupport P b i j hij hji).isNilpotent_of_degree_pos
    (by decide)

/-- Actual coefficient reduction preserves bracket nilpotence in every
commutative ring, including characteristics two and three. -/
theorem raisingOver_a2_bracket_isNilpotent (R : Type*) [CommRing R]
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    IsNilpotent (raisingOver P b R i * raisingOver P b R j -
      raisingOver P b R j * raisingOver P b R i) := by
  have h := (raising_a2_bracket_isNilpotent P b i j hij hji).map
    (Int.castRingHom R).mapMatrix
  simp only [map_sub, map_mul] at h
  simpa only [raisingOver, RingHom.mapMatrix_apply] using h

end Atlas.Chevalley.Integral
