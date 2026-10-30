import FamilyWork.F4RootWeights

/-! Source-only comparison of the literal E6 inversion length with an actual
weighted F4 root-inversion statistic. Positivity is transported by genuine
diagram symmetrizations in the audited rational fixed space. Weighted inversion
descent is proved separately, rather than assumed from a weighted word formula.
No Weyl enumeration or Poincare evaluation occurs. Uncompiled and unaudited. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6.E6WeightedLength
open Classical RootData FixedWeylFaithfulness FixedSpaceAdapter
  F4ActionAdapter FoldedWeylIdentification F4RootWeights

local instance weightedLengthRootFintype : Fintype E6Data.Root := Fintype.ofFinite _

theorem pi_sumCoords {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → ℚ) :
    (Pi.basisFun ℚ κ).sumCoords x = ∑ k, x k := by
  simp only [Module.Basis.coe_sumCoords_of_fintype, LinearMap.sum_apply,
    Module.Basis.coord_apply, Pi.basisFun_repr]

section PositiveCoordinates

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Positivity in the actual base is exactly nonnegativity of its rational root coordinates. -/
theorem rationalRoot_positive_iff (β : ι) :
    b.IsPos β ↔ ∀ i : b.support, 0 ≤ rationalRootCoordinates P b β i := by
  constructor
  · intro hβ i
    rw [rationalRootCoordinates_coefficient]
    exact_mod_cast rootSimpleCoefficients_nonneg P b hβ i
  · intro hβ
    have hh : 0 ≤ (b.height β : ℚ) := by
      rw [← rationalRootCoordinates_sumCoords P b β, pi_sumCoords]
      exact Finset.sum_nonneg (fun i _ => hβ i)
    apply b.isPos_iff'.mpr
    exact_mod_cast hh

end PositiveCoordinates

theorem f4Root_positive_iff (β : F4Data.Root) :
    F4Data.base.IsPos β ↔ ∀ a : Fin 4, 0 ≤ f4RootVector β a := by
  constructor
  · intro hβ a
    exact (rationalRoot_positive_iff F4Data.pairing F4Data.base β).mp hβ
      (F4Data.baseIndexEquiv a)
  · intro hβ
    apply (rationalRoot_positive_iff F4Data.pairing F4Data.base β).mpr
    intro j
    obtain ⟨a, rfl⟩ := F4Data.baseIndexEquiv.surjective j
    exact hβ a

/-- The explicit fixed-space adapter preserves the nonnegative coordinate cone. -/
theorem fixedCoordinates_nonnegative_iff (x : fixedRootSpace) :
    (∀ j : E6Data.base.support, 0 ≤ x.val j) ↔
      ∀ a : Fin 4, 0 ≤ fixedRootSpaceCoordinates x a := by
  constructor
  · intro hx a
    rw [fixedRootSpaceCoordinates_public]
    fin_cases a <;> exact hx _
  · intro hx j
    obtain ⟨i, rfl⟩ := latticeBaseEquiv.surjective j
    change 0 ≤ rootSpaceToLattice x.val i
    rw [← fixedRootSpaceCoordinates_expand x]
    fin_cases i
    · exact hx 0
    · exact hx 1
    · exact hx 2
    · exact hx 1
    · exact hx 0
    · exact hx 3

theorem rootDiagram_height (β : E6Data.Root) :
    E6Data.base.height (rootDiagram β) = E6Data.base.height β := by
  simp only [e6_height_eq_coordinate_sum, rootDiagram_val, latticeDiagram_apply]
  exact Equiv.sum_comp latticeNode β.val

/-- Literal two-term symmetrization; fixed roots are doubled, not silently rescaled. -/
def diagramSymmetrization (β : E6Data.Root) : fixedRootSpace :=
  ⟨rootVector β + rootVector (rootDiagram β), by
    change rootSpaceDiagram (rootVector β + rootVector (rootDiagram β)) = _
    rw [map_add, rootSpaceDiagram_root, rootSpaceDiagram_root, rootDiagram_involutive]
    exact add_comm _ _⟩

theorem diagramSymmetrization_height (β : E6Data.Root) :
    heightFunctional (diagramSymmetrization β).val = 2 * (E6Data.base.height β : ℚ) := by
  change heightFunctional (rootVector β + rootVector (rootDiagram β)) = _
  rw [map_add, height_rootVector, height_rootVector, rootDiagram_height]
  ring

/-- A root and its diagram mate have the same sign. Their genuine fixed-space
symmetrization has nonnegative coordinates exactly for positive roots. -/
theorem diagramSymmetrization_positive_iff (β : E6Data.Root) :
    E6Data.base.IsPos β ↔
      ∀ a : Fin 4, 0 ≤ fixedRootSpaceCoordinates (diagramSymmetrization β) a := by
  constructor
  · intro hβ
    apply (fixedCoordinates_nonnegative_iff (diagramSymmetrization β)).mp
    intro j
    exact add_nonneg
      ((rationalRoot_positive_iff E6Data.pairing E6Data.base β).mp hβ j)
      ((rationalRoot_positive_iff E6Data.pairing E6Data.base (rootDiagram β)).mp
        ((e6_rootDiagram_isPos_iff β).mpr hβ) j)
  · intro hβ
    have hv := (fixedCoordinates_nonnegative_iff (diagramSymmetrization β)).mpr hβ
    have hh : 0 ≤ heightFunctional (diagramSymmetrization β).val := by
      change 0 ≤ (Pi.basisFun ℚ E6Data.base.support).sumCoords
        (diagramSymmetrization β).val
      rw [pi_sumCoords]
      exact Finset.sum_nonneg (fun j _ => hv j)
    rw [diagramSymmetrization_height] at hh
    have hh' : 0 ≤ (E6Data.base.height β : ℚ) := by linarith
    apply E6Data.base.isPos_iff'.mpr
    exact_mod_cast hh'

theorem diagramSymmetrization_weyl (w : diagramFixedWeylSubgroup) (β : E6Data.Root) :
    fixedRootSpaceRestriction w.val (fixed_commute w) (diagramSymmetrization β) =
      diagramSymmetrization (w.val.val β) := by
  apply Subtype.ext
  change weylLinear w.val (rootVector β + rootVector (rootDiagram β)) =
    rootVector (w.val.val β) + rootVector (rootDiagram (w.val.val β))
  rw [map_add, weylLinear_root, weylLinear_root, ← fixed_commute w β]

/-- Representatives in the inherited public E6 simple-node indexing. -/
def foldedSimpleNode : Fin 4 → Fin 6 := ![0, 2, 3, 1]

abbrev foldedSimpleRoot (a : Fin 4) : E6Data.Root :=
  (E6Data.baseIndexEquiv (foldedSimpleNode a)).val

/-- Symmetrization contributes one pair-sum or twice a fixed simple root. -/
def foldedSimpleScale : Fin 4 → ℚ := ![1, 1, 2, 2]

theorem foldedSimpleScale_pos (a : Fin 4) : 0 < foldedSimpleScale a := by
  fin_cases a <;> norm_num [foldedSimpleScale]

theorem diagramSymmetrization_simple (a : Fin 4) :
    fixedRootSpaceCoordinates (diagramSymmetrization (foldedSimpleRoot a)) =
      foldedSimpleScale a • f4RootVector (F4Data.baseIndexEquiv a).val := by
  have hs (i k : Fin 6) :
      rootVector (E6Data.baseIndexEquiv i).val (E6Data.baseIndexEquiv k) =
        if i = k then 1 else 0 := by
    change rationalRootCoordinates E6Data.pairing E6Data.base
      (E6Data.baseIndexEquiv i).val (E6Data.baseIndexEquiv k) = _
    rw [rationalRootCoordinates_simple]
    simp only [Equiv.apply_eq_iff_eq]
  have hd (i k : Fin 6) :
      rootVector (rootDiagram (E6Data.baseIndexEquiv i).val)
        (E6Data.baseIndexEquiv k) = if simpleNode i = k then 1 else 0 := by
    rw [e6_rootDiagram_baseIndex]
    exact hs (simpleNode i) k
  rw [fixedRootSpaceCoordinates_public, f4RootVector_simple]
  funext j
  fin_cases a <;> fin_cases j <;>
    simp only [diagramSymmetrization, foldedSimpleRoot, foldedSimpleNode, foldedSimpleScale,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.add_apply, Pi.smul_apply,
      hs, hd, simpleNode_table, Pi.single_apply, smul_eq_mul] <;>
      norm_num only [Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk] <;> norm_num

/-- The simple-orbit comparison is transported by every actual fixed Weyl element. -/
theorem diagramSymmetrization_weyl_simple (w : diagramFixedWeylSubgroup) (a : Fin 4) :
    fixedRootSpaceCoordinates (diagramSymmetrization (w.val.val (foldedSimpleRoot a))) =
      foldedSimpleScale a •
        f4RootVector ((fixedWeylEquivF4 w).val (F4Data.baseIndexEquiv a).val) := by
  have he := congrArg
    (fun T : Module.End ℚ FourSpace =>
      T (fixedRootSpaceCoordinates (diagramSymmetrization (foldedSimpleRoot a))))
    (fixedWeylEquivF4_action w)
  rw [fixedAction_apply, LinearEquiv.symm_apply_apply, diagramSymmetrization_weyl,
    diagramSymmetrization_simple, map_smul, f4Action_root] at he
  simpa only [RingHom.id_apply] using he.symm

/-- Exact simple-descent sign comparison under the actual multiplicative identification. -/
theorem simple_image_positive_iff (w : diagramFixedWeylSubgroup) (a : Fin 4) :
    E6Data.base.IsPos (w.val.val (foldedSimpleRoot a)) ↔
      F4Data.base.IsPos ((fixedWeylEquivF4 w).val (F4Data.baseIndexEquiv a).val) := by
  rw [diagramSymmetrization_positive_iff, diagramSymmetrization_weyl_simple,
    f4Root_positive_iff]
  simp only [Pi.smul_apply, smul_eq_mul,
    mul_nonneg_iff_of_pos_left (foldedSimpleScale_pos a)]

/-- A negative image removes one fixed simple letter or a commuting pair of E6 letters. -/
theorem e6Length_mul_generator_of_negative (w : diagramFixedWeylSubgroup) (a : Fin 4)
    (hneg : ¬ E6Data.base.IsPos (w.val.val (foldedSimpleRoot a))) :
    rootWeylLength E6Data.pairing E6Data.base (w * fixedGenerator a).val +
        e6FoldedWeylWeight a = rootWeylLength E6Data.pairing E6Data.base w.val := by
  fin_cases a
  · change rootWeylLength E6Data.pairing E6Data.base
      (w.val * (e6RootSimpleReflection 0 * e6RootSimpleReflection 5)) + 2 = _
    simpa only [show simpleNode (0 : Fin 6) = 5 from rfl, mul_assoc] using
      e6RootWeyl_length_pair_descent w.val (fixed_commute w) 0 (by decide) hneg
  · change rootWeylLength E6Data.pairing E6Data.base
      (w.val * (e6RootSimpleReflection 2 * e6RootSimpleReflection 4)) + 2 = _
    simpa only [show simpleNode (2 : Fin 6) = 4 from rfl, mul_assoc] using
      e6RootWeyl_length_pair_descent w.val (fixed_commute w) 2 (by decide) hneg
  · exact rootWeylLength_mul_simple_of_negative E6Data.pairing E6Data.base
      w.val (E6Data.baseIndexEquiv 3) hneg
  · exact rootWeylLength_mul_simple_of_negative E6Data.pairing E6Data.base
      w.val (E6Data.baseIndexEquiv 1) hneg

/-- The actual E6 Coxeter length equals the independently defined weighted
inversion sum on actual F4 roots. The proof is descent induction, not a
recognition argument or an assumed weighted reduced-expression theorem. -/
theorem e6Length_eq_f4WeightedInversions (w : diagramFixedWeylSubgroup) :
    rootWeylLength E6Data.pairing E6Data.base w.val =
      f4WeightedInversions (fixedWeylEquivF4 w) := by
  have aux : ∀ n : ℕ, ∀ w : diagramFixedWeylSubgroup,
      rootWeylLength E6Data.pairing E6Data.base w.val = n →
      rootWeylLength E6Data.pairing E6Data.base w.val =
        f4WeightedInversions (fixedWeylEquivF4 w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      by_cases hw : w = 1
      · subst w
        simp only [Subgroup.coe_one, map_one, rootWeylLength_one,
          f4WeightedInversions_one]
      · have hF4 : fixedWeylEquivF4 w ≠ 1 := by
          intro he
          apply hw
          apply fixedWeylEquivF4.injective
          simpa only [map_one] using he
        obtain ⟨j, hj⟩ := rootWeyl_exists_simple_descent_of_ne_one
          F4Data.pairing F4Data.base (fixedWeylEquivF4 w) hF4
        obtain ⟨a, rfl⟩ := F4Data.baseIndexEquiv.surjective j
        have hE6 : ¬ E6Data.base.IsPos (w.val.val (foldedSimpleRoot a)) :=
          fun hp => hj ((simple_image_positive_iff w a).mp hp)
        let v : diagramFixedWeylSubgroup := w * fixedGenerator a
        have hd : rootWeylLength E6Data.pairing E6Data.base v.val +
            e6FoldedWeylWeight a = rootWeylLength E6Data.pairing E6Data.base w.val :=
          e6Length_mul_generator_of_negative w a hE6
        have hweight := e6FoldedWeylWeight_pos a
        have hvlt : rootWeylLength E6Data.pairing E6Data.base v.val < n := by omega
        have hi := ih _ hvlt v rfl
        have hs : f4WeightedInversions (fixedWeylEquivF4 v) + e6FoldedWeylWeight a =
            f4WeightedInversions (fixedWeylEquivF4 w) := by
          dsimp only [v]
          rw [map_mul, fixedWeylEquivF4_generator]
          exact f4WeightedInversions_mul_simple_of_negative (fixedWeylEquivF4 w) a hj
        omega
  exact aux _ w rfl

theorem e6InversionCount_eq_f4WeightedInversions (w : diagramFixedWeylSubgroup) :
    rootInversionCount E6Data.pairing E6Data.base w.val =
      f4WeightedInversions (fixedWeylEquivF4 w) := by
  rw [rootInversionCount_eq_rootWeylLength, e6Length_eq_f4WeightedInversions]

theorem e6Length_eq_long_short_inversion_sum (w : diagramFixedWeylSubgroup) :
    rootWeylLength E6Data.pairing E6Data.base w.val =
      ∑ β ∈ rootInversions F4Data.pairing F4Data.base (fixedWeylEquivF4 w),
        if Atlas.F4.RootData.IsLong β then 2 else 1 :=
  (e6Length_eq_f4WeightedInversions w).trans
    (f4WeightedInversions_eq_sum (fixedWeylEquivF4 w))

theorem inheritedE6Length_eq_f4WeightedInversions (w : F4Weyl) :
    inheritedE6Length w = f4WeightedInversions w := by
  unfold inheritedE6Length
  simpa only [MulEquiv.apply_symm_apply] using
    e6Length_eq_f4WeightedInversions (fixedWeylEquivF4.symm w)

/-- Exact adapter for the existing literal fixed Bruhat index and exponent. -/
theorem fixedBruhatIndex_length_eq_weighted (w : E6DiagramFixedWeyl) :
    rootWeylLength (rootDatum .E6).pairing (rootDatum .E6).base w.val =
      f4WeightedInversions (fixedBruhatIndexEquivF4 w) :=
  e6Length_eq_f4WeightedInversions (fixedBruhatIndexEquiv w)

end Atlas.Chevalley.TwistedE6.E6WeightedLength
