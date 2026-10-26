import Atlas.LinearGroups.Orthogonal.OddCoordinateGeneration

/-! Transport the two short families from one axis using mixed long roots.
The conclusion is an explicit image criterion, with no assumed spin map. -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable (r : ℕ) (F : Type*) [Field F]

def oddLongWeyl (i j : Fin r) (hij : i ≠ j) : O_B r F :=
  oddLong r F i j hij 1 * oddLong r F j i (Ne.symm hij) (-1) * oddLong r F i j hij 1

theorem oddLongWeyl_e (i j : Fin r) (hij : i ≠ j) :
    (oddLongWeyl r F i j hij).val (e j,0) = (e i,0) := by
  change (oddLong r F i j hij 1).val
    ((oddLong r F j i (Ne.symm hij) (-1)).val ((oddLong r F i j hij 1).val (e j,0))) = _
  apply Prod.ext
  · funext k
    cases k with
    | inl k =>
      simp only [oddLong_apply_x]
      by_cases hi : i = k
      · subst k
        simp only [e, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq, eq_self, hij, Ne.symm hij, ite_true, ite_false] <;> ring
      · by_cases hj : j = k
        · subst k
          simp only [e, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq,
            reduceCtorEq, eq_self, hij, Ne.symm hij, ite_true, ite_false] <;> ring
        · simp only [e, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq,
            reduceCtorEq, eq_self, hij, Ne.symm hij, hi, Ne.symm hi,
            hj, Ne.symm hj, ite_true, ite_false] <;> ring
    | inr k => simp [e, Pi.single_apply]
  · simp

theorem oddLongWeyl_f (i j : Fin r) (hij : i ≠ j) :
    (oddLongWeyl r F i j hij).val (f j,0) = (f i,0) := by
  change (oddLong r F i j hij 1).val
    ((oddLong r F j i (Ne.symm hij) (-1)).val ((oddLong r F i j hij 1).val (f j,0))) = _
  apply Prod.ext
  · funext k
    cases k with
    | inl k => simp [f, Pi.single_apply]
    | inr k =>
      simp only [oddLong_apply_y]
      by_cases hi : i = k
      · subst k
        simp only [f, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq, eq_self, hij, Ne.symm hij, ite_true, ite_false] <;> ring
      · by_cases hj : j = k
        · subst k
          simp only [f, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq,
            reduceCtorEq, eq_self, hij, Ne.symm hij, ite_true, ite_false] <;> ring
        · simp only [f, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq,
            reduceCtorEq, eq_self, hij, Ne.symm hij, hi, Ne.symm hi,
            hj, Ne.symm hj, ite_true, ite_false] <;> ring
  · simp

theorem oddLongWeyl_z (i j : Fin r) (hij : i ≠ j) (t : F) :
    (oddLongWeyl r F i j hij).val (0,t) = (0,t) := by
  change (oddLong r F i j hij 1).val
    ((oddLong r F j i (Ne.symm hij) (-1)).val ((oddLong r F i j hij 1).val (0,t))) = _
  apply Prod.ext
  · funext k
    cases k <;> simp
  · simp

theorem oddLongWeyl_conj_upper (i j : Fin r) (hij : i ≠ j) (t : F) :
    oddLongWeyl r F i j hij * oddShortUpper r F j t *
      (oddLongWeyl r F i j hij)⁻¹ = oddShortUpper r F i t := by
  rw [oddShortUpper, siegelElement_conj]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel (formB r F) ((oddLongWeyl r F i j hij).val (e j,0))
    ((oddLongWeyl r F i j hij).val (0,t)) x = siegel (formB r F) (e i,0) (0,t) x
  rw [oddLongWeyl_e, oddLongWeyl_z]

theorem oddLongWeyl_conj_lower (i j : Fin r) (hij : i ≠ j) (t : F) :
    oddLongWeyl r F i j hij * oddShortLower r F j t *
      (oddLongWeyl r F i j hij)⁻¹ = oddShortLower r F i t := by
  rw [oddShortLower, siegelElement_conj]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel (formB r F) ((oddLongWeyl r F i j hij).val (f j,0))
    ((oddLongWeyl r F i j hij).val (0,-t)) x = siegel (formB r F) (f i,0) (0,-t) x
  rw [oddLongWeyl_f, oddLongWeyl_z]

/-- All mixed long roots and the two short families at one chosen axis generate
the existing elementary odd orthogonal subgroup, over every field. -/
theorem elementary_le_of_odd_long_and_one_axis (hr : 2 ≤ r)
    (H : Subgroup (O_B r F)) (k : Fin r)
    (hl : ∀ i j (hij : i ≠ j) t, oddLong r F i j hij t ∈ H)
    (hu : ∀ t, oddShortUpper r F k t ∈ H)
    (hd : ∀ t, oddShortLower r F k t ∈ H) :
    elementarySubgroup (formB r F) ≤ H := by
  have hw (i j : Fin r) (hij : i ≠ j) : oddLongWeyl r F i j hij ∈ H :=
    H.mul_mem (H.mul_mem (hl i j hij 1) (hl j i (Ne.symm hij) (-1))) (hl i j hij 1)
  apply elementary_le_of_odd_coordinate_roots r F hr H hl
  · intro i t
    by_cases hi : i=k
    · subst i
      exact hu t
    · rw [← oddLongWeyl_conj_upper r F i k hi t]
      exact H.mul_mem (H.mul_mem (hw i k hi) (hu t)) (H.inv_mem (hw i k hi))
  · intro i t
    by_cases hi : i=k
    · subst i
      exact hd t
    · rw [← oddLongWeyl_conj_lower r F i k hi t]
      exact H.mul_mem (H.mul_mem (hw i k hi) (hd t)) (H.inv_mem (hw i k hi))

/-- A reusable range criterion; the homomorphism and every marked lift are
explicit hypotheses, not an assertion that a global spin map already exists. -/
theorem elementary_le_range_of_odd_markings (hr : 2 ≤ r)
    {G : Type*} [Group G] (φ : G →* O_B r F) (k : Fin r)
    (hl : ∀ i j (hij : i ≠ j) t, ∃ g, φ g = oddLong r F i j hij t)
    (hu : ∀ t, ∃ g, φ g = oddShortUpper r F k t)
    (hd : ∀ t, ∃ g, φ g = oddShortLower r F k t) :
    elementarySubgroup (formB r F) ≤ φ.range :=
  elementary_le_of_odd_long_and_one_axis r F hr φ.range k hl hu hd

end Atlas.Orthogonal
