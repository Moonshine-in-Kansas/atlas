import Atlas.Fischer.CubicTriangleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicCoordinate_pair_transport (i j a b : Omega) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ g : Mathieu24CodeModel,g.val i=a ∧ g.val j=b := by
  let e : Fin 2 ↪ Omega := ⟨![i,j],by intro x y h; fin_cases x <;> fin_cases y <;> simp_all⟩
  let f : Fin 2 ↪ Omega := ⟨![a,b],by intro x y h; fin_cases x <;> fin_cases y <;> simp_all⟩
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 := by
    letI := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by norm_num [Omega,HexIndex])
  obtain ⟨g,hg⟩ := MulAction.isMultiplyPretransitive_iff.mp ht e f
  exact ⟨g,congrArg (fun e => e 0) hg,congrArg (fun e => e 1) hg⟩

theorem cubicCoordinate_point_transport (i a : Omega) :
    ∃ g : Mathieu24CodeModel,g.val i=a := by
  let e : Fin 1 ↪ Omega := ⟨fun _ => i,fun _ _ _ => Subsingleton.elim _ _⟩
  let f : Fin 1 ↪ Omega := ⟨fun _ => a,fun _ _ _ => Subsingleton.elim _ _⟩
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 1 := by
    letI := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 1 ≤ 5)
      (by norm_num [Omega,HexIndex])
  obtain ⟨g,hg⟩ := MulAction.isMultiplyPretransitive_iff.mp ht e f
  exact ⟨g,congrArg (fun e => e 0) hg⟩

abbrev CubicCoordinateInvariant (f : Omega → Omega → Omega → Scalar) : Prop :=
  ∀ (g : Mathieu24CodeModel) i j k,f (g.val i) (g.val j) (g.val k)=f i j k

theorem cubicInvariant_diagonal_average (f : Omega → Omega → Omega → Scalar)
    (hf : CubicCoordinateInvariant f) (i : Omega) :
    (∑ a,f a a a)=24*f i i i := by
  have he (a : Omega) : f a a a=f i i i := by
    obtain ⟨g,hg⟩ := cubicCoordinate_point_transport i a
    simpa only [hg] using hf g i i i
  simp_rw [he]
  have hc : Fintype.card Omega=24 := by decide
  simp [hc]

theorem cubicInvariant_two_equal_average (f : Omega → Omega → Omega → Scalar)
    (hf : CubicCoordinateInvariant f) (i j : Omega) (hij : i ≠ j) :
    (∑ a,∑ b,if a ≠ b then f a a b else 0)=552*f i i j := by
  have he (a b : Omega) : (if a ≠ b then f a a b else 0)=
      (if a ≠ b then (1 : Scalar) else 0)*f i i j := by
    by_cases hab : a=b
    · simp [hab]
    · obtain ⟨g,hga,hgb⟩ := cubicCoordinate_pair_transport i j a b hij hab
      have hv := hf g i i j
      simp only [hga,hgb] at hv
      simp [hab,hv]
  simp_rw [he,← Finset.sum_mul]
  have hc : Fintype.card Omega=24 := by decide
  have hn : (∑ a : Omega,∑ b : Omega,if a ≠ b then (1 : Scalar) else 0)=552 := by
    have hh := cubicTriangle_two_equal_sum (fun _ : Omega => (1 : Scalar))
      (fun _ => 1) (fun _ => 1)
    norm_num [hc] at hh
    simpa using hh
  rw [hn]

theorem cubicInvariant_distinct_average (f : Omega → Omega → Omega → Scalar)
    (hf : CubicCoordinateInvariant f) (i j k : Omega)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ a,∑ b,∑ c,if a ≠ b ∧ a ≠ c ∧ b ≠ c then f a b c else 0)=12144*f i j k := by
  have he (a b c : Omega) :
      (if a ≠ b ∧ a ≠ c ∧ b ≠ c then f a b c else 0)=
      (if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : Scalar) else 0)*f i j k := by
    by_cases habc : a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨g,hga,hgb,hgc⟩ := mathieu24_ordered_triple_transport i j k a b c
        hij hik.symm hjk.symm habc.1 habc.2.1.symm habc.2.2.symm
      have hv := hf g i j k
      simp only [hga,hgb,hgc] at hv
      simp [habc,hv]
    · simp [habc]
  simp_rw [he,← Finset.sum_mul]
  have hc : Fintype.card Omega=24 := by decide
  have hn : (∑ a : Omega,∑ b : Omega,∑ c : Omega,
      if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : Scalar) else 0)=12144 := by
    have hh := cubicTriangle_distinct_sum (fun _ : Omega => (1 : Scalar))
      (fun _ => 1) (fun _ => 1)
    norm_num [hc] at hh
    simpa using hh
  rw [hn]

end Atlas.Fischer
