import Atlas.LinearGroups.Chevalley.Integral.MinusculeDOrbit
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDParityMoves

/-! actual D reflections preserve each half-spin sign-product fibre. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

/-- Exact doubled spin pairing at each D root. -/
theorem twice_spinWeight_long_pairing (n : ℕ) (σ : Fin (n+2) → Bool)
    (i j : Fin (n+2)) (hij : i≠j) (t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) :
    2 * spinWeight n σ (corootElement (pairingD (n+2)) (longRoot false i j hij t u ht hu)) =
      t * sign (σ i) + u * sign (σ j) := by
  have h := twice_spinWeight_apply n σ
    (corootElement (pairingD (n+2)) (longRoot false i j hij t u ht hu))
  change 2 * spinWeight n σ (corootElement (pairingD (n+2)) (longRoot false i j hij t u ht hu)) =
    ∑ k, sign (σ k) * coroot (longRoot false i j hij t u ht hu) (Pi.single k 1) at h
  simp only [coroot_long] at h
  simp only [Pi.single_apply, mul_ite, mul_zero, mul_one, mul_add,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  simpa [mul_comm] using h

/-- Both parity fibres satisfy the minuscule bound at every actual D root. -/
theorem spinWeight_minuscule (n : ℕ) (σ : Fin (n+2) → Bool) (a : DRoot (n+2)) :
    spinWeight n σ (corootElement (pairingD (n+2)) a) = -1 ∨
    spinWeight n σ (corootElement (pairingD (n+2)) a) = 0 ∨
    spinWeight n σ (corootElement (pairingD (n+2)) a) = 1 := by
  rcases signed_support_classification a with ⟨h,_⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · cases h
  · have he : a=longRoot false i j hij t u ht hu := Subtype.ext ha
    subst a
    have h := twice_spinWeight_long_pairing n σ i j hij t u ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      cases hi : σ i <;> cases hj : σ j <;> simp [sign, hi, hj] at h <;> omega

def signVector (n : ℕ) (σ : Fin (n+2) → Bool) : ClassicalData.Lattice (n+2) := fun k => sign (σ k)

theorem signVector_expansion (n : ℕ) (σ : Fin (n+2) → Bool) :
    signVector n σ = ∑ k, sign (σ k) • (Pi.single k 1 : Fin (n+2) → ℤ) := by
  ext j
  simp [signVector, Pi.single_apply]

theorem twice_spinWeight_evaluation (n : ℕ) (σ : Fin (n+2) → Bool)
    (x : CorootLattice (pairingD (n+2))) : 2*spinWeight n σ x = x.val (signVector n σ) := by
  rw [twice_spinWeight_apply, signVector_expansion]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- A signed-pair reflection is an actual signed coordinate exchange. -/
theorem reflect_long_coordinates {r : ℕ} (i j : Fin r) (hij : i≠j)
    (t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) (x : ClassicalData.Lattice r) (k : Fin r) :
    reflect (longRoot false i j hij t u ht hu) x k =
      if k=i then -t*u*x j else if k=j then -t*u*x i else x k := by
  change (x-coroot (longRoot false i j hij t u ht hu) x •
    (longRoot false i j hij t u ht hu).val) k = _
  rw [coroot_long]
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    by_cases hi : k=i <;> by_cases hj : k=j <;>
    simp [longRoot,hi,hj,hij,eq_comm]

theorem signVector_signedSwap (n : ℕ) (σ : Fin (n+2) → Bool)
    (i j : Fin (n+2)) (hij : i≠j) (t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) :
    signVector n (DParity.signedSwap σ i j (decide (t=u))) =
      reflect (longRoot false i j hij t u ht hu) (signVector n σ) := by
  ext k
  rw [reflect_long_coordinates]
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
  all_goals
    by_cases hi : k=i
    · subst k
      cases hσi : σ i <;> cases hσj : σ j <;>
        simp [signVector,sign,DParity.signedSwap,DParity.pairFlip,DParity.flip,DParity.swap,
          hij,Ne.symm hij,hσi,hσj]
    · by_cases hj : k=j
      · subst k
        cases hσi : σ i <;> cases hσj : σ j <;>
          simp [signVector,sign,DParity.signedSwap,DParity.pairFlip,DParity.flip,DParity.swap,
            hij,Ne.symm hij,hσi,hσj]
      · simp [signVector,DParity.signedSwap,DParity.pairFlip,DParity.flip,DParity.swap,
          hi,hj,Ne.symm hi,Ne.symm hj,Equiv.swap_apply_of_ne_of_ne hi hj]

/-- The coordinate action is the actual weight reflection, by integral cancellation. -/
theorem spinWeight_long_reflection (n : ℕ) (σ : Fin (n+2) → Bool)
    (i j : Fin (n+2)) (hij : i≠j) (t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) :
    weightReflection (pairingD (n+2)) (longRoot false i j hij t u ht hu) (spinWeight n σ) =
      spinWeight n (DParity.signedSwap σ i j (decide (t=u))) := by
  let a := longRoot false i j hij t u ht hu
  ext x
  have hx := twice_spinWeight_evaluation n σ x
  have ha := twice_spinWeight_evaluation n σ (corootElement (pairingD (n+2)) a)
  have hy := twice_spinWeight_evaluation n (DParity.signedSwap σ i j (decide (t=u))) x
  rw [signVector_signedSwap] at hy
  change 2*spinWeight n σ (corootElement (pairingD (n+2)) a)=coroot a (signVector n σ) at ha
  change 2*spinWeight n (DParity.signedSwap σ i j (decide (t=u))) x =
    x.val (signVector n σ-coroot a (signVector n σ) • a.val) at hy
  rw [map_sub,map_smul] at hy
  simp only [smul_eq_mul] at hy
  change spinWeight n σ x-spinWeight n σ (corootElement (pairingD (n+2)) a)*x.val a.val = _
  rw [← hx,← ha] at hy
  nlinarith [hy]

theorem halfSpinOrbit_closed (n : ℕ) (ε : Bool) (a : DRoot (n+2))
    (μ : WeightLattice (pairingD (n+2))) (hμ : μ∈halfSpinOrbit n ε) :
    weightReflection (pairingD (n+2)) a μ∈halfSpinOrbit n ε := by
  obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hμ
  rcases signed_support_classification a with ⟨h,_⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · cases h
  · have he : a=longRoot false i j hij t u ht hu := Subtype.ext ha
    subst a
    rw [spinWeight_long_reflection]
    let τ : DParity.Fiber (n+2) ε :=
      ⟨DParity.signedSwap σ.val i j (decide (t=u)),
        (DParity.product_signedSwap σ.val i j _).trans σ.property⟩
    exact Finset.mem_image.mpr ⟨τ,Finset.mem_univ _,rfl⟩

def ReflectionStep (n : ℕ) (μ ν : WeightLattice (pairingD (n+2))) : Prop :=
  ∃ a : DRoot (n+2), weightReflection (pairingD (n+2)) a μ=ν

/-- Two genuine D root reflections flip an arbitrary pair of signs. -/
theorem pairFlip_reachable (n : ℕ) (σ : Fin (n+2) → Bool) (i j : Fin (n+2)) (hij : i≠j) :
    Relation.ReflTransGen (ReflectionStep n) (spinWeight n σ) (spinWeight n (DParity.pairFlip σ i j)) := by
  have hswap : DParity.swap (DParity.swap σ i j) i j=σ := by
    funext k
    simp [DParity.swap]
  have h₁ : ReflectionStep n (spinWeight n σ) (spinWeight n (DParity.swap σ i j)) := by
    refine ⟨longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl), ?_⟩
    simpa [DParity.signedSwap] using spinWeight_long_reflection n σ i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have h₂ : ReflectionStep n (spinWeight n (DParity.swap σ i j)) (spinWeight n (DParity.pairFlip σ i j)) := by
    refine ⟨longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl), ?_⟩
    simpa [DParity.signedSwap,hswap] using
      spinWeight_long_reflection n (DParity.swap σ i j) i j hij 1 1 (Or.inl rfl) (Or.inl rfl)
  exact (Relation.ReflTransGen.single h₁).trans (Relation.ReflTransGen.single h₂)

theorem halfSpinOrbit_transitive (n : ℕ) (ε : Bool) (μ ν : WeightLattice (pairingD (n+2)))
    (hμ : μ∈halfSpinOrbit n ε) (hν : ν∈halfSpinOrbit n ε) :
    Relation.ReflTransGen (ReflectionStep n) μ ν := by
  obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hμ
  obtain ⟨τ,_,rfl⟩ := Finset.mem_image.mp hν
  have h := DParity.pair_reachable (0 : Fin (n+2)) σ.val τ.val (σ.property.trans τ.property.symm)
  have lift : DParity.PairStep ≤
      (fun ρ η => Relation.ReflTransGen (ReflectionStep n) (spinWeight n ρ) (spinWeight n η)) := by
    intro ρ η step
    obtain ⟨i,j,hij,rfl⟩ := step
    exact pairFlip_reachable n ρ i j hij
  exact Relation.ReflTransGen.lift' (spinWeight n) lift _ _ h

end Atlas.Chevalley.Integral.Minuscule.TypeD
