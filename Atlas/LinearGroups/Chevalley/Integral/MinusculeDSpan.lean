import Atlas.LinearGroups.Chevalley.Integral.MinusculeDAction

/-! integral P/Q generation using both actual D half-spin weights. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

def coordinateWeight {r : ℕ} (i : Fin r) : WeightLattice (pairingD r) where
  toFun x := x.val (Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rootWeight_difference {r : ℕ} (i j : Fin r) (hij : i≠j) :
    rootWeight (pairingD r) (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) =
      coordinateWeight i-coordinateWeight j := by
  ext x
  change x.val (Pi.single i 1+Pi.single j (-1)) = x.val (Pi.single i 1)-x.val (Pi.single j 1)
  simp [Pi.single_neg, sub_eq_add_neg]

/-- The difference of the selected half-spin weights is a genuine coordinate weight. -/
theorem selected_difference (n : ℕ) :
    spinWeight n (fun _ => true)-spinWeight n (lastNegative n) = coordinateWeight (Fin.last (n+1)) := by
  ext x
  have hp := twice_spinWeight_apply n (fun _ => true) x
  have hm := twice_spinWeight_apply n (lastNegative n) x
  have hd : (∑ k, sign true*x.val (Pi.single k 1))-
      (∑ k, sign (lastNegative n k)*x.val (Pi.single k 1)) =
      2*x.val (Pi.single (Fin.last (n+1)) 1) := by
    rw [← Finset.sum_sub_distrib]
    have hs : ∀ k : Fin (n+2), sign true*x.val (Pi.single k 1)-
        sign (lastNegative n k)*x.val (Pi.single k 1) =
        if k=Fin.last (n+1) then 2*x.val (Pi.single k 1) else 0 := by
      intro k
      simp [lastNegative,sign,Fin.ext_iff]
      split_ifs <;> ring
    simp only [hs]
    simp
  change spinWeight n (fun _ => true) x-spinWeight n (lastNegative n) x = x.val (Pi.single (Fin.last (n+1)) 1)
  omega

/-- Earlier fundamental weights are coordinate prefixes; the two final weights remain separate. -/
theorem nonfork_fundamentalWeight (n : ℕ) (i : Fin (n+2)) (hi : i.val<n) :
    fundamentalWeights (pairingD (n+2)) (baseD n) (baseDIndexEquiv n i) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n+2) => k.val ≤ i.val), coordinateWeight k := by
  apply (corootBasis (pairingD (n+2)) (baseD n)).ext
  intro j
  obtain ⟨j,rfl⟩ := (baseDIndexEquiv n).surjective j
  rw [fundamentalWeights_pairing]
  have hb : corootBasis (pairingD (n+2)) (baseD n) (baseDIndexEquiv n j)=
      corootElement (pairingD (n+2)) (simpleD n j) := by
    apply Subtype.ext
    exact (baseD n).flip.coe_toWeightBasisInt_apply
      (⟨simpleD n j,(baseDIndexEquiv n j).property⟩ : (baseD n).flip.support)
  rw [hb]
  simp only [LinearMap.sum_apply]
  change (if baseDIndexEquiv n j=baseDIndexEquiv n i then 1 else 0) =
    ∑ k ∈ Finset.univ.filter (fun k : Fin (n+2) => k.val ≤ i.val), coroot (simpleD n j) (Pi.single k 1)
  simp only [simpleD_coroot,functional_apply,dot_single,mul_one,simpleD_vector]
  by_cases hj : j.val=n+1
  · simp [hj,Pi.add_apply,Pi.single_apply,Finset.sum_add_distrib]
    simp only [Fin.ext_iff,Fin.le_def]
    split_ifs <;> omega
  · simp [hj,Pi.sub_apply,Pi.single_apply,Finset.sum_sub_distrib]
    simp only [Fin.ext_iff,Fin.le_def,Fin.val_mk]
    split_ifs <;> (try simp only [Fin.le_def,Fin.val_mk] at *) <;> omega

/-- Both chosen half-spin weights together with the actual root lattice generate P. -/
theorem root_and_two_spin_weights_span (n : ℕ) :
    Submodule.span ℤ (Set.range (rootWeight (pairingD (n+2))) ∪
      {spinWeight n (fun _ => true),spinWeight n (lastNegative n)}) = ⊤ := by
  let S := Submodule.span ℤ (Set.range (rootWeight (pairingD (n+2))) ∪
    {spinWeight n (fun _ => true),spinWeight n (lastNegative n)})
  have hp : spinWeight n (fun _ => true)∈S := Submodule.subset_span (Or.inr (Or.inl rfl))
  have hm : spinWeight n (lastNegative n)∈S := Submodule.subset_span (Or.inr (Or.inr rfl))
  have hl : coordinateWeight (Fin.last (n+1))∈S := by
    rw [← selected_difference]
    exact Submodule.sub_mem _ hp hm
  have hc : ∀ k : Fin (n+2), coordinateWeight k∈S := by
    intro k
    by_cases hk : k=Fin.last (n+1)
    · simpa [hk] using hl
    · have hr : rootWeight (pairingD (n+2))
          (longRoot false k (Fin.last (n+1)) hk 1 (-1) (Or.inl rfl) (Or.inr rfl))∈S :=
        Submodule.subset_span (Or.inl ⟨_,rfl⟩)
      rw [rootWeight_difference] at hr
      simpa using Submodule.add_mem _ hr hl
  apply top_unique
  rw [← (fundamentalWeights (pairingD (n+2)) (baseD n)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  obtain ⟨i,rfl⟩ := (baseDIndexEquiv n).surjective j
  by_cases hi : i.val<n
  · rw [nonfork_fundamentalWeight n i hi]
    exact Submodule.sum_mem _ (fun k _ => hc k)
  · by_cases he : i.val=n
    · have he' : i=(⟨n,by omega⟩ : Fin (n+2)) := Fin.ext he
      rw [he',← negative_spinWeight]
      exact hm
    · have he' : i=Fin.last (n+1) := Fin.ext (by change i.val=n+1; have := i.isLt; omega)
      rw [he',← positive_spinWeight]
      exact hp

end Atlas.Chevalley.Integral.Minuscule.TypeD
