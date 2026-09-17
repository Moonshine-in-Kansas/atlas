import Atlas.Fischer.ReflectingRootAutomaticMoments

noncomputable section
namespace Atlas.Fischer

/-- Distinct partners with nonzero actual Hermitian pairing. -/
def reflectingNonzeroNeighbors {J : Type*} [Fintype J]
    (r : J → Coordinates) (i : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => j ≠ i ∧ hermitian (r i) (r j) ≠ 0)

/-- The actual zero-pairing partners; a normalized root is never its own partner. -/
def reflectingZeroNeighbors {J : Type*} [Fintype J]
    (r : J → Coordinates) (i : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => hermitian (r i) (r j)=0)

/-- Off-diagonal squared pairing magnitudes are zero or one intrinsically. -/
theorem reflectingRoot_pairing_norm {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (i j : J) (hij : i ≠ j) :
    hermitian (r i) (r j)*hermitian (r j) (r i)=
      if hermitian (r i) (r j)=0 then 0 else 1 := by
  classical
  rcases reflectingRoot_pairing_zero_or_mu3 (r i) (r j) (hr i) (hr j) (hd i j hij)
    with hz | ⟨a,ha⟩
  · simp [hz]
  · have hc : (a.val.val : Scalar)^3=1 := (mem_rootsOfUnity' _ _).mp a.property
    rw [← hermitian_star (r i) (r j),ha,if_neg (Units.ne_zero a.val),mul_comm,cube_root_unit_norm hc]

/-- The second moment forces the exact distinct nonzero-pairing valency. -/
theorem reflectingNonzeroNeighbors_card {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (i : J) :
    (reflectingNonzeroNeighbors r i).card=31671 := by
  classical
  have hw (j : J) : hermitian (r i) (r j)*hermitian (r j) (r i)=
      (if j=i then (81 : Scalar) else 0)+
        (if j ≠ i ∧ hermitian (r i) (r j) ≠ 0 then 1 else 0) := by
    by_cases hj : j=i
    · subst j
      rw [(hr i).1.1]
      norm_num
    · rw [reflectingRoot_pairing_norm r hr hd i j (Ne.symm hj)]
      by_cases hh : hermitian (r i) (r j)=0 <;> simp [hj,hh]
  have hm := reflectingRoot_second_moment r hr hd hc (r i) (r i)
  rw [(hr i).1.1] at hm
  simp only [hw,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hm
  have hn : (∑ j : J, if j ≠ i ∧ hermitian (r i) (r j) ≠ 0 then (1 : Scalar) else 0)=
      ((reflectingNonzeroNeighbors r i).card : Scalar) := by
    rw [← Finset.sum_filter]
    simp [reflectingNonzeroNeighbors]
  rw [hn] at hm
  have he : ((reflectingNonzeroNeighbors r i).card : Scalar)=31671 := by
    linear_combination hm
  exact_mod_cast he

/-- The exact zero-pairing valency follows by complementing the diagonal and
nonzero partners inside the actual finite family. -/
theorem reflectingZeroNeighbors_card {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (i : J) :
    (reflectingZeroNeighbors r i).card=275264 := by
  classical
  have hn : i ∉ reflectingNonzeroNeighbors r i := by simp [reflectingNonzeroNeighbors]
  have he : reflectingZeroNeighbors r i=(insert i (reflectingNonzeroNeighbors r i))ᶜ := by
    ext j
    by_cases hj : j=i
    · subst j
      simp [reflectingZeroNeighbors,reflectingNonzeroNeighbors,(hr i).1.1]
    · simp [reflectingZeroNeighbors,reflectingNonzeroNeighbors,hj]
  rw [he,Finset.card_compl,Finset.card_insert_of_notMem hn,
    reflectingNonzeroNeighbors_card r hr hd hc,hc]

end Atlas.Fischer
