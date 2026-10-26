import Atlas.Rudvalis.BinaryWeightEight

/-! The torsion minimum via block parity, affine moments and one-block shortening. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem binaryTorsion_row_even (w : BinaryWord) (hw : w ∈ binaryTorsion) (p : Point) :
    Even (hammingNorm (fun x : E => w (p,x))) := by
  have h := hw (rowWord p) (binaryResidue_row_word p 1)
  rw [Atlas.Codes.binaryDot_apply, Fintype.sum_prod_type] at h
  simp [rowWord, ite_mul] at h
  exact (Atlas.Codes.even_weight_iff _).mpr h

theorem cube_affine_dual_minimum (w : E → Bit)
    (h0 : (∑ x, w x) = 0)
    (h1 : ∀ i : Fin 3, (∑ x, x i * w x) = 0)
    (hw : w ≠ 0) : 4 ≤ hammingNorm w := by
  have hc : ∀ v : Fin 8 → Bit,
      (∑ i, v i) = 0 →
      (∀ j : Fin 3, (∑ i, binaryLabel i j * v i) = 0) →
      v ≠ 0 → 4 ≤ hammingNorm v := by decide +kernel
  have he (f : E → Bit) : (∑ i : Fin 8, f (binaryLabel i)) = ∑ x : E, f x :=
    Equiv.sum_comp innerEquiv f
  have hn : (fun i : Fin 8 => w (binaryLabel i)) ≠ 0 := by
    intro hz
    apply hw
    funext x
    obtain ⟨i,rfl⟩ := binaryLabel_bijective.surjective x
    exact congrFun hz i
  have h := hc (fun i => w (binaryLabel i)) ((he w).trans h0)
    (fun j => (he (fun x => x j*w x)).trans (h1 j)) hn
  have hnorm : hammingNorm (fun i => w (binaryLabel i)) = hammingNorm w := by
    rw [Atlas.Codes.hammingNorm_eq_sum, Atlas.Codes.hammingNorm_eq_sum]
    exact Equiv.sum_comp innerEquiv (fun x => if w x = 0 then (0 : ℕ) else 1)
  rwa [hnorm] at h

theorem point_pair_separator (p q : Point) (hpq : p ≠ q) :
    ∃ u : E, dot u p.val = 1 ∧ dot u q.val = 0 := by
  decide +kernel +revert

def outerMatrix (b u : E) : Matrix (Fin 3) (Fin 3) Bit := fun j i => b j*u i

theorem matrixAt_outer (b u p : E) : matrixAt (outerMatrix b u) p = dot u p • b := by
  ext j
  simp [matrixAt,outerMatrix,dot,Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm]

/-- With only two active rows, affine moment tests separate those rows. -/
theorem binaryTorsion_two_rows_moment (w : BinaryWord) (hw : w ∈ binaryTorsion)
    (p q : Point) (hpq : p ≠ q)
    (hs : ∀ r, r ≠ p → r ≠ q → ∀ x, w (r,x) = 0) (i : Fin 3) :
    (∑ x : E, x i * w (p,x)) = 0 := by
  classical
  obtain ⟨u,hup,huq⟩ := point_pair_separator p q hpq
  let M := outerMatrix (Pi.single i 1) u
  let v := binaryNormalMap (0,M,0)
  have hv (r : Point) (x : E) : v (r,x) = dot (matrixAt M r.val) x := by
    simp [v,binaryNormalMap,theta,quadratic,eta,dot]
  have hvp (x : E) : v (p,x) = x i := by
    rw [hv,matrixAt_outer,hup,one_smul]
    simp [dot,Pi.single_apply,ite_mul]
  have hvq (x : E) : v (q,x) = 0 := by
    rw [hv,matrixAt_outer,huq,zero_smul]
    simp [dot]
  have h := hw v ⟨_,rfl⟩
  rw [Atlas.Codes.binaryDot_apply, Fintype.sum_prod_type] at h
  have he : (∑ r : Point, ∑ x : E, v (r,x)*w (r,x)) =
      ∑ x : E, v (p,x)*w (p,x) := by
    apply Finset.sum_eq_single p
    · intro r _ hr
      by_cases hrq : r=q
      · subst r
        simp [hvq]
      · simp [hs r hr hrq]
    · simp
  rw [he] at h
  simpa only [hvp] using h

theorem binaryTorsion_minimum (w : BinaryWord) (hw : w ∈ binaryTorsion) (hne : w ≠ 0) :
    6 ≤ hammingNorm w := by
  classical
  let n (p : Point) := hammingNorm (fun x : E => w (p,x))
  have hsum (s : Finset Point) : (∑ p ∈ s, n p) ≤ hammingNorm w := by
    rw [Atlas.Codes.hammingNorm_prod]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  have htwo (p : Point) (hp : (fun x : E => w (p,x)) ≠ 0) : 2 ≤ n p :=
    Atlas.Codes.positive_even_weight _ hp (binaryTorsion_row_even w hw p)
  obtain ⟨z,hz⟩ := Function.ne_iff.mp hne
  let p := z.1
  have hp : (fun x : E => w (p,x)) ≠ 0 := by
    intro h
    exact hz (congrFun h z.2)
  by_cases hq : ∃ q, q ≠ p ∧ (fun x : E => w (q,x)) ≠ 0
  · obtain ⟨q,hqp,hq⟩ := hq
    have hpq := Ne.symm hqp
    by_cases hr : ∃ r, r ≠ p ∧ r ≠ q ∧ (fun x : E => w (r,x)) ≠ 0
    · obtain ⟨r,hrp,hrq,hr⟩ := hr
      have hs := hsum {p,q,r}
      simp [hpq,hrp,hrq,Ne.symm hrp,Ne.symm hrq] at hs
      have := htwo p hp
      have := htwo q hq
      have := htwo r hr
      omega
    · have hsupport (r : Point) (hrp : r ≠ p) (hrq : r ≠ q) (x : E) : w (r,x) = 0 := by
        have hh : (fun y : E => w (r,y)) = 0 := by
          by_contra hn
          exact hr ⟨r,hrp,hrq,hn⟩
        exact congrFun hh x
      have hp4 : 4 ≤ n p := cube_affine_dual_minimum _
        ((Atlas.Codes.even_weight_iff _).mp (binaryTorsion_row_even w hw p))
        (binaryTorsion_two_rows_moment w hw p q hpq hsupport) hp
      have hq4 : 4 ≤ n q := cube_affine_dual_minimum _
        ((Atlas.Codes.even_weight_iff _).mp (binaryTorsion_row_even w hw q))
        (binaryTorsion_two_rows_moment w hw q p hqp (fun r hrq hrp => hsupport r hrp hrq)) hq
      have hs := hsum {p,q}
      simp [hpq] at hs
      omega
  · have hs : blockSupported p w := by
      intro q hqp x
      have hh : (fun y : E => w (q,y)) = 0 := by
        by_contra hn
        exact hq ⟨q,hqp,hn⟩
      exact congrFun hh x
    obtain ⟨a,ha⟩ := (binaryTorsion_one_block_iff p w hs).mp hw
    rcases Atlas.Codes.bit_cases a with h | h
    · subst a
      simp at ha
      exact (hne ha).elim
    · subst a
      have hh : w = rowWord p := ha
      rw [hh,rowWord_weight]
      decide

end Atlas.Rudvalis
