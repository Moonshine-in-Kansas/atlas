import Atlas.Rudvalis.BinaryOrthogonality

/-! Puncturing onto one eight-point block, and the dual shortening theorem. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def columnMatrix (k : Fin 3) (b : E) : Matrix (Fin 3) (Fin 3) Bit :=
  fun j i => if i=k then b j else 0

theorem matrixAt_column (k : Fin 3) (b p : E) :
    matrixAt (columnMatrix k b) p = p k • b := by
  ext j
  simp [matrixAt, columnMatrix, ite_mul, mul_comm]

theorem point_has_one (p : Point) : ∃ k, p.val k = 1 := by
  decide +kernel +revert

/-- Every degree-at-most-two Boolean polynomial occurs on any prescribed block. -/
theorem binaryResidue_block_polynomial (p : Point) (a : Bit) (b c : E) :
    ∃ w ∈ binaryResidue, ∀ x, w (p,x) = a + dot b x + quadratic c x := by
  obtain ⟨k,hk⟩ := point_has_one p
  let M := columnMatrix k (b-eta p c)
  have hm : matrixAt M p.val = b-eta p c := by
    rw [matrixAt_column, hk, one_smul]
  refine ⟨binaryNormalMap (fun _ => a,M,c), ⟨_,rfl⟩, ?_⟩
  intro x
  change a + dot (matrixAt M p.val) x + theta p c x = _
  rw [hm]
  simp [theta, dot, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Dual of the seven Boolean monomials on an eight-point cube is repetition.
This certificate concerns only 256 local words, not the 56-coordinate code. -/
theorem cube_dual_repetition (w : E → Bit)
    (h0 : (∑ x, w x) = 0)
    (h1 : ∀ i : Fin 3, (∑ x, x i * w x) = 0)
    (h2 : ∀ i : Fin 3, (∑ x, quadratic (Pi.single i 1) x * w x) = 0) :
    ∀ x, w x = w 0 := by
  have hc : ∀ v : Fin 8 → Bit,
      (∑ i, v i) = 0 →
      (∀ j : Fin 3, (∑ i, binaryLabel i j * v i) = 0) →
      (∀ j : Fin 3, (∑ i, quadratic (Pi.single j 1) (binaryLabel i) * v i) = 0) →
      ∀ i, v i = v 0 := by decide +kernel
  have he (f : E → Bit) : (∑ i : Fin 8, f (binaryLabel i)) = ∑ x : E, f x :=
    Equiv.sum_comp innerEquiv f
  have hh := hc (fun i => w (binaryLabel i)) ((he w).trans h0)
    (fun j => (he (fun x => x j * w x)).trans (h1 j))
    (fun j => (he (fun x => quadratic (Pi.single j 1) x * w x)).trans (h2 j))
  intro x
  obtain ⟨i,rfl⟩ := binaryLabel_bijective.surjective x
  have hz : binaryLabel 0 = (0 : E) := by decide
  simpa only [hz] using hh i

def blockSupported (p : Point) (w : BinaryWord) : Prop :=
  ∀ q, q ≠ p → ∀ x, w (q,x) = 0

theorem binaryDot_supported (p : Point) (w v : BinaryWord) (hw : blockSupported p w) :
    Atlas.Codes.binaryDot v w = ∑ x : E, v (p,x) * w (p,x) := by
  classical
  rw [Atlas.Codes.binaryDot_apply, Fintype.sum_prod_type]
  apply Finset.sum_eq_single p
  · intro q _ hq
    simp [hw q hq]
  · simp

/-- A torsion word supported in one block is constant on that block. -/
theorem binaryTorsion_one_block_constant (p : Point) (w : BinaryWord)
    (hw : w ∈ binaryTorsion) (hs : blockSupported p w) :
    ∀ x, w (p,x) = w (p,0) := by
  have hp (a : Bit) (b c : E) :
      (∑ x : E, (a + dot b x + quadratic c x) * w (p,x)) = 0 := by
    obtain ⟨v,hv,hvx⟩ := binaryResidue_block_polynomial p a b c
    have h := hw v hv
    rw [binaryDot_supported p w v hs] at h
    simpa only [hvx] using h
  apply cube_dual_repetition
  · simpa [dot,quadratic] using hp 1 0 0
  · intro i
    simpa [dot,quadratic,Pi.single_apply,ite_mul] using hp 0 (Pi.single i 1) 0
  · intro i
    simpa [dot] using hp 0 0 (Pi.single i 1)

/-- Every constant row word already lies in the residue code. -/
theorem binaryResidue_row_word (p : Point) (a : Bit) :
    (fun z : Coordinate => if z.1=p then a else 0) ∈ binaryResidue := by
  classical
  refine ⟨(fun q => if q=p then a else 0,0,0), ?_⟩
  funext z
  simp [binaryNormalMap,theta,quadratic,dot,eta,matrixAt]

/-- The shortening of the torsion code to one block is exactly repetition. -/
theorem binaryTorsion_one_block_iff (p : Point) (w : BinaryWord)
    (hs : blockSupported p w) :
    w ∈ binaryTorsion ↔ ∃ a : Bit, w = fun z => if z.1=p then a else 0 := by
  classical
  constructor
  · intro hw
    refine ⟨w (p,0), ?_⟩
    funext z
    obtain ⟨q,x⟩ := z
    by_cases hq : q=p
    · subst q
      simpa using binaryTorsion_one_block_constant p w hw hs x
    · simpa [hq] using hs q hq x
  · rintro ⟨a,rfl⟩
    exact binaryResidue_self_orthogonal (binaryResidue_row_word p a)

end Atlas.Rudvalis
