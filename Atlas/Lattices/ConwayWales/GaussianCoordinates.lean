import Atlas.Lattices.ConwayWales.SeedLattice

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

/-- The actual Gaussian integers inside the ambient complex field. -/
def gaussianIntegers : Subring ℂ := GaussianInt.toComplex.range

theorem gaussian_I : Complex.I ∈ gaussianIntegers := by
  refine ⟨⟨0,1⟩, ?_⟩
  norm_num [GaussianInt.toComplex, Zsqrtd.lift]

theorem gaussian_star {z : ℂ} (hz : z ∈ gaussianIntegers) : star z ∈ gaussianIntegers := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨star w, GaussianInt.toComplex_star w⟩

/-- Coordinate order Z[i] + Z[i]j + Z[i]k + Z[i]l. -/
def gaussianOrder : Subring Q where
  carrier := {x | x.re ∈ gaussianIntegers ∧ x.imI ∈ gaussianIntegers ∧
    x.imJ ∈ gaussianIntegers ∧ x.imK ∈ gaussianIntegers}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨h0,h1,h2,h3⟩
    rcases hy with ⟨k0,k1,k2,k3⟩
    exact ⟨gaussianIntegers.add_mem h0 k0, gaussianIntegers.add_mem h1 k1,
      gaussianIntegers.add_mem h2 k2, gaussianIntegers.add_mem h3 k3⟩
  neg_mem' := by
    intro x hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    exact ⟨gaussianIntegers.neg_mem h0, gaussianIntegers.neg_mem h1,
      gaussianIntegers.neg_mem h2, gaussianIntegers.neg_mem h3⟩
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨h0,h1,h2,h3⟩
    rcases hy with ⟨k0,k1,k2,k3⟩
    constructor
    · simpa only [Quaternion.re_mul] using gaussianIntegers.sub_mem
        (gaussianIntegers.sub_mem (gaussianIntegers.sub_mem
          (gaussianIntegers.mul_mem h0 k0) (gaussianIntegers.mul_mem h1 k1))
          (gaussianIntegers.mul_mem h2 k2)) (gaussianIntegers.mul_mem h3 k3)
    constructor
    · simpa only [Quaternion.imI_mul] using gaussianIntegers.sub_mem
        (gaussianIntegers.add_mem (gaussianIntegers.add_mem
          (gaussianIntegers.mul_mem h0 k1) (gaussianIntegers.mul_mem h1 k0))
          (gaussianIntegers.mul_mem h2 k3)) (gaussianIntegers.mul_mem h3 k2)
    constructor
    · simpa only [Quaternion.imJ_mul] using gaussianIntegers.add_mem
        (gaussianIntegers.add_mem (gaussianIntegers.sub_mem
          (gaussianIntegers.mul_mem h0 k2) (gaussianIntegers.mul_mem h1 k3))
          (gaussianIntegers.mul_mem h2 k0)) (gaussianIntegers.mul_mem h3 k1)
    · simpa only [Quaternion.imK_mul] using gaussianIntegers.add_mem
        (gaussianIntegers.sub_mem (gaussianIntegers.add_mem
          (gaussianIntegers.mul_mem h0 k3) (gaussianIntegers.mul_mem h1 k2))
          (gaussianIntegers.mul_mem h2 k1)) (gaussianIntegers.mul_mem h3 k0)

theorem gaussianOrder_smul {z : ℂ} {q : Q} (hz : z ∈ gaussianIntegers)
    (hq : q ∈ gaussianOrder) : z • q ∈ gaussianOrder := by
  rcases hq with ⟨h0,h1,h2,h3⟩
  exact ⟨gaussianIntegers.mul_mem hz h0, gaussianIntegers.mul_mem hz h1,
    gaussianIntegers.mul_mem hz h2, gaussianIntegers.mul_mem hz h3⟩

theorem basis_mem_gaussianOrder (u : Fin 4) : quaternionBasis u ∈ gaussianOrder := by
  fin_cases u <;> simp [quaternionBasis, j, k, l, gaussianOrder]

theorem A_mem_gaussianOrder (r : Row) : A r ∈ gaussianOrder := by
  fin_cases r <;> simp [A, gaussianOrder, gaussian_I]

theorem B_mem_gaussianOrder (r : Row) : B r ∈ gaussianOrder := by
  fin_cases r <;> simp [B, gaussianOrder, gaussian_I]

theorem C_mem_gaussianOrder (r : Row) : C r ∈ gaussianOrder := by
  fin_cases r <;> simp [C, gaussianOrder, gaussian_I]

/-- Half-integral Gaussian quaternion coordinates; no duality is assumed. -/
def halfIntegralModule : Submodule GaussianInt Space where
  carrier := {v | ∀ r, (2 : ℂ) • v r ∈ gaussianOrder}
  zero_mem' := by intro r; simp
  add_mem' := by
    intro v w hv hw r
    simpa only [Pi.add_apply, smul_add] using gaussianOrder.add_mem (hv r) (hw r)
  smul_mem' := by
    intro z v hv r
    change (2 : ℂ) • (GaussianInt.toComplex z • v r) ∈ gaussianOrder
    rw [smul_comm]
    exact gaussianOrder_smul ⟨z,rfl⟩ (hv r)

theorem seedGenerator_halfIntegral (t : Fin 3) (d : Row) (u : Fin 4) :
    seedGenerator t d u ∈ halfIntegralModule := by
  intro r
  fin_cases t
  · change (2 : ℂ) • (if r = d then (2 : ℂ) • quaternionBasis u else 0) ∈ gaussianOrder
    split_ifs
    · exact gaussianOrder_smul (by simpa using gaussianIntegers.add_mem gaussianIntegers.one_mem gaussianIntegers.one_mem)
        (gaussianOrder_smul (by simpa using gaussianIntegers.add_mem gaussianIntegers.one_mem gaussianIntegers.one_mem) (basis_mem_gaussianOrder u))
    · simp
  · change (2 : ℂ) • (((1 / 2 : ℂ) • A (r - d)) * quaternionBasis u) ∈ gaussianOrder
    rw [← smul_mul_assoc, smul_smul]
    norm_num
    exact gaussianOrder.mul_mem (A_mem_gaussianOrder _) (basis_mem_gaussianOrder _)
  · change (2 : ℂ) • (((1 / 2 : ℂ) • B (r - d)) * quaternionBasis u) ∈ gaussianOrder
    rw [← smul_mul_assoc, smul_smul]
    norm_num
    exact gaussianOrder.mul_mem (B_mem_gaussianOrder _) (basis_mem_gaussianOrder _)

theorem seedLattice_le_halfIntegral : seedLattice ≤ halfIntegralModule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨t,d,u⟩,rfl⟩
  exact seedGenerator_halfIntegral t d u


theorem gaussian_smul_mem_seedLattice {z : ℂ} {v : Space}
    (hz : z ∈ gaussianIntegers) (hv : v ∈ seedLattice) : z • v ∈ seedLattice := by
  obtain ⟨w,rfl⟩ := hz
  exact seedLattice_gaussian_smul w v hv

theorem doubled_coordinate_mem (d : Row) (u : Fin 4) {z : ℂ}
    (hz : z ∈ gaussianIntegers) : (2 * z) • coordinateVector d u ∈ seedLattice := by
  have h := gaussian_smul_mem_seedLattice hz (coordinate_mem_seedLattice d u)
  convert h using 1
  funext r
  by_cases hr : r = d <;> simp [coordinateVector, hr, smul_smul, mul_comm]

theorem doubled_order_vectors_mem (v : Space) (hv : ∀ r, v r ∈ gaussianOrder) :
    (2 : ℂ) • v ∈ seedLattice := by
  rw [← coordinate_expansion ((2 : ℂ) • v)]
  apply Submodule.sum_mem
  intro d _
  rcases hv d with ⟨h0,h1,h2,h3⟩
  exact seedLattice.add_mem (seedLattice.add_mem (seedLattice.add_mem
    (doubled_coordinate_mem d 0 h0) (doubled_coordinate_mem d 1 h1))
    (doubled_coordinate_mem d 2 h2)) (doubled_coordinate_mem d 3 h3)

theorem right_order_mem_seedLattice (v : Space)
    (hv : ∀ u, (fun r => v r * quaternionBasis u) ∈ seedLattice)
    (q : Q) (hq : q ∈ gaussianOrder) : (fun r => v r * q) ∈ seedLattice := by
  rcases hq with ⟨h0,h1,h2,h3⟩
  have h := seedLattice.add_mem (seedLattice.add_mem (seedLattice.add_mem
    (gaussian_smul_mem_seedLattice h0 (hv 0))
    (gaussian_smul_mem_seedLattice h1 (hv 1)))
    (gaussian_smul_mem_seedLattice h2 (hv 2)))
    (gaussian_smul_mem_seedLattice h3 (hv 3))
  convert h using 1
  funext r
  conv_lhs => rw [← quaternion_expansion q]
  simp only [mul_add, mul_smul_comm, Pi.add_apply, Pi.smul_apply]

/-- The manuscript's coordinate-order presentation, before any integrality or
self-duality theorem. The Gaussian span expresses the indicated module sum. -/
def orderPresentation : Submodule GaussianInt Space := Submodule.span GaussianInt
  {v | (∃ w : Space, (∀ r, w r ∈ gaussianOrder) ∧ v = (2 : ℂ) • w) ∨
    (∃ d : Row, ∃ q : Q, q ∈ gaussianOrder ∧ v = fun r => a (r - d) * q) ∨
    (∃ d : Row, ∃ q : Q, q ∈ gaussianOrder ∧ v = fun r => b (r - d) * q)}

theorem orderPresentation_eq_seedLattice : orderPresentation = seedLattice := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨w,hw,rfl⟩ | ⟨d,q,hq,rfl⟩ | ⟨d,q,hq,rfl⟩
    · exact doubled_order_vectors_mem w hw
    · exact right_order_mem_seedLattice (fun r => a (r-d)) (fun u => seedGenerator_mem 1 d u) q hq
    · exact right_order_mem_seedLattice (fun r => b (r-d)) (fun u => seedGenerator_mem 2 d u) q hq
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨t,d,u⟩,rfl⟩
    apply Submodule.subset_span
    fin_cases t
    · left
      refine ⟨coordinateVector d u, ?_, ?_⟩
      · intro r
        by_cases h : r = d <;> simp [coordinateVector, h, basis_mem_gaussianOrder]
      · funext r
        by_cases h : r = d <;> simp [seedGenerator, coordinateVector, h]
    · exact Or.inr (Or.inl ⟨d,quaternionBasis u,basis_mem_gaussianOrder u,rfl⟩)
    · exact Or.inr (Or.inr ⟨d,quaternionBasis u,basis_mem_gaussianOrder u,rfl⟩)


theorem seedGenerator_right_order (t : Fin 3) (d : Row) (u : Fin 4)
    (q : Q) (hq : q ∈ gaussianOrder) :
    (fun r => seedGenerator t d u r * q) ∈ seedLattice := by
  fin_cases t
  · have h := doubled_order_vectors_mem
      (fun r => if r = d then quaternionBasis u * q else 0) (by
        intro r
        split_ifs
        · exact gaussianOrder.mul_mem (basis_mem_gaussianOrder u) hq
        · exact gaussianOrder.zero_mem)
    convert h using 1
    funext r
    by_cases hr : r = d <;> simp [seedGenerator, hr, smul_mul_assoc]
  · have h := right_order_mem_seedLattice (fun r => a (r-d))
      (fun z => seedGenerator_mem 1 d z) (quaternionBasis u * q)
      (gaussianOrder.mul_mem (basis_mem_gaussianOrder u) hq)
    change (fun r => (a (r-d) * quaternionBasis u) * q) ∈ seedLattice
    simpa only [mul_assoc] using h
  · have h := right_order_mem_seedLattice (fun r => b (r-d))
      (fun z => seedGenerator_mem 2 d z) (quaternionBasis u * q)
      (gaussianOrder.mul_mem (basis_mem_gaussianOrder u) hq)
    change (fun r => (b (r-d) * quaternionBasis u) * q) ∈ seedLattice
    simpa only [mul_assoc] using h

theorem seedLattice_right_order (v : Space) (hv : v ∈ seedLattice)
    (q : Q) (hq : q ∈ gaussianOrder) : (fun r => v r * q) ∈ seedLattice := by
  change v ∈ Submodule.span GaussianInt _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨t,d,u⟩,rfl⟩ := hv
    exact seedGenerator_right_order t d u q hq
  | zero =>
    simp only [Pi.zero_apply, zero_mul]
    exact seedLattice.zero_mem
  | add x y hx hy ihx ihy =>
    convert seedLattice.add_mem ihx ihy using 1
    funext r
    exact add_mul (x r) (y r) q
  | smul z x hx ih =>
    have h := seedLattice_gaussian_smul z _ ih
    change (fun r => (GaussianInt.toComplex z • x r) * q) ∈ seedLattice
    convert h using 1
    funext r
    exact smul_mul_assoc (GaussianInt.toComplex z) (x r) q

end Atlas.ConwayWales
