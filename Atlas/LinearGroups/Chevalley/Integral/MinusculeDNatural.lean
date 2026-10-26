import Atlas.LinearGroups.Chevalley.Integral.MinusculeDSpan

/-! The actual natural D weights on the integral coroot lattice.
These supply a new minuscule orbit, without identifying a group or a quadratic representation. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

/-- Restrict evaluation by an integral vector to the actual D coroot lattice. -/
def vectorWeight {r : ℕ} (v : ClassicalData.Lattice r) : WeightLattice (pairingD r) where
  toFun x := x.val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem vectorWeight_coroot {r : ℕ} (v : ClassicalData.Lattice r) (a : DRoot r) :
    vectorWeight v (corootElement (pairingD r) a) = coroot a v := rfl

/-- Integral vector reflection agrees with the actual reflection on weights. -/
theorem vectorWeight_reflection {r : ℕ} (v : ClassicalData.Lattice r) (a : DRoot r) :
    weightReflection (pairingD r) a (vectorWeight v) = vectorWeight (reflect a v) := by
  ext x
  change x.val v - coroot a v * x.val a.val =
    x.val (v - coroot a v • a.val)
  simp only [map_sub, map_smul, smul_eq_mul]

/-- The signed natural coordinate weight; its values are integral. -/
def naturalWeight {r : ℕ} (k : Fin r) (s : ℤ) : WeightLattice (pairingD r) :=
  vectorWeight (s • (Pi.single k 1 : ClassicalData.Lattice r))

@[simp] theorem naturalWeight_apply {r : ℕ} (k : Fin r) (s : ℤ)
    (x : CorootLattice (pairingD r)) :
    naturalWeight k s x = s * x.val (Pi.single k 1) := by
  change x.val (s • (Pi.single k 1 : ClassicalData.Lattice r)) = _
  simp only [map_smul, smul_eq_mul]

@[simp] theorem naturalWeight_pairing {r : ℕ} (k : Fin r) (s : ℤ) (a : DRoot r) :
    naturalWeight k s (corootElement (pairingD r) a) = s * a.val k := by
  rw [naturalWeight_apply]
  change s * coroot a (Pi.single k 1) = _
  rw [dcoroot_eq_functional]
  simp only [functional_apply, dot_single, mul_one]

theorem naturalWeight_minuscule {r : ℕ} (k : Fin r) (s : ℤ) (hs : s=1 ∨ s= -1)
    (a : DRoot r) :
    naturalWeight k s (corootElement (pairingD r) a) = -1 ∨
    naturalWeight k s (corootElement (pairingD r) a) = 0 ∨
    naturalWeight k s (corootElement (pairingD r) a) = 1 := by
  rw [naturalWeight_pairing]
  rcases hs with rfl | rfl <;>
    rcases coordinate_cases a k with h | h | h <;> simp [h]

/-- Exact signed-coordinate action for every D root, including the fork root. -/
theorem naturalWeight_reflection_long {r : ℕ} (k i j : Fin r) (hij : i≠j)
    (s t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) :
    weightReflection (pairingD r) (longRoot false i j hij t u ht hu)
        (naturalWeight k s) =
      if k=i then naturalWeight j (-s*t*u)
      else if k=j then naturalWeight i (-s*t*u) else naturalWeight k s := by
  have hv : reflect (longRoot false i j hij t u ht hu)
      (s • (Pi.single k 1 : ClassicalData.Lattice r)) =
      if k=i then (-s*t*u) • (Pi.single j 1 : ClassicalData.Lattice r)
      else if k=j then (-s*t*u) • (Pi.single i 1 : ClassicalData.Lattice r)
      else s • (Pi.single k 1 : ClassicalData.Lattice r) := by
    ext l
    rw [reflect_long_coordinates]
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      by_cases hk : k=i <;> by_cases hl : k=j <;>
      by_cases hi : l=i <;> by_cases hj : l=j <;>
      simp [hk, hl, hi, hj, hij, eq_comm, Pi.single_apply] <;>
      first | (subst k; contradiction) | ring
  unfold naturalWeight
  rw [vectorWeight_reflection, hv]
  split_ifs <;> rfl

/-- The two signed coordinate labels as a finite set of actual weights. -/
def naturalOrbit (r : ℕ) : Finset (WeightLattice (pairingD r)) :=
  Finset.univ.image (fun ks : Fin r × Bool => naturalWeight ks.1 (sign ks.2))

theorem naturalWeight_mem_naturalOrbit {r : ℕ} (k : Fin r) (s : ℤ)
    (hs : s=1 ∨ s= -1) : naturalWeight k s ∈ naturalOrbit r := by
  rcases hs with rfl | rfl
  · exact Finset.mem_image.mpr ⟨(k,true), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(k,false), Finset.mem_univ _, rfl⟩

theorem naturalOrbit_closed {r : ℕ} (a : DRoot r) (μ : WeightLattice (pairingD r))
    (hμ : μ ∈ naturalOrbit r) :
    weightReflection (pairingD r) a μ ∈ naturalOrbit r := by
  obtain ⟨⟨k,b⟩, _, rfl⟩ := Finset.mem_image.mp hμ
  rcases signed_support_classification a with ⟨h,_⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · cases h
  · have he : a=longRoot false i j hij t u ht hu := Subtype.ext ha
    subst a
    rw [naturalWeight_reflection_long]
    split_ifs <;> apply naturalWeight_mem_naturalOrbit <;>
      rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> cases b <;> simp [sign]

theorem naturalOrbit_minuscule {r : ℕ} (μ : WeightLattice (pairingD r))
    (hμ : μ ∈ naturalOrbit r) (a : DRoot r) :
    μ (corootElement (pairingD r) a) = -1 ∨
    μ (corootElement (pairingD r) a) = 0 ∨ μ (corootElement (pairingD r) a) = 1 := by
  obtain ⟨⟨k,b⟩, _, rfl⟩ := Finset.mem_image.mp hμ
  apply naturalWeight_minuscule
  cases b <;> simp [sign]

/-- The signed labels remain distinct on Q∨; the factor 2 is used only over ℤ. -/
theorem naturalOrbit_parameter_injective (n : ℕ) :
    Function.Injective (fun ks : Fin (n+2) × Bool => naturalWeight ks.1 (sign ks.2)) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  obtain ⟨k,hki⟩ := exists_ne i
  have he := congrArg (fun μ : WeightLattice (pairingD (n+2)) =>
    μ (doubleCoordinate n i k (Ne.symm hki))) h
  simp only [naturalWeight_apply, doubleCoordinate_apply, ite_true] at he
  have hij : i=j := by
    by_contra hn
    cases s <;> cases t <;> simp [sign, hn, Ne.symm hn] at he
  subst j
  have hst : s=t := by
    cases s <;> cases t <;> first | rfl | (norm_num [sign] at he)
  subst t
  rfl

theorem naturalOrbit_card (n : ℕ) : (naturalOrbit (n+2)).card = 2*(n+2) := by
  rw [naturalOrbit, Finset.card_image_of_injective _ (naturalOrbit_parameter_injective n)]
  simp [Nat.mul_comm]

/-- The previously checked half-spin weight difference is the positive natural weight. -/
theorem selected_difference_natural (n : ℕ) :
    spinWeight n (fun _ => true) - spinWeight n (lastNegative n) =
      naturalWeight (Fin.last (n+1)) 1 := by
  rw [selected_difference]
  ext x
  simp only [naturalWeight_apply, one_mul]
  rfl

end Atlas.Chevalley.Integral.Minuscule.TypeD
