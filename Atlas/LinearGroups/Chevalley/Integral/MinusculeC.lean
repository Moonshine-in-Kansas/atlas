import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice
import Mathlib.Tactic

/-! Type-C defining weights on the actual integral coroot lattice. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeC
open Classical ClassicalData

/-- Signed coordinate evaluation on the actual C coroot lattice. -/
def naturalWeight {r : ℕ} (k : Fin r) (s : ℤ) : WeightLattice (pairingC r) where
  toFun x := s * x.val k
  map_add' x y := by simp [mul_add]
  map_smul' t x := by simp [mul_left_comm]

@[simp] theorem naturalWeight_pairing {r : ℕ} (k : Fin r) (s : ℤ) (a : BRoot r) :
    naturalWeight k s (corootElement (pairingC r) a) = s * a.val k := rfl

/-- The all-root minuscule bound follows from the checked coordinate classification. -/
theorem naturalWeight_minuscule {r : ℕ} (k : Fin r) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (a : BRoot r) :
    naturalWeight k s (corootElement (pairingC r) a) = -1 ∨
    naturalWeight k s (corootElement (pairingC r) a) = 0 ∨
    naturalWeight k s (corootElement (pairingC r) a) = 1 := by
  rw [naturalWeight_pairing]
  rcases hs with rfl | rfl <;>
    rcases coordinate_cases a k with h | h | h <;> simp [h]

/-- A long C root has weight 2s times the corresponding coordinate evaluation. -/
theorem short_label_rootWeight {r : ℕ} (k : Fin r) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    rootWeight (pairingC r) (shortRoot k s hs) = naturalWeight k (2*s) := by
  ext x
  change coroot (shortRoot k s hs) x.val = (2*s) * x.val k
  exact coroot_short k s hs x.val

/-- A short C root is the indicated sum of two coordinate evaluations. -/
theorem long_label_rootWeight {r : ℕ} (i j : Fin r) (hij : i ≠ j)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    rootWeight (pairingC r) (longRoot true i j hij s t hs ht) =
      naturalWeight i s + naturalWeight j t := by
  ext x
  change coroot (longRoot true i j hij s t hs ht) x.val = s*x.val i+t*x.val j
  exact coroot_long true i j hij s t hs ht x.val

/-- Exact reflection formula before splitting the signed coordinate support. -/
theorem naturalWeight_reflection_apply {r : ℕ} (k : Fin r) (s : ℤ) (a : BRoot r)
    (x : CorootLattice (pairingC r)) :
    weightReflection (pairingC r) a (naturalWeight k s) x =
      s*x.val k - (s*a.val k)*coroot a x.val := rfl

end Atlas.Chevalley.Integral.Minuscule.TypeC

namespace Atlas.Chevalley.Integral.Minuscule.TypeC
open Classical ClassicalData

def sign (b : Bool) : ℤ := if b then 1 else -1

def orbit (r : ℕ) : Finset (WeightLattice (pairingC r)) :=
  Finset.univ.image (fun ks : Fin r × Bool => naturalWeight ks.1 (sign ks.2))

theorem naturalWeight_mem_orbit {r : ℕ} (k : Fin r) (s : ℤ) (hs : s=1 ∨ s= -1) :
    naturalWeight k s ∈ orbit r := by
  rcases hs with rfl | rfl
  · exact Finset.mem_image.mpr ⟨(k,true), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(k,false), Finset.mem_univ _, rfl⟩

theorem orbit_parameter_injective (r : ℕ) :
    Function.Injective (fun ks : Fin r × Bool => naturalWeight ks.1 (sign ks.2)) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  have hi := congrArg (fun μ : WeightLattice (pairingC r) =>
    μ (corootElement (pairingC r) (shortRoot i 1 (Or.inl rfl)))) h
  change sign s * (Pi.single i (1 : ℤ) : Fin r → ℤ) i =
    sign t * (Pi.single i (1 : ℤ) : Fin r → ℤ) j at hi
  have hij : i=j := by
    by_contra hn
    cases s <;> cases t <;>
      simp [Pi.single_apply, sign, hn, Ne.symm hn] at hi
  subst j
  have hi2 : sign s = sign t := by simpa using hi
  have hst : s=t := by
    cases s <;> cases t <;> first | rfl | (norm_num [sign] at hi2)
  subst t
  rfl

theorem orbit_card (r : ℕ) : (orbit r).card = 2*r := by
  rw [orbit, Finset.card_image_of_injective _ (orbit_parameter_injective r)]
  simp [Nat.mul_comm]

/-- Reflection in a long C root flips one sign. -/
theorem reflection_short_label {r : ℕ} (k i : Fin r) (s t : ℤ) (ht : t=1 ∨ t= -1) :
    weightReflection (pairingC r) (shortRoot i t ht) (naturalWeight k s) =
      if k=i then naturalWeight k (-s) else naturalWeight k s := by
  ext x
  rw [naturalWeight_reflection_apply, coroot_short]
  rcases ht with rfl | rfl <;> by_cases hk : k=i <;>
    simp [shortRoot, Pi.single_apply, hk, eq_comm, naturalWeight] <;> ring

/-- Reflection in a short C root exchanges the two supported coordinates. -/
theorem reflection_long_label {r : ℕ} (k i j : Fin r) (hij : i≠j)
    (s t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) :
    weightReflection (pairingC r) (longRoot true i j hij t u ht hu) (naturalWeight k s) =
      if k=i then naturalWeight j (-s*t*u)
      else if k=j then naturalWeight i (-s*t*u) else naturalWeight k s := by
  ext x
  rw [naturalWeight_reflection_apply, coroot_long]
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    by_cases hk : k=i <;> by_cases hl : k=j <;>
    simp [longRoot, Pi.single_apply, hk, hl, hij, eq_comm, naturalWeight] <;>
    first | (subst k; contradiction) | ring

theorem orbit_closed {r : ℕ} (a : BRoot r) (μ : WeightLattice (pairingC r))
    (hμ : μ ∈ orbit r) : weightReflection (pairingC r) a μ ∈ orbit r := by
  obtain ⟨⟨k,b⟩, _, rfl⟩ := Finset.mem_image.mp hμ
  rcases signed_support_classification a with ⟨_, i,t,ht,ha⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · have he : a=shortRoot i t ht := Subtype.ext ha
    subst a
    rw [reflection_short_label]
    split_ifs <;> apply naturalWeight_mem_orbit <;> cases b <;> simp [sign]
  · have he : a=longRoot true i j hij t u ht hu := Subtype.ext ha
    subst a
    rw [reflection_long_label]
    split_ifs <;> apply naturalWeight_mem_orbit <;>
      rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> cases b <;> simp [sign]

/-- A step is an actual root reflection on the already constructed weight lattice. -/
def ReflectionStep {r : ℕ} (μ ν : WeightLattice (pairingC r)) : Prop :=
  ∃ a : BRoot r, weightReflection (pairingC r) a μ = ν

/-- A short C root exchanges two coordinates without changing the chosen sign. -/
theorem coordinate_reachable {r : ℕ} (i j : Fin r) (s : ℤ) :
    Relation.ReflTransGen ReflectionStep (naturalWeight i s) (naturalWeight j s) := by
  by_cases hij : i=j
  · subst j
    exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    refine ⟨longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl), ?_⟩
    rw [reflection_long_label]
    simp

/-- A long C root flips a coordinate sign. -/
theorem sign_reachable {r : ℕ} (j : Fin r) (s t : Bool) :
    Relation.ReflTransGen ReflectionStep (naturalWeight j (sign s))
      (naturalWeight j (sign t)) := by
  by_cases h : s=t
  · subst t
    exact Relation.ReflTransGen.refl
  · have ht : sign t = -sign s := by cases s <;> cases t <;> simp_all [sign]
    apply Relation.ReflTransGen.single
    refine ⟨shortRoot j 1 (Or.inl rfl), ?_⟩
    rw [reflection_short_label]
    simp [ht]

/-- Any two members of the actual signed defining orbit are connected by
actual reflections; the proof uses at most one coordinate swap and one sign flip. -/
theorem orbit_transitive {r : ℕ} (μ ν : WeightLattice (pairingC r))
    (hμ : μ ∈ orbit r) (hν : ν ∈ orbit r) :
    Relation.ReflTransGen ReflectionStep μ ν := by
  obtain ⟨⟨i,s⟩, _, rfl⟩ := Finset.mem_image.mp hμ
  obtain ⟨⟨j,t⟩, _, rfl⟩ := Finset.mem_image.mp hν
  exact (coordinate_reachable i j (sign s)).trans (sign_reachable j s t)

/-- Fundamental C weights are actual prefix sums of positive coordinate evaluations. -/
theorem fundamentalWeight_eq_prefix (n : ℕ) (i : Fin (n+1)) :
    fundamentalWeights (pairingC (n+1)) (baseC n) (baseCIndexEquiv n i) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n+1) => k.val ≤ i.val), naturalWeight k 1 := by
  apply (corootBasis (pairingC (n+1)) (baseC n)).ext
  intro j
  obtain ⟨j,rfl⟩ := (baseCIndexEquiv n).surjective j
  rw [fundamentalWeights_pairing]
  have hb : corootBasis (pairingC (n+1)) (baseC n) (baseCIndexEquiv n j) =
      corootElement (pairingC (n+1)) (simpleB n j) := by
    apply Subtype.ext
    exact (baseC n).flip.coe_toWeightBasisInt_apply
      (⟨simpleB n j, (baseCIndexEquiv n j).property⟩ : (baseC n).flip.support)
  rw [hb]
  simp only [LinearMap.sum_apply, naturalWeight_pairing, one_mul, simpleB_vector]
  unfold chainVector
  by_cases hj : j.val < n
  · simp [hj, Pi.sub_apply, Pi.single_apply, Finset.sum_sub_distrib]
    simp only [Fin.ext_iff, Fin.le_def, Fin.val_mk]
    split_ifs <;> (try simp only [Fin.le_def, Fin.val_mk] at *) <;> omega
  · simp [hj, Pi.single_apply]
    simp only [Fin.ext_iff, Fin.le_def]
    split_ifs <;> have := i.isLt <;> have := j.isLt <;> omega

theorem positive_coordinate_span (n : ℕ) :
    Submodule.span ℤ (Set.range (fun k : Fin (n+1) => naturalWeight k 1)) = ⊤ := by
  apply top_unique
  rw [← (fundamentalWeights (pairingC (n+1)) (baseC n)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  obtain ⟨i,rfl⟩ := (baseCIndexEquiv n).surjective j
  rw [fundamentalWeight_eq_prefix]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.subset_span ⟨k,rfl⟩

/-- The first pinned C node is the selected minuscule fundamental weight. -/
theorem selected_fundamentalWeight (n : ℕ) :
    fundamentalWeights (pairingC (n+1)) (baseC n) (baseCIndexEquiv n 0) =
      naturalWeight 0 1 := by
  have hf : Finset.univ.filter (fun k : Fin (n+1) => k.val ≤ (0 : Fin (n+1)).val) = {0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact Fin.ext (Nat.eq_zero_of_le_zero h)
    · intro h
      subst k
      exact Nat.le_refl _
  rw [fundamentalWeight_eq_prefix, hf, Finset.sum_singleton]

/-- The actual root lattice and one defining weight generate the full weight lattice. -/
theorem root_and_one_weight_span (n : ℕ) :
    Submodule.span ℤ (Set.range (rootWeight (pairingC (n+1))) ∪
      {naturalWeight (0 : Fin (n+1)) 1}) = ⊤ := by
  apply top_unique
  rw [← positive_coordinate_span n]
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  by_cases hk : k=0
  · subst k
    exact Submodule.subset_span (Or.inr rfl)
  · have hr : rootWeight (pairingC (n+1))
        (longRoot true k 0 hk 1 (-1) (Or.inl rfl) (Or.inr rfl)) ∈
        Submodule.span ℤ (Set.range (rootWeight (pairingC (n+1))) ∪
          {naturalWeight (0 : Fin (n+1)) 1}) := Submodule.subset_span (Or.inl ⟨_,rfl⟩)
    have hz : naturalWeight (0 : Fin (n+1)) 1 ∈
        Submodule.span ℤ (Set.range (rootWeight (pairingC (n+1))) ∪
          {naturalWeight (0 : Fin (n+1)) 1}) := Submodule.subset_span (Or.inr rfl)
    have he : naturalWeight (0 : Fin (n+1)) (-1) = -naturalWeight 0 1 := by
      ext x
      simp [naturalWeight]
    rw [long_label_rootWeight, he] at hr
    simpa using Submodule.add_mem _ hr hz

end Atlas.Chevalley.Integral.Minuscule.TypeC
