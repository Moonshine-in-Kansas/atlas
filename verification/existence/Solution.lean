import Atlas

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.cyclic (p : ℕ) (hp : p.Prime) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = p ∧ IsSimpleGroup G ∧ IsMulCommutative G := by
  refine ⟨Atlas.Families.Cyclic.Model p, inferInstance,
    Atlas.Families.Cyclic.finite p hp.pos, Atlas.Families.Cyclic.card p hp.pos,
    Atlas.Families.Cyclic.isSimpleGroup p hp, ?_⟩
  infer_instance

theorem AtlasExistence.alternating (n : ℕ) (hn : 5 ≤ n) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = n.factorial / 2 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.Families.Alternating.Model n, inferInstance, inferInstance,
    Atlas.Families.Alternating.card_factorial n (by omega),
    Atlas.Families.Alternating.isSimpleGroup n hn,
    not_comm_of_pair (Atlas.Families.Alternating.exists_mul_ne_mul n (by omega))⟩

theorem AtlasExistence.typeA {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) / Nat.gcd n (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  obtain ⟨G, g, _, hf, hs, ha, ho, _⟩ := Atlas.exists_typeA (F := F) n hn h2 h3
  exact ⟨G, g, hf, ho, hs, ha⟩

theorem AtlasExistence.typeB {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : 1 ≤ n ∧ 2 ≤ Nat.card F ∧ (n, Nat.card F) ≠ (1, 2) ∧
      (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  refine ⟨Atlas.Orthogonal.B n F, inferInstance, inferInstance, ?_,
    Atlas.Orthogonal.B_simple_all_rank n h, Atlas.Orthogonal.B_noncommutative_all_rank n h⟩
  exact Atlas.Orthogonal.B_card_all_rank n h.1

theorem AtlasExistence.typeC {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : (n = 1 ∧ 3 < Nat.card F) ∨ (2 ≤ n ∧ (n, Nat.card F) ≠ (2, 2))) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  refine ⟨Atlas.Symplectic.PSp n F, inferInstance, inferInstance, ?_,
    Atlas.Symplectic.simple_of_good h, Atlas.Symplectic.projective_not_commutative h⟩
  apply Atlas.Symplectic.card_psp
  rcases h with h | h <;> omega

theorem AtlasExistence.typeD {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1)) * (Nat.card F ^ n - 1) *
      ∏ i ∈ Finset.range (n - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ n - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.Orthogonal.DPlus n F, inferInstance, inferInstance,
    Atlas.Orthogonal.DPlus_card n hn, Atlas.Orthogonal.DPlus_simple n hn,
    Atlas.Orthogonal.DPlus_noncommutative n hn⟩

theorem AtlasExistence.G2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.G2.Model F, inferInstance, inferInstance, Atlas.G2.card_Model,
    Atlas.G2.isSimple hq, not_comm_of_pair Atlas.G2.exists_mul_ne_mul⟩

theorem AtlasExistence.ReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hq : Nat.card F = 3 ^ (2 * m + 1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.ReeG2.Model F m, inferInstance, inferInstance, Atlas.ReeG2.order m hq,
    Atlas.ReeG2.simple m ⟨hm, hq⟩, not_comm_of_pair (Atlas.ReeG2.model_noncommutative m hq)⟩

theorem AtlasExistence.M11  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 7920 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu11.Model Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, inferInstance, Atlas.Sporadic.Mathieu11.finite Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint,
      Atlas.Sporadic.Mathieu11.card Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, Atlas.Sporadic.Mathieu11.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint,
      not_comm_of_pair (Atlas.Sporadic.Mathieu11.exists_mul_ne_mul Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint)⟩

theorem AtlasExistence.M12  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 95040 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu12.Model Atlas.Sporadic.Mathieu12.standardDodecad, inferInstance, Atlas.Sporadic.Mathieu12.finite Atlas.Sporadic.Mathieu12.standardDodecad,
      Atlas.Sporadic.Mathieu12.card Atlas.Sporadic.Mathieu12.standardDodecad, Atlas.Sporadic.Mathieu12.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad,
      not_comm_of_pair (Atlas.Sporadic.Mathieu12.exists_mul_ne_mul Atlas.Sporadic.Mathieu12.standardDodecad)⟩

theorem AtlasExistence.M22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 443520 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu22.Model ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩, inferInstance, Atlas.Sporadic.Mathieu22.finite ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩,
      Atlas.Sporadic.Mathieu22.card ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩, Atlas.Sporadic.Mathieu22.isSimpleGroup ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩,
      not_comm_of_pair (Atlas.Sporadic.Mathieu22.exists_mul_ne_mul ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩)⟩

theorem AtlasExistence.M23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 10200960 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu23.Model ((0,0),0), inferInstance, Atlas.Sporadic.Mathieu23.finite ((0,0),0),
      Atlas.Sporadic.Mathieu23.card ((0,0),0), Atlas.Sporadic.Mathieu23.isSimpleGroup ((0,0),0),
      not_comm_of_pair (Atlas.Sporadic.Mathieu23.exists_mul_ne_mul ((0,0),0))⟩

theorem AtlasExistence.M24  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 244823040 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu24.Model , inferInstance, Atlas.Sporadic.Mathieu24.finite ,
      Atlas.Sporadic.Mathieu24.card , Atlas.Sporadic.Mathieu24.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Mathieu24.exists_mul_ne_mul )⟩

theorem AtlasExistence.Co1  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4157776806543360000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Conway1.Model , inferInstance, Atlas.Sporadic.Conway1.finite ,
      Atlas.Sporadic.Conway1.card , Atlas.Sporadic.Conway1.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Conway1.exists_mul_ne_mul )⟩

theorem AtlasExistence.Co2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 42305421312000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Conway2.Model , inferInstance, Atlas.Sporadic.Conway2.finite ,
      Atlas.Sporadic.Conway2.card , Atlas.Sporadic.Conway2.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Conway2.exists_mul_ne_mul )⟩

theorem AtlasExistence.Co3  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 495766656000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Conway3.Model , inferInstance, Atlas.Sporadic.Conway3.finite ,
      Atlas.Sporadic.Conway3.card , Atlas.Sporadic.Conway3.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Conway3.exists_mul_ne_mul )⟩

theorem AtlasExistence.McL  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 898128000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.McLaughlin.Model , inferInstance, Atlas.Sporadic.McLaughlin.finite ,
      Atlas.Sporadic.McLaughlin.card , Atlas.Sporadic.McLaughlin.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.McLaughlin.exists_mul_ne_mul )⟩

theorem AtlasExistence.HS  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 44352000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.HigmanSims.Model , inferInstance, Atlas.Sporadic.HigmanSims.finite ,
      Atlas.Sporadic.HigmanSims.card , Atlas.Sporadic.HigmanSims.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.HigmanSims.exists_mul_ne_mul )⟩

theorem AtlasExistence.Suz  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 448345497600 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Suzuki.Model , inferInstance, Atlas.Sporadic.Suzuki.finite ,
      Atlas.Sporadic.Suzuki.card , Atlas.Sporadic.Suzuki.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Suzuki.exists_mul_ne_mul )⟩

theorem AtlasExistence.J2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 604800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Janko2.Model , inferInstance, Atlas.Sporadic.Janko2.finite ,
      Atlas.Sporadic.Janko2.card , Atlas.Sporadic.Janko2.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Janko2.exists_mul_ne_mul )⟩

theorem AtlasExistence.Fi22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 64561751654400 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Fischer22.Model , inferInstance, Atlas.Sporadic.Fischer22.finite ,
      Atlas.Sporadic.Fischer22.card , Atlas.Sporadic.Fischer22.simple ,
      Atlas.Sporadic.Fischer22.noncommutative⟩

theorem AtlasExistence.Fi23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4089470473293004800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Fischer23.Model , inferInstance, Atlas.Sporadic.Fischer23.finite ,
      Atlas.Sporadic.Fischer23.card , Atlas.Sporadic.Fischer23.simple ,
      Atlas.Sporadic.Fischer23.noncommutative⟩

theorem AtlasExistence.Fi24Prime  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 1255205709190661721292800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Fischer24Prime.Model , inferInstance, Atlas.Sporadic.Fischer24Prime.finite ,
      Atlas.Sporadic.Fischer24Prime.card , Atlas.Sporadic.Fischer24Prime.simple ,
      Atlas.Sporadic.Fischer24Prime.noncommutative⟩

