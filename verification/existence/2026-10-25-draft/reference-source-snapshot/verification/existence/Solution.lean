import Atlas

open scoped BigOperators
universe u v

theorem AtlasExistence.cyclic (p : ℕ) (hp : p.Prime) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = p ∧ IsSimpleGroup G ∧ IsMulCommutative G := by
  refine ⟨Atlas.Families.Cyclic.Model p, inferInstance,
    Atlas.Families.Cyclic.finite p hp.pos, Atlas.Families.Cyclic.card p hp.pos,
    Atlas.Families.Cyclic.isSimpleGroup p hp, ?_⟩
  infer_instance

theorem AtlasExistence.alternating (n : ℕ) (hn : 5 ≤ n) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = n.factorial / 2 ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Families.Alternating.Model n, inferInstance, inferInstance,
    Atlas.Families.Alternating.card_factorial n (by omega),
    Atlas.Families.Alternating.isSimpleGroup n hn⟩

theorem AtlasExistence.typeA {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) / Nat.gcd n (Nat.card F - 1) ∧ IsSimpleGroup G := by
  obtain ⟨G, g, _, hf, hs, ha, ho, _⟩ := Atlas.exists_typeA (F := F) n hn h2 h3
  exact ⟨G, g, hf, ho, hs⟩

theorem AtlasExistence.typeB {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : 1 ≤ n ∧ 2 ≤ Nat.card F ∧ (n, Nat.card F) ≠ (1, 2) ∧
      (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  refine ⟨Atlas.Orthogonal.B n F, inferInstance, inferInstance, ?_,
    Atlas.Orthogonal.B_simple_all_rank n h⟩
  exact Atlas.Orthogonal.B_card_all_rank n h.1

theorem AtlasExistence.typeC {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : (n = 1 ∧ 3 < Nat.card F) ∨ (2 ≤ n ∧ (n, Nat.card F) ≠ (2, 2))) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  refine ⟨Atlas.Symplectic.PSp n F, inferInstance, inferInstance, ?_,
    Atlas.Symplectic.simple_of_good h⟩
  apply Atlas.Symplectic.card_psp
  rcases h with h | h <;> omega

theorem AtlasExistence.typeD {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1)) * (Nat.card F ^ n - 1) *
      ∏ i ∈ Finset.range (n - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ n - 1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Orthogonal.DPlus n F, inferInstance, inferInstance,
    Atlas.Orthogonal.DPlus_card n hn, Atlas.Orthogonal.DPlus_simple n hn⟩

theorem AtlasExistence.G2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.G2.Model F, inferInstance, inferInstance, Atlas.G2.card_Model,
    Atlas.G2.isSimple hq⟩

theorem AtlasExistence.ReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hq : Nat.card F = 3 ^ (2 * m + 1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.ReeG2.Model F m, inferInstance, inferInstance, Atlas.ReeG2.order m hq,
    Atlas.ReeG2.simple m ⟨hm, hq⟩⟩

theorem AtlasExistence.M11  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 7920 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu11.Model Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, inferInstance, Atlas.Sporadic.Mathieu11.finite Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint,
      Atlas.Sporadic.Mathieu11.card Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, Atlas.Sporadic.Mathieu11.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint⟩

theorem AtlasExistence.M12  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 95040 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu12.Model Atlas.Sporadic.Mathieu12.standardDodecad, inferInstance, Atlas.Sporadic.Mathieu12.finite Atlas.Sporadic.Mathieu12.standardDodecad,
      Atlas.Sporadic.Mathieu12.card Atlas.Sporadic.Mathieu12.standardDodecad, Atlas.Sporadic.Mathieu12.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad⟩

theorem AtlasExistence.M22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 443520 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu22.Model ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩, inferInstance, Atlas.Sporadic.Mathieu22.finite ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩,
      Atlas.Sporadic.Mathieu22.card ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩, Atlas.Sporadic.Mathieu22.isSimpleGroup ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩⟩

theorem AtlasExistence.M23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 10200960 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu23.Model ((0,0),0), inferInstance, Atlas.Sporadic.Mathieu23.finite ((0,0),0),
      Atlas.Sporadic.Mathieu23.card ((0,0),0), Atlas.Sporadic.Mathieu23.isSimpleGroup ((0,0),0)⟩

theorem AtlasExistence.M24  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 244823040 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu24.Model , inferInstance, Atlas.Sporadic.Mathieu24.finite ,
      Atlas.Sporadic.Mathieu24.card , Atlas.Sporadic.Mathieu24.isSimpleGroup ⟩

theorem AtlasExistence.Co1  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4157776806543360000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Conway1.Model , inferInstance, Atlas.Sporadic.Conway1.finite ,
      Atlas.Sporadic.Conway1.card , Atlas.Sporadic.Conway1.isSimpleGroup ⟩

theorem AtlasExistence.Co2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 42305421312000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Conway2.Model , inferInstance, Atlas.Sporadic.Conway2.finite ,
      Atlas.Sporadic.Conway2.card , Atlas.Sporadic.Conway2.isSimpleGroup ⟩

theorem AtlasExistence.Co3  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 495766656000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Conway3.Model , inferInstance, Atlas.Sporadic.Conway3.finite ,
      Atlas.Sporadic.Conway3.card , Atlas.Sporadic.Conway3.isSimpleGroup ⟩

theorem AtlasExistence.McL  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 898128000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.McLaughlin.Model , inferInstance, Atlas.Sporadic.McLaughlin.finite ,
      Atlas.Sporadic.McLaughlin.card , Atlas.Sporadic.McLaughlin.isSimpleGroup ⟩

theorem AtlasExistence.HS  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 44352000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.HigmanSims.Model , inferInstance, Atlas.Sporadic.HigmanSims.finite ,
      Atlas.Sporadic.HigmanSims.card , Atlas.Sporadic.HigmanSims.isSimpleGroup ⟩

theorem AtlasExistence.Suz  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 448345497600 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Suzuki.Model , inferInstance, Atlas.Sporadic.Suzuki.finite ,
      Atlas.Sporadic.Suzuki.card , Atlas.Sporadic.Suzuki.isSimpleGroup ⟩

theorem AtlasExistence.J2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 604800 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Janko2.Model , inferInstance, Atlas.Sporadic.Janko2.finite ,
      Atlas.Sporadic.Janko2.card , Atlas.Sporadic.Janko2.isSimpleGroup ⟩

theorem AtlasExistence.Fi22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 64561751654400 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Fischer22.Model , inferInstance, Atlas.Sporadic.Fischer22.finite ,
      Atlas.Sporadic.Fischer22.card , Atlas.Sporadic.Fischer22.simple ⟩

theorem AtlasExistence.Fi23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4089470473293004800 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Fischer23.Model , inferInstance, Atlas.Sporadic.Fischer23.finite ,
      Atlas.Sporadic.Fischer23.card , Atlas.Sporadic.Fischer23.simple ⟩

theorem AtlasExistence.Fi24Prime  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 1255205709190661721292800 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Fischer24Prime.Model , inferInstance, Atlas.Sporadic.Fischer24Prime.finite ,
      Atlas.Sporadic.Fischer24Prime.card , Atlas.Sporadic.Fischer24Prime.simple ⟩


theorem AtlasExistence.type2A {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n)
    (h22 : (n, Nat.card F) ≠ (2,2)) (h23 : (n, Nat.card F) ≠ (2,3))
    (h32 : (n, Nat.card F) ≠ (3,2)) :
  ∃ (G : Type v) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n*(n-1)/2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then Nat.card F^i-1 else Nat.card F^i+1)) /
      Nat.gcd n (Nat.card F+1) ∧ IsSimpleGroup G := by
  have h := Atlas.type2A_construction hdeg n hn ⟨hn,h22,h23,h32⟩
  exact ⟨Atlas.Unitary.PSU F K n hdeg, inferInstance, h.finite,
    h.order, h.simple⟩

theorem AtlasExistence.type2D {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type (max u v)) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F^(n*(n-1)) * (Nat.card F^n+1) *
      ∏ i ∈ Finset.range (n-1), (Nat.card F^(2*(i+1))-1)) /
      Nat.gcd 4 (Nat.card F^n+1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Orthogonal.DMinus n F K hdeg, inferInstance, inferInstance,
    Atlas.Orthogonal.Minus.family_order hdeg n (by omega),
    Atlas.Orthogonal.Minus.family_simple hdeg n hn⟩

theorem AtlasExistence.SuzukiFamily {F : Type u} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hm : 1 ≤ m) (hq : Nat.card F = 2^(2*m+1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F^2*(Nat.card F^2+1)*(Nat.card F-1) ∧
      IsSimpleGroup G := by
  have h := Atlas.typeSuzuki_construction m hq hm
  exact ⟨Atlas.SuzukiFamily.Group F m, inferInstance, h.finite, h.order, h.simple⟩

theorem AtlasExistence.Triality {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 3) :
  ∃ (G : Type v) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F^12*(Nat.card F^8+Nat.card F^4+1)*
      (Nat.card F^6-1)*(Nat.card F^2-1) ∧ IsSimpleGroup G := by
  obtain ⟨G,g,hf,hs,ha,ho,_⟩ := Atlas.exists_type3D4 hdeg
  exact ⟨G,g,hf,ho,hs⟩

theorem AtlasExistence.F4 {F : Type u} [Field F] [Finite F] :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F^24*(Nat.card F^12-1)*(Nat.card F^8-1)*
      (Nat.card F^6-1)*(Nat.card F^2-1) ∧ IsSimpleGroup G := by
  have h := Atlas.typeF4_construction (F := F)
  exact ⟨Atlas.F4.Model F,inferInstance,h.finite,h.order,h.simple⟩

theorem AtlasExistence.Ru :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 145926144000 ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Sporadic.Rudvalis.Model,inferInstance,Atlas.Sporadic.Rudvalis.finite,
    Atlas.Sporadic.Rudvalis.card,Atlas.Sporadic.Rudvalis.isSimpleGroup⟩

theorem AtlasExistence.Tits :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 17971200 ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Tits.Model,inferInstance,Atlas.Tits.finite,Atlas.Tits.card,
    Atlas.Tits.isSimpleGroup⟩
