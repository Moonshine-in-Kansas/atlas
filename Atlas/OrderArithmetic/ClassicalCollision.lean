import Atlas.OrderArithmetic.ClassicalInvariantClassification
import Atlas.OrderArithmetic.ResidualSeparation
import Atlas.OrderArithmetic.ElementaryClassification

namespace Atlas.OrderArithmetic

theorem BC_collision {r q : ℕ} (hr : 2 ≤ r) (hq : PrimePower q) :
    Collision (.B r q) (.C r q) := by
  by_cases h : r = 2 ∨ (3 ≤ r ∧ Even q)
  · exact Or.inl (by simp [normalize, h])
  · have hr3 : 3 ≤ r := by omega
    have ho : Odd q := by
      rcases Nat.even_or_odd q with he | ho
      · exact False.elim (h (Or.inr ⟨hr3, he⟩))
      · exact ho
    apply Or.inr
    simp only [normalize, if_neg h]
    exact Or.inr (Or.inr ⟨r, q, hr3, hq, ho, Or.inl ⟨rfl, rfl⟩⟩)

theorem field_eq_of_equal_order_and_exponent {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (ha : characteristicExponent x = characteristicExponent y) :
    fieldSize x = fieldSize y := by
  have hv := equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he
  rw [ha] at hv
  have hpos := characteristicExponent_pos hy hly
  have hfg : f = g := by nlinarith
  rw [hqx, hqy, hfg]

theorem field_square_of_equal_order_and_double_exponent {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y)
    (ha : characteristicExponent y = 2 * characteristicExponent x) :
    fieldSize x = fieldSize y ^ 2 := by
  have hv := equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he
  rw [ha] at hv
  have hpos := characteristicExponent_pos hx hlx
  have hfg : f = g * 2 := by nlinarith
  rw [hqx, hqy, ← pow_mul, hfg]

theorem same_profile_collision {x y : RawEntry} {P : ClassicalIndexProfile}
    (hx : Admissible x) (hy : Admissible y) (hpx : P.Represents x)
    (hpy : P.Represents y) (hq : fieldSize x = fieldSize y) : Collision x y := by
  cases P with
  | BC k =>
    obtain ⟨q, h | h⟩ := hpx <;> obtain ⟨Q, h' | h'⟩ := hpy <;> subst x <;> subst y
    all_goals change q = Q at hq; subst Q
    · exact Or.inl rfl
    · exact BC_collision (by omega) hx.2.1
    · exact collision_symm (BC_collision (by omega) hx.2.1)
    · exact Or.inl rfl
  | linear k | unitaryOdd k | unitaryEven k | unitaryFour | Dplus k | Dminus k =>
    obtain ⟨q, rfl⟩ := hpx
    obtain ⟨Q, rfl⟩ := hpy
    change q = Q at hq
    subst Q
    exact Or.inl rfl

theorem characteristicExponent_minus_eq_twice_linear (r q Q : ℕ) :
    characteristicExponent (.Dminus r Q) = 2 * characteristicExponent (.linear r q) := by
  change r * (r - 1) = 2 * (r * (r - 1) / 2)
  have h := Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one r)
  nlinarith

/-- Same-characteristic equal orders eliminate the two residual profile pairs.
The compatibility hypothesis is purely the numerical shape relation. -/
theorem compatible_profiles_collision {x y : RawEntry} {P R : ClassicalIndexProfile}
    {p f g : ℕ} (hx : Admissible x) (hy : Admissible y)
    (hlx : IsLie x) (hly : IsLie y) (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hpx : P.Represents x) (hry : R.Represents y)
    (hc : ClassicalIndexProfile.Compatible P R) : Collision x y := by
  rcases ClassicalIndexProfile.compatible_alternatives hc with
    hsame | ⟨hP, hR⟩ | ⟨hP, hR⟩ | ⟨k, hP, hR⟩ | ⟨k, hP, hR⟩
  · subst R
    have ha : characteristicExponent x = characteristicExponent y := by
      have h1 := hpx.twiceExponent_eq
      have h2 := hry.twiceExponent_eq
      omega
    exact same_profile_collision hx hy hpx hry
      (field_eq_of_equal_order_and_exponent hx hy hlx hly hp hf hg hqx hqy he ha)
  · subst P
    subst R
    obtain ⟨q, rfl⟩ := hpx
    obtain ⟨Q, rfl⟩ := hry
    have hsquare : q = Q ^ 2 :=
      field_square_of_equal_order_and_double_exponent hx hy hlx hly hp hf hg hqx hqy he
        (by norm_num [characteristicExponent])
    subst q
    exact (linear_three_square_ne_unitary_four hy.2.1 he).elim
  · subst P
    subst R
    obtain ⟨q, rfl⟩ := hpx
    obtain ⟨Q, rfl⟩ := hry
    have hsquare : Q = q ^ 2 :=
      field_square_of_equal_order_and_double_exponent hy hx hly hlx hp hg hf hqy hqx he.symm
        (by norm_num [characteristicExponent])
    subst Q
    exact (linear_three_square_ne_unitary_four hx.2.1 he.symm).elim
  · subst P
    subst R
    obtain ⟨q, rfl⟩ := hpx
    obtain ⟨Q, rfl⟩ := hry
    have hrank : k + 2 + 2 = k + 4 := by omega
    simp only [hrank] at *
    have hsquare : q = Q ^ 2 :=
      field_square_of_equal_order_and_double_exponent hx hy hlx hly hp hf hg hqx hqy he
        (characteristicExponent_minus_eq_twice_linear _ _ _)
    subst q
    exact (linear_square_ne_minus hy.2 (by omega) he).elim
  · subst P
    subst R
    obtain ⟨q, rfl⟩ := hpx
    obtain ⟨Q, rfl⟩ := hry
    have hrank : k + 2 + 2 = k + 4 := by omega
    simp only [hrank] at *
    have hsquare : Q = q ^ 2 :=
      field_square_of_equal_order_and_double_exponent hy hx hly hlx hp hg hf hqy hqx he.symm
        (characteristicExponent_minus_eq_twice_linear _ _ _)
    subst Q
    exact (linear_square_ne_minus hx.2 (by omega) he.symm).elim

/-- Complete classical comparison once the two scaled numerical index equalities
are available. The outstanding primitive-divisor argument must supply those
equalities outside its separately treated finite exceptional branches. -/
theorem classical_collision_of_scaled_indices {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y)
    (hm : f * topIndex x = g * topIndex y)
    (hs : f * secondIndex x = g * secondIndex y) : Collision x y := by
  have hlx := classical_isLie hcx
  have hly := classical_isLie hcy
  have ha := index_ratio_of_equal_order_and_top_index hx hy hlx hly hp hf hg hqx hqy he hm
  have hsec := index_ratio_of_scaled_equalities hf hs hm
  obtain ⟨P, R, hpx, hry, hc⟩ :=
    classicalInvariantCompatible_of_cross_equalities hx hy hcx hcy ha hsec
  exact compatible_profiles_collision hx hy hlx hly hp hf hg hqx hqy he hpx hry hc

end Atlas.OrderArithmetic
