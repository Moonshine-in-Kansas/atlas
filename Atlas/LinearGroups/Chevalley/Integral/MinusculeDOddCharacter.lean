import Atlas.LinearGroups.Chevalley.Integral.MinusculeDNormalForms

/-! explicit odd-rank D weight/root quotient isomorphism. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD

/-- Odd rank gives a unit residue, proved by elementary integer remainders. -/
theorem odd_rank_mod_four (n : ℕ) (hn : Odd (n+2)) :
    (n+2 : ZMod 4)=1 ∨ (n+2 : ZMod 4)=3 := by
  obtain ⟨k,hk⟩ := hn
  have hm : (n+2)%4=1 ∨ (n+2)%4=3 := by omega
  rcases hm with hm | hm
  · left
    have he : ((n+2 : ℕ) : ZMod 4)=1 := by
      rw [← ZMod.natCast_mod (n+2) 4,hm]
      rfl
    simpa using he
  · right
    have he : ((n+2 : ℕ) : ZMod 4)=3 := by
      rw [← ZMod.natCast_mod (n+2) 4,hm]
      rfl
    simpa using he

theorem odd_quotientTotal_bijective (n : ℕ) (hn : Odd (n+2)) :
    Function.Bijective (quotientTotal n) := by
  have hr := odd_rank_mod_four n hn
  constructor
  · intro x y h
    have h01 : (0 : ZMod 4) ≠ 1 := by decide
    have h02 : (0 : ZMod 4) ≠ 2 := by decide
    have h03 : (0 : ZMod 4) ≠ 3 := by decide
    have h12 : (1 : ZMod 4) ≠ 2 := by decide
    have h13 : (1 : ZMod 4) ≠ 3 := by decide
    have h23 : (2 : ZMod 4) ≠ 3 := by decide
    obtain ⟨⟨a,b⟩,rfl⟩ := normalForm_surjective n x
    obtain ⟨⟨c,d⟩,rfl⟩ := normalForm_surjective n y
    rcases hr with hr | hr <;> cases a <;> cases b <;> cases c <;> cases d
    all_goals try rfl
    all_goals try norm_num [normalForm,map_add,quotientTotal_positive,quotientTotal_vector,hr,
      show (4 : ZMod 4) = 0 by decide, show (5 : ZMod 4) = 1 by decide] at h
    all_goals try simp only [show (5 : ZMod 4) = 1 by decide] at h
    all_goals simp_all
  · intro z
    rcases hr with hr | hr <;> fin_cases z
    · refine ⟨normalForm n (false,false), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (true,false), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (false,true), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (true,true), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (false,false), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (true,true), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (false,true), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl
    · refine ⟨normalForm n (true,false), ?_⟩
      norm_num [normalForm, map_add, quotientTotal_positive, quotientTotal_vector, hr] <;> rfl

/-- The total doubled-coordinate evaluation identifies the actual quotient with Z/4. -/
def oddWeightRootEquiv (n : ℕ) (hn : Odd (n+2)) : WeightRootQuotient n ≃+ ZMod 4 :=
  (LinearEquiv.ofBijective (quotientTotal n) (odd_quotientTotal_bijective n hn)).toAddEquiv

end Atlas.Chevalley.Integral.Minuscule.TypeD
