import Atlas.LinearGroups.Chevalley.Integral.MinusculeDNormalForms

/-! an explicit second mod-two character for even D rank. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

/-- The sum of e_i-e_0 over nonzero i, as a literal sum of actual coroots. -/
def balancedTest (n : ℕ) : CorootLattice (pairingD (n+2)) :=
  ∑ i : Fin (n+2), if hi : i=0 then 0 else
    corootElement (pairingD (n+2)) (longRoot false i 0 hi 1 (-1) (Or.inl rfl) (Or.inr rfl))

theorem balancedTest_apply (n : ℕ) (x : ClassicalData.Lattice (n+2)) :
    (balancedTest n).val x = (∑ i, x i) - (n+2 : ℤ)*x 0 := by
  have he : ∀ i : Fin (n+2),
      ((if hi : i=0 then 0 else corootElement (pairingD (n+2))
        (longRoot false i 0 hi 1 (-1) (Or.inl rfl) (Or.inr rfl))) :
        CorootLattice (pairingD (n+2))).val x = x i-x 0 := by
    intro i
    by_cases hi : i=0
    · subst i; simp
    · simp only [hi,dif_neg]
      change coroot (longRoot false i 0 hi 1 (-1) _ _) x = _
      rw [coroot_long]
      ring
  simp only [balancedTest,Submodule.coe_sum,LinearMap.sum_apply,he]
  simp [Finset.sum_sub_distrib]

def balancedCharacter (n : ℕ) : WeightLattice (pairingD (n+2)) →ₗ[ℤ] ZMod 2 where
  toFun μ := (μ (balancedTest n) : ZMod 2)
  map_add' μ ν := by simp
  map_smul' t μ := by simp [Int.cast_mul]

theorem balancedCharacter_root (n : ℕ) (hn : Even (n+2)) (a : DRoot (n+2)) :
    balancedCharacter n (rootWeight (pairingD (n+2)) a) = 0 := by
  change (((balancedTest n).val a.val : ℤ) : ZMod 2) = 0
  rw [balancedTest_apply]
  have hr : (n+2 : ZMod 2)=0 := by
    obtain ⟨k,hk⟩ := hn
    have hcast : (n+2 : ZMod 2) = (k : ZMod 2)+(k : ZMod 2) := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using congrArg (fun j : ℕ => (j : ZMod 2)) hk
    rw [hcast]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide]
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,hr,zero_mul,sub_zero]
  rcases signed_support_classification a with ⟨h,_⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · cases h
  · rw [ha]
    simp only [Pi.add_apply,Pi.single_apply,Finset.sum_add_distrib,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num <;> decide

def quotientBalanced (n : ℕ) (hn : Even (n+2)) : WeightRootQuotient n →ₗ[ℤ] ZMod 2 :=
  (rootLattice (pairingD (n+2))).liftQ (balancedCharacter n) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact balancedCharacter_root n hn a)

theorem quotientBalanced_positive (n : ℕ) (hn : Even (n+2)) :
    quotientBalanced n hn (positiveSpinClass n)=0 := by
  have h := twice_spinWeight_evaluation n (fun _ => true) (balancedTest n)
  rw [balancedTest_apply] at h
  simp [signVector,sign] at h
  change ((spinWeight n (fun _ => true) (balancedTest n) : ℤ) : ZMod 2)=0
  have hz : spinWeight n (fun _ => true) (balancedTest n)=0 := by omega
  rw [hz,Int.cast_zero]

theorem quotientBalanced_vector (n : ℕ) (hn : Even (n+2)) :
    quotientBalanced n hn (vectorClass n)=1 := by
  change (((balancedTest n).val (Pi.single (Fin.last (n+1)) 1) : ℤ) : ZMod 2)=1
  rw [balancedTest_apply]
  have hl : (Fin.last (n+1) : Fin (n+2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    change n+1=0 at this
    omega
  simp [Pi.single_apply,hl,Ne.symm hl]

/-- The two coordinates distinguish the explicit four normal forms in even rank. -/
def evenQuotientCharacters (n : ℕ) (hn : Even (n+2)) :
    WeightRootQuotient n →ₗ[ℤ] (ZMod 2 × ZMod 2) :=
  (quotientSpinParity n).prod (quotientBalanced n hn)

theorem evenQuotientCharacters_bijective (n : ℕ) (hn : Even (n+2)) :
    Function.Bijective (evenQuotientCharacters n hn) := by
  constructor
  · intro x y h
    obtain ⟨⟨a,b⟩,rfl⟩ := normalForm_surjective n x
    obtain ⟨⟨c,d⟩,rfl⟩ := normalForm_surjective n y
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    cases a <;> cases b <;> cases c <;> cases d
    all_goals try rfl
    all_goals try simp [show (0 : ZMod 2) ≠ 1 by decide, evenQuotientCharacters,normalForm,map_add,quotientSpinParity_positive,
      quotientSpinParity_vector,quotientBalanced_positive,quotientBalanced_vector] at h₁
    all_goals simp [show (0 : ZMod 2) ≠ 1 by decide, evenQuotientCharacters,normalForm,map_add,quotientSpinParity_positive,
      quotientSpinParity_vector,quotientBalanced_positive,quotientBalanced_vector] at h₂
  · rintro ⟨a,b⟩
    fin_cases a <;> fin_cases b
    · refine ⟨normalForm n (false,false), ?_⟩
      simp [evenQuotientCharacters, normalForm, map_add, quotientSpinParity_positive,
        quotientSpinParity_vector, quotientBalanced_positive, quotientBalanced_vector] <;> decide
    · refine ⟨normalForm n (false,true), ?_⟩
      simp [evenQuotientCharacters, normalForm, map_add, quotientSpinParity_positive,
        quotientSpinParity_vector, quotientBalanced_positive, quotientBalanced_vector] <;> decide
    · refine ⟨normalForm n (true,false), ?_⟩
      simp [evenQuotientCharacters, normalForm, map_add, quotientSpinParity_positive,
        quotientSpinParity_vector, quotientBalanced_positive, quotientBalanced_vector] <;> decide
    · refine ⟨normalForm n (true,true), ?_⟩
      simp [evenQuotientCharacters, normalForm, map_add, quotientSpinParity_positive,
        quotientSpinParity_vector, quotientBalanced_positive, quotientBalanced_vector] <;> decide

/-- Explicit additive isomorphism, with both coordinates actual coroot evaluations. -/
def evenWeightRootEquiv (n : ℕ) (hn : Even (n+2)) :
    WeightRootQuotient n ≃+ (ZMod 2 × ZMod 2) :=
  (LinearEquiv.ofBijective (evenQuotientCharacters n hn)
    (evenQuotientCharacters_bijective n hn)).toAddEquiv

end Atlas.Chevalley.Integral.Minuscule.TypeD

