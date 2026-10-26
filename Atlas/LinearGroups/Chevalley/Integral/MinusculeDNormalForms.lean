import Atlas.LinearGroups.Chevalley.Integral.MinusculeDCharacters

/-! four explicit normal forms in the actual D weight/root quotient. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

theorem weightClass_integer_span (n : ℕ) (μ : WeightLattice (pairingD (n+2))) :
    ∃ a b : ℤ, weightClass n μ = a • positiveSpinClass n + b • vectorClass n := by
  have hμ : μ ∈ Submodule.span ℤ
      (Set.range (rootWeight (pairingD (n+2))) ∪
        {spinWeight n (fun _ => true),spinWeight n (lastNegative n)}) := by
    rw [root_and_two_spin_weights_span]
    trivial
  induction hμ using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | hx
    · refine ⟨0,0,?_⟩
      simp only [zero_smul,add_zero]
      exact (weightClass_zero_iff n _).mpr (rootWeight_mem_rootLattice _ a)
    · rcases hx with rfl | rfl
      · exact ⟨1,0,by simp [positiveSpinClass]⟩
      · refine ⟨1,-1,?_⟩
        change negativeSpinClass n = _
        have h := spin_class_difference n
        rw [one_smul,neg_one_smul,← sub_eq_add_neg]
        exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)
  | zero => exact ⟨0,0,by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a,b,ha⟩ := ihx
    obtain ⟨c,d,hc⟩ := ihy
    refine ⟨a+c,b+d,?_⟩
    rw [map_add,ha,hc]
    module
  | smul t x hx ih =>
    obtain ⟨a,b,ha⟩ := ih
    refine ⟨t*a,t*b,?_⟩
    rw [map_smul,ha]
    module

theorem quotient_integer_span (n : ℕ) (x : WeightRootQuotient n) :
    ∃ a b : ℤ, x = a • positiveSpinClass n + b • vectorClass n := by
  induction x using Submodule.Quotient.induction_on with
  | _ μ => exact weightClass_integer_span n μ

/-- Euclidean reduction, keeping the rank-sensitive carries explicit. -/
theorem integer_normal_form (n : ℕ) (a b : ℤ) :
    a • positiveSpinClass n + b • vectorClass n =
      (a % 2) • positiveSpinClass n + (((a/2)*(n+2)+b) % 2) • vectorClass n := by
  let c : ℤ := (a/2)*(n+2)+b
  have ha : a % 2 + (a/2)*2 = a := by omega
  have hc : c % 2 + (c/2)*2 = c := by omega
  calc
    _ = (a % 2) • positiveSpinClass n + (a/2) • ((2 : ℤ) • positiveSpinClass n) +
        b • vectorClass n := by rw [smul_smul,← add_smul,ha]
    _ = (a % 2) • positiveSpinClass n + c • vectorClass n := by
      rw [twice_positiveSpinClass]
      dsimp [c]
      module
    _ = (a % 2) • positiveSpinClass n +
        ((c % 2) • vectorClass n + (c/2) • ((2 : ℤ) • vectorClass n)) := by
      rw [smul_smul,← add_smul,hc]
    _ = _ := by rw [twice_vectorClass,smul_zero,add_zero]

theorem quotient_four_forms (n : ℕ) (x : WeightRootQuotient n) :
    x=0 ∨ x=vectorClass n ∨ x=positiveSpinClass n ∨ x=positiveSpinClass n+vectorClass n := by
  obtain ⟨a,b,rfl⟩ := quotient_integer_span n x
  rw [integer_normal_form]
  have ha : a%2=0 ∨ a%2=1 := by omega
  have hb : ((a/2)*(n+2)+b)%2=0 ∨ ((a/2)*(n+2)+b)%2=1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha,hb]

def normalForm (n : ℕ) (p : Bool × Bool) : WeightRootQuotient n :=
  (if p.1 then positiveSpinClass n else 0) + (if p.2 then vectorClass n else 0)

theorem normalForm_surjective (n : ℕ) : Function.Surjective (normalForm n) := by
  intro x
  rcases quotient_four_forms n x with h | h | h | h
  · exact ⟨(false,false),by simpa [normalForm] using h.symm⟩
  · exact ⟨(false,true),by simpa [normalForm] using h.symm⟩
  · exact ⟨(true,false),by simpa [normalForm] using h.symm⟩
  · exact ⟨(true,true),by simpa [normalForm] using h.symm⟩

theorem normalForm_injective (n : ℕ) : Function.Injective (normalForm n) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  have htwo' : (0 : ZMod 4) ≠ 2 := by decide
  have h₂ := congrArg (quotientSpinParity n) h
  have h₄ := congrArg (quotientTotal n) h
  cases a <;> cases b <;> cases c <;> cases d
  all_goals try rfl
  all_goals try norm_num [normalForm, map_add, quotientSpinParity_positive,
    quotientSpinParity_vector] at h₂
  all_goals try norm_num [normalForm, map_add, quotientTotal_positive,
    quotientTotal_vector] at h₄
  all_goals aesop


def normalFormEquiv (n : ℕ) : (Bool × Bool) ≃ WeightRootQuotient n :=
  Equiv.ofBijective (normalForm n) ⟨normalForm_injective n,normalForm_surjective n⟩

theorem weightRootQuotient_card (n : ℕ) : Nat.card (WeightRootQuotient n)=4 := by
  rw [← Nat.card_congr (normalFormEquiv n)]
  simp

end Atlas.Chevalley.Integral.Minuscule.TypeD
