import Atlas.LinearGroups.Type2A
import Atlas.LinearGroups.Unitary.ProjectiveOrderChecks

/-! Small-parameter regressions for the same actual uniform construction. -/
noncomputable section
namespace Atlas.Unitary.OrderChecks

theorem psu_three_ternary_simple : IsSimpleGroup (PSU (ZMod 3) TernaryExtension 3 ternary_degree) :=
  simple_of_good ternary_degree (by norm_num [Good, Nat.card_zmod])

theorem psu_four_binary_simple : IsSimpleGroup (PSU (ZMod 2) BinaryExtension 4 binary_degree) :=
  simple_of_good binary_degree (by norm_num [Good, Nat.card_zmod])

theorem psu_four_ternary_simple : IsSimpleGroup (PSU (ZMod 3) TernaryExtension 4 ternary_degree) :=
  simple_of_good ternary_degree (by norm_num [Good, Nat.card_zmod])

theorem psu_five_binary_simple : IsSimpleGroup (PSU (ZMod 2) BinaryExtension 5 binary_degree) :=
  simple_of_good binary_degree (by norm_num [Good, Nat.card_zmod])

theorem psu_two_binary_not_simple : ¬ IsSimpleGroup (PSU (ZMod 2) BinaryExtension 2 binary_degree) :=
  Atlas.Unitary.psu_two_binary_not_simple binary_degree (by simp)

theorem psu_two_ternary_not_simple : ¬ IsSimpleGroup (PSU (ZMod 3) TernaryExtension 2 ternary_degree) :=
  Atlas.Unitary.psu_two_ternary_not_simple ternary_degree (by simp)

theorem psu_three_binary_not_simple : ¬ IsSimpleGroup (PSU (ZMod 2) BinaryExtension 3 binary_degree) :=
  projective_three_binary_not_simple binary_degree (by simp)

theorem points_three_ternary : Nat.card (IsotropicPoints (ZMod 3) TernaryExtension 3) = 28 := by
  rw [card_isotropicPoints_dim_three ternary_degree]
  norm_num

theorem points_four_binary : Nat.card (IsotropicPoints (ZMod 2) BinaryExtension 4) = 45 := by
  rw [card_isotropicPoints binary_degree 3]
  norm_num [orderFactor]

/-- The q=4 rank-one check is an actual prime-power construction witness. -/
theorem psu_two_quaternary_regression :
    ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K)
      (_ : Algebra F K) (hdeg : Module.finrank F K = 2),
      Nat.card F = 4 ∧ Nat.card (PSU F K 2 hdeg) = 60 ∧
      IsSimpleGroup (PSU F K 2 hdeg) ∧ ¬ IsMulCommutative (PSU F K 2 hdeg) := by
  obtain ⟨F,K,iF,iK,fF,fK,a,hdeg,hF,hK,h⟩ :=
    Atlas.type2A_prime_power 2 2 2 (by decide) (by decide) (by decide) (by norm_num [Good])
  letI := iF
  letI := iK
  letI := fF
  letI := fK
  letI := a
  refine ⟨F,K,iF,iK,fF,fK,a,hdeg,by simpa using hF, ?_,h.simple,h.nonabelian⟩
  rw [h.order,hF]
  norm_num [orderFactor]
end Atlas.Unitary.OrderChecks
