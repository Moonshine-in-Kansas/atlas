import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2RootRelations
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2LoweringConjugation
import Atlas.LinearGroups.Chevalley.AdjointOddCartan
import Atlas.LinearGroups.Chevalley.ModelPerfectnessOdd

/-! Actual C2 adjoint perfectness in characteristic different
from two. It uses actual root/torus commutators and the certified C2 root
relations; no order, simplicity or external group identification is used. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open Group ClassicalData
open scoped commutatorElement
local instance c2PerfectRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance c2PerfectBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem c2_short_cartan_odd :
    Odd ((baseC 1).cartanMatrix (baseCIndexEquiv 1 0) (baseCIndexEquiv 1 1)) := by
  rw [baseC_cartan]
  decide

variable (K : Type*) [Field K]

theorem c2_Xshort_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    adjointX (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 0) t ∈
      commutator (Adjoint (pairingC 2) (baseC 1) K) :=
  adjointX_mem_commutator_of_odd_cartan (pairingC 2) (baseC 1) K hchar
    (baseCIndexEquiv 1 0) (baseCIndexEquiv 1 1) c2_short_cartan_odd t

theorem c2_Yshort_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    adjointY (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 0) t ∈
      commutator (Adjoint (pairingC 2) (baseC 1) K) :=
  adjointY_mem_commutator_of_odd_cartan (pairingC 2) (baseC 1) K hchar
    (baseCIndexEquiv 1 0) (baseCIndexEquiv 1 1) c2_short_cartan_odd t

/-- The coefficient -2 is inverted only here, never in the integral construction. -/
theorem c2_W_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    c2W t ∈ commutator (Adjoint (pairingC 2) (baseC 1) K) := by
  have htwo : (2 : K) ≠ 0 := by
    intro h
    apply hchar
    linear_combination -h
  have hp : (-2 : K) * 1 * (-t / 2) = t := by
    field_simp [htwo] <;> ring
  rw [← hp, ← c2_short_short_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem unconjugate_mem_normal {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (n x : G) (h : n * x * n⁻¹ ∈ H) : x ∈ H := by
  have hc := (inferInstance : H.Normal).conj_mem' _ h n
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc

/-- The second positive simple-root subgroup is conjugate to W. -/
theorem c2_Xlong_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    adjointX (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 1) t ∈
      commutator (Adjoint (pairingC 2) (baseC 1) K) :=
  unconjugate_mem_normal (commutator (Adjoint (pairingC 2) (baseC 1) K))
    (adjointWeyl (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 0) 1)
    (adjointX (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 1) t)
    (c2_W_mem_commutator K hchar t)

/-- The long negative generator is obtained by the actual long Weyl conjugation. -/
theorem c2_Ylong_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    adjointY (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 1) t ∈
      commutator (Adjoint (pairingC 2) (baseC 1) K) := by
  let H := commutator (Adjoint (pairingC 2) (baseC 1) K)
  have h := (inferInstance : H.Normal).conj_mem _
    (c2_Xlong_mem_commutator K hchar (-t))
    (adjointWeyl (pairingC 2) (baseC 1) K (baseCIndexEquiv 1 1) 1)
  simpa only [c2_weyl_long_conjugate_X, neg_neg] using h

/-- Perfectness of the actual elementary C2 adjoint matrix group. -/
theorem c2_adjoint_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Adjoint (pairingC 2) (baseC 1) K) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply adjoint_induction (pairingC 2) (baseC 1) K ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨k,rfl⟩ := (baseCIndexEquiv 1).surjective i
    fin_cases k
    · exact c2_Xshort_mem_commutator K hchar t
    · exact c2_Xlong_mem_commutator K hchar t
  · intro i t
    obtain ⟨k,rfl⟩ := (baseCIndexEquiv 1).surjective i
    fin_cases k
    · exact c2_Yshort_mem_commutator K hchar t
    · exact c2_Ylong_mem_commutator K hchar t

/-- The missing ternary rank-two perfectness case, still on the same actual model. -/
theorem c2_adjoint_isPerfect_of_card_three [Fintype K] (hq : Fintype.card K = 3) :
    IsPerfect (Adjoint (pairingC 2) (baseC 1) K) :=
  c2_adjoint_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

end Atlas.Chevalley.Integral.RankTwo
