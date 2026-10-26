import Atlas.LinearGroups.ReeF4.SpecialIsotropy
import Atlas.LinearGroups.ReeF4.SpecialAdjacency

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Intrinsic special projective points lie on the actual Albert quadratic cone. -/
theorem specialPoint_rep_quadratic_zero (m : ℕ) (p : SpecialPoints (F := F) m) :
    traceZeroQuadratic p.val.rep = 0 :=
  p.property.quadratic_zero

/-- Includes the zero scalar, without pretending zero is a special vector. -/
theorem IsSpecialVector.quadratic_smul_zero {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (a : F) : traceZeroQuadratic (a • u) = 0 := by
  by_cases ha : a = 0
  · subst a
    simp [traceZeroQuadratic,quadraticTrace,SplitOctonion.norm]
  · exact (hu.smul_intrinsic a ha).quadratic_zero

/-- Admissible pairs of special vectors span a totally singular two-space
(or a smaller subspace when the vectors are dependent). -/
theorem special_pair_combination_quadratic_zero {m : ℕ} {u v : TraceZero F}
    (hu : IsSpecialVector m u) (hv : IsSpecialVector m v)
    (huv : StarDomain u v) (a b : F) :
    traceZeroQuadratic (a • u + b • v) = 0 := by
  have hd := starDomain_smul_right b (starDomain_smul_left a huv)
  have hp := traceZeroPolar_quadratic (a • u) (b • v)
  rw [hd.1,hu.quadratic_smul_zero,hv.quadratic_smul_zero,sub_zero,sub_zero] at hp
  exact hp.symm

theorem special_pair_span_quadratic_zero {m : ℕ} {u v : TraceZero F}
    (hu : IsSpecialVector m u) (hv : IsSpecialVector m v)
    (huv : StarDomain u v) (w : TraceZero F)
    (hw : w ∈ Submodule.span F {u,v}) : traceZeroQuadratic w = 0 := by
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hw
  rw [←he]
  exact special_pair_combination_quadratic_zero hu hv huv a b

/-- This establishes singularity of the span; it does not assert that all
its nonzero vectors are special, or that it is a line of the Ree geometry. -/
theorem specialAdjacent_span_quadratic_zero {m : ℕ}
    {p q : SpecialPoints (F := F) m} (hpq : SpecialAdjacent m p q)
    (w : TraceZero F) (hw : w ∈ Submodule.span F {p.val.rep,q.val.rep}) :
    traceZeroQuadratic w = 0 := by
  obtain ⟨hd,_⟩ := hpq.2
  exact special_pair_span_quadratic_zero p.property q.property hd w hw
end Atlas.ReeF4
