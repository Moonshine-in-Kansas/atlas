import Atlas.LinearGroups.Unitary.GenerationThreeComplete
import Atlas.FieldTheory.FiniteQuadraticCounts

/-! The full actual three-dimensional root subgroup: parameter bijection,
order q³, and the exact trace-zero center, uniformly in every characteristic. -/
noncomputable section
set_option maxHeartbeats 400000
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

variable (hdeg : Module.finrank F K = 2) (a b : K)
variable (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)

/-- The actual subgroup of standard SU₃ matrices parametrized by the full
upper unipotent group in the proved Witt basis. -/
def threeRootGroup : Subgroup (SU F K 3 hdeg) where
  carrier := {g | ∃ c d, ∃ hcd : rootThreeCondition (F := F) c d,
    g = rootThreeUnitary hdeg a b ha hb c d hcd}
  one_mem' := by
    have hz : rootThreeCondition (F := F) (0 : K) 0 := by simp [rootThreeCondition]
    refine ⟨0,0,hz, ?_⟩
    apply threeWittHom_injective hdeg a b ha
    rw [map_one, threeWittHom_root, rootThreeMatrix_zero]
  mul_mem' := by
    rintro g h ⟨c,d,hcd,rfl⟩ ⟨e,f,hef,rfl⟩
    exact ⟨c+e,d+f-conjugation F K c*e,rootThreeCondition_mul hdeg c d e f hcd hef,
      rootThreeUnitary_mul hdeg a b ha hb c d e f hcd hef⟩
  inv_mem' := by
    rintro g ⟨c,d,hcd,rfl⟩
    refine ⟨-c,-d-c*conjugation F K c,rootThreeCondition_inverse hdeg c d hcd, ?_⟩
    apply mul_left_cancel (a := rootThreeUnitary hdeg a b ha hb c d hcd)
    rw [mul_inv_cancel]
    symm
    apply threeWittHom_injective hdeg a b ha
    rw [map_mul, map_one, threeWittHom_root, threeWittHom_root]
    exact rootThreeMatrix_inverse c d

def threeRootElement (c d : K) (hcd : rootThreeCondition (F := F) c d) :
    threeRootGroup hdeg a b ha hb :=
  ⟨rootThreeUnitary hdeg a b ha hb c d hcd, c,d,hcd,rfl⟩

private theorem threeRootElement_parameters {c d e f : K}
    (hcd : rootThreeCondition (F := F) c d) (hef : rootThreeCondition (F := F) e f)
    (he : threeRootElement hdeg a b ha hb c d hcd = threeRootElement hdeg a b ha hb e f hef) :
    (c,d) = (e,f) := by
  apply rootThreeMatrix_injective (F := F)
  have h := congrArg (fun g : threeRootGroup hdeg a b ha hb =>
    threeWittHom hdeg a b ha g.val) he
  simpa only [threeRootElement, threeWittHom_root] using h

/-- Unique two-parameter normal form, with the genuine trace constraint. -/
def threeRootParameterEquiv : {p : K × K // rootThreeCondition (F := F) p.1 p.2} ≃
    threeRootGroup hdeg a b ha hb :=
  Equiv.ofBijective (fun p => threeRootElement hdeg a b ha hb p.val.1 p.val.2 p.prop) (by
    constructor
    · intro p q he
      exact Subtype.ext (threeRootElement_parameters hdeg a b ha hb p.prop q.prop he)
    · rintro ⟨g,c,d,hcd,rfl⟩
      exact ⟨⟨(c,d),hcd⟩,rfl⟩)

theorem rootThreeCondition_iff_trace (hdeg : Module.finrank F K = 2) (c d : K) :
    rootThreeCondition (F := F) c d ↔ trace F K d = -norm F K c := by
  constructor
  · intro h
    apply (algebraMap F K).injective
    rw [trace_formula hdeg, map_neg, norm_formula hdeg]
    dsimp [rootThreeCondition] at h
    linear_combination h
  · intro h
    have he := congrArg (algebraMap F K) h
    rw [trace_formula hdeg, map_neg, norm_formula hdeg] at he
    dsimp [rootThreeCondition]
    linear_combination he

theorem card_threeRootGroup : Nat.card (threeRootGroup hdeg a b ha hb) = Nat.card F ^ 3 := by
  letI := Fintype.ofFinite K
  rw [← Nat.card_congr (threeRootParameterEquiv hdeg a b ha hb),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (rootThreeCondition (F := F))), Nat.card_sigma]
  have hf (c : K) : Nat.card {d : K // rootThreeCondition (F := F) c d} = Nat.card F := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (rootThreeCondition_iff_trace hdeg c))]
    exact trace_fiber_card hdeg (-norm F K c)
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [card_extension hdeg]
  ring

/-- A root element is central precisely when its first parameter vanishes. -/
theorem threeRootElement_mem_center_iff (c d : K) (hcd : rootThreeCondition (F := F) c d) :
    threeRootElement hdeg a b ha hb c d hcd ∈
      Subgroup.center (threeRootGroup hdeg a b ha hb) ↔ c = 0 := by
  constructor
  · intro hc
    have hrel (e : K) : conjugation F K c * e = conjugation F K e * c := by
      obtain ⟨f,hef⟩ := exists_rootThree_parameter hdeg e
      have he := (Subgroup.mem_center_iff.mp hc) (threeRootElement hdeg a b ha hb e f hef)
      have hm := congrArg (fun g : threeRootGroup hdeg a b ha hb =>
        threeWittHom hdeg a b ha g.val) he
      change threeWittHom hdeg a b ha
        (rootThreeUnitary hdeg a b ha hb e f hef * rootThreeUnitary hdeg a b ha hb c d hcd) =
        threeWittHom hdeg a b ha
        (rootThreeUnitary hdeg a b ha hb c d hcd * rootThreeUnitary hdeg a b ha hb e f hef) at hm
      simp only [map_mul, threeWittHom_root, rootThreeMatrix_mul] at hm
      have hx := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hm
      change f+d-conjugation F K e*c = d+f-conjugation F K c*e at hx
      linear_combination hx
    have hfixc : conjugation F K c = c := by simpa using hrel 1
    by_contra hne
    apply conjugation_ne_one hdeg
    apply AlgEquiv.ext
    intro e
    change conjugation F K e = e
    apply mul_right_cancel₀ hne
    have he := hrel e
    rw [hfixc] at he
    linear_combination -he
  · rintro rfl
    rw [Subgroup.mem_center_iff]
    rintro ⟨g,e,f,hef,rfl⟩
    apply Subtype.ext
    apply threeWittHom_injective hdeg a b ha
    change threeWittHom hdeg a b ha
      (rootThreeUnitary hdeg a b ha hb e f hef * rootThreeUnitary hdeg a b ha hb 0 d hcd) =
      threeWittHom hdeg a b ha
      (rootThreeUnitary hdeg a b ha hb 0 d hcd * rootThreeUnitary hdeg a b ha hb e f hef)
    simp only [map_mul, threeWittHom_root]
    exact (rootThreeMatrix_center_commutes e f d).symm

/-- Exact center description inside the actual root subgroup, with the
trace-zero parameter condition visible. -/
theorem threeRootGroup_center_iff (g : threeRootGroup hdeg a b ha hb) :
    g ∈ Subgroup.center (threeRootGroup hdeg a b ha hb) ↔
      ∃ d : K, d + conjugation F K d = 0 ∧
        threeWittHom hdeg a b ha g.val = rootThreeMatrix (F := F) 0 d := by
  obtain ⟨g,c,d,hcd,rfl⟩ := g
  change threeRootElement hdeg a b ha hb c d hcd ∈ _ ↔ _
  rw [threeRootElement_mem_center_iff]
  constructor
  · rintro rfl
    refine ⟨d, ?_, threeWittHom_root hdeg a b ha hb 0 d hcd⟩
    simpa [rootThreeCondition] using hcd
  · rintro ⟨z,hz,he⟩
    have he' : rootThreeMatrix (F := F) c d = rootThreeMatrix (F := F) 0 z := by
      simpa only [threeRootElement, threeWittHom_root] using he
    have hp : (c,d) = ((0 : K),z) := by
      apply rootThreeMatrix_injective (F := F)
      exact he'
    exact congrArg Prod.fst hp
end Atlas.Unitary
