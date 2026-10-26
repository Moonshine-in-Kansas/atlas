import Atlas.Sporadic.Janko1.GeneratorChecks
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! The prescribed generators as actual automorphisms of the installed octonions.
The generated subgroup is the fixed candidate throughout the J₁ development. -/
namespace Atlas.Janko1

def generatorEquiv (g : Fin 4) : SplitOctonion.Carrier Field ≃ₗ[Field]
    SplitOctonion.Carrier Field :=
  LinearEquiv.ofLinearMap (generatorLinear g)
    ((generatorLinear g) ^ (generatorExponent g - 1))
    (by
      change generatorLinear g * generatorLinear g ^ (generatorExponent g - 1) = 1
      rw [← pow_succ']
      have hn : generatorExponent g - 1 + 1 = generatorExponent g := by fin_cases g <;> decide
      rw [hn, generatorLinear_pow])
    (by
      change generatorLinear g ^ (generatorExponent g - 1) * generatorLinear g = 1
      rw [← pow_succ]
      have hn : generatorExponent g - 1 + 1 = generatorExponent g := by fin_cases g <;> decide
      rw [hn, generatorLinear_pow])

def generator (g : Fin 4) : G2.Model Field :=
  ⟨generatorEquiv g, generatorLinear_mul g⟩

def P : G2.Model Field := generator 0
def Q : G2.Model Field := generator 1
def R : G2.Model Field := generator 2
def S : G2.Model Field := generator 3

def generated : Subgroup (G2.Model Field) := Subgroup.closure {P,Q,R,S}
abbrev Model := ↥generated

def H : Subgroup (G2.Model Field) := Subgroup.closure {P,Q,R}

theorem P_mem : P ∈ generated := Subgroup.subset_closure (by simp)
theorem Q_mem : Q ∈ generated := Subgroup.subset_closure (by simp)
theorem R_mem : R ∈ generated := Subgroup.subset_closure (by simp)
theorem S_mem : S ∈ generated := Subgroup.subset_closure (by simp)

theorem H_le_generated : H ≤ generated := by
  apply (Subgroup.closure_le generated).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact P_mem
  · exact Q_mem
  · exact R_mem

theorem generator_unit (g : Fin 4) : (generator g).val SplitOctonion.unit =
    SplitOctonion.unit := SplitOctonion.automorphism_unit _

theorem generator_norm (g : Fin 4) (x : SplitOctonion.Carrier Field) :
    SplitOctonion.norm ((generator g).val x) = SplitOctonion.norm x :=
  SplitOctonion.automorphism_norm _ _

theorem P_Q_ne : P*Q ≠ Q*P := by
  intro h
  have he := congrArg (fun g : G2.Model Field => g.val (imaginaryVector 0)) h
  have hn : (P*Q).val (imaginaryVector 0) ≠ (Q*P).val (imaginaryVector 0) := by decide
  exact hn he

theorem exists_mul_ne_mul : ∃ x y : Model, x*y ≠ y*x := by
  refine ⟨⟨P,P_mem⟩, ⟨Q,Q_mem⟩, ?_⟩
  intro h
  exact P_Q_ne (congrArg Subtype.val h)

end Atlas.Janko1
