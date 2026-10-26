import Atlas.Sporadic.Janko1.Relations
import Atlas.Sporadic.Janko1.WordRelations
import Atlas.GroupTheory.FourGeneratorPerfect
import Atlas.GroupTheory.ConjugateProduct

/-! Perfectness of the actual octonion subgroup, independent of its order. -/
namespace Atlas.Janko1

def modelP : Model := ⟨P, P_mem⟩
def modelQ : Model := ⟨Q, Q_mem⟩
def modelR : Model := ⟨R, R_mem⟩
def modelS : Model := ⟨S, S_mem⟩

theorem model_generators : Subgroup.closure {modelP,modelQ,modelR,modelS} = ⊤ := by
  apply (Subgroup.map_injective generated.subtype_injective)
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change generated = (⊤ : Subgroup Model).map generated.subtype
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem conjugates_R_product :
    ((List.range 7).map (fun j => P^j * R * (P^j)⁻¹)).prod = 1 := by
  rw [GroupTheory.conjugate_product_formula, rp_pow, P_pow]
  simp

theorem isPerfect : Group.IsPerfect Model := by
  apply GroupTheory.four_generator_perfect modelP modelQ modelR modelS model_generators
  · apply Subtype.ext
    exact Q_mul_P
  · apply Subtype.ext
    exact rp_pow
  · apply Subtype.ext
    exact sr_pow
  · apply Subtype.ext
    exact pqsr_pow
  · apply Subtype.ext
    exact Q_pow
  · apply Subtype.ext
    exact R_pow
  · apply Subtype.ext
    exact S_pow

end Atlas.Janko1
