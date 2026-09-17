import Atlas.Conway.OrthogonalOrbitDivisibility

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def leechVectorStabilizer (H : Subgroup LeechIsometryGroup) (v : leech) : Subgroup H :=
  (MulAction.stabilizer (leech ≃ₗ[ℤ] leech) v).comap
    (leechIsometries.subtype.comp H.subtype)

theorem leechVectorStabilizer_fixes (H : Subgroup LeechIsometryGroup) (v : leech)
    (g : leechVectorStabilizer H v) : g.val.val.val v = v := g.prop

theorem oddMinimumVector_zero (a : Omega) :
    (oddMinimumVector a 0).val = oddProfileBase {a} ∅ := by
  ext i
  simp [oddMinimumVector,signedOddProfile,signChange]

theorem odd_point_stabilizer_orbit_dvd (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup ≤ H) (a : Omega) (x : LeechShell 4)
    (hx : integerDot (oddProfileBase {a} ∅) x.val.val = 0) :
    23 ∣ Nat.card (MulAction.orbit (leechVectorStabilizer H (oddMinimumVector a 0)) x) := by
  obtain ⟨g,ha,_,hg⟩ := minimum_point_cycle_invariant_card a
  have hN : permutationEmbedding g ∈ monomialSubgroup := by
    refine ⟨SemidirectProduct.inr g,?_⟩
    exact congrArg (fun f => f g) monomial_inr
  have hfix : (permutationEmbedding g).val (oddMinimumVector a 0) = oddMinimumVector a 0 := by
    apply Subtype.ext
    change integerPermutation g.val (oddMinimumVector a 0).val = _
    rw [oddMinimumVector_zero,permutation_odd_singleton,ha]
  let k : leechVectorStabilizer H (oddMinimumVector a 0) :=
    ⟨⟨permutationEmbedding g,hH hN⟩,hfix⟩
  apply hg
  · intro y
    change k • y ∈ MulAction.orbit (leechVectorStabilizer H (oddMinimumVector a 0)) x ↔ _
    simp only [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨l,hl⟩
      exact ⟨k⁻¹*l,by rw [mul_smul,hl,inv_smul_smul]⟩
    · rintro ⟨l,hl⟩
      exact ⟨k*l,by rw [mul_smul,hl]⟩
  · intro y hy
    obtain ⟨l,rfl⟩ := MulAction.mem_orbit_iff.mp hy
    have he := l.val.val.prop (oddMinimumVector a 0) x.val
    rw [leechVectorStabilizer_fixes] at he
    rw [oddMinimumVector_zero] at he
    exact he.trans hx

end Atlas.Conway
