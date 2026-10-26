import Atlas.LinearGroups.ReeF4.SpecialElementaryUpperReduction

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every intrinsic special vector is reduced by an actual elementary word.
No count, stabilizer theorem, or equality E=Model is assumed. -/
theorem IsSpecialVector.elementary_reduces_to_lowest {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F} (hu : IsSpecialVector m u) :
    ElementaryReducesToLowest hcard u := by
  obtain ⟨r,hr,hn,hz⟩ := hu.exists_allowed_leading_root hcard
  fin_cases r <;> norm_num [allowedSpecialLeadingRoot,Fin.ext_iff] at hr
  · exact elementary_reduction_leading2 hcard ⟨hn,hz⟩
  · exact elementary_reduction_leading4 hcard hu ⟨hn,hz⟩
  · exact elementary_reduction_leading7 hcard hu ⟨hn,hz⟩
  · exact elementary_reduction_leading9 hcard hu ⟨hn,hz⟩
  · exact elementary_reduction_leading18 hcard ⟨hn,hz⟩
  · exact elementary_reduction_leading19 hcard hu ⟨hn,hz⟩
  · exact elementary_reduction_leading24 hcard hu ⟨hn,hz⟩
  · exact elementary_reduction_leading25 hcard hu ⟨hn,hz⟩
/-- Transitivity on actual nonzero special vectors by the displayed elementary
subgroup, without identifying it with the full stabilizer. -/
theorem elementary_specialVector_transitive {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u v : TraceZero F}
    (hu : IsSpecialVector m u) (hv : IsSpecialVector m v) :
    ∃ g : elementarySubgroup hcard, g.val.val u=v := by
  obtain ⟨a,ha,hea⟩ := hu.elementary_reduces_to_lowest hcard
  obtain ⟨b,hb,heb⟩ := hv.elementary_reduces_to_lowest hcard
  refine ⟨⟨b⁻¹*a,(elementarySubgroup hcard).mul_mem
    ((elementarySubgroup hcard).inv_mem hb) ha⟩,?_⟩
  apply b.val.injective
  change b.val (b.val.symm (a.val u))=b.val v
  rw [b.val.apply_symm_apply,hea,heb]
end Atlas.ReeF4

