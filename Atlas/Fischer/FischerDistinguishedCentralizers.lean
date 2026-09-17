import Atlas.Fischer.FischerFirstCentralizer
import Atlas.Fischer.FischerDoubleCoverTransport
import Atlas.Fischer.CommutingTupleHomogeneity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private def actualCentralizerTransport {A B : Set rootGeneratedRayGroup}
    (e : MulAut rootGeneratedRayGroup) (h : e '' A = B) :
    Subgroup.centralizer A ≃* Subgroup.centralizer B where
  toFun x := ⟨e x.val, by
    rintro y hy
    rw [← h] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [map_mul] using congrArg e (x.prop z hz)⟩
  invFun x := ⟨e.symm x.val, by
    intro y hy
    have hh := x.prop (e y) (h ▸ Set.mem_image_of_mem e hy)
    simpa only [map_mul,e.symm_apply_apply] using congrArg e.symm hh⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

/-- The literal centralizer of any distinguished involution, without a coordinate restriction. -/
abbrev distinguishedCentralizer (d : rootGeneratedRayGroup) :=
  Subgroup.centralizer ({d} : Set rootGeneratedRayGroup)

/-- The literal centralizer of an ordered commuting pair. -/
abbrev distinguishedPairCentralizer (d e : rootGeneratedRayGroup) :=
  Subgroup.centralizer ({d,e} : Set rootGeneratedRayGroup)

/-- Conjugation, with its actual underlying map, identifies arbitrary centralizers. -/
def distinguishedCentralizerTransport (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    distinguishedCentralizer d ≃* residueCentralizer {i} :=
  actualCentralizerTransport (MulAut.conj g) (by
    change (MulAut.conj g) '' {d}=residueBasicSet {i}
    ext x
    simp [residueBasicSet,MulAut.conj_apply,h])

theorem distinguishedCentralizerTransport_val (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (x : distinguishedCentralizer d) :
    (distinguishedCentralizerTransport d i g h x).val=g*x.val*g⁻¹ := rfl

/-- Every original distinguished element can be transported to any marked basic element. -/
theorem distinguished_conjugate_basic (d : rootGeneratedRayGroup)
    (hd : d ∈ Set.range distinguishedRootElement) (i : Omega) :
    ∃ g : rootGeneratedRayGroup, g*d*g⁻¹=distinguishedRootElement (.inl i) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ((distinguishedRootClass_isConj_iff (.inl i) d).mp hd).symm
  exact ⟨g,hg⟩

/-- Actual ordered pair transport does not interchange the factor subsequently killed. -/
def distinguishedPairCentralizerTransport (d e : rootGeneratedRayGroup) (i j : Omega)
    (g : rootGeneratedRayGroup)
    (hd : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (he : g*e*g⁻¹=distinguishedRootElement (.inl j)) :
    distinguishedPairCentralizer d e ≃* residueCentralizer {i,j} :=
  actualCentralizerTransport (MulAut.conj g) (by
    change (MulAut.conj g) '' {d,e}=residueBasicSet {i,j}
    ext x
    simp [residueBasicSet,MulAut.conj_apply,hd,he])

theorem distinguishedPairCentralizerTransport_val (d e : rootGeneratedRayGroup) (i j : Omega)
    (g : rootGeneratedRayGroup)
    (hd : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (he : g*e*g⁻¹=distinguishedRootElement (.inl j))
    (x : distinguishedPairCentralizer d e) :
    (distinguishedPairCentralizerTransport d e i j g hd he x).val=g*x.val*g⁻¹ := rfl

/-- Every ordered commuting distinct pair admits simultaneous basic coordinates. -/
theorem distinguished_pair_into_basic (d e : rootGeneratedRayGroup)
    (hd : d ∈ Set.range distinguishedRootElement)
    (he : e ∈ Set.range distinguishedRootElement) (hne : d≠e) (hc : Commute d e) :
    ∃ (g : rootGeneratedRayGroup) (i j : Omega), i≠j ∧
      g*d*g⁻¹=distinguishedRootElement (.inl i) ∧
      g*e*g⁻¹=distinguishedRootElement (.inl j) := by
  let t : Fin 2 ↪ rootGeneratedRayGroup :=
    ⟨![d,e],by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all⟩
  have ht : ∀ k, t k ∈ Set.range distinguishedRootElement := by
    intro k
    fin_cases k <;> assumption
  have hct : ∀ k l, Commute (t k) (t l) := by
    intro k l
    fin_cases k <;> fin_cases l
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  obtain ⟨g,a,hg⟩ := commutingTuple_into_standard t ht hct
  exact ⟨g,a 0,a 1,fun h => by have := a.injective h; simpa using this,hg 0,hg 1⟩

end Atlas.Fischer
