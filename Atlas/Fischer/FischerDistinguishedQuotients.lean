import Atlas.Fischer.FischerDistinguishedCentralizers

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual cyclic subgroup killed in an arbitrary first centralizer. -/
def distinguishedCentralKernel (d : rootGeneratedRayGroup) : Subgroup (distinguishedCentralizer d) :=
  (Subgroup.closure {d}).subgroupOf (distinguishedCentralizer d)

/-- Only the ordered first factor is killed in the arbitrary double centralizer. -/
def distinguishedPairFirstKernel (d e : rootGeneratedRayGroup) : Subgroup (distinguishedPairCentralizer d e) :=
  (Subgroup.closure {d}).subgroupOf (distinguishedPairCentralizer d e)

private theorem closure_factor_central {d : rootGeneratedRayGroup} {A : Set rootGeneratedRayGroup}
    (hd : d∈A) : (Subgroup.closure {d}).subgroupOf (Subgroup.centralizer A) ≤
      Subgroup.center (Subgroup.centralizer A) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hg : g.val ∈ Subgroup.centralizer ({d} : Set rootGeneratedRayGroup) := by
    intro y hy
    have he : y=d := hy
    subst y
    exact g.prop d hd
  exact Subgroup.closure_le_centralizer_centralizer ({d} : Set rootGeneratedRayGroup) hx g.val hg

instance distinguishedCentralKernel_normal (d : rootGeneratedRayGroup) :
    (distinguishedCentralKernel d).Normal where
  conj_mem x hx g := by
    have hc := Subgroup.mem_center_iff.mp (closure_factor_central (Set.mem_singleton d) hx) g
    have hh : g*x*g⁻¹=x := by rw [hc]; group
    rw [hh]
    exact hx

instance distinguishedPairFirstKernel_normal (d e : rootGeneratedRayGroup) :
    (distinguishedPairFirstKernel d e).Normal where
  conj_mem x hx g := by
    have hc := Subgroup.mem_center_iff.mp (closure_factor_central (Set.mem_insert d {e}) hx) g
    have hh : g*x*g⁻¹=x := by rw [hc]; group
    rw [hh]
    exact hx

abbrev DistinguishedResidue (d : rootGeneratedRayGroup) :=
  distinguishedCentralizer d ⧸ distinguishedCentralKernel d

abbrev DistinguishedDoubleCover (d e : rootGeneratedRayGroup) :=
  distinguishedPairCentralizer d e ⧸ distinguishedPairFirstKernel d e

private theorem closure_conj_singleton (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    (Subgroup.closure {d}).map (MulAut.conj g).toMonoidHom=residueElementary {i} := by
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  simp [residueBasicSet,MulAut.conj_apply,h]

theorem distinguishedCentralKernel_transport (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    (distinguishedCentralKernel d).map (distinguishedCentralizerTransport d i g h).toMonoidHom=
      residueCentralElementary {i} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change g*x.val*g⁻¹ ∈ residueElementary {i}
    rw [← closure_conj_singleton d i g h]
    exact ⟨x.val,hx,rfl⟩
  · intro hy
    have hh : y.val ∈ (Subgroup.closure {d}).map (MulAut.conj g).toMonoidHom := by
      rw [closure_conj_singleton d i g h]
      exact hy
    obtain ⟨z,hz,hzy⟩ := hh
    refine ⟨(distinguishedCentralizerTransport d i g h).symm y,?_,
      (distinguishedCentralizerTransport d i g h).apply_symm_apply y⟩
    change (MulAut.conj g).symm y.val ∈ Subgroup.closure {d}
    rw [← hzy]
    change (MulAut.conj g).symm ((MulAut.conj g) z) ∈ Subgroup.closure {d}
    rw [MulEquiv.symm_apply_apply]
    exact hz

def distinguishedResidueTransport (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    DistinguishedResidue d ≃* ResidueGroup {i} :=
  QuotientGroup.congr _ _ (distinguishedCentralizerTransport d i g h)
    (distinguishedCentralKernel_transport d i g h)

theorem distinguishedPairFirstKernel_transport (d e : rootGeneratedRayGroup) (i j : Omega)
    (g : rootGeneratedRayGroup)
    (hd : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (he : g*e*g⁻¹=distinguishedRootElement (.inl j)) :
    (distinguishedPairFirstKernel d e).map
      (distinguishedPairCentralizerTransport d e i j g hd he).toMonoidHom=
      doubleCentralizerFirstKernel i j := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change g*x.val*g⁻¹ ∈ residueElementary {i}
    rw [← closure_conj_singleton d i g hd]
    exact ⟨x.val,hx,rfl⟩
  · intro hy
    have hh : y.val ∈ (Subgroup.closure {d}).map (MulAut.conj g).toMonoidHom := by
      rw [closure_conj_singleton d i g hd]
      exact hy
    obtain ⟨z,hz,hzy⟩ := hh
    refine ⟨(distinguishedPairCentralizerTransport d e i j g hd he).symm y,?_,
      (distinguishedPairCentralizerTransport d e i j g hd he).apply_symm_apply y⟩
    change (MulAut.conj g).symm y.val ∈ Subgroup.closure {d}
    rw [← hzy]
    change (MulAut.conj g).symm ((MulAut.conj g) z) ∈ Subgroup.closure {d}
    rw [MulEquiv.symm_apply_apply]
    exact hz

/-- The arbitrary ordered double quotient is identified through actual conjugation. -/
def distinguishedDoubleCoverTransport (d e : rootGeneratedRayGroup) (i j : Omega)
    (g : rootGeneratedRayGroup)
    (hd : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (he : g*e*g⁻¹=distinguishedRootElement (.inl j)) :
    DistinguishedDoubleCover d e ≃* FischerDoubleCover i j :=
  QuotientGroup.congr _ _ (distinguishedPairCentralizerTransport d e i j g hd he)
    (distinguishedPairFirstKernel_transport d e i j g hd he)

/-- The arbitrary quotient identification sends each actual representative by the same conjugator. -/
theorem distinguishedDoubleCoverTransport_mk (d e : rootGeneratedRayGroup) (i j : Omega)
    (g : rootGeneratedRayGroup)
    (hd : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (he : g*e*g⁻¹=distinguishedRootElement (.inl j)) (x : distinguishedPairCentralizer d e) :
    distinguishedDoubleCoverTransport d e i j g hd he
      (QuotientGroup.mk' (distinguishedPairFirstKernel d e) x)=
      QuotientGroup.mk' (doubleCentralizerFirstKernel i j)
        (distinguishedPairCentralizerTransport d e i j g hd he x) := rfl

/-- Every actual ordered commuting distinct pair has the constructed double-cover model. -/
theorem distinguishedDoubleCover_structure (d e : rootGeneratedRayGroup)
    (hd : d ∈ Set.range distinguishedRootElement)
    (he : e ∈ Set.range distinguishedRootElement) (hne : d≠e) (hc : Commute d e) :
    ∃ i j : Omega, i≠j ∧ Nonempty (DistinguishedDoubleCover d e ≃* FischerDoubleCover i j) := by
  obtain ⟨g,i,j,hij,hdi,hej⟩ := distinguished_pair_into_basic d e hd he hne hc
  exact ⟨i,j,hij,⟨distinguishedDoubleCoverTransport d e i j g hdi hej⟩⟩

end Atlas.Fischer
