import Atlas.Fischer.FischerDistinguishedQuotients

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The literal centralizer inside the actual positive ray group. -/
def distinguishedPositiveCentralizer (d : rootGeneratedRayGroup) : Subgroup rootGeneratedRayParity.ker :=
  (distinguishedCentralizer d).comap rootGeneratedRayParity.ker.subtype

def distinguishedCentralizerParity (d : rootGeneratedRayGroup) : distinguishedCentralizer d →* Multiplicative Bit :=
  rootGeneratedRayParity.comp (distinguishedCentralizer d).subtype

def distinguishedEvenCentralizerEquiv (d : rootGeneratedRayGroup) :
    (distinguishedCentralizerParity d).ker ≃* distinguishedPositiveCentralizer d where
  toFun x := ⟨⟨x.val.val,x.prop⟩,x.val.prop⟩
  invFun x := ⟨⟨x.val.val,x.prop⟩,x.val.prop⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

theorem distinguishedCentralizerTransport_parity (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (x : distinguishedCentralizer d) :
    firstCentralizerParity i (distinguishedCentralizerTransport d i g h x)=
      distinguishedCentralizerParity d x := by
  change rootGeneratedRayParity (g*x.val*g⁻¹)=rootGeneratedRayParity x.val
  simp only [map_mul,map_inv]
  rw [mul_comm (rootGeneratedRayParity g),mul_assoc,mul_inv_cancel,mul_one]

theorem distinguishedEvenKernel_transport (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    (distinguishedCentralizerParity d).ker.map
      (distinguishedCentralizerTransport d i g h).toMonoidHom=(firstCentralizerParity i).ker := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change firstCentralizerParity i (distinguishedCentralizerTransport d i g h x)=1
    rw [distinguishedCentralizerTransport_parity]
    exact hx
  · intro hy
    refine ⟨(distinguishedCentralizerTransport d i g h).symm y,?_,
      (distinguishedCentralizerTransport d i g h).apply_symm_apply y⟩
    change distinguishedCentralizerParity d ((distinguishedCentralizerTransport d i g h).symm y)=1
    rw [← distinguishedCentralizerTransport_parity d i g h,
      MulEquiv.apply_symm_apply]
    exact hy

def distinguishedEvenKernelTransport (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    (distinguishedCentralizerParity d).ker ≃* (firstCentralizerParity i).ker :=
  ((distinguishedCentralizerParity d).ker.equivMapOfInjective
    (distinguishedCentralizerTransport d i g h).toMonoidHom
    (distinguishedCentralizerTransport d i g h).injective).trans
    (MulEquiv.subgroupCongr (distinguishedEvenKernel_transport d i g h))

def distinguishedCentralKernelTransport (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    distinguishedCentralKernel d ≃* residueCentralElementary {i} :=
  ((distinguishedCentralKernel d).equivMapOfInjective
    (distinguishedCentralizerTransport d i g h).toMonoidHom
    (distinguishedCentralizerTransport d i g h).injective).trans
    (MulEquiv.subgroupCongr (distinguishedCentralKernel_transport d i g h))

/-- The actual arbitrary first centralizer splits as its marked cyclic factor and its even centralizer. -/
def distinguishedCentralizerDirectProduct (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    distinguishedCentralizer d ≃* distinguishedCentralKernel d × distinguishedPositiveCentralizer d :=
  (distinguishedCentralizerTransport d i g h).trans
    ((firstCentralizerProductEquiv i).symm.trans
      (MulEquiv.prodCongr (distinguishedCentralKernelTransport d i g h).symm
        ((distinguishedEvenKernelTransport d i g h).symm.trans (distinguishedEvenCentralizerEquiv d))))

/-- The singleton quotient identifies with the literal centralizer in the positive group. -/
def distinguishedResiduePositiveEquiv (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    DistinguishedResidue d ≃* distinguishedPositiveCentralizer d :=
  (distinguishedResidueTransport d i g h).trans ((firstResidueEvenEquiv i).trans
    ((distinguishedEvenKernelTransport d i g h).symm.trans (distinguishedEvenCentralizerEquiv d)))

/-- Both first-centralizer identifications hold for every original distinguished involution. -/
theorem distinguishedCentralizer_structure (d : rootGeneratedRayGroup)
    (hd : d ∈ Set.range distinguishedRootElement) (i : Omega) :
    Nonempty (distinguishedCentralizer d ≃* distinguishedCentralKernel d × distinguishedPositiveCentralizer d) ∧
    Nonempty (distinguishedPositiveCentralizer d ≃* ResidueGroup {i}) := by
  obtain ⟨g,hg⟩ := distinguished_conjugate_basic d hd i
  exact ⟨⟨distinguishedCentralizerDirectProduct d i g hg⟩,
    ⟨(distinguishedResiduePositiveEquiv d i g hg).symm.trans (distinguishedResidueTransport d i g hg)⟩⟩

end Atlas.Fischer
