import Atlas.Fischer.FischerDistinguishedPositiveCentralizers

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual even section, obtained from the original centralizer quotient. -/
def distinguishedEvenSection (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i)) :
    distinguishedCentralizer d →* distinguishedPositiveCentralizer d :=
  (distinguishedResiduePositiveEquiv d i g h).toMonoidHom.comp
    (QuotientGroup.mk' (distinguishedCentralKernel d))

theorem distinguishedEvenSection_conjugate (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (x : distinguishedCentralizer d) :
    g*(distinguishedEvenSection d i g h x).val.val*g⁻¹=
      (firstCentralizerEvenPart i (distinguishedCentralizerTransport d i g h x)).val.val := by
  change ((distinguishedEvenKernelTransport d i g h)
    ((distinguishedEvenKernelTransport d i g h).symm
      (firstCentralizerEvenPart i (distinguishedCentralizerTransport d i g h x)))).val.val = _
  rw [MulEquiv.apply_symm_apply]

theorem distinguishedEvenSection_even (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (x : distinguishedCentralizer d) (hx : distinguishedCentralizerParity d x=1) :
    (distinguishedEvenSection d i g h x).val.val=x.val := by
  apply (MulAut.conj g).injective
  change g*(distinguishedEvenSection d i g h x).val.val*g⁻¹=g*x.val*g⁻¹
  rw [distinguishedEvenSection_conjugate]
  let y : (firstCentralizerParity i).ker :=
    ⟨distinguishedCentralizerTransport d i g h x,by
      change firstCentralizerParity i (distinguishedCentralizerTransport d i g h x)=1
      rw [distinguishedCentralizerTransport_parity]; exact hx⟩
  exact congrArg (fun z : (firstCentralizerParity i).ker => z.val.val)
    (firstCentralizerEvenPart_even i y)

/-- For every odd centralizing e, the section is literally d e in the original group. -/
theorem distinguishedEvenSection_odd (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (x : distinguishedCentralizer d)
    (hx : distinguishedCentralizerParity d x=Multiplicative.ofAdd (1 : Bit)) :
    (distinguishedEvenSection d i g h x).val.val=d*x.val := by
  apply (MulAut.conj g).injective
  change g*(distinguishedEvenSection d i g h x).val.val*g⁻¹=g*(d*x.val)*g⁻¹
  rw [distinguishedEvenSection_conjugate]
  have ho := congrArg (fun z : residueCentralizer {i} => z.val)
    (firstCentralizerEvenPart_odd i (distinguishedCentralizerTransport d i g h x)
      (by rw [distinguishedCentralizerTransport_parity]; exact hx))
  rw [ho]
  change distinguishedRootElement (.inl i)*(g*x.val*g⁻¹)=g*(d*x.val)*g⁻¹
  rw [← h]
  group

/-- The even section has precisely the original conjugation action on all commuting points. -/
theorem distinguishedEvenSection_action (d : rootGeneratedRayGroup) (i : Omega)
    (g : rootGeneratedRayGroup) (h : g*d*g⁻¹=distinguishedRootElement (.inl i))
    (x : distinguishedCentralizer d) (y : rootGeneratedRayGroup) (hy : Commute d y) :
    (distinguishedEvenSection d i g h x).val.val*y*(distinguishedEvenSection d i g h x).val.val⁻¹=
      x.val*y*x.val⁻¹ := by
  have hp : distinguishedCentralizerParity d x=1 ∨
      distinguishedCentralizerParity d x=Multiplicative.ofAdd (1 : Bit) := by
    obtain ⟨b,hb⟩ := (Multiplicative.ofAdd : Bit ≃ Multiplicative Bit).surjective
      (distinguishedCentralizerParity d x)
    fin_cases b
    · exact Or.inl hb.symm
    · exact Or.inr hb.symm
  rcases hp with hp|hp
  · rw [distinguishedEvenSection_even d i g h x hp]
  · rw [distinguishedEvenSection_odd d i g h x hp]
    have hx : d*x.val=x.val*d := x.prop d (Set.mem_singleton d)
    rw [hx]
    calc
      (x.val*d)*y*(x.val*d)⁻¹=x.val*(d*y*d⁻¹)*x.val⁻¹ := by group
      _ = x.val*y*x.val⁻¹ := by rw [hy.eq]; group

end Atlas.Fischer
