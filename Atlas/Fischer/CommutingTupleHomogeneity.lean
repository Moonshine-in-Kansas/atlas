import Atlas.Fischer.CommutingTupleNormalization
import Atlas.Fischer.GeneratedFrameMathieuFull
import Atlas.Mathieu.Mathieu24FiveTransitive

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem generated_basic_permutation (m : Mathieu24CodeModel) :
    ∃ g : rootGeneratedRayGroup, ∀ i : Omega,
      g * distinguishedRootElement (.inl i) * g⁻¹ = distinguishedRootElement (.inl (m.val i)) := by
  have hm : m ∈ generatedFrameMathieuImage := by rw [generatedFrameMathieuImage_eq_top]; trivial
  obtain ⟨e,he,hme⟩ := hm
  let g : rootGeneratedRayGroup := ⟨semilinearDisplayedRayAction e.val,he⟩
  refine ⟨g, fun i => ?_⟩
  apply distinguishedRootElement_conjugation
  apply Subtype.ext
  change (semilinearDisplayedRayAction e.val (displayedRayOfParameter (.inl i))).val = _
  rw [semilinearDisplayedRayAction_parameter_value]
  change rootRay (e.val.val (basicAxis i)) = rootRay (basicAxis (m.val i))
  have hh := basicFrameCoordinate_ray e i
  change rootRay (e.val.val (basicAxis i)) = rootRay (basicAxis ((basicFrameCoordinateHom e).val i)) at hh
  rw [hme] at hh
  exact hh

/-- Ordered commuting distinguished tuples of every length at most five are
conjugate in the actual generated group. -/
theorem commutingTuples_homogeneous {s : ℕ} (hs : s ≤ 5)
    (t u : Fin s ↪ rootGeneratedRayGroup)
    (ht : ∀ k, t k ∈ Set.range distinguishedRootElement)
    (hu : ∀ k, u k ∈ Set.range distinguishedRootElement)
    (hct : ∀ k l, Commute (t k) (t l))
    (hcu : ∀ k l, Commute (u k) (u l)) :
    ∃ g : rootGeneratedRayGroup, ∀ k, g * t k * g⁻¹ = u k := by
  obtain ⟨g,a,hg⟩ := commutingTuple_into_standard t ht hct
  obtain ⟨h,b,hh⟩ := commutingTuple_into_standard u hu hcu
  haveI := mathieu24_five_transitive
  haveI : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega s :=
    MulAction.isMultiplyPretransitive_of_le hs (by
      rw [Nat.card_eq_fintype_card]; decide)
  obtain ⟨m,hm⟩ := MulAction.isMultiplyPretransitive_iff.mp
    (inferInstance : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega s) a b
  obtain ⟨q,hq⟩ := generated_basic_permutation m
  refine ⟨h⁻¹*q*g,fun k => ?_⟩
  have hmk : m.val (a k)=b k := by
    exact congrArg (fun f : Fin s ↪ Omega => f k) hm
  have h1 : q * (g * t k * g⁻¹) * q⁻¹ = h * u k * h⁻¹ := by
    rw [hg k,hq,hmk,hh k]
  calc
    (h⁻¹*q*g) * t k * (h⁻¹*q*g)⁻¹ = h⁻¹ * (q*(g*t k*g⁻¹)*q⁻¹) * h := by group
    _ = u k := by rw [h1]; group

end Atlas.Fischer
