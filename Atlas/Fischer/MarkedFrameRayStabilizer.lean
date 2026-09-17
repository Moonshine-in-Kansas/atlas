import Atlas.Fischer.StandardFrameRayStabilizer
import Atlas.Fischer.ParkerMarkedStabilizers

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual subgroup fixing the standard frame setwise and the marked
basic tuple pointwise by conjugation. -/
def markedFrameRayStabilizer {k : ℕ} (e : Fin k ↪ Omega) : Subgroup rootGeneratedRayGroup :=
  standardFrameRayStabilizer ⊓ Subgroup.centralizer
    (Set.range (fun a : Fin k => distinguishedRootElement (.inl (e a))))

theorem parkerRayHom_mem_marked_iff {k : ℕ} (e : Fin k ↪ Omega) (h : ParkerStandardGroup) :
    parkerRayHom h ∈ markedFrameRayStabilizer e ↔ h ∈ parkerMarkedStabilizer e := by
  constructor
  · intro hh
    change ∀ x : Set.range e, (parkerStandardProjection h).val x.val=x.val
    rintro ⟨x,a,rfl⟩
    apply (parkerRayHom_commutes_basic_iff h (e a)).mp
    exact (hh.2 _ ⟨a,rfl⟩).symm
  · intro hh
    refine ⟨parkerRayHom_mem_frame h,?_⟩
    rintro _ ⟨a,rfl⟩
    have hc := (parkerRayHom_commutes_basic_iff h (e a)).mpr (hh ⟨e a,⟨a,rfl⟩⟩)
    exact hc.eq.symm

/-- Exact subgroup identification in the existing ray group, not an order
recognition argument. -/
theorem parkerMarkedStabilizer_ray_image {k : ℕ} (e : Fin k ↪ Omega) :
    (parkerMarkedStabilizer e).map parkerRayHom=markedFrameRayStabilizer e := by
  apply le_antisymm
  · rintro x ⟨h,hh,rfl⟩
    exact (parkerRayHom_mem_marked_iff e h).mpr hh
  · intro g hg
    have hm : g ∈ parkerRayHom.range := by rw [parkerRayHom_range]; exact hg.1
    obtain ⟨h,rfl⟩ := hm
    exact ⟨h,(parkerRayHom_mem_marked_iff e h).mp hg,rfl⟩

def parkerMarkedRayHom {k : ℕ} (e : Fin k ↪ Omega) :
    parkerMarkedStabilizer e →* markedFrameRayStabilizer e :=
  (parkerRayHom.comp (parkerMarkedStabilizer e).subtype).codRestrict
    (markedFrameRayStabilizer e) (fun h => (parkerRayHom_mem_marked_iff e h.val).mpr h.property)

def parkerMarkedFrameEquiv {k : ℕ} (e : Fin k ↪ Omega) :
    parkerMarkedStabilizer e ≃* markedFrameRayStabilizer e :=
  MulEquiv.ofBijective (parkerMarkedRayHom e) ⟨by
    intro h j he
    apply Subtype.ext
    exact parkerRayHom_injective (congrArg Subtype.val he),by
    intro g
    have hg : g.val ∈ (parkerMarkedStabilizer e).map parkerRayHom := by
      rw [parkerMarkedStabilizer_ray_image]
      exact g.property
    obtain ⟨h,hh,hg⟩ := hg
    exact ⟨⟨h,hh⟩,Subtype.ext hg⟩⟩

theorem markedFrameRayStabilizer_order {k : ℕ} (e : Fin k ↪ Omega) :
    Nat.card (markedFrameRayStabilizer e)=4096*Nat.card (orderedPointStabilizer e) := by
  rw [← Nat.card_congr (parkerMarkedFrameEquiv e).toEquiv,parkerMarkedStabilizer_order]

/-- The actual pentad-and-standard-frame stabilizer has order196608. -/
theorem markedFrameRayStabilizer_five_order (e : Fin 5 ↪ Omega) :
    Nat.card (markedFrameRayStabilizer e)=196608 := by
  rw [← Nat.card_congr (parkerMarkedFrameEquiv e).toEquiv,parkerMarkedStabilizer_five_order]

end Atlas.Fischer
