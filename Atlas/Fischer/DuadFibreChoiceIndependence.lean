import Atlas.Fischer.ReflectingRayFamily
import Atlas.Fischer.DuadFibreCount
import Mathlib.Data.Set.Card

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- After extremal closure, the actual duadic point shape identifies the chosen
same-duad fibre and fixes the scalar phase to one. -/
theorem reflectingRoot_duadic_shape_is_chosen (p : RootDuad) (x : Coordinates)
    (hx : IsReflectingRoot x)
    (hs : ∀ i, x (.inl i) = if i ∈ p.val then (-7 / 8 : Scalar) else 1 / 8) :
    ∃ ξ, x = chosenDuadicRoot p ξ := by
  obtain ⟨t, ht⟩ := reflectingRootParameter_exhaust x hx
  rcases t with i | (t | t)
  · exact False.elim (basic_duadic_shape_rays_ne i p.val p.property x hs ht.symm)
  · exact False.elim (octadic_duadic_shape_rays_ne (chosenOctadCalibration t.1) t.2
      p.val p.property x hs ht.symm)
  · rcases t with ⟨q, η⟩
    have he : p = q := Subtype.ext (duadic_shape_ray_implies_duad_eq
      p.val q.val p.property q.property x (chosenDuadicRoot q η) hs
      (chosenDuadicRoot_axis_coefficient q η) ht)
    subst q
    refine ⟨η, ?_⟩
    exact rootRay_eq_of_axisSum (chosenDuadicRoot p η) x
      (by rw [rootAxisSum_duadic_shape p.val p.property x hs, chosenDuadicRoot_axisSum])
      (by rw [chosenDuadicRoot_axisSum]; norm_num) ht

theorem duadCharacterProduct_is_chosen (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    ∃ η, duadCharacterProduct p hp F G hFG Q R ξ = chosenDuadicRoot ⟨p, hp⟩ η := by
  apply reflectingRoot_duadic_shape_is_chosen ⟨p, hp⟩ _
    (duadCharacterProduct_isReflectingRoot p hp F G hFG Q R ξ)
  intro i
  unfold duadCharacterProduct
  rw [duadOctadicProduct_axis_coefficient (hFG ▸ hp), hFG]

/-- The arbitrary-pair fibre equals the actual chosen fibre. Closure is used only
for inclusion; both independent1024-point counts supply the reverse inclusion. -/
theorem duadProductFibre_eq_chosen (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    DuadProductFibre p hp F G hFG Q R = Set.range (chosenDuadicRoot ⟨p, hp⟩) := by
  have ht : Nat.card (Set.range (chosenDuadicRoot ⟨p, hp⟩)) = 1024 :=
    duadProductFibre_card p hp
      (duadChosenOctadPair p hp).1 (duadChosenOctadPair p hp).2
      (duadChosenOctadPair_intersection p hp) (chosenOctadCalibration _) (chosenOctadCalibration _)
  apply Set.eq_of_subset_of_ncard_le
  · rintro x ⟨ξ, rfl⟩
    obtain ⟨η, hη⟩ := duadCharacterProduct_is_chosen p hp F G hFG Q R ξ
    exact ⟨η, hη.symm⟩
  · change Nat.card (Set.range (chosenDuadicRoot ⟨p, hp⟩)) ≤
      Nat.card (DuadProductFibre p hp F G hFG Q R)
    rw [ht, duadProductFibre_card]
  · letI : Finite (Set.range (chosenDuadicRoot ⟨p, hp⟩)) :=
      Nat.finite_of_card_ne_zero (by rw [ht]; decide)
    exact Set.toFinite _

/-- Full octad-pair and calibration independence of the actual vector fibre,
proved after classification and not used to establish the initial ray count. -/
theorem duadProductFibre_choice_independent (p : Finset Omega) (hp : p.card = 2)
    (F G F' G' : Octad) (hFG : F.val ∩ G.val = p) (hFG' : F'.val ∩ G'.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (Q' : OctadCalibration F') (R' : OctadCalibration G') :
    DuadProductFibre p hp F G hFG Q R = DuadProductFibre p hp F' G' hFG' Q' R' :=
  (duadProductFibre_eq_chosen p hp F G hFG Q R).trans
    (duadProductFibre_eq_chosen p hp F' G' hFG' Q' R').symm

end Atlas.Fischer
