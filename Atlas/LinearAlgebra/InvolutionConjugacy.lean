import Atlas.LinearAlgebra.InvolutionEigenspaceRestrictions

/-! # Conjugators assembled from the two actual eigenspaces -/
noncomputable section
namespace Atlas.LinearInvolution
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Specified equivalences of the two eigenspaces determine an ambient conjugator. -/
def conjugator (t : V →ₗ[F] V) (s : W →ₗ[F] W)
    (ht : Function.Involutive t) (hs : Function.Involutive s) (h2 : (2 : F) ≠ 0)
    (ep : plus t ≃ₗ[F] plus s) (em : minus t ≃ₗ[F] minus s) : V ≃ₗ[F] W :=
  (decomposition t ht h2).symm.trans ((ep.prodCongr em).trans (decomposition s hs h2))

theorem conjugator_decomposition (t : V →ₗ[F] V) (s : W →ₗ[F] W)
    (ht : Function.Involutive t) (hs : Function.Involutive s) (h2 : (2 : F) ≠ 0)
    (ep : plus t ≃ₗ[F] plus s) (em : minus t ≃ₗ[F] minus s) (x : plus t × minus t) :
    conjugator t s ht hs h2 ep em (decomposition t ht h2 x) =
      decomposition s hs h2 (ep x.1, em x.2) := by
  simp [conjugator]

theorem conjugator_intertwines (t : V →ₗ[F] V) (s : W →ₗ[F] W)
    (ht : Function.Involutive t) (hs : Function.Involutive s) (h2 : (2 : F) ≠ 0)
    (ep : plus t ≃ₗ[F] plus s) (em : minus t ≃ₗ[F] minus s) (x : V) :
    conjugator t s ht hs h2 ep em (t x) = s (conjugator t s ht hs h2 ep em x) := by
  obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition t ht h2).surjective x
  have he : t (decomposition t ht h2 (p,m)) = decomposition t ht h2 (p,-m) := by
    rw [decomposition_action]
    change p.val - m.val = p.val + (-m).val
    simp [sub_eq_add_neg]
  rw [he,conjugator_decomposition,conjugator_decomposition,decomposition_action]
  change (ep p).val + (em (-m)).val = (ep p).val - (em m).val
  simp [sub_eq_add_neg]

theorem decomposition_bilinear (b : LinearMap.BilinForm F V) (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0)
    (x y : plus t × minus t) :
    b (decomposition t ht h2 x) (decomposition t ht h2 y) =
      b x.1.val y.1.val + b x.2.val y.2.val := by
  change b (x.1.val + x.2.val) (y.1.val + y.2.val) = _
  simp only [map_add,LinearMap.add_apply]
  have hcross : b x.2.val y.1.val = 0 := orthogonal b.flip t (fun x y => hb y x) h2 y.1 x.2
  rw [orthogonal b t hb h2 x.1 y.2,hcross]
  simp

theorem conjugator_preserves (b : LinearMap.BilinForm F V) (c : LinearMap.BilinForm F W)
    (t : V →ₗ[F] V) (s : W →ₗ[F] W) (ht : Function.Involutive t) (hs : Function.Involutive s)
    (hb : ∀ x y, b (t x) (t y) = b x y) (hc : ∀ x y, c (s x) (s y) = c x y)
    (h2 : (2 : F) ≠ 0) (ep : plus t ≃ₗ[F] plus s) (em : minus t ≃ₗ[F] minus s)
    (hp : ∀ x y, c (ep x).val (ep y).val = b x.val y.val)
    (hm : ∀ x y, c (em x).val (em y).val = b x.val y.val) (x y : V) :
    c (conjugator t s ht hs h2 ep em x) (conjugator t s ht hs h2 ep em y) = b x y := by
  obtain ⟨u,rfl⟩ := (decomposition t ht h2).surjective x
  obtain ⟨v,rfl⟩ := (decomposition t ht h2).surjective y
  rw [conjugator_decomposition,conjugator_decomposition,
    decomposition_bilinear c s hs hc h2,decomposition_bilinear b t ht hb h2,hp,hm]
end Atlas.LinearInvolution
