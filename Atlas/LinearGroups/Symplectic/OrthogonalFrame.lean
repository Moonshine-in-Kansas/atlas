import Atlas.LinearGroups.Symplectic.Basis
import Atlas.LinearAlgebra.AlternatingFrame

noncomputable section
namespace Atlas.Symplectic
variable {F : Type*} [Field F]

@[simp] theorem headTail_e_succ {n : ℕ} (i : Fin n) :
    headTail n (e (F := F) i.succ) = ((0,0),e i) := by
  simp [headTail,e,Pi.single_apply]
  funext j
  cases j <;> simp [Pi.single_apply]

/-- Extend two independent orthogonal vectors to an actual alternating isometry. -/
theorem exists_isometry_orthogonal_pair {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*(n+2))
    (u v : V) (hu : u ≠ 0) (hv : v ∉ Submodule.span F {u}) (huv : B u v = 0) :
    ∃ g : B.IsometryEquiv (form (n := n+2) (F := F)),
      g u = e 0 ∧ g v = e 1 := by
  obtain ⟨f,huf,hvf⟩ := Atlas.AlternatingForm.split_retaining_orthogonal B hA hB hu hv huv
  have hvu : B v u = 0 := hvf.1
  have hvf₂ : B v f = 0 := hvf.2
  let W := Atlas.AlternatingForm.complement B u f
  let C := B.restrict W
  let vW : W := ⟨v,hvf⟩
  have hvW : vW ≠ 0 := by
    intro h
    have hv0 : v = 0 := congrArg Subtype.val h
    exact hv (hv0 ▸ (Submodule.span F {u}).zero_mem)
  have hC := Atlas.AlternatingForm.complement_alternating B hA u f huf
  have hCN := Atlas.AlternatingForm.complement_nondegenerate B hA u f huf hB
  have hW : Module.finrank F W = 2*(n+1) := by
    have h := Atlas.AlternatingForm.finrank_complement B hA u f huf
    change Module.finrank F W + 2 = Module.finrank F V at h
    omega
  obtain ⟨w,hw⟩ := Atlas.AlternatingForm.exists_partner C hCN hvW
  obtain ⟨k,hkv,_⟩ := exists_isometry_pair n C hC hCN hW vW w hw
  let s := Atlas.AlternatingForm.split B hA u f huf
  let t : V ≃ₗ[F] Vector (n+2) F :=
    (s.trans ((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv)).trans
      (headTail (n+1)).symm
  have ht (z : V) : headTail (n+1) (t z) = ((s z).1,k (s z).2) := by simp [t]
  have htB : ∀ x y, form (t x) (t y) = B x y := by
    intro x y
    rw [form_headTail,ht,ht]
    have hk := k.map_app (s y).2 (s x).2
    change form (k (s x).2) (k (s y).2) = B (s x).2.val (s y).2.val at hk
    rw [hk]
    have hb := Atlas.AlternatingForm.split_form B hA u f huf (s x) (s y)
    simpa only [s,LinearEquiv.symm_apply_apply] using hb.symm
  refine ⟨{ toLinearEquiv := t, map_app' := htB },?_,?_⟩
  · change t u = e 0
    apply (headTail (n+1)).injective
    rw [ht]
    have hs : s u = ((1,0),0) := by
      apply Prod.ext
      · simp [s,Atlas.AlternatingForm.split,huf,hA.self_eq_zero]
      · apply Subtype.ext
        change u-Atlas.AlternatingForm.planeProjection B u f u=0
        rw [Atlas.AlternatingForm.projection_e B hA u f huf,sub_self]
    rw [hs]
    simp [headTail,e,Pi.single_apply]
    rfl
  · change t v = e 1
    apply (headTail (n+1)).injective
    rw [ht]
    have hs : s v = ((0,0),vW) := by
      apply Prod.ext
      · change (B v f,-B v u)=(0,0)
        exact Prod.ext hvf₂ (by change -B v u = 0; rw [hvu,neg_zero])
      · apply Subtype.ext
        change v-Atlas.AlternatingForm.planeProjection B u f v=v
        simp [Atlas.AlternatingForm.planeProjection,hvu,hvf₂]
    rw [hs,hkv]
    exact (headTail_e_succ (F := F) (n := n+1) 0).symm

end Atlas.Symplectic
