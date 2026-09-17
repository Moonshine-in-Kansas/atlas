import Atlas.LinearGroups.Symplectic.Center

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- Every nonidentity transvection has a nonidentity image in the actual central quotient. -/
theorem projection_transvection_ne_one {v : Vector n F} (hv : v ≠ 0) {a : F} (ha : a ≠ 0) :
    projection (transvection v a) ≠ 1 := by
  intro h
  have hc : transvection v a ∈ Subgroup.center (Sp n F) := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨c,hc⟩ := central_is_scalar _ hc
  have hcv : c • v = (1 : F) • v := by
    simpa [transvection_apply] using (hc v).symm
  have hc1 := smul_left_injective F hv hcv
  have ht : transvection v a = 1 := by
    apply ext_action
    intro x
    rw [hc,hc1,one_smul,one_smul]
  exact transvection_ne_one hv ha ht

theorem projective_nontrivial (hn : 0 < n) : Nontrivial (PSp n F) := by
  let i : Fin n := ⟨0,hn⟩
  have he : e (F := F) i ≠ 0 := by
    intro h
    have := congrFun h (.inl i)
    simp [e] at this
  exact ⟨⟨projection (transvection (e i) 1),1,projection_transvection_ne_one he one_ne_zero⟩⟩

end Atlas.Symplectic
