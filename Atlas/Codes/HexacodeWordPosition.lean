import Atlas.Codes.HexacodeFiberFixed

noncomputable section
namespace Atlas.Codes

theorem hexPointKernel_fixed_word_other_zero (i : HexIndex) (b : hexPointKernel i)
    (h : hexZeroCoordinate i) (hh : h ≠ 0) (hb : hexZeroLinear i b.val h = h)
    (j : HexIndex) (hji : j ≠ i) (hj : h.val.val j = 0) : b.val.val.val.perm j = j := by
  obtain ⟨j₀,hj₀,huniq⟩ := hexZeroCoordinate_unique_other_zero i h hh
  have he : j₀ = j := (huniq j ⟨hji,hj⟩).symm
  subst j₀
  have hpre : h.val.val (b.val.val.val.perm.symm j) = 0 := by
    have he := congrArg (fun u : hexZeroCoordinate i => u.val.val j) hb
    change b.val.val.val.localMap j (h.val.val (b.val.val.val.perm.symm j)) = h.val.val j at he
    rw [hj] at he
    exact (b.val.val.val.localMap j).map_eq_zero_iff.mp he
  have hprei : b.val.val.val.perm.symm j ≠ i := by
    intro he
    have he' := congrArg b.val.val.val.perm he
    rw [Equiv.apply_symm_apply,b.val.prop] at he'
    exact hji he'
  have he' := congrArg b.val.val.val.perm (huniq _ ⟨hprei,hpre⟩)
  simpa using he'.symm

theorem hexPointKernel_fixed_word_position (i : HexIndex) (b : hexPointKernel i)
    (h : hexZeroCoordinate i) (hh : h ≠ 0) (hb : hexZeroLinear i b.val h = h)
    (k : HexIndex) (hk : h.val.val k ≠ 0) (hbk : b.val.val.val.perm k = k) : b = 1 := by
  classical
  obtain ⟨j,hj,huniq⟩ := hexZeroCoordinate_unique_other_zero i h hh
  have hpre : h.val.val (b.val.val.val.perm.symm j) = 0 := by
    have he := congrArg (fun u : hexZeroCoordinate i => u.val.val j) hb
    change b.val.val.val.localMap j (h.val.val (b.val.val.val.perm.symm j)) = h.val.val j at he
    rw [hj.2] at he
    exact (b.val.val.val.localMap j).map_eq_zero_iff.mp he
  have hprei : b.val.val.val.perm.symm j ≠ i := by
    intro he
    have he' := congrArg b.val.val.val.perm he
    rw [Equiv.apply_symm_apply,b.val.prop] at he'
    exact hj.1 he'
  have hp : b.val.val.val.perm j = j := by
    have he := congrArg b.val.val.val.perm (huniq _ ⟨hprei,hpre⟩)
    simpa using he.symm
  let g : hexFiberStabilizer i j := ⟨b,hp⟩
  let u : hexDoubleZero i j := ⟨h.val,h.prop,hj.2⟩
  have hu : u ≠ 0 := fun hz => hh (Subtype.ext (congrArg (fun w : hexDoubleZero i j => w.val) hz))
  have hki : k ≠ i := fun he => hk (he.symm ▸ h.prop)
  have hkj : k ≠ j := fun he => hk (he.symm ▸ hj.2)
  let K : (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex) := ⟨k,by simp [hki,hkj]⟩
  have hg : hexAction g.val.val.val u.val = u.val := congrArg Subtype.val hb
  have he := hexFiber_fixed_word_position i j hj.1.symm g u hu hg K hbk
  exact congrArg Subtype.val he

end Atlas.Codes
