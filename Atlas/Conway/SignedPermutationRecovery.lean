import Atlas.Lattices.LeechVisibleSymmetries

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- Recover the sign word from the odd glue vector of the actual lattice. -/
theorem signedPermutation_sign_mem (c : BinaryWord) (σ : Equiv.Perm Omega)
    (h : ∀ x : leech, signChange c (integerPermutation σ x.val) ∈ leech) : c ∈ golay := by
  let a : Omega := ((0,0),0)
  let u : leech := ⟨oddGlue a,oddGlue_mem a⟩
  have hp (i : Omega) : signChange c (integerPermutation σ u.val) i % 2 = 1 := by
    simp only [signChange,LinearMap.coe_mk,AddHom.coe_mk,integerPermutation,LinearEquiv.coe_mk,
      u,oddGlue]
    split_ifs <;> norm_num
  have hr : halfResidue (signChange c (integerPermutation σ u.val)) 1 = c := by
    ext i
    rcases bit_cases (c i) with hc | hc <;>
      by_cases hi : σ.symm i = a <;>
      simp [halfResidue,integerReduction,signChange,integerPermutation,u,oddGlue,hc,hi]
  obtain ⟨m,(rfl | rfl),hm,hc,_⟩ := (mem_leech _).mp (h u)
  · have hh := hm a; have hh' := hp a; omega
  · rwa [hr] at hc

theorem latticePermutation_codePreserving (σ : Equiv.Perm Omega)
    (h : ∀ x : leech, integerPermutation σ x.val ∈ leech) : CodePreserving σ := by
  have forward (c : BinaryWord) (hc : c ∈ golay) : coordinatePermutation σ c ∈ golay := by
    obtain ⟨x,hx⟩ := evenResidue_surjective ⟨c,hc⟩
    let y : leech := ⟨x.val,Or.inl x.prop⟩
    have hr : halfResidue (integerPermutation σ y.val) 0 = coordinatePermutation σ c := by
      have he : halfResidue x.val 0 = c := congrArg Subtype.val hx
      change coordinatePermutation σ (halfResidue x.val 0) = _
      rw [he]
    obtain ⟨m,(rfl | rfl),hm,hc',_⟩ := (mem_leech _).mp (h y)
    · rwa [hr] at hc'
    · have hh := hm ((0,0),0)
      have hp := even_mem_coordinate_even x.val x.prop (σ.symm ((0,0),0))
      change x.val (σ.symm ((0,0),0)) % 2 = 1 at hh
      omega
  let f : golay → golay := fun c => ⟨coordinatePermutation σ c.val,forward c.val c.prop⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    ext i
    have hi := congrFun hh (σ i)
    simpa [f,coordinatePermutation] using hi
  intro c
  constructor
  · exact forward c
  · intro hc
    obtain ⟨d,hd⟩ := (Finite.surjective_of_injective hf) ⟨coordinatePermutation σ c,hc⟩
    have he : d.val = c := by
      ext i
      have hi := congrFun (congrArg Subtype.val hd) (σ i)
      simpa [f,coordinatePermutation] using hi
    exact he ▸ d.prop

theorem signedPermutation_parameters (c : BinaryWord) (σ : Equiv.Perm Omega)
    (h : ∀ x : leech, signChange c (integerPermutation σ x.val) ∈ leech) :
    c ∈ golay ∧ CodePreserving σ := by
  have hc := signedPermutation_sign_mem c σ h
  refine ⟨hc,latticePermutation_codePreserving σ (fun x => ?_)⟩
  have hh := signChange_preserves c hc _ (h x)
  rwa [signChange_involutive] at hh

end Atlas.Conway
