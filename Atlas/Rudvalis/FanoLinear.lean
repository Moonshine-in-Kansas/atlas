import Atlas.Rudvalis.FanoSupports

/-! The intrinsic seven-block action extends uniquely to the three-dimensional binary space. -/
namespace Atlas.Rudvalis

noncomputable def pointPermutationExtend (σ : Equiv.Perm Point) (x : E) : E :=
  if hx : x=0 then 0 else (σ ⟨x,hx⟩).val

@[simp] theorem pointPermutationExtend_zero (σ : Equiv.Perm Point) :
    pointPermutationExtend σ 0=0 := by simp [pointPermutationExtend]

@[simp] theorem pointPermutationExtend_point (σ : Equiv.Perm Point) (p : Point) :
    pointPermutationExtend σ p.val=(σ p).val := by simp [pointPermutationExtend,p.prop]

theorem pointPermutationExtend_bijective (σ : Equiv.Perm Point) :
    Function.Bijective (pointPermutationExtend σ) := by
  constructor
  · intro x y h
    by_cases hx : x=0
    · subst x
      by_cases hy : y=0
      · exact hy.symm
      · have ht := (σ ⟨y,hy⟩).prop
        simp only [pointPermutationExtend_zero,pointPermutationExtend,hy,↓reduceDIte] at h
        exact False.elim (ht h.symm)
    · by_cases hy : y=0
      · subst y
        have ht := (σ ⟨x,hx⟩).prop
        simp only [pointPermutationExtend_zero,pointPermutationExtend,hx,↓reduceDIte] at h
        exact False.elim (ht h)
      · simp only [pointPermutationExtend,hx,hy,↓reduceDIte] at h
        have he : σ ⟨x,hx⟩=σ ⟨y,hy⟩ := Subtype.ext h
        exact congrArg Subtype.val (σ.injective he)
  · intro y
    by_cases hy : y=0
    · exact ⟨0,by simpa [hy]⟩
    · refine ⟨(σ.symm ⟨y,hy⟩).val, ?_⟩
      rw [pointPermutationExtend_point,σ.apply_symm_apply]

theorem linearOnes_image_pullback (σ : Equiv.Perm Point) (u v : E)
    (h : (linearOnes u).image σ.symm=linearOnes v) (p : Point) :
    dot u (σ p).val=dot v p.val := by
  have he : dot u (σ p).val=1 ↔ dot v p.val=1 := by
    have hm := Finset.ext_iff.mp h p
    have hp : p ∈ (linearOnes u).image σ.symm ↔ σ p ∈ linearOnes u := by
      constructor
      · rintro hp
        obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hp
        have hq' : q=σ p := by rw [← he,σ.apply_symm_apply]
        exact hq' ▸ hq
      · intro hp
        exact Finset.mem_image.mpr ⟨σ p,hp,σ.symm_apply_apply p⟩
    simpa only [linearOnes,Finset.mem_filter,Finset.mem_univ,true_and] using hp.symm.trans hm
  rcases Atlas.Codes.bit_cases (dot u (σ p).val) with hu | hu <;>
    rcases Atlas.Codes.bit_cases (dot v p.val) with hv | hv <;> simp_all

theorem dot_basisPoint (i : Fin 3) (x : E) : dot (basisPoint i).val x=x i := by
  fin_cases i <;> simp [basisPoint,binaryLabel,dot,Fin.sum_univ_succ]

theorem binaryBlockHom_coordinate_linear (g : binaryPermutationGroup) (i : Fin 3) :
    ∃ v : E, ∀ x : E, pointPermutationExtend (binaryBlockHom g) x i=dot v x := by
  obtain ⟨v,hv⟩ := binaryBlockHom_preserves_fano (g⁻¹)
    (linearOnes (basisPoint i).val) ⟨basisPoint i,rfl⟩
  have hm : (linearOnes (basisPoint i).val).image (binaryBlockHom g).symm=linearOnes v.val := by
    simpa only [map_inv,Equiv.Perm.inv_def] using hv
  refine ⟨v.val, ?_⟩
  intro x
  by_cases hx : x=0
  · simp [hx,dot]
  · have he := linearOnes_image_pullback (binaryBlockHom g) (basisPoint i).val v.val hm ⟨x,hx⟩
    rw [dot_basisPoint] at he
    simpa [pointPermutationExtend,hx] using he

noncomputable def binaryBlockLinearMap (g : binaryPermutationGroup) : E →ₗ[Bit] E where
  toFun := pointPermutationExtend (binaryBlockHom g)
  map_add' x y := by
    ext i
    obtain ⟨v,hv⟩ := binaryBlockHom_coordinate_linear g i
    simp only [Pi.add_apply,hv,dot_add_right]
  map_smul' a x := by
    rcases Atlas.Codes.bit_cases a with ha | ha <;> simp [ha]

noncomputable def binaryBlockLinearEquiv (g : binaryPermutationGroup) : E ≃ₗ[Bit] E :=
  LinearEquiv.ofBijective (binaryBlockLinearMap g) (pointPermutationExtend_bijective _)

@[simp] theorem binaryBlockLinearEquiv_point (g : binaryPermutationGroup) (p : Point) :
    binaryBlockLinearEquiv g p.val=(binaryBlockHom g p).val :=
  pointPermutationExtend_point _ _


noncomputable def binaryBlockLinearHom : binaryPermutationGroup →* (E ≃ₗ[Bit] E) where
  toFun := binaryBlockLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    by_cases hx : x=0
    · subst x
      simp
    · change pointPermutationExtend (binaryBlockHom 1) x=x
      rw [map_one]
      simp [pointPermutationExtend,hx]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    by_cases hx : x=0
    · subst x
      simp
    · let p : Point := ⟨x,hx⟩
      change binaryBlockLinearEquiv (g*h) p.val =
        binaryBlockLinearEquiv g (binaryBlockLinearEquiv h p.val)
      rw [binaryBlockLinearEquiv_point,binaryBlockLinearEquiv_point,
        binaryBlockLinearEquiv_point,map_mul]
      rfl

theorem binaryBlockLinearHom_ker : binaryBlockLinearHom.ker=binaryBlockHom.ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    apply Equiv.ext
    intro p
    apply Subtype.ext
    have he := congrArg (fun e : E ≃ₗ[Bit] E => e p.val) h
    change binaryBlockLinearEquiv g p.val=p.val at he
    rw [binaryBlockLinearEquiv_point] at he
    exact he
  · intro h
    apply LinearEquiv.ext
    intro x
    change pointPermutationExtend (binaryBlockHom g) x=x
    rw [h]
    by_cases hx : x=0 <;> simp [pointPermutationExtend,hx]

end Atlas.Rudvalis

