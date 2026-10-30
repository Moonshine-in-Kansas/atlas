import Atlas.LinearGroups.SuzukiFamily.TensorRecognition

noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def tensorBasis (i : Fin 4) : Fin 4 → F := Pi.single i 1

def partialTensor (m : ℕ) (x y : Fin 4 → F) : Fin 4 → F :=
  fun i => (theta F m).symm (rawPartialTensor x y i)

def PreservesPartialTensor (m : ℕ) (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) : Prop :=
  ∀ x y, tensorPolar x y=0 → g (partialTensor m x y)=partialTensor m (g x) (g y)

theorem tensorBasis_special_first (m : ℕ) :
    IsTensorSpecial m (tensorBasis (F := F) 0) := by
  refine ⟨?_,tensorBasis 1,?_,?_⟩
  · intro h
    have hh := congrFun h 0
    simpa [tensorBasis] using hh
  · norm_num [tensorPolar,tensorBasis,Pi.single_apply,Fin.ext_iff]
  · intro i
    fin_cases i <;> simp [rawPartialTensor,tensorBasis,Pi.single_apply]

theorem tensorBasis_special_last (m : ℕ) :
    IsTensorSpecial m (tensorBasis (F := F) 3) := by
  refine ⟨?_,tensorBasis 2,?_,?_⟩
  · intro h
    have hh := congrFun h 3
    simpa [tensorBasis] using hh
  · norm_num [tensorPolar,tensorBasis,Pi.single_apply,Fin.ext_iff]
  · intro i
    fin_cases i <;> simp [rawPartialTensor,tensorBasis,Pi.single_apply]

theorem IsTensorSpecial.map {m : ℕ}
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hB : ∀ x y, tensorPolar (g x) (g y)=tensorPolar x y)
    (hT : PreservesPartialTensor m g) {x : Fin 4 → F} (hx : IsTensorSpecial m x) :
    IsTensorSpecial m (g x) := by
  obtain ⟨hn,y,hp,he⟩ := hx
  have hv : partialTensor m x y=x := by
    funext i
    change (theta F m).symm (rawPartialTensor x y i)=x i
    rw [he,RingEquiv.symm_apply_apply]
  have ht := hT x y hp
  rw [hv] at ht
  refine ⟨fun h => hn (g.injective (by simpa using h)),g y,?_,?_⟩
  · rw [hB,hp]
  · intro i
    have hh := congrArg (theta F m) (congrFun ht i)
    simpa only [partialTensor,RingEquiv.apply_symm_apply] using hh.symm

theorem partialTensor_basis01 (m : ℕ) :
    partialTensor m (tensorBasis (F := F) 0) (tensorBasis 1)=tensorBasis 0 := by
  funext i
  fin_cases i <;> simp [partialTensor,rawPartialTensor,tensorBasis,Pi.single_apply]

theorem partialTensor_basis02 (m : ℕ) :
    partialTensor m (tensorBasis (F := F) 0) (tensorBasis 2)=tensorBasis 1 := by
  funext i
  fin_cases i <;> simp [partialTensor,rawPartialTensor,tensorBasis,Pi.single_apply]

theorem partialTensor_preserves_column01 {m : ℕ}
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (hT : PreservesPartialTensor m g) :
    rawPartialTensor (g (tensorBasis 0)) (g (tensorBasis 1))=
      fun i => theta F m (g (tensorBasis 0) i) := by
  have ht := hT (tensorBasis 0) (tensorBasis 1)
    (by norm_num [tensorPolar,tensorBasis,Pi.single_apply,Fin.ext_iff])
  rw [partialTensor_basis01] at ht
  funext i
  have hh := congrArg (theta F m) (congrFun ht i)
  simpa only [partialTensor,RingEquiv.apply_symm_apply] using hh.symm

theorem partialTensor_preserves_column02 {m : ℕ}
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (hT : PreservesPartialTensor m g) :
    rawPartialTensor (g (tensorBasis 0)) (g (tensorBasis 2))=
      fun i => theta F m (g (tensorBasis 1) i) := by
  have ht := hT (tensorBasis 0) (tensorBasis 2)
    (by norm_num [tensorPolar,tensorBasis,Pi.single_apply,Fin.ext_iff])
  rw [partialTensor_basis02] at ht
  funext i
  have hh := congrArg (theta F m) (congrFun ht i)
  simpa only [partialTensor,RingEquiv.apply_symm_apply] using hh.symm


theorem tensor_pair_normalization {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hB : ∀ x y, tensorPolar (g x) (g y)=tensorPolar x y)
    (hT : PreservesPartialTensor m g) :
    ∃ s : Group F m, ∃ a d : Fˣ,
      columnEquiv s.val (g (tensorBasis 0)) = a • tensorBasis 0 ∧
      columnEquiv s.val (g (tensorBasis 3)) = d • tensorBasis 3 := by
  have hfirst := (tensorBasis_special_first (F := F) m).map g hB hT
  have hlast := (tensorBasis_special_last (F := F) m).map g hB hT
  let p := Projectivization.mk F (g (tensorBasis 3)) hlast.1
  let q := Projectivization.mk F (g (tensorBasis 0)) hfirst.1
  have hp : p ∈ pointSet m := tensorSpecial_projective_mem hcard hlast
  have hq : q ∈ pointSet m := tensorSpecial_projective_mem hcard hfirst
  have hpq : p ≠ q := by
    intro he
    obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he
    have hz : (t:F) • tensorBasis (F := F) 0 = tensorBasis 3 := by
      apply g.injective
      simpa only [map_smul,Units.smul_def] using ht
    have hh := congrFun hz 0
    have ht0 : (t:F)=0 := by simpa [tensorBasis,Pi.single_apply] using hh
    exact t.ne_zero ht0
  obtain ⟨s,hs3,hs0⟩ := move_pair_to_base m hcard hp hq hpq
  have he0 : affineVector (F := F) m 0 0=tensorBasis 0 := by
    funext i
    fin_cases i <;> simp [affineVector,norm,tensorBasis,Pi.single_apply]
  have he3 : (infinityVector : Fin 4 → F)=tensorBasis 3 := by
    funext i
    fin_cases i <;> simp [infinityVector,tensorBasis,Pi.single_apply]
  change Projectivization.mk F (columnEquiv s.val (g (tensorBasis 0))) _ =
    Projectivization.mk F (affineVector m 0 0) _ at hs0
  change Projectivization.mk F (columnEquiv s.val (g (tensorBasis 3))) _ =
    Projectivization.mk F infinityVector _ at hs3
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hs0
  obtain ⟨d,hd⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hs3
  refine ⟨s,a,d,?_,?_⟩
  · simpa only [he0] using ha.symm
  · simpa only [he3] using hd.symm

end Atlas.SuzukiFamily
