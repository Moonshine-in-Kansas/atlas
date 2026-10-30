import Atlas.LinearGroups.SuzukiFamily.PointTransitivity

/-! Generic four-dimensional partial-tensor recognition infrastructure.
Independent of the Ree construction. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def tensorPolar (x y : Fin 4 → F) : F :=
  x 0*y 3+x 3*y 0+x 1*y 2+x 2*y 1

def rawPartialTensor (x y : Fin 4 → F) : Fin 4 → F :=
  ![x 0*y 1+x 1*y 0,x 0*y 2+x 2*y 0,
    x 1*y 3+x 3*y 1,x 2*y 3+x 3*y 2]

def IsTensorSpecial (m : ℕ) (x : Fin 4 → F) : Prop :=
  x ≠ 0 ∧ ∃ y, tensorPolar x y = 0 ∧ ∀ i, rawPartialTensor x y i = theta F m (x i)

private theorem tensor_affine_elimination (a c d A C y0 y1 y2 y3 : F)
    (h0 : y1+a*y0=1) (h1 : y2+c*y0=A)
    (h2 : a*y3+d*y1=C) (hp : y3+d*y0+a*y2+c*y1=0) :
    d=C+a^2*A+a*c := by
  have hi : d+C+a^2*A+a*c =
      (a*y3+d*y1+C)+a*(y3+d*y0+a*y2+c*y1)+
        (a*c+d)*(y1+a*y0+1)+a^2*(y2+c*y0+A) := by
    apply CharTwo.add_eq_zero.mp
    ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
  rw [h0,h1,h2,hp] at hi
  simp only [CharTwo.add_self_eq_zero,mul_zero,add_zero] at hi
  apply CharTwo.add_eq_zero.mp
  simpa only [add_assoc] using hi

theorem tensorSpecial_affine_normalized {m : ℕ} {x : Fin 4 → F}
    (hcard : Nat.card F = 2^(2*m+1)) (hx : IsTensorSpecial m x) (h0 : x 0 = 1) :
    x = affineVector m (x 1) (x 2+x 1*theta F m (x 1)) := by
  obtain ⟨_,y,hp,he⟩ := hx
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  simp only [rawPartialTensor,Matrix.cons_val,h0,one_mul,map_one] at he0 he1 he2
  change x 0*y 3+x 3*y 0+x 1*y 2+x 2*y 1=0 at hp
  rw [h0,one_mul] at hp
  have hd := tensor_affine_elimination (x 1) (x 2) (x 3)
    (theta F m (x 1)) (theta F m (x 2)) (y 0) (y 1) (y 2) (y 3)
      he0 he1 he2 hp
  funext i
  fin_cases i
  · simpa [affineVector] using h0
  · rfl
  · change x 2 = x 1*theta F m (x 1)+(x 2+x 1*theta F m (x 1))
    rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
  · change x 3 = norm m (x 1) (x 2+x 1*theta F m (x 1))
    rw [hd]
    simp only [norm,map_add,map_mul,theta_square hcard]
    apply CharTwo.add_eq_zero.mp
    ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]

theorem tensorSpecial_zero_first {m : ℕ} {x : Fin 4 → F}
    (hx : IsTensorSpecial m x) (h0 : x 0 = 0) : x 1 = 0 ∧ x 2 = 0 := by
  obtain ⟨_,y,hp,he⟩ := hx
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  simp only [rawPartialTensor,Matrix.cons_val,h0,zero_mul,zero_add,map_zero] at he0 he1 he2
  have ht (a : F) (h : theta F m a = 0) : a = 0 :=
    (theta F m).injective (by simpa only [map_zero] using h)
  have h1 : x 1=0 := by
    by_contra hn
    have hy0 : y 0=0 := (mul_eq_zero.mp he0).resolve_left hn
    exact hn (ht _ (by simpa only [hy0,mul_zero] using he1.symm))
  refine ⟨h1,?_⟩
  by_contra hn
  have hy0 : y 0=0 := by
    have hh : x 2*y 0=0 := by simpa only [h1,map_zero] using he1
    exact (mul_eq_zero.mp hh).resolve_left hn
  have hy1 : y 1=0 := by
    have hh : x 2*y 1=0 := by
      simpa only [tensorPolar,h0,h1,hy0,zero_mul,mul_zero,zero_add,add_zero] using hp
    exact (mul_eq_zero.mp hh).resolve_left hn
  exact hn (ht _ (by simpa only [h1,hy1,zero_mul,mul_zero,zero_add] using he2.symm))

/-- The last diagonal step of tensor recognition, with the parameter visible. -/
theorem tensor_diagonal_parameters {m : ℕ} (d : Fin 4 → F)
    (h03 : d 0*d 3=1) (h12 : d 1*d 2=1)
    (ht : theta F m (d 1)=d 0*d 2) :
    ∃ t : Fˣ, d = ![(t:F)*theta F m (t:F),(t:F),↑(t⁻¹),↑(t⁻¹)*theta F m ↑(t⁻¹)] := by
  have h1 : d 1≠0 := left_ne_zero_of_mul_eq_one h12
  let t : Fˣ := Units.mk0 (d 1) h1
  refine ⟨t,?_⟩
  have hd2 : d 2=(d 1)⁻¹ := by
    apply (mul_left_cancel₀ h1)
    rw [h12,mul_inv_cancel₀ h1]
  have hd0 : d 0=d 1*theta F m (d 1) := by
    rw [ht,← mul_assoc,mul_comm (d 1) (d 0),mul_assoc,h12,mul_one]
  have hd3 : d 3=(d 1)⁻¹*theta F m ((d 1)⁻¹) := by
    have hn : d 0≠0 := left_ne_zero_of_mul_eq_one h03
    apply (mul_left_cancel₀ hn)
    rw [h03,hd0]
    have htheta : theta F m (d 1) ≠ 0 := fun h => h1 ((theta F m).injective (by simpa using h))
    field_simp
    simp only [map_div₀,map_one,one_div,map_inv₀,mul_inv_cancel₀ htheta]
  funext i
  fin_cases i
  · exact hd0
  · rfl
  · exact hd2
  · exact hd3


theorem rawPartialTensor_smul (a b : F) (x y : Fin 4 → F) :
    rawPartialTensor (a • x) (b • y) = (a*b) • rawPartialTensor x y := by
  funext i
  fin_cases i <;> simp [rawPartialTensor,Pi.smul_apply,smul_eq_mul] <;> ring

theorem tensorPolar_smul (a b : F) (x y : Fin 4 → F) :
    tensorPolar (a • x) (b • y) = (a*b)*tensorPolar x y := by
  simp [tensorPolar,Pi.smul_apply,smul_eq_mul]
  ring

theorem IsTensorSpecial.smul {m : ℕ} {x : Fin 4 → F}
    (hx : IsTensorSpecial m x) (c : F) (hc : c ≠ 0) : IsTensorSpecial m (c • x) := by
  obtain ⟨hn,y,hp,he⟩ := hx
  have hmul : c*(theta F m c/c)=theta F m c := by field_simp
  refine ⟨smul_ne_zero hc hn,(theta F m c/c) • y,?_,?_⟩
  · rw [tensorPolar_smul,hp,mul_zero]
  · intro i
    rw [rawPartialTensor_smul]
    change (c*(theta F m c/c))*rawPartialTensor x y i=theta F m (c*x i)
    rw [hmul,he,map_mul]

theorem tensorSpecial_projective_mem {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {x : Fin 4 → F}
    (hx : IsTensorSpecial m x) : Projectivization.mk F x hx.1 ∈ pointSet m := by
  by_cases h0 : x 0=0
  · obtain ⟨h1,h2⟩ := tensorSpecial_zero_first hx h0
    have h3 : x 3≠0 := by
      intro h3
      apply hx.1
      funext i
      fin_cases i <;> simp_all
    refine ⟨none,?_⟩
    change infinityPoint=Projectivization.mk F x hx.1
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    refine ⟨(Units.mk0 (x 3) h3)⁻¹,?_⟩
    funext i
    fin_cases i <;> simp [infinityVector,Units.smul_def,h0,h1,h2,h3]
  · let x' : Fin 4 → F := (x 0)⁻¹ • x
    have hx' : IsTensorSpecial m x' := hx.smul _ (inv_ne_zero h0)
    have hx0 : x' 0=1 := by simp [x',h0]
    have ha := tensorSpecial_affine_normalized hcard hx' hx0
    refine ⟨some (x' 1,x' 2+x' 1*theta F m (x' 1)),?_⟩
    change affinePoint m (x' 1) (x' 2+x' 1*theta F m (x' 1))=
      Projectivization.mk F x hx.1
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    exact ⟨(Units.mk0 (x 0) h0)⁻¹,ha⟩

end Atlas.SuzukiFamily
