import Mathlib.GroupTheory.GroupAction.Basic

/-! Transport of an abelian character between point stabilizers. -/
namespace Atlas.GroupTheory
variable {G X A : Type*} [Group G] [MulAction G X] [CommGroup A]

/-- Conjugation by a transporter identifies the destination stabilizer with the source. -/
def stabilizerTransportHom (x y : X) (r : G) (hr : r • x = y) :
    MulAction.stabilizer G y →* MulAction.stabilizer G x where
  toFun a := ⟨r⁻¹*a.val*r,by
    change (r⁻¹*a.val*r) • x = x
    rw [mul_smul,mul_smul,hr,a.prop,←hr,inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

/-- Abelian characters on a stabilizer are independent of the transporter. -/
theorem stabilizer_character_independent (x y : X)
    (φ : MulAction.stabilizer G x →* A) (r s : G)
    (hr : r • x=y) (hs : s • x=y) (a : MulAction.stabilizer G y) :
    φ (stabilizerTransportHom x y r hr a) =
      φ (stabilizerTransportHom x y s hs a) := by
  let t : MulAction.stabilizer G x := ⟨s⁻¹*r,by
    change (s⁻¹*r) • x=x
    rw [mul_smul,hr,←hs,inv_smul_smul]⟩
  have he : stabilizerTransportHom x y r hr a =
      t⁻¹ * stabilizerTransportHom x y s hs a * t := by
    apply Subtype.ext
    change r⁻¹*a.val*r=(s⁻¹*r)⁻¹*(s⁻¹*a.val*s)*(s⁻¹*r)
    simp [mul_inv_rev,mul_assoc]
  rw [he,map_mul,map_mul,map_inv]
  simp [mul_comm,mul_left_comm,mul_assoc]

/-- Simultaneously transporting the point and conjugating the stabilizer element
preserves the transported character. -/
theorem stabilizer_character_conjugate (x y : X)
    (φ : MulAction.stabilizer G x →* A) (r h : G)
    (hr : r • x=y) (a : MulAction.stabilizer G y) :
    φ (stabilizerTransportHom x (h • y) (h*r) (by rw [mul_smul,hr])
      ⟨h*a.val*h⁻¹,by
        change (h*a.val*h⁻¹) • (h • y)=h • y
        rw [mul_smul,mul_smul,inv_smul_smul,a.prop]⟩) =
      φ (stabilizerTransportHom x y r hr a) := by
  congr 1
  apply Subtype.ext
  change (h*r)⁻¹*(h*a.val*h⁻¹)*(h*r)=r⁻¹*a.val*r
  simp [mul_inv_rev,mul_assoc]

end Atlas.GroupTheory
