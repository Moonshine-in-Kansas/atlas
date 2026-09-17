import Atlas.LinearAlgebra.SymplecticSquareMinusOne

/-! # Actual conjugacy of symplectic square-minus-one operators -/
noncomputable section
namespace Atlas.AlternatingForm
universe u v w
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)
variable (t : V →ₗ[F] V) (ht : ∀ x, t (t x) = -x)
variable (hp : ∀ x y, B (t x) (t y) = B x y)
variable (x : V) (hx : B x (t x) = 1)

def squareMinusOneComplementOperator : complement B x (t x) →ₗ[F] complement B x (t x) where
  toFun y := ⟨t y.val,squareMinusOne_complement_stable B hA t ht hp x hx y.val y.prop⟩
  map_add' y z := Subtype.ext (map_add t y.val z.val)
  map_smul' a y := Subtype.ext (map_smul t a y.val)

theorem squareMinusOneComplementOperator_square (y : complement B x (t x)) :
    squareMinusOneComplementOperator B hA t ht hp x hx
      (squareMinusOneComplementOperator B hA t ht hp x hx y) = -y :=
  Subtype.ext (ht y.val)

theorem squareMinusOneComplementOperator_preserves (y z : complement B x (t x)) :
    (B.restrict (complement B x (t x)))
      (squareMinusOneComplementOperator B hA t ht hp x hx y)
      (squareMinusOneComplementOperator B hA t ht hp x hx z) =
    (B.restrict (complement B x (t x))) y z := hp y.val z.val

/-- In normalized split coordinates the plane operator is (a,b) ↦ (-b,a). -/
theorem squareMinusOne_split_operator (z : (F × F) × complement B x (t x)) :
    t ((split B hA x (t x) hx).symm z) =
      (split B hA x (t x) hx).symm
        ((-z.1.2,z.1.1),squareMinusOneComplementOperator B hA t ht hp x hx z.2) := by
  change t (z.1.1 • x + z.1.2 • t x + z.2.val) =
    -z.1.2 • x + z.1.1 • t x + t z.2.val
  rw [map_add,map_add,map_smul,map_smul,ht]
  module

include hA ht hp in
/-- Same-dimensional symplectic square-minus-one spaces are actually isometric with intertwining operators. -/
theorem squareMinusOne_isometry_exists {W : Type w} [AddCommGroup W] [Module F W]
    [Finite F] [FiniteDimensional F V] [FiniteDimensional F W]
    (hB : B.Nondegenerate) (C : LinearMap.BilinForm F W) (hCalt : C.IsAlt)
    (hC : C.Nondegenerate) (s : W →ₗ[F] W) (hs : ∀ y, s (s y) = -y)
    (hsp : ∀ y z, C (s y) (s z) = C y z)
    (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F V = Module.finrank F W) :
    ∃ e : V ≃ₗ[F] W, (∀ y z, C (e y) (e z) = B y z) ∧ (∀ y, e (t y) = s (e y)) := by
  generalize hn : Module.finrank F V = n
  induction n using Nat.strong_induction_on generalizing V W with
  | h n ih =>
    by_cases hn0 : n = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
      haveI : Subsingleton W := Module.finrank_zero_iff.mp (hdim.symm.trans (hn.trans hn0))
      refine ⟨LinearEquiv.ofSubsingleton V W,?_,fun _ => Subsingleton.elim _ _⟩
      intro y z
      have hy : y = 0 := Subsingleton.elim _ _
      have hz : z = 0 := Subsingleton.elim _ _
      simp [hy,hz]
    · haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
      haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (M := W) (by omega)
      obtain ⟨a,ha⟩ := squareMinusOne_exists_normalized B hA t ht hp hB h2
      obtain ⟨b,hb⟩ := squareMinusOne_exists_normalized C hCalt s hs hsp hC h2
      let P := complement B a (t a)
      let R := complement C b (s b)
      let BP := B.restrict P
      let CR := C.restrict R
      let tp := squareMinusOneComplementOperator B hA t ht hp a ha
      let sr := squareMinusOneComplementOperator C hCalt s hs hsp b hb
      have hPdim := finrank_complement B hA a (t a) ha
      have hRdim := finrank_complement C hCalt b (s b) hb
      have hlt : Module.finrank F P < n := by dsimp only [P]; omega
      have heq : Module.finrank F P = Module.finrank F R := by dsimp only [P,R]; omega
      obtain ⟨i,hi,hit⟩ := ih (Module.finrank F P) hlt
        BP (complement_alternating B hA a (t a) ha) tp
        (squareMinusOneComplementOperator_square B hA t ht hp a ha)
        (squareMinusOneComplementOperator_preserves B hA t ht hp a ha)
        (complement_nondegenerate B hA a (t a) ha hB)
        CR (complement_alternating C hCalt b (s b) hb)
        (complement_nondegenerate C hCalt b (s b) hb hC) sr
        (squareMinusOneComplementOperator_square C hCalt s hs hsp b hb)
        (squareMinusOneComplementOperator_preserves C hCalt s hs hsp b hb)
        heq rfl
      let L := split B hA a (t a) ha
      let M := split C hCalt b (s b) hb
      let E : V ≃ₗ[F] W := L.trans (((LinearEquiv.refl F (F×F)).prodCongr i).trans M.symm)
      have hE (z : (F × F) × P) : E (L.symm z) = M.symm (z.1,i z.2) := by
        change M.symm (((LinearEquiv.refl F (F×F)).prodCongr i) (L (L.symm z))) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      refine ⟨E,?_,?_⟩

      · intro y z
        obtain ⟨y,rfl⟩ := L.symm.surjective y
        obtain ⟨z,rfl⟩ := L.symm.surjective z
        rw [hE,hE]
        rw [split_form C hCalt b (s b) hb,split_form B hA a (t a) ha]
        have hh := hi y.2 z.2
        change C (i y.2).val (i z.2).val = B y.2.val z.2.val at hh
        rw [hh]
      · intro y
        obtain ⟨y,rfl⟩ := L.symm.surjective y
        rw [squareMinusOne_split_operator B hA t ht hp a ha]
        change E (L.symm ((-y.1.2,y.1.1),tp y.2)) = s (E (L.symm y))
        rw [hE,hE]
        rw [squareMinusOne_split_operator C hCalt s hs hsp b hb]
        rw [hit]

include hA ht hp in
/-- Any two square-minus-one symplectic operators on the same finite-dimensional space are actually conjugate. -/
theorem squareMinusOne_conjugacy [Finite F] [FiniteDimensional F V]
    (hB : B.Nondegenerate) (s : V →ₗ[F] V) (hs : ∀ y, s (s y) = -y)
    (hsp : ∀ y z, B (s y) (s z) = B y z) (h2 : (2 : F) ≠ 0) :
    ∃ g : V ≃ₗ[F] V, (∀ y z, B (g y) (g z) = B y z) ∧
      (∀ y, g (t (g.symm y)) = s y) := by
  obtain ⟨g,hg,hgt⟩ := squareMinusOne_isometry_exists B hA t ht hp hB B hA hB s hs hsp h2 rfl
  refine ⟨g,hg,?_⟩
  intro y
  rw [hgt,LinearEquiv.apply_symm_apply]

end Atlas.AlternatingForm


