import Atlas.Rudvalis.LatticeCoordinates
import Atlas.Rudvalis.CodeGaussian
import Atlas.Rudvalis.MonomialSeedCriterion
import Atlas.Codes.QuaternaryIntegerLift

/-! Signed-code symmetries act faithfully on the exact rational Construction-A lattice. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

variable {R : Type*} [CommRing R]

def liftedSign (b : Binary) (x : R) : R := if b=0 then x else -x

theorem liftedSign_add (b c : Binary) (x : R) :
    liftedSign (b+c) x=liftedSign b (liftedSign c x) := by
  have h : ∀ a : Binary,a=0 ∨ a=1 := by decide +kernel
  rcases h b with rfl|rfl <;> rcases h c with rfl|rfl <;>
    simp [liftedSign,show (1 : Binary)+1=0 by decide]

def liftedMonomialAction (g : SignedCoordinates Coordinate) : RationalSpace ≃ₗ[ℚ] RationalSpace where
  toFun v i := liftedSign (g.left.toAdd i) (v (g.right.symm i))
  invFun v i := liftedSign (g.left.toAdd (g.right i)) (v (g.right i))
  left_inv v := by ext i; simp [liftedSign]; split <;> simp_all
  right_inv v := by ext i; simp [liftedSign]; split <;> simp_all
  map_add' v w := by ext i; simp [liftedSign]; split <;> simp_all [add_comm]
  map_smul' a v := by ext i; simp [liftedSign]

def rationalMonomialHom : SignedCoordinates Coordinate →* (RationalSpace ≃ₗ[ℚ] RationalSpace) where
  toFun := liftedMonomialAction
  map_one' := by ext v i; change liftedSign 0 (v i)=v i; simp [liftedSign]
  map_mul' g h := by
    ext v i
    change liftedSign (g.left.toAdd i+h.left.toAdd (g.right.symm i))
      (v (h.right.symm (g.right.symm i)))=
      liftedSign (g.left.toAdd i) (liftedSign (h.left.toAdd (g.right.symm i))
        (v (h.right.symm (g.right.symm i))))
    exact liftedSign_add _ _ _

def integerMonomial (g : SignedCoordinates Coordinate) (z : IntegerCoordinates) : IntegerCoordinates :=
  fun i => liftedSign (g.left.toAdd i) (z (g.right.symm i))

theorem integerMonomial_reduce (g : SignedCoordinates Coordinate) (z : IntegerCoordinates) :
    reduceModFour (integerMonomial g z)=monomialHom g (reduceModFour z) := by
  ext i
  change ((liftedSign (g.left.toAdd i) (z (g.right.symm i)) : ℤ) : ZMod 4)=
    signedScalar (g.left.toAdd i) (z (g.right.symm i) : ZMod 4)
  simp [liftedSign,signedScalar]

theorem rationalMonomial_half (g : SignedCoordinates Coordinate) (z : IntegerCoordinates) :
    rationalMonomialHom g (halfCoordinates z)=halfCoordinates (integerMonomial g z) := by
  ext i
  change liftedSign (g.left.toAdd i) ((z (g.right.symm i) : ℚ)/2)=
    ((liftedSign (g.left.toAdd i) (z (g.right.symm i)) : ℤ) : ℚ)/2
  by_cases h : g.left.toAdd i=0 <;> simp [liftedSign,h,neg_div]

theorem rationalMonomial_pairing (g : SignedCoordinates Coordinate) (v w : RationalSpace) :
    rationalDot (rationalMonomialHom g v) (rationalMonomialHom g w)=rationalDot v w := by
  have he (i : Coordinate) : liftedSign (g.left.toAdd i) (v (g.right.symm i))*
      liftedSign (g.left.toAdd i) (w (g.right.symm i))=v (g.right.symm i)*w (g.right.symm i) := by
    simp [liftedSign]; split <;> simp_all
  change (∑i,liftedSign (g.left.toAdd i) (v (g.right.symm i))*liftedSign (g.left.toAdd i) (w (g.right.symm i)))=_
  simp_rw [he]
  exact Equiv.sum_comp g.right.symm (fun i => v i*w i)

theorem codeGroup_lattice_preserves (g : codeGroup) (v : RationalSpace)
    (hv : v∈rudvalisLattice) : rationalMonomialHom g.val v∈rudvalisLattice := by
  obtain ⟨z,hz,rfl⟩ := hv
  rw [rationalMonomial_half,halfCoordinates_mem,integerMonomial_reduce]
  exact (g.prop _).mp hz

theorem codeGroup_lattice_iff (g : codeGroup) (v : RationalSpace) :
    v∈rudvalisLattice ↔ rationalMonomialHom g.val v∈rudvalisLattice := by
  constructor
  · exact codeGroup_lattice_preserves g v
  · intro h
    have he := codeGroup_lattice_preserves g⁻¹ _ h
    simpa using he

theorem signed_lattice_stabilizer_iff (g : SignedCoordinates Coordinate) :
    (∀ v,v∈rudvalisLattice ↔ rationalMonomialHom g v∈rudvalisLattice) ↔ g∈codeGroup := by
  constructor
  · intro hg
    apply codeGroup_mem_of_preserves
    intro w hw
    let z : IntegerCoordinates := fun i => integerRepresentative (w i)
    have hz : reduceModFour z=w := by ext i; exact integerRepresentative_cast (w i)
    have hl : halfCoordinates z∈rudvalisLattice := halfCoordinates_mem z |>.mpr (hz ▸ hw)
    have ht := (hg _).mp hl
    rw [rationalMonomial_half,halfCoordinates_mem,integerMonomial_reduce,hz] at ht
    exact ht
  · intro hg
    exact codeGroup_lattice_iff ⟨g,hg⟩

theorem rationalMonomialHom_injective : Function.Injective rationalMonomialHom := by
  classical
  intro g h he
  have hp : g.right=h.right := by
    suffices hi : g.right.symm=h.right.symm from by simpa using congrArg Equiv.symm hi
    apply Equiv.ext
    intro i
    by_contra hn
    let v : RationalSpace := fun j => if j=g.right.symm i then 1 else 0
    have hh := congrArg (fun L : RationalSpace ≃ₗ[ℚ] RationalSpace => L v i) he
    change liftedSign (g.left.toAdd i) (v (g.right.symm i))=
      liftedSign (h.left.toAdd i) (v (h.right.symm i)) at hh
    have hz : h.right.symm i≠g.right.symm i := Ne.symm hn
    simp only [v,if_pos rfl,if_neg hz] at hh
    have hnonzero : ∀ b : Binary,liftedSign b (1 : ℚ)≠0 := by decide +kernel
    have hzero : liftedSign (h.left.toAdd i) (0 : ℚ)=0 := by simp [liftedSign]
    rw [hzero] at hh
    exact hnonzero _ hh
  have hs : g.left=h.left := by
    change g.left.toAdd=h.left.toAdd
    funext i
    have hh := congrArg (fun L : RationalSpace ≃ₗ[ℚ] RationalSpace => L (fun _ => 1) i) he
    have hk : ∀ b c : Binary,liftedSign b (1 : ℚ)=liftedSign c 1 → b=c := by decide +kernel
    exact hk _ _ hh
  exact SemidirectProduct.ext hs hp

def negativeMonomial : SignedCoordinates Coordinate :=
  SemidirectProduct.inl (Multiplicative.ofAdd (fun _ => 1))

theorem negativeMonomial_quaternary (w : QuaternaryWord) : monomialHom negativeMonomial w= -w := by
  ext i
  change signedScalar 1 (w i)= -w i
  simp [signedScalar]

theorem negativeMonomial_rational (v : RationalSpace) : rationalMonomialHom negativeMonomial v= -v := by
  ext i
  change liftedSign 1 (v i)= -v i
  simp [liftedSign]

theorem codeI_squared_signed : codeI.val*codeI.val=negativeMonomial := by
  apply monomialHom_injective
  apply LinearEquiv.ext
  intro w
  rw [map_mul]
  change monomialHom codeI.val (monomialHom codeI.val w)=monomialHom negativeMonomial w
  rw [codeI_square_action,negativeMonomial_quaternary]

noncomputable def rationalI : RationalSpace ≃ₗ[ℚ] RationalSpace := rationalMonomialHom codeI.val

theorem rationalI_square (v : RationalSpace) : rationalI (rationalI v)= -v := by
  change rationalMonomialHom codeI.val (rationalMonomialHom codeI.val v)= -v
  rw [←LinearEquiv.mul_apply,←map_mul,codeI_squared_signed,negativeMonomial_rational]

theorem rationalI_lattice (v : RationalSpace) : v∈rudvalisLattice ↔ rationalI v∈rudvalisLattice :=
  codeGroup_lattice_iff codeI v

theorem rationalI_pairing (v w : RationalSpace) : rationalDot (rationalI v) (rationalI w)=rationalDot v w :=
  rationalMonomial_pairing codeI.val v w

theorem codeGroup_rational_gaussian_linear (g : codeGroup) (v : RationalSpace) :
    rationalMonomialHom g.val (rationalI v)=rationalI (rationalMonomialHom g.val v) := by
  have h := congrArg (fun a : codeGroup => rationalMonomialHom a.val v) (codeGroup_commute_I g)
  change rationalMonomialHom (g.val*codeI.val) v=rationalMonomialHom (codeI.val*g.val) v at h
  simpa only [map_mul,LinearEquiv.mul_apply,rationalI] using h

end Atlas.Rudvalis
