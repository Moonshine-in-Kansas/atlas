import Atlas.Codes.HexacodeFiberStabilizer
import Atlas.GroupTheory.AlternatingHomSign

noncomputable section
namespace Atlas.Codes

local instance (i j : HexIndex) : Fintype {u : hexDoubleZero i j // u ≠ 0} :=
  Fintype.ofFinite _

def hexFiberPermutation (i j : HexIndex) (g : hexFiberStabilizer i j) :
    Equiv.Perm {u : hexDoubleZero i j // u ≠ 0} where
  toFun u := ⟨hexDoubleZeroAction i j g.val g.prop u.val, by
    intro h
    apply u.prop
    apply Subtype.ext
    apply (hexAction g.val.val.val).injective
    exact (congrArg (fun w : hexDoubleZero i j => w.val) h).trans (map_zero _).symm⟩
  invFun u := ⟨hexDoubleZeroAction i j g⁻¹.val g⁻¹.prop u.val, by
    intro h
    apply u.prop
    apply Subtype.ext
    apply (hexAction g⁻¹.val.val.val).injective
    exact (congrArg (fun w : hexDoubleZero i j => w.val) h).trans (map_zero _).symm⟩
  left_inv u := by
    apply Subtype.ext; apply Subtype.ext
    change hexAction g.val.val.val⁻¹ (hexAction g.val.val.val u.val.val) = u.val.val
    rw [map_inv]
    exact (hexAction g.val.val.val).symm_apply_apply _
  right_inv u := by
    apply Subtype.ext; apply Subtype.ext
    change hexAction g.val.val.val (hexAction g.val.val.val⁻¹ u.val.val) = u.val.val
    rw [map_inv]
    exact (hexAction g.val.val.val).apply_symm_apply _

def hexFiberPermutationHom (i j : HexIndex) : hexFiberStabilizer i j →*
    Equiv.Perm {u : hexDoubleZero i j // u ≠ 0} where
  toFun := hexFiberPermutation i j
  map_one' := by
    apply Equiv.ext; intro u; apply Subtype.ext; apply Subtype.ext
    change hexAction 1 u.val.val = u.val.val
    rw [map_one]; rfl
  map_mul' g h := by
    apply Equiv.ext; intro u; apply Subtype.ext; apply Subtype.ext
    change hexAction (g.val.val.val * h.val.val.val) u.val.val =
      hexAction g.val.val.val (hexAction h.val.val.val u.val.val)
    rw [map_mul]; rfl

theorem hexFiberPermutation_transitive (i j : HexIndex) (hij : i ≠ j)
    (u v : {u : hexDoubleZero i j // u ≠ 0}) :
    ∃ g : hexFiberStabilizer i j, hexFiberPermutationHom i j g u = v := by
  obtain ⟨g,hj,hg⟩ := hex_fiber_transitive i j hij u.val v.val u.prop v.prop
  exact ⟨⟨g,hj⟩,Subtype.ext (Subtype.ext hg)⟩

theorem hexFiberPermutation_even (i j : HexIndex) (g : hexFiberStabilizer i j) :
    Equiv.Perm.sign (hexFiberPermutationHom i j g) = 1 := by
  classical
  letI := Fintype.ofFinite {u : hexDoubleZero i j // u ≠ 0}
  have h := Atlas.GroupTheory.alternating_hom_sign
    ((hexFiberPermutationHom i j).comp (hexFiberA4Equiv i j).symm.toMonoidHom)
    (hexFiberA4Equiv i j g)
  simpa using h

theorem hexFiberPermutation_range (i j : HexIndex) (hij : i ≠ j) :
    (hexFiberPermutationHom i j).range =
      alternatingGroup {u : hexDoubleZero i j // u ≠ 0} := by
  classical
  have hc := hexDoubleZero_nonzero_card i j hij
  haveI : Nontrivial {u : hexDoubleZero i j // u ≠ 0} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have ha : Nat.card (alternatingGroup {u : hexDoubleZero i j // u ≠ 0}) = 3 := by
    rw [nat_card_alternatingGroup,hc]
    decide
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g,rfl⟩
    exact hexFiberPermutation_even i j g
  · obtain ⟨u⟩ := (inferInstance : Nonempty {u : hexDoubleZero i j // u ≠ 0})
    have hs : Function.Surjective
        (fun g : (hexFiberPermutationHom i j).range => g.val u) := by
      intro v
      obtain ⟨g,hg⟩ := hexFiberPermutation_transitive i j hij u v
      exact ⟨⟨hexFiberPermutationHom i j g,⟨g,rfl⟩⟩,hg⟩
    have hh := Nat.card_le_card_of_surjective _ hs
    rwa [hc,← ha] at hh

theorem hexFiberPermutation_kernel_card (i j : HexIndex) (hij : i ≠ j) :
    Nat.card (hexFiberPermutationHom i j).ker = 4 := by
  classical
  have hc := hexDoubleZero_nonzero_card i j hij
  haveI : Nontrivial {u : hexDoubleZero i j // u ≠ 0} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have h := (hexFiberPermutationHom i j).ker.card_mul_index
  rw [Subgroup.index_ker,hexFiberPermutation_range i j hij,
    nat_card_alternatingGroup,hc,hexFiberStabilizer_card i j hij] at h
  change Nat.card (hexFiberPermutationHom i j).ker * 3 = 12 at h
  omega

end Atlas.Codes
