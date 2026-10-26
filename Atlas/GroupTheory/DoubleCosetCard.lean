import Mathlib.GroupTheory.DoubleCoset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! Cardinality of a concrete double coset via its intersection fibers. -/
noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G]

def doubleCosetIntersection (B : Subgroup G) (n : G) : Subgroup G :=
  B ⊓ B.comap (MulAut.conj n⁻¹).toMonoidHom

def doubleCosetMap (B : Subgroup G) (n : G) (p : B × B) :
    DoubleCoset.doubleCoset n (B : Set G) B :=
  ⟨p.1.val*n*p.2.val,DoubleCoset.mem_doubleCoset.mpr ⟨_,p.1.property,_,p.2.property,rfl⟩⟩

theorem doubleCosetMap_surjective (B : Subgroup G) (n : G) :
    Function.Surjective (doubleCosetMap B n) := by
  rintro ⟨g,hg⟩
  obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩

def doubleCosetFiberMap (B : Subgroup G) (n : G) (p : B × B)
    (h : doubleCosetIntersection B n) : {r : B × B // doubleCosetMap B n r = doubleCosetMap B n p} :=
  ⟨(⟨p.1.val*h.val,B.mul_mem p.1.property h.property.1⟩,
      ⟨(n⁻¹*h.val⁻¹*n)*p.2.val,B.mul_mem (by
        have hh := B.inv_mem h.property.2
        simpa [MulAut.conj_apply, mul_assoc] using hh) p.2.property⟩),by
    apply Subtype.ext
    change (p.1.val*h.val)*n*((n⁻¹*h.val⁻¹*n)*p.2.val) = p.1.val*n*p.2.val
    group⟩

theorem doubleCosetFiberMap_bijective (B : Subgroup G) (n : G) (p : B × B) :
    Function.Bijective (doubleCosetFiberMap B n p) := by
  constructor
  · intro h k he
    have hh := congrArg (fun x => x.val.1.val) he
    exact Subtype.ext (mul_left_cancel hh)
  · rintro ⟨r,hr⟩
    have he : r.1.val*n*r.2.val=p.1.val*n*p.2.val := congrArg Subtype.val hr
    have he' : n⁻¹*(p.1.val⁻¹*r.1.val)*n=p.2.val*r.2.val⁻¹ := by
      calc
        _ = n⁻¹*p.1.val⁻¹*(r.1.val*n*r.2.val)*r.2.val⁻¹ := by group
        _ = _ := by rw [he]; group
    let h : doubleCosetIntersection B n := ⟨p.1.val⁻¹*r.1.val,
      ⟨B.mul_mem (B.inv_mem p.1.property) r.1.property,by
        change (MulAut.conj n⁻¹) (p.1.val⁻¹*r.1.val) ∈ B
        have hm : n⁻¹*(p.1.val⁻¹*r.1.val)*n ∈ B := by
          rw [he']
          exact B.mul_mem p.2.property (B.inv_mem r.2.property)
        simpa [MulAut.conj_apply,mul_assoc] using hm
⟩⟩
    refine ⟨h,Subtype.ext (Prod.ext ?_ ?_)⟩
    · apply Subtype.ext
      change p.1.val*(p.1.val⁻¹*r.1.val)=r.1.val
      group
    · apply Subtype.ext
      change (n⁻¹*(p.1.val⁻¹*r.1.val)⁻¹*n)*p.2.val=r.2.val
      have hh : n⁻¹*(p.1.val⁻¹*r.1.val)⁻¹*n = (n⁻¹*(p.1.val⁻¹*r.1.val)*n)⁻¹ := by group
      rw [hh,he']
      group

theorem card_doubleCoset_mul_intersection (B : Subgroup G) (n : G) :
    Nat.card (DoubleCoset.doubleCoset n (B : Set G) B) *
      Nat.card (doubleCosetIntersection B n) = Nat.card B * Nat.card B := by
  classical
  let f := doubleCosetMap B n
  have hf := doubleCosetMap_surjective B n
  let e (g : DoubleCoset.doubleCoset n (B : Set G) B) :
      {r : B × B // f r=g} ≃ doubleCosetIntersection B n := by
    let p := Classical.choose (hf g)
    have hp : f p=g := Classical.choose_spec (hf g)
    rw [← hp]
    exact (Equiv.ofBijective _ (doubleCosetFiberMap_bijective B n p)).symm
  have hc := Nat.card_congr ((Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd _ _)))
  simpa only [Nat.card_prod] using hc.symm

end Atlas.GroupTheory
