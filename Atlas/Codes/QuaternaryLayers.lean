import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

/-! Generic residue and torsion layers of codes over Z/4. -/
namespace Atlas.Codes.Quaternary
open scoped BigOperators

abbrev Binary := ZMod 2
abbrev Quat := ZMod 4

def reduceScalar : Quat →+* Binary := ZMod.castHom (by decide : 2 ∣ 4) Binary

def doubleScalar : Binary →+ Quat where
  toFun a := if a=0 then 0 else 2
  map_zero' := by simp
  map_add' := by decide +kernel

theorem doubleScalar_injective : Function.Injective doubleScalar := by decide +kernel

theorem reduceScalar_double (a : Binary) : reduceScalar (doubleScalar a)=0 := by
  decide +kernel +revert

theorem doubleScalar_reduce (a : Quat) : doubleScalar (reduceScalar a)=2*a := by
  decide +kernel +revert

theorem reduceScalar_eq_zero (a : Quat) :
    reduceScalar a=0 ↔ ∃ b : Binary, doubleScalar b=a := by decide +kernel +revert

theorem doubleScalar_pair (a : Binary) (b : Quat) :
    doubleScalar (a*reduceScalar b)=doubleScalar a*b := by decide +kernel +revert

variable {ι : Type*}

def reduce : (ι → Quat) →+ (ι → Binary) where
  toFun u i := reduceScalar (u i)
  map_zero' := by ext i; exact map_zero reduceScalar
  map_add' := by intros; ext i; exact map_add reduceScalar _ _

def double : (ι → Binary) →+ (ι → Quat) where
  toFun u i := doubleScalar (u i)
  map_zero' := by ext i; exact map_zero doubleScalar
  map_add' := by intros; ext i; exact map_add doubleScalar _ _

theorem double_injective : Function.Injective (double (ι := ι)) := by
  intro a b h
  funext i
  exact doubleScalar_injective (congrFun h i)

theorem reduce_double (a : ι → Binary) : reduce (double a)=0 := by
  ext i
  exact reduceScalar_double _

theorem double_reduce (a : ι → Quat) : double (reduce a)=2 • a := by
  ext i
  change doubleScalar (reduceScalar (a i)) = (2 : ℕ) • a i
  rw [doubleScalar_reduce,two_nsmul,two_mul]

theorem reduce_eq_zero (a : ι → Quat) : reduce a=0 ↔ ∃ b, double b=a := by
  constructor
  · intro ha
    have hb (i : ι) : ∃ b : Binary, doubleScalar b=a i :=
      (reduceScalar_eq_zero _).mp (congrFun ha i)
    choose b hb using hb
    exact ⟨b,funext hb⟩
  · rintro ⟨b,rfl⟩
    exact reduce_double _

theorem reduce_kernel : (reduce (ι := ι)).ker=(double (ι := ι)).range := by
  ext a
  exact reduce_eq_zero a

variable [Fintype ι]

def binaryForm : LinearMap.BilinForm Binary (ι → Binary) := dotProductBilin Binary Binary

def quaternaryForm : LinearMap.BilinForm Quat (ι → Quat) := dotProductBilin Quat Quat

theorem double_pairing (a : ι → Binary) (b : ι → Quat) :
    quaternaryForm (double a) b=doubleScalar (binaryForm a (reduce b)) := by
  change (∑ i, doubleScalar (a i)*b i)=doubleScalar (∑ i,a i*reduceScalar (b i))
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (doubleScalar_pair _ _).symm)

theorem double_double_pairing (a b : ι → Binary) :
    quaternaryForm (double a) (double b)=0 := by
  rw [double_pairing,reduce_double,map_zero,map_zero]

theorem double_pairing_zero (a : ι → Binary) (b : ι → Quat) :
    quaternaryForm (double a) b=0 ↔ binaryForm a (reduce b)=0 := by
  rw [double_pairing]
  exact doubleScalar_injective.eq_iff' (map_zero doubleScalar)


theorem binaryForm_symmetric (a b : ι → Binary) : binaryForm a b=binaryForm b a := by
  change (∑ i,a i*b i)=∑ i,b i*a i
  simp [mul_comm]

theorem quaternaryForm_symmetric (a b : ι → Quat) : quaternaryForm a b=quaternaryForm b a := by
  change (∑ i,a i*b i)=∑ i,b i*a i
  simp [mul_comm]

theorem binaryForm_nondegenerate : (binaryForm (ι := ι)).Nondegenerate := by
  classical
  have hl : ∀ u : ι → Binary, (∀ v,binaryForm u v=0) → u=0 := by
    intro u hu
    funext i
    simpa [binaryForm,dotProductBilin,dotProduct,Pi.single_apply,mul_ite] using hu (Pi.single i 1)
  exact ⟨hl,fun u hu => hl u (fun v => by rw [binaryForm_symmetric]; exact hu v)⟩

theorem binaryForm_double_orthogonal (D : Submodule Binary (ι → Binary)) :
    binaryForm.orthogonal (binaryForm.orthogonal D)=D :=
  LinearMap.BilinForm.orthogonal_orthogonal binaryForm_nondegenerate
    (by intro a b h; rw [binaryForm_symmetric]; exact h) D

theorem double_mem_orthogonal_iff
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d)
    (b : ι → Binary) : double b∈quaternaryForm.orthogonal Q ↔ b∈binaryForm.orthogonal D := by
  constructor
  · intro hb d hd
    obtain ⟨q,hq,hqd⟩ := (hres d).mp hd
    have he := hb q hq
    rw [quaternaryForm_symmetric,double_pairing_zero] at he
    rw [binaryForm_symmetric,← hqd]
    exact he
  · intro hb q hq
    rw [quaternaryForm_symmetric,double_pairing_zero,binaryForm_symmetric]
    exact hb (reduce q) ((hres _).mpr ⟨q,hq,rfl⟩)

theorem torsion_eq_orthogonal
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d)
    (hself : Q≤quaternaryForm.orthogonal Q)
    (heven : ∀ b : ι → Binary, b∈binaryForm.orthogonal D → double b∈Q)
    (b : ι → Binary) : double b∈Q ↔ b∈binaryForm.orthogonal D :=
  ⟨fun hb => (double_mem_orthogonal_iff Q D hres b).mp (hself hb),heven b⟩

theorem selfdual_of_layers
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d)
    (hself : Q≤quaternaryForm.orthogonal Q)
    (heven : ∀ b : ι → Binary, b∈binaryForm.orthogonal D → double b∈Q) :
    quaternaryForm.orthogonal Q=Q := by
  apply le_antisymm ?_ hself
  intro v hv
  have hr : reduce v∈D := by
    rw [← binaryForm_double_orthogonal D]
    intro b hb
    exact (double_pairing_zero b v).mp (hv (double b) (heven b hb))
  obtain ⟨q,hq,hqv⟩ := (hres _).mp hr
  have hz : reduce (v-q)=0 := by rw [map_sub,hqv,sub_self]
  obtain ⟨b,hb⟩ := (reduce_eq_zero _).mp hz
  have hbo : double b∈quaternaryForm.orthogonal Q := by
    rw [hb]
    exact (quaternaryForm.orthogonal Q).sub_mem hv (hself hq)
  have hbq : double b∈Q := heven b ((double_mem_orthogonal_iff Q D hres b).mp hbo)
  have he : v=double b+q := by rw [hb,sub_add_cancel]
  rw [he]
  exact Q.add_mem hbq hq

def codeReduction
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d) : Q →+ D where
  toFun q := ⟨reduce q.val,(hres _).mpr ⟨q.val,q.prop,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero reduce)
  map_add' a b := Subtype.ext (map_add reduce a.val b.val)

omit [Fintype ι] in
theorem codeReduction_surjective
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d) :
    Function.Surjective (codeReduction Q D hres) := by
  intro d
  obtain ⟨q,hq,hd⟩ := (hres d.val).mp d.prop
  exact ⟨⟨q,hq⟩,Subtype.ext hd⟩

noncomputable def torsionKernelEquiv
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d)
    (hself : Q≤quaternaryForm.orthogonal Q)
    (heven : ∀ b : ι → Binary, b∈binaryForm.orthogonal D → double b∈Q) :
    binaryForm.orthogonal D ≃ (codeReduction Q D hres).ker :=
  Equiv.ofBijective
    (fun b => ⟨⟨double b.val,heven b.val b.prop⟩,
      AddMonoidHom.mem_ker.mpr (Subtype.ext (reduce_double b.val))⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      apply double_injective
      exact congrArg (fun q : (codeReduction Q D hres).ker => q.val.val) h
    · intro q
      have hz : reduce q.val.val=0 := congrArg Subtype.val (AddMonoidHom.mem_ker.mp q.prop)
      obtain ⟨b,hb⟩ := (reduce_eq_zero _).mp hz
      have hbd : b∈binaryForm.orthogonal D :=
        (torsion_eq_orthogonal Q D hres hself heven b).mp (hb.symm ▸ q.val.prop)
      exact ⟨⟨b,hbd⟩,Subtype.ext (Subtype.ext hb)⟩)

theorem card_of_layers
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d)
    (hself : Q≤quaternaryForm.orthogonal Q)
    (heven : ∀ b : ι → Binary, b∈binaryForm.orthogonal D → double b∈Q) :
    Nat.card Q=Nat.card (binaryForm.orthogonal D)*Nat.card D := by
  rw [← (codeReduction Q D hres).ker.card_mul_index,AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (codeReduction_surjective Q D hres),AddSubgroup.card_top]
  rw [← Nat.card_congr (torsionKernelEquiv Q D hres hself heven)]

theorem card_pow_of_layers
    (Q : Submodule Quat (ι → Quat)) (D : Submodule Binary (ι → Binary))
    (hres : ∀ d : ι → Binary, d∈D ↔ ∃ q : ι → Quat, q∈Q ∧ reduce q=d)
    (hself : Q≤quaternaryForm.orthogonal Q)
    (heven : ∀ b : ι → Binary, b∈binaryForm.orthogonal D → double b∈Q) :
    Nat.card Q=2^Fintype.card ι := by
  classical
  rw [card_of_layers Q D hres hself heven,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := Binary) (V := binaryForm.orthogonal D),
    Module.card_eq_pow_finrank (K := Binary) (V := D),← pow_add]
  have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := binaryForm) D
  rw [binaryForm_nondegenerate.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hd
  rw [add_comm,hd]
  simp [Binary,ZMod.card]

end Atlas.Codes.Quaternary


