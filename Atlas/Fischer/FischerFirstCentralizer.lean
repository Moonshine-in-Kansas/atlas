import Atlas.Fischer.GeneratedRayParity
import Atlas.Fischer.ResiduePerfectness
import Atlas.GroupTheory.CentralKernelProduct

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def firstCentralizerParity (i : Omega) : residueCentralizer {i} →* Multiplicative Bit :=
  rootGeneratedRayParity.comp (residueCentralizer {i}).subtype

def firstCentralizerMarked (i : Omega) : residueCentralElementary {i} :=
  ⟨⟨distinguishedRootElement (.inl i),residueElementary_le_centralizer {i}
      (Subgroup.subset_closure ⟨i,by simp,rfl⟩)⟩,
    Subgroup.subset_closure ⟨i,by simp,rfl⟩⟩

theorem firstCentralizerParity_marked (i : Omega) :
    firstCentralizerParity i (firstCentralizerMarked i).val=Multiplicative.ofAdd (1 : Bit) :=
  distinguishedRootElement_parity (.inl i)

theorem firstCentralizerParity_marked_bijective (i : Omega) :
    Function.Bijective ((firstCentralizerParity i).comp (residueCentralElementary {i}).subtype) := by
  apply Function.Surjective.bijective_of_nat_card_le
  · intro b
    obtain ⟨b,rfl⟩ := (Multiplicative.ofAdd : Bit ≃ Multiplicative Bit).surjective b
    fin_cases b
    · exact ⟨1,map_one _⟩
    · exact ⟨firstCentralizerMarked i,firstCentralizerParity_marked i⟩
  · rw [residueCentralElementary_card {i} (by simp)]
    simp only [Finset.card_singleton]
    change 2 ≤ Nat.card (Multiplicative Bit)
    rw [Nat.card_eq_fintype_card]
    decide

/-- Multiplication of the marked involution subgroup and the even centralizer. -/
def firstCentralizerProductEquiv (i : Omega) :
    residueCentralElementary {i} × (firstCentralizerParity i).ker ≃* residueCentralizer {i} :=
  Atlas.GroupTheory.centralKernelProductEquiv (firstCentralizerParity i)
    (residueCentralElementary {i}) (residueCentralElementary_le_center {i})
    (firstCentralizerParity_marked_bijective i)

def firstCentralizerEvenPart (i : Omega) : residueCentralizer {i} →* (firstCentralizerParity i).ker :=
  (MonoidHom.snd _ _).comp (firstCentralizerProductEquiv i).symm.toMonoidHom

theorem firstCentralizerEvenPart_kernel (i : Omega) :
    (firstCentralizerEvenPart i).ker=residueCentralElementary {i} := by
  ext x
  constructor
  · intro hx
    let a := (firstCentralizerProductEquiv i).symm x
    have ha : a.2=1 := hx
    have he := (firstCentralizerProductEquiv i).apply_symm_apply x
    change a.1.val*a.2.val=x at he
    rw [ha,Subgroup.coe_one,mul_one] at he
    exact he ▸ a.1.prop
  · intro hx
    have he : (firstCentralizerProductEquiv i) (⟨x,hx⟩,1)=x := mul_one x
    have hi := (firstCentralizerProductEquiv i).symm_apply_apply (⟨x,hx⟩,1)
    rw [he] at hi
    exact congrArg Prod.snd hi

theorem firstCentralizerEvenPart_surjective (i : Omega) : Function.Surjective (firstCentralizerEvenPart i) := by
  intro x
  refine ⟨(firstCentralizerProductEquiv i) (1,x),?_⟩
  exact congrArg Prod.snd ((firstCentralizerProductEquiv i).symm_apply_apply (1,x))

/-- The singleton residue is the actual even centralizer, via the even representative. -/
def firstResidueEvenEquiv (i : Omega) : ResidueGroup {i} ≃* (firstCentralizerParity i).ker :=
  (QuotientGroup.quotientMulEquivOfEq (firstCentralizerEvenPart_kernel i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (firstCentralizerEvenPart_surjective i))

/-- The even representative embeds the actual singleton residue into the positive ray group. -/
def firstResiduePositiveEmbedding (i : Omega) : ResidueGroup {i} →* (rootGeneratedRayParity).ker :=
  { toFun := fun x => ⟨(firstResidueEvenEquiv i x).val.val,(firstResidueEvenEquiv i x).prop⟩
    map_one' := by
      apply Subtype.ext
      exact congrArg (fun x : (firstCentralizerParity i).ker => x.val.val)
        (map_one (firstResidueEvenEquiv i))
    map_mul' := fun x y => by
      apply Subtype.ext
      exact congrArg (fun x : (firstCentralizerParity i).ker => x.val.val)
        (map_mul (firstResidueEvenEquiv i) x y) }

theorem firstResiduePositiveEmbedding_injective (i : Omega) :
    Function.Injective (firstResiduePositiveEmbedding i) := by
  intro x y h
  apply (firstResidueEvenEquiv i).injective
  have he : (firstResidueEvenEquiv i x).val.val = (firstResidueEvenEquiv i y).val.val :=
    congrArg (fun z : (rootGeneratedRayParity).ker => z.val) h
  exact Subtype.ext (Subtype.ext he)

theorem firstCentralizerEvenPart_even (i : Omega) (x : (firstCentralizerParity i).ker) :
    firstCentralizerEvenPart i x.val=x := by
  have he : firstCentralizerProductEquiv i (1,x)=x.val := one_mul x.val
  have hi := congrArg Prod.snd ((firstCentralizerProductEquiv i).symm_apply_apply (1,x))
  rw [he] at hi
  exact hi

theorem firstResidueEvenEquiv_mk (i : Omega) (x : residueCentralizer {i}) :
    firstResidueEvenEquiv i (QuotientGroup.mk' (residueCentralElementary {i}) x)=
      firstCentralizerEvenPart i x := rfl

/-- The explicit section sends every odd centralizing element e to d e. -/
theorem firstCentralizerEvenPart_odd (i : Omega) (x : residueCentralizer {i})
    (hx : firstCentralizerParity i x=Multiplicative.ofAdd (1 : Bit)) :
    (firstCentralizerEvenPart i x).val=(firstCentralizerMarked i).val*x := by
  have hs : (firstCentralizerMarked i).val*(firstCentralizerMarked i).val=1 := by
    apply Subtype.ext
    have h := pow_orderOf_eq_one (distinguishedRootElement (.inl i))
    rw [distinguishedRootElement_order,pow_two] at h
    exact h
  have hp : firstCentralizerParity i ((firstCentralizerMarked i).val*x)=1 := by
    rw [map_mul,firstCentralizerParity_marked,hx]
    rfl
  let y : (firstCentralizerParity i).ker := ⟨(firstCentralizerMarked i).val*x,hp⟩
  have he : firstCentralizerProductEquiv i (firstCentralizerMarked i,y)=x := by
    change (firstCentralizerMarked i).val*((firstCentralizerMarked i).val*x)=x
    rw [← mul_assoc,hs,one_mul]
  have hi := congrArg Prod.snd ((firstCentralizerProductEquiv i).symm_apply_apply
    (firstCentralizerMarked i,y))
  rw [he] at hi
  exact congrArg Subtype.val hi

theorem firstCentralizerEvenPart_quotient (i : Omega) (x : residueCentralizer {i}) :
    QuotientGroup.mk' (residueCentralElementary {i}) (firstCentralizerEvenPart i x).val=
      QuotientGroup.mk' (residueCentralElementary {i}) x := by
  apply (firstResidueEvenEquiv i).injective
  rw [firstResidueEvenEquiv_mk,firstResidueEvenEquiv_mk,firstCentralizerEvenPart_even]

/-- The section preserves the action on the original residue points. -/
theorem firstCentralizerEvenPart_action (i : Omega) (g : residueCentralizer {i})
    (x : ResiduePoint {i}) : (firstCentralizerEvenPart i g).val • x=g • x := by
  have h := congrArg (fun q : ResidueGroup {i} => q • x)
    (firstCentralizerEvenPart_quotient i g)
  apply Subtype.ext
  exact (residueGroup_mk_smul_val {i} _ x).symm.trans
    ((congrArg Subtype.val h).trans (residueGroup_mk_smul_val {i} _ x))

/-- The centralizer in the actual positive group of the ambient odd marked involution. -/
def firstPositiveCentralizer (i : Omega) : Subgroup (rootGeneratedRayParity).ker :=
  (residueCentralizer {i}).comap (rootGeneratedRayParity).ker.subtype

def firstEvenCentralizerEquiv (i : Omega) :
    (firstCentralizerParity i).ker ≃* firstPositiveCentralizer i where
  toFun x := ⟨⟨x.val.val,x.prop⟩,x.val.prop⟩
  invFun x := ⟨⟨x.val.val,x.prop⟩,x.val.prop⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

/-- The actual singleton residue identifies with the centralizer inside the positive group. -/
def firstResiduePositiveCentralizerEquiv (i : Omega) :
    ResidueGroup {i} ≃* firstPositiveCentralizer i :=
  (firstResidueEvenEquiv i).trans (firstEvenCentralizerEquiv i)

def firstCentralizerDirectProduct (i : Omega) :
    residueCentralizer {i} ≃* residueCentralElementary {i} × firstPositiveCentralizer i :=
  (firstCentralizerProductEquiv i).symm.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (firstEvenCentralizerEquiv i))

end Atlas.Fischer
