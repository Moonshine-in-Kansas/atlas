import Atlas.Rudvalis.BinaryOrthogonality
import Atlas.Rudvalis.UniformBlockLinear

/-! Literal three-block binary glue on labels 1,5,4 (coordinate rows 1,2,4). -/
namespace Atlas.Rudvalis
open scoped BigOperators

abbrev FrameGlueCoordinate := Fin 3 × E
abbrev FrameGlueWord := FrameGlueCoordinate → Bit
abbrev FrameGlueParameters := (Fin 3 → Bit) × (Fin 2 → E) × E

def frameGluePoint (i : Fin 3) : Point :=
  ⟨binaryLabel (![1,5,4] i),by fin_cases i <;> decide⟩

def frameGlueLinear (u : Fin 2 → E) (i : Fin 3) : E := ![u 0,u 1,u 0+u 1] i

def frameGlueNormalMap : FrameGlueParameters →ₗ[Bit] FrameGlueWord where
  toFun a z := a.1 z.1+dot (frameGlueLinear a.2.1 z.1) z.2+theta (frameGluePoint z.1) a.2.2 z.2
  map_add' a b := by
    funext z
    rcases z with ⟨i,x⟩
    fin_cases i <;> simp [frameGlueLinear,theta,quadratic,dot,eta,Fin.sum_univ_succ] <;> ring
  map_smul' b a := by
    funext z
    rcases z with ⟨i,x⟩
    fin_cases i <;> simp [frameGlueLinear,theta,quadratic,dot,eta,Fin.sum_univ_succ] <;> ring

def frameGlueCode : Submodule Bit FrameGlueWord := frameGlueNormalMap.range

theorem frameGlueNormalMap_injective : Function.Injective frameGlueNormalMap := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  have h (i : Fin 3) : a.1 i=0 ∧ frameGlueLinear a.2.1 i+eta (frameGluePoint i) a.2.2=0 ∧ a.2.2=0 := by
    apply affine_quadratic_zero
    intro x
    have hx := congrFun ha (i,x)
    change a.1 i+dot (frameGlueLinear a.2.1 i) x+theta (frameGluePoint i) a.2.2 x=0 at hx
    simpa [theta,dot_add_left,add_assoc,add_comm,add_left_comm] using hx
  have hc : a.2.2=0 := (h 0).2.2
  have hε : a.1=0 := funext (fun i => (h i).1)
  have hu : a.2.1=0 := by
    funext i
    fin_cases i
    · simpa [frameGlueLinear,hc,eta] using (h 0).2.1
    · simpa [frameGlueLinear,hc,eta] using (h 1).2.1
  exact Prod.ext hε (Prod.ext hu hc)

theorem frameGlueCode_finrank : Module.finrank Bit frameGlueCode=12 := by
  rw [frameGlueCode,LinearMap.finrank_range_of_inj frameGlueNormalMap_injective]
  simp [FrameGlueParameters,E,Module.finrank_prod,Module.finrank_pi_fintype]

abbrev FrameGlueGeneratorIndex := Fin 3 ⊕ ((Fin 2 × Fin 3) ⊕ Fin 3)

def frameGlueParameterGenerator : FrameGlueGeneratorIndex → FrameGlueParameters
  | .inl i => (Pi.single i 1,0,0)
  | .inr (.inl (i,j)) => (0,Pi.single i (Pi.single j 1),0)
  | .inr (.inr j) => (0,0,Pi.single j 1)

def frameGlueParameterCoefficient (a : FrameGlueParameters) : FrameGlueGeneratorIndex → Bit
  | .inl i => a.1 i
  | .inr (.inl (i,j)) => a.2.1 i j
  | .inr (.inr j) => a.2.2 j

theorem frameGlueParameter_expansion (a : FrameGlueParameters) :
    (∑ i,frameGlueParameterCoefficient a i • frameGlueParameterGenerator i)=a := by
  classical
  apply Prod.ext
  · ext i
    simp [frameGlueParameterCoefficient,frameGlueParameterGenerator,Fintype.sum_sum_type,
      Fintype.sum_prod_type,Pi.single_apply,Prod.fst_sum,Finset.sum_apply]
  · apply Prod.ext
    · ext i j
      simp [frameGlueParameterCoefficient,frameGlueParameterGenerator,Fintype.sum_sum_type,
        Fintype.sum_prod_type,Pi.single_apply,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply]
      fin_cases i <;> simp [Finset.sum_apply,Pi.single_apply,mul_ite]
    · ext j
      simp [frameGlueParameterCoefficient,frameGlueParameterGenerator,Fintype.sum_sum_type,
        Fintype.sum_prod_type,Pi.single_apply,Prod.snd_sum,Finset.sum_apply]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem frameGlueGenerator_orthogonal (i j : FrameGlueGeneratorIndex) :
    Atlas.Codes.binaryDot (frameGlueNormalMap (frameGlueParameterGenerator i))
      (frameGlueNormalMap (frameGlueParameterGenerator j))=0 := by
  decide +kernel +revert

theorem frameGlueCode_self_orthogonal :
    frameGlueCode≤(Atlas.Codes.binaryDot (ι := FrameGlueCoordinate)).orthogonal frameGlueCode := by
  rintro v ⟨a,rfl⟩ w ⟨b,rfl⟩
  rw [← frameGlueParameter_expansion a,← frameGlueParameter_expansion b]
  simp [map_sum,map_smul,frameGlueGenerator_orthogonal]

theorem frameGlueCode_self_dual :
    (Atlas.Codes.binaryDot (ι := FrameGlueCoordinate)).orthogonal frameGlueCode=frameGlueCode := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq frameGlueCode_self_orthogonal
  rw [LinearMap.BilinForm.finrank_orthogonal Atlas.Codes.binaryDot_nondegenerate,frameGlueCode_finrank]
  simp [FrameGlueCoordinate,E]

end Atlas.Rudvalis
