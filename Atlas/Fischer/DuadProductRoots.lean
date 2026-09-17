import Atlas.Fischer.DuadOctadicOrthogonality
import Atlas.Fischer.OctadicAlgebraAutomorphisms
import Atlas.Fischer.ConjugateRootTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual products of the two calibrated octadic character families. No sign
function or coordinate formula is stipulated in this definition. -/
def duadOctadicProduct {F G : Octad} (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) : Coordinates :=
  product (octadicRoot Q χ) (octadicRoot R ψ)

theorem duadOctadicProduct_eq_reflection {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    duadOctadicProduct Q R χ ψ=octadicReflection Q χ (octadicRoot R ψ) := by
  rw [octadicReflection_apply,rootMap,duadPair_octadicRoot_orthogonal F G hFG,
    zero_smul,sub_zero]
  exact product_comm _ _

theorem duadOctadicProduct_isRoot {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) : IsRoot (duadOctadicProduct Q R χ ψ) := by
  rw [duadOctadicProduct_eq_reflection hFG]
  exact isRoot_conjugate_transport (octadicReflection Q χ)
    (fun x y => (octadicReflection_product Q χ x y).symm)
    (octadicReflection_hermitian Q χ) _ (octadicRoot_isRoot R ψ)

theorem duadOctadicProduct_rootMap_conjugation {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) (x : Coordinates) :
    rootMap (duadOctadicProduct Q R χ ψ) x=
      octadicReflection Q χ (octadicReflection R ψ (octadicReflection Q χ x)) := by
  have h := rootMap_covariance_conjugate (octadicReflection Q χ)
    (fun u v => (octadicReflection_product Q χ u v).symm)
    (octadicReflection_hermitian Q χ) (octadicRoot R ψ) (octadicReflection Q χ x)
  rw [octadicReflection_involutive,← duadOctadicProduct_eq_reflection hFG] at h
  exact h

theorem duadOctadicProduct_antiunitary {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    RootMapAntiunitary (duadOctadicProduct Q R χ ψ) := by
  rw [duadOctadicProduct_eq_reflection hFG]
  exact rootMapAntiunitary_conjugate_transport (octadicReflection Q χ)
    (fun x y => (octadicReflection_product Q χ x y).symm)
    (octadicReflection_hermitian Q χ) _ (octadicRoot_antiunitary R ψ)

theorem duadOctadicProduct_algebra_package {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    IsRoot (duadOctadicProduct Q R χ ψ) ∧ RootMapAntiunitary (duadOctadicProduct Q R χ ψ) ∧
    Function.Involutive (rootMap (duadOctadicProduct Q R χ ψ)) ∧
    ∀ x y, rootMap (duadOctadicProduct Q R χ ψ) (product x y)=
      product (rootMap (duadOctadicProduct Q R χ ψ) x) (rootMap (duadOctadicProduct Q R χ ψ) y) := by
  have hr := duadOctadicProduct_isRoot hFG Q R χ ψ
  have ha := duadOctadicProduct_antiunitary hFG Q R χ ψ
  exact ⟨hr,ha,rootMap_algebra_criterion _ hr.1 hr.2 ha⟩

end Atlas.Fischer
