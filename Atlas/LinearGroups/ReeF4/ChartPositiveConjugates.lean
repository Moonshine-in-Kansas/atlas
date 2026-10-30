import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.AlternatingFactorSimp
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
import Atlas.LinearGroups.ReeF4.ElementaryRootWords

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def chartLongPrefix (m k : ℕ) : Model F m := (weylSigmaModel m * weylRhoModel m)^k

def chartShortPrefix (m k : ℕ) : Model F m := chartLongPrefix m k * weylSigmaModel m

def chartLongPermutation (k : ℕ) : Equiv.Perm WeylCoordinate :=
  (weylSigmaPermutation * weylRhoPermutation)^k

def chartShortPermutation (k : ℕ) : Equiv.Perm WeylCoordinate :=
  chartLongPermutation k * weylSigmaPermutation

theorem chartLongPrefix_compatible (m k : ℕ) :
    WeylCoordinateCompatible (chartLongPrefix (F := F) m k).val (chartLongPermutation k) :=
  weylCoordinateCompatible_pow
    (weylCoordinateCompatible_mul weylSigma_coordinateCompatible weylRho_coordinateCompatible) k

theorem chartShortPrefix_compatible (m k : ℕ) :
    WeylCoordinateCompatible (chartShortPrefix (F := F) m k).val (chartShortPermutation k) :=
  weylCoordinateCompatible_mul (chartLongPrefix_compatible m k) weylSigma_coordinateCompatible

def carrierConjugate (p : Equiv.Perm WeylCoordinate) (f : Carrier F → Carrier F)
    (w : Carrier F) : Carrier F := carrierPermute p (f (carrierPermute p.symm w))

theorem modelConjugate_formula {m : ℕ} (g h : Model F m) (p : Equiv.Perm WeylCoordinate)
    (hg : WeylCoordinateCompatible g.val p) (f : Carrier F → Carrier F)
    (hf : ∀ w : TraceZero F, (h.val w).val=f w.val) (w : TraceZero F) :
    ((g*h*g⁻¹).val w).val=carrierConjugate p f w.val := by
  simp only [modelProduct_apply]
  rw [coordinateCompatible_val hg,hf]
  change carrierPermute p (f (((g.val)⁻¹ w).val)) = _
  rw [coordinateCompatible_inv_val hg]
  rfl

def chartLongConjugate {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (k : ℕ) (a : F) : Model F m :=
  chartLongPrefix m k * modelLongSL2RootHom hcard (Multiplicative.ofAdd a) * (chartLongPrefix m k)⁻¹

def chartShortConjugate {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (k : ℕ) (a b : F) : Model F m :=
  chartShortPrefix m k * shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b)) *
    (chartShortPrefix m k)⁻¹

theorem chartLongConjugate_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (k : ℕ) (a : F)
    (w : TraceZero F) : ((chartLongConjugate hcard k a).val w).val=
    carrierConjugate (chartLongPermutation k) (longSL2Formula a (theta F m a)) w.val :=
  modelConjugate_formula _ _ _ (chartLongPrefix_compatible m k) _ (fun _ => rfl) w

theorem chartShortConjugate_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (k : ℕ) (a b : F)
    (w : TraceZero F) : ((chartShortConjugate hcard k a b).val w).val=
    carrierConjugate (chartShortPermutation k)
      (shortRootParameterFormula (theta F m).toRingHom a ∘
       shortRootCenterFormula (theta F m).toRingHom b) w.val :=
  modelConjugate_formula _ _ _ (chartShortPrefix_compatible m k) _ (fun _ => rfl) w

end Atlas.ReeF4
