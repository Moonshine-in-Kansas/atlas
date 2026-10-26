import Atlas.LinearGroups.ReeF4.RootTriangularBridge

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def carrierPermute (p : Equiv.Perm WeylCoordinate) (w : Carrier F) : Carrier F :=
  wilsonCoordinatesEquiv.symm (fun i j =>
    wilsonCoordinatesEquiv w (p.symm (i,j)).1 (p.symm (i,j)).2)

theorem coordinateCompatible_val {e : TraceZero F ≃ₗ[F] TraceZero F}
    {p : Equiv.Perm WeylCoordinate} (he : WeylCoordinateCompatible e p)
    (w : TraceZero F) : (e w).val = carrierPermute p w.val := by
  apply wilsonCoordinatesEquiv.injective
  funext i j
  simpa only [carrierPermute, LinearEquiv.apply_symm_apply, weylCoordinateRead] using he w (i,j)

theorem coordinateCompatible_inv_val {e : TraceZero F ≃ₗ[F] TraceZero F}
    {p : Equiv.Perm WeylCoordinate} (he : WeylCoordinateCompatible e p)
    (w : TraceZero F) : (e⁻¹ w).val = carrierPermute p.symm w.val := by
  apply wilsonCoordinatesEquiv.injective
  funext i j
  have h := he (e⁻¹ w) (p (i,j))
  simpa [carrierPermute, weylCoordinateRead] using h.symm

def alternatingShortFormula (m : ℕ) (k : Fin 4) (a b : F) (w : Carrier F) : Carrier F :=
  carrierPermute (alternatingShortPermutation k)
    (shortRootParameterFormula (theta F m).toRingHom a
      (shortRootCenterFormula (theta F m).toRingHom b
        (carrierPermute (alternatingShortPermutation k).symm w)))

def alternatingLongFormula (m : ℕ) (k : Fin 4) (u : F) (w : Carrier F) : Carrier F :=
  carrierPermute (alternatingLongPermutation k)
    (longSL2Formula u (theta F m u)
      (carrierPermute (alternatingLongPermutation k).symm w))

theorem alternatingShortFactor_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (k : Fin 4) (a b : F) (w : TraceZero F) :
    ((alternatingShortRootHom hcard k (shortRootParameters m hcard (a,b))).val w).val =
      alternatingShortFormula m k a b w.val := by
  let e := (alternatingShortPrefix (F := F) m k).val
  change (e (shortRootPairEquiv m hcard a b (e⁻¹ w))).val = _
  rw [coordinateCompatible_val (alternatingShortPrefix_compatible m k)]
  change carrierPermute _ (shortRootParameterFormula _ a
    (shortRootCenterFormula _ b (e⁻¹ w).val)) = _
  rw [coordinateCompatible_inv_val (alternatingShortPrefix_compatible m k)]
  rfl

theorem alternatingLongFactor_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (k : Fin 4) (u : F) (w : TraceZero F) :
    ((alternatingLongRootHom hcard k (Multiplicative.ofAdd u)).val w).val =
      alternatingLongFormula m k u w.val := by
  let e := (alternatingLongPrefix (F := F) m k).val
  change (e (longSL2Equiv u (theta F m u) (e⁻¹ w))).val = _
  rw [coordinateCompatible_val (alternatingLongPrefix_compatible m k)]
  change carrierPermute _ (longSL2Formula u (theta F m u) (e⁻¹ w).val) = _
  rw [coordinateCompatible_inv_val (alternatingLongPrefix_compatible m k)]
  rfl

def alternatingWordFormula (m : ℕ) (u : Fin 4 → F) (v : Fin 4 → F × F)
    (w : Carrier F) : Carrier F :=
  alternatingShortFormula m 0 (v 0).1 (v 0).2 (alternatingLongFormula m 0 (u 0)
  (alternatingShortFormula m 1 (v 1).1 (v 1).2 (alternatingLongFormula m 1 (u 1)
  (alternatingShortFormula m 2 (v 2).1 (v 2).2 (alternatingLongFormula m 2 (u 2)
  (alternatingShortFormula m 3 (v 3).1 (v 3).2 (alternatingLongFormula m 3 (u 3) w)))))))

theorem alternatingShortFactor_pair_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (k : Fin 4) (v : F × F) (w : TraceZero F) :
    ((alternatingShortRootHom hcard k (shortRootParameters m hcard v)).val w).val =
      alternatingShortFormula m k v.1 v.2 w.val :=
  alternatingShortFactor_val hcard k v.1 v.2 w

private theorem listProdFinFour {G : Type*} [Monoid G] (f : Fin 4 → G) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * f 3)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rfl

private theorem model_mul_apply (m : ℕ) (g h : Model F m) (w : TraceZero F) :
    (g*h).val w = g.val (h.val w) := rfl

set_option maxHeartbeats 2000000 in
-- Expand the eight actual factors before applying their coordinate formulas.
theorem alternatingRootWord_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (u : Fin 4 → F) (v : Fin 4 → F × F) (w : TraceZero F) :
    ((alternatingRootWord hcard u v).val w).val = alternatingWordFormula m u v w.val := by
  unfold alternatingRootWord
  rw [listProdFinFour]
  simp only [model_mul_apply, alternatingShortFactor_pair_val, alternatingLongFactor_val,
    alternatingWordFormula]

end Atlas.ReeF4
