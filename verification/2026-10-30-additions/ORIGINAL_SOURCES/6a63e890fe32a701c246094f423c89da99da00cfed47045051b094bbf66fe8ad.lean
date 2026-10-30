import Atlas.LinearGroups.ReeF4.ChartLongConjugate0
import Atlas.LinearGroups.ReeF4.ChartLongConjugate1
import Atlas.LinearGroups.ReeF4.ChartLongConjugate2
import Atlas.LinearGroups.ReeF4.ChartLongConjugate3
import Atlas.LinearGroups.ReeF4.ChartShortConjugate0
import Atlas.LinearGroups.ReeF4.ChartShortConjugate1
import Atlas.LinearGroups.ReeF4.ChartShortConjugate2
import Atlas.LinearGroups.ReeF4.ChartTerminalEndpoints
import Atlas.LinearGroups.ReeF4.SpecialA4Chart
import Atlas.GroupTheory.SevenPivotFactorization

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def chartTransportProduct {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (a : Fin 4 → F) (p : Fin 3 → F×F) : Model F m :=
  (negativeA2ChartWord hcard (a 0))⁻¹ *
  ((negativeC3ChartWord hcard (p 0))⁻¹ *
  ((negativeA2ChartWord hcard (a 1))⁻¹ *
  ((negativeC3ChartWord hcard (p 1))⁻¹ *
  ((negativeA2ChartWord hcard (a 2))⁻¹ *
  ((negativeC3ChartWord hcard (p 2))⁻¹ * (negativeA2ChartWord hcard (a 3))⁻¹)))))

def chartUnipotentWord {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (a : Fin 4 → F) (p : Fin 3 → F×F) : Model F m :=
  (chartLongConjugate hcard 0 (a 0))⁻¹ *
  ((chartShortConjugate hcard 0 (p 0).1 (p 0).2)⁻¹ *
  ((chartLongConjugate hcard 1 (a 1))⁻¹ *
  ((chartShortConjugate hcard 1 (p 1).1 (p 1).2)⁻¹ *
  ((chartLongConjugate hcard 2 (a 2))⁻¹ *
  ((chartShortConjugate hcard 2 (p 2).1 (p 2).2)⁻¹ * (chartLongConjugate hcard 3 (a 3))⁻¹)))))

private theorem negativeA2ChartWord_model {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) :
    negativeA2ChartWord hcard a=weylSigmaModel m * modelLongSL2RootHom hcard (Multiplicative.ofAdd a) := by
  apply Subtype.ext
  rfl
private theorem negativeC3ChartWord_model {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (p : F×F) :
    negativeC3ChartWord hcard p=weylRhoModel m * shortRootModelEmbedding hcard (shortRootParameters m hcard p) := by
  apply Subtype.ext
  rfl

theorem chartTransportProduct_factorization {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (a : Fin 4 → F) (p : Fin 3 → F×F) :
    chartTransportProduct hcard a p=chartUnipotentWord hcard a p * chartShortPrefix m 3 := by
  have hr : (weylRhoModel (F := F) m)⁻¹=weylRhoModel m := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change weylRho * weylRho = (1 : Atlas.Albert.TraceZero F ≃ₗ[F] Atlas.Albert.TraceZero F)
    simpa only [pow_two] using weylRho_square (F := F)
  have hs : (weylSigmaModel (F := F) m)⁻¹=weylSigmaModel m := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change weylSigma * weylSigma = (1 : Atlas.Albert.TraceZero F ≃ₗ[F] Atlas.Albert.TraceZero F)
    simpa only [pow_two] using weylSigma_square (F := F)
  simp only [chartTransportProduct,negativeA2ChartWord_model,negativeC3ChartWord_model]
  rw [Atlas.GroupTheory.sevenPivotFactorizationInverse _ _ _ _ _ _ _ _ _ hr hs]
  simp only [chartUnipotentWord,chartLongConjugate,chartShortConjugate,chartLongPrefix,
    chartShortPrefix,pow_zero,pow_one,one_mul,mul_one,inv_one,mul_assoc]

theorem chartUnipotentWord_mem {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (a : Fin 4 → F) (p : Fin 3 → F×F) :
    chartUnipotentWord hcard a p∈positiveRootSubgroup hcard := by
  unfold chartUnipotentWord
  rw [chartLongConjugate_eq_positive_0,chartLongConjugate_eq_positive_1,
    chartLongConjugate_eq_positive_2,chartLongConjugate_eq_positive_3,
    chartShortConjugate_eq_positive_0,chartShortConjugate_eq_positive_1,
    chartShortConjugate_eq_positive_2]
  have hl (k : Fin 4) (u : F) : positiveLongFactor hcard k u ∈ positiveRootSubgroup hcard :=
    alternatingLongRoot_mem_positiveRootSubgroup hcard k (Multiplicative.ofAdd u)
  have hs (k : Fin 4) (u v : F) : positiveShortFactor hcard k u v ∈ positiveRootSubgroup hcard :=
    alternatingShortRoot_mem_positiveRootSubgroup hcard k (shortRootParameters m hcard (u,v))
  exact (positiveRootSubgroup hcard).mul_mem
    ((positiveRootSubgroup hcard).inv_mem (hl 3 (a 0)))
    ((positiveRootSubgroup hcard).mul_mem
      ((positiveRootSubgroup hcard).inv_mem (hs 3 (p 0).1 (p 0).2))
      ((positiveRootSubgroup hcard).mul_mem
        ((positiveRootSubgroup hcard).inv_mem (hl 2 (a 1)))
        ((positiveRootSubgroup hcard).mul_mem
          ((positiveRootSubgroup hcard).inv_mem (hs 2 (p 1).1 (p 1).2))
          ((positiveRootSubgroup hcard).mul_mem
            ((positiveRootSubgroup hcard).inv_mem (hl 1 (a 2)))
            ((positiveRootSubgroup hcard).mul_mem
              ((positiveRootSubgroup hcard).inv_mem (hs 1 (p 2).1 (p 2).2))
              ((positiveRootSubgroup hcard).inv_mem (hl 0 (a 3))))))))

private theorem chart9_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 25) :
    ((normalizedChart9Equiv hcard).symm p).val=
      ((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val := by
  have he : a4ChartWord hcard p.1=negativeA2ChartWord hcard p.1 := by
    apply Subtype.ext
    rfl
  change ((a4ChartWord hcard p.1)⁻¹).val p.2.val=_
  rw [he]
private theorem chart25_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 24) :
    ((normalizedChart25Equiv hcard).symm p).val=
      ((negativeC3ChartWord hcard p.1)⁻¹).val p.2.val := rfl
private theorem chart24_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 7) :
    ((normalizedChart24Equiv hcard).symm p).val=
      ((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val := rfl
private theorem chart7_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 4) :
    ((normalizedChart7Equiv hcard).symm p).val=
      ((negativeC3ChartWord hcard p.1)⁻¹).val p.2.val := rfl
private theorem chart4_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : F × NormalizedSpecialChart (F := F) m 19) :
    ((normalizedChart4Equiv hcard).symm p).val=
      ((negativeA2ChartWord hcard p.1)⁻¹).val p.2.val := rfl
private theorem chart19_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : (F×F) × NormalizedSpecialChart (F := F) m 18) :
    ((normalizedChart19Equiv hcard).symm p).val=
      ((negativeC3ChartWord hcard p.1)⁻¹).val p.2.val := rfl
private theorem chart18_symm_val {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) :
    ((normalizedChart18Equiv hcard).symm a).val=(nextChartPoint hcard a).val := rfl

theorem chart9_transport_exists {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (z : NormalizedSpecialChart (F := F) m 9) :
    ∃ (a : Fin 4 → F) (p : Fin 3 → F×F),
      (chartTransportProduct hcard a p).val (rootVector (0,0))=z.val := by
  obtain ⟨⟨a0,z25⟩,h9⟩ := (normalizedChart9Equiv hcard).symm.surjective z
  have e9 : z.val=((negativeA2ChartWord hcard a0)⁻¹).val z25.val :=
    (congrArg Subtype.val h9).symm.trans (chart9_symm_val hcard (a0,z25))
  obtain ⟨⟨p0,z24⟩,h25⟩ := (normalizedChart25Equiv hcard).symm.surjective z25
  have e25 : z25.val=((negativeC3ChartWord hcard p0)⁻¹).val z24.val :=
    (congrArg Subtype.val h25).symm.trans (chart25_symm_val hcard (p0,z24))
  obtain ⟨⟨a1,z7⟩,h24⟩ := (normalizedChart24Equiv hcard).symm.surjective z24
  have e24 : z24.val=((negativeA2ChartWord hcard a1)⁻¹).val z7.val :=
    (congrArg Subtype.val h24).symm.trans (chart24_symm_val hcard (a1,z7))
  obtain ⟨⟨p1,z4⟩,h7⟩ := (normalizedChart7Equiv hcard).symm.surjective z7
  have e7 : z7.val=((negativeC3ChartWord hcard p1)⁻¹).val z4.val :=
    (congrArg Subtype.val h7).symm.trans (chart7_symm_val hcard (p1,z4))
  obtain ⟨⟨a2,z19⟩,h4⟩ := (normalizedChart4Equiv hcard).symm.surjective z4
  have e4 : z4.val=((negativeA2ChartWord hcard a2)⁻¹).val z19.val :=
    (congrArg Subtype.val h4).symm.trans (chart4_symm_val hcard (a2,z19))
  obtain ⟨⟨p2,z18⟩,h19⟩ := (normalizedChart19Equiv hcard).symm.surjective z19
  have e19 : z19.val=((negativeC3ChartWord hcard p2)⁻¹).val z18.val :=
    (congrArg Subtype.val h19).symm.trans (chart19_symm_val hcard (p2,z18))
  obtain ⟨a3,h18⟩ := (normalizedChart18Equiv hcard).symm.surjective z18
  have e18 : z18.val=(nextChartPoint hcard a3).val :=
    (congrArg Subtype.val h18).symm.trans (chart18_symm_val hcard a3)
  refine ⟨![a0,a1,a2,a3],![p0,p1,p2],?_⟩
  simp only [chartTransportProduct,modelProduct_apply,Fin.reduceFinMk,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,chartTerminalWord_inverse_root]
  rw [e9,e25,e24,e7,e4,e19,e18]

/-- Every normalized top-chart vector is obtained from A4 by an actual U element. -/
theorem positiveRoot_chart9_orbit {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (z : NormalizedSpecialChart (F := F) m 9) :
    ∃ g : positiveRootSubgroup hcard, g.val.val (rootVector (0,7))=z.val := by
  obtain ⟨a,p,hz⟩ := chart9_transport_exists hcard z
  refine ⟨⟨chartUnipotentWord hcard a p,chartUnipotentWord_mem hcard a p⟩,?_⟩
  rw [chartTransportProduct_factorization,modelProduct_apply,chartFinalWeyl_root] at hz
  exact hz

/-- U acts transitively on actual normalized vectors, not just their lines. -/
theorem positiveRoot_chart9_transitive {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (z z' : NormalizedSpecialChart (F := F) m 9) :
    ∃ g : positiveRootSubgroup hcard, g.val.val z.val=z'.val := by
  obtain ⟨u,hu⟩ := positiveRoot_chart9_orbit hcard z
  obtain ⟨v,hv⟩ := positiveRoot_chart9_orbit hcard z'
  refine ⟨v*u⁻¹,?_⟩
  rw [←hu]
  change v.val.val (u.val.val.symm (u.val.val (rootVector (0,7))))=z'.val
  rw [LinearEquiv.symm_apply_apply]
  exact hv

end Atlas.ReeF4
