import Atlas.LinearGroups.ReeF4.TorusDiagonal

/-! Preservation of the actual quadratic polynomial by the source torus;
reciprocal marked root weights suffice, without finite-field restrictions. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem torusBlock_norm (m : ℕ) (a b : Fˣ) (k : Fin 3)
    (x : SplitOctonion.Carrier F) :
    SplitOctonion.norm (fun j => (torusWeight (G := Fˣ) m a b (k,j) : F) * x j) =
      SplitOctonion.norm x := by
  have hp (j : Fin 8) :
      ((torusWeight (G := Fˣ) m a b (k,j) : F) * x j) *
        ((torusWeight (G := Fˣ) m a b (k,Fin.rev j) : F) * x (Fin.rev j)) = x j * x (Fin.rev j) := by
    rw [torusWeight_opposite m a b (k,j)]
    calc
      _ = ((torusWeight (G := Fˣ) m a b (k,j) : F) *
          (((torusWeight (G := Fˣ) m a b (k,j))⁻¹ : Fˣ) : F)) * (x j * x (Fin.rev j)) := by ring
      _ = _ := by simp
  simpa only [SplitOctonion.norm,
    show Fin.rev (0 : Fin 8) = 7 by decide,
    show Fin.rev (1 : Fin 8) = 6 by decide,
    show Fin.rev (2 : Fin 8) = 5 by decide,
    show Fin.rev (3 : Fin 8) = 4 by decide] using
    congrArg₂ (fun u v : F => u + v)
      (congrArg₂ (fun u v : F => u + v)
        (congrArg₂ (fun u v : F => u + v) (hp 0) (hp 1)) (hp 2)) (hp 3)

theorem torusFormula_quadratic (m : ℕ) (a b : Fˣ) (w : Carrier F) :
    quadraticTrace (rootDiagonalFormula (torusWeight (G := Fˣ) m a b) w) = quadraticTrace w := by
  simp only [quadraticTrace, rootDiagonalFormula, torusBlock_norm]

theorem torusEquiv_quadratic (m : ℕ) (a b : Fˣ) (w : TraceZero F) :
    traceZeroQuadratic (torusEquiv m a b w) = traceZeroQuadratic w :=
  torusFormula_quadratic m a b w.val

end Atlas.ReeF4
