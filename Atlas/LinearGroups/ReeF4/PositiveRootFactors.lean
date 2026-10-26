import Atlas.LinearGroups.ReeF4.AlternatingRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
abbrev positiveShortFactor {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) (a b : F) : Model F m :=
  alternatingShortRootHom hcard k (shortRootParameters m hcard (a,b))
abbrev positiveLongFactor {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) (u : F) : Model F m :=
  alternatingLongRootHom hcard k (Multiplicative.ofAdd u)
end Atlas.ReeF4
