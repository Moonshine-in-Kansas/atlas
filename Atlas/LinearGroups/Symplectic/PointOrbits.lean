import Atlas.LinearGroups.Symplectic.PointGeometry

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- Orthogonal lines other than the base line form a full point-stabilizer orbit. -/
theorem orthogonal_stabilizer_transitive (n : ℕ) (p x y : Points (n+2) F)
    (hx : p ≠ x) (hy : p ≠ y) (hox : Orthogonal p x) (hoy : Orthogonal p y) :
    ∃ g : MulAction.stabilizer (PSp (n+2) F) p, g • x = y := by
  obtain ⟨a,hap,hax⟩ := normalize_orthogonal_pair n p x hx hox
  obtain ⟨b,hbp,hby⟩ := normalize_orthogonal_pair n p y hy hoy
  have hp : (b⁻¹*a) • p = p := by rw [mul_smul,hap,← hbp,inv_smul_smul]
  have hxy : (b⁻¹*a) • x = y := by rw [mul_smul,hax,← hby,inv_smul_smul]
  exact ⟨⟨projection (b⁻¹*a),hp⟩,hxy⟩

/-- Nonorthogonal lines form the other full point-stabilizer orbit. -/
theorem nonorthogonal_stabilizer_transitive (n : ℕ) (p x y : Points (n+1) F)
    (hox : ¬ Orthogonal p x) (hoy : ¬ Orthogonal p y) :
    ∃ g : MulAction.stabilizer (PSp (n+1) F) p, g • x = y := by
  obtain ⟨a,hap,hax⟩ := normalize_nonorthogonal_pair n p x hox
  obtain ⟨b,hbp,hby⟩ := normalize_nonorthogonal_pair n p y hoy
  have hp : (b⁻¹*a) • p = p := by rw [mul_smul,hap,← hbp,inv_smul_smul]
  have hxy : (b⁻¹*a) • x = y := by rw [mul_smul,hax,← hby,inv_smul_smul]
  exact ⟨⟨projection (b⁻¹*a),hp⟩,hxy⟩

/-- The three geometric classes are the base line, its punctured perp, and its complement. -/
def suborbitIndex (p x : Points n F) : Fin 3 := by
  classical
  exact if x=p then 0 else if Orthogonal p x then 1 else 2

@[simp] theorem suborbitIndex_self (p : Points n F) : suborbitIndex p p = 0 := by
  simp [suborbitIndex]

theorem suborbitIndex_invariant (p x : Points n F)
    (g : MulAction.stabilizer (PSp n F) p) : suborbitIndex p (g • x) = suborbitIndex p x := by
  classical
  have hgp : g.val • p = p := g.prop
  have he : g.val • x = p ↔ x=p := by
    simpa only [hgp] using (show g.val • x = g.val • p ↔ x=p from smul_left_cancel_iff g.val)
  have ho : Orthogonal p (g.val • x) ↔ Orthogonal p x := by
    simpa only [hgp] using projective_orthogonal_smul g.val p x
  change suborbitIndex p (g.val • x) = _
  simp only [suborbitIndex,he,ho]

theorem suborbitIndex_transitive (hn : 2 ≤ n) (p x y : Points n F)
    (h : suborbitIndex p x = suborbitIndex p y) :
    ∃ g : MulAction.stabilizer (PSp n F) p, g • x = y := by
  classical
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  by_cases hx : x=p
  · have hy : y=p := by
      by_contra hy
      by_cases hoy : Orthogonal p y <;> simp [suborbitIndex,hx,hy,hoy] at h
    subst x; subst y
    exact ⟨1,one_smul _ _⟩
  · by_cases hy : y=p
    · by_cases hox : Orthogonal p x <;> simp [suborbitIndex,hx,hy,hox] at h
    · by_cases hox : Orthogonal p x
      · by_cases hoy : Orthogonal p y
        · exact orthogonal_stabilizer_transitive k p x y (Ne.symm hx) (Ne.symm hy) hox hoy
        · simp [suborbitIndex,hx,hy,hox,hoy] at h
      · by_cases hoy : Orthogonal p y
        · simp [suborbitIndex,hx,hy,hox,hoy] at h
        · exact nonorthogonal_stabilizer_transitive (k+1) p x y hox hoy

/-- Equality of the geometric classes is exactly equality of point-stabilizer orbits. -/
theorem stabilizer_orbit_iff (hn : 2 ≤ n) (p x y : Points n F) :
    y ∈ MulAction.orbit (MulAction.stabilizer (PSp n F) p) x ↔
      suborbitIndex p x = suborbitIndex p y := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (suborbitIndex_invariant p x g).symm
  · exact suborbitIndex_transitive hn p x y

end Atlas.Symplectic
