# Principal compiled theorem statements

Generated from the successful compiled-declaration audit at source commit
`935474b0c3678e053e1152a49ed6593bd8ad44c9`. These are verbatim elaborated `#check @name`
outputs, with explicit parameters, typeclasses and universes; proof bodies are omitted.
The selections are the catalogue's primary order and simplicity interfaces.
Exact-exception and other structural results remain in the catalogue and full audit.
Definitions of the named models are linked through their source files; this is a
signature reference, not a self-contained definition of every dependency.

The source-bound [audit](AUDIT.md) records trust and verification scope.
Regenerate using `ruby verification/statements.rb refresh`.

## C_p

Model: `Atlas.Families.Cyclic.Model` ([source](Atlas/Families/Cyclic/Basic.lean)).

### Order

`Atlas.Families.Cyclic.card` — [source](Atlas/Families/Cyclic/Basic.lean).

```lean
Atlas.Families.Cyclic.card : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    @Eq.{1} Nat (Nat.card.{0} (Atlas.Families.Cyclic.Model m)) (Atlas.Families.Cyclic.order m)
```

### Simplicity

`Atlas.Families.Cyclic.isSimpleGroup` — [source](Atlas/Families/Cyclic/Basic.lean).

```lean
Atlas.Families.Cyclic.isSimpleGroup : ∀ (p : Nat),
  Atlas.Families.Cyclic.IsAdmissible p →
    @IsSimpleGroup.{0} (Atlas.Families.Cyclic.Model p)
      (@Multiplicative.group.{0} (ZMod p)
        (@AddGroupWithOne.toAddGroup.{0} (ZMod p)
          (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))
```

## A_n

Model: `Atlas.Families.Alternating.Model` ([source](Atlas/Families/Alternating/Basic.lean)).

### Order

`Atlas.Families.Alternating.card_factorial` — [source](Atlas/Families/Alternating/Basic.lean).

```lean
Atlas.Families.Alternating.card_factorial : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    @Eq.{1} Nat (Nat.card.{0} (Atlas.Families.Alternating.Model n))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n.factorial
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
```

### Simplicity

`Atlas.Families.Alternating.isSimpleGroup` — [source](Atlas/Families/Alternating/Basic.lean).

```lean
Atlas.Families.Alternating.isSimpleGroup : ∀ (n : Nat),
  Atlas.Families.Alternating.IsAdmissible n →
    @IsSimpleGroup.{0} (Atlas.Families.Alternating.Model n)
      (@Subgroup.toGroup.{0} (Equiv.Perm.{1} (Fin n)) (@Equiv.Perm.permGroup.{0} (Fin n))
        (@alternatingGroup.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)))
```

## PSL_n(q)

Model: `Matrix.ProjectiveSpecialLinearGroup` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean)).

### Order

`Atlas.card_psl_factor` — [source](Atlas/LinearGroups/ProjectiveSpecialLinear.lean).

```lean
@Atlas.card_psl_factor.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] (n : Nat)
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] [Finite.{u_1 + 1} F],
  @Eq.{1} Nat
    (Nat.card.{u_1}
      (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
        (@Field.toCommRing.{u_1} F inst)))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (∏
          i ∈
            @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n,
          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) i)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (n.gcd
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simplicity

`Atlas.psl_simple_iff` — [source](Atlas/LinearGroups/PSLFamily.lean).

```lean
@Atlas.psl_simple_iff.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    Iff
      (@IsSimpleGroup.{u_1}
        (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
          (@Field.toCommRing.{u_1} F inst))
        (@QuotientGroup.Quotient.group.{u_1}
          (@Matrix.SpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
            (@Field.toCommRing.{u_1} F inst))
          (@Matrix.SpecialLinearGroup.instGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
            (@Field.toCommRing.{u_1} F inst))
          (@Subgroup.center.{u_1}
            (@Matrix.SpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
              (@Field.toCommRing.{u_1} F inst))
            (@Matrix.SpecialLinearGroup.instGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
              (@Field.toCommRing.{u_1} F inst)))
          ⋯))
      (And
        (@Ne.{1} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat n (Nat.card.{u_1} F))
          (@Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@Ne.{1} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat n (Nat.card.{u_1} F))
          (@Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
```

## B_n(q) / PΩ(2n+1,q)

Model: `Atlas.Orthogonal.B` ([source](Atlas/LinearGroups/Orthogonal/BFamily.lean)).

### Order

`Atlas.Orthogonal.B_card_all_rank` — [source](Atlas/LinearGroups/Orthogonal/BAllRanks.lean).

```lean
@Atlas.Orthogonal.B_card_all_rank.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Orthogonal.B.{u_1} n F inst)) (Atlas.Orthogonal.B_order n (Nat.card.{u_1} F))
```

### Simplicity

`Atlas.Orthogonal.B_simple_all_rank` — [source](Atlas/LinearGroups/Orthogonal/BAllRanksConstruction.lean).

```lean
@Atlas.Orthogonal.B_simple_all_rank.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  Atlas.Orthogonal.B_good n (Nat.card.{u_1} F) →
    @IsSimpleGroup.{u_1} (@Atlas.Orthogonal.B.{u_1} n F inst)
      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, u_1} F (Atlas.Orthogonal.VectorB.{u_1} n F) inst
        (@Prod.instAddCommGroup.{u_1, u_1} (Atlas.Orthogonal.VectorD.{u_1} n F) F
          (@Pi.addCommGroup.{0, u_1} (Atlas.Orthogonal.Index n) (fun a => F) fun i =>
            @Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst)))
          (@Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
        (@Prod.instModule.{u_1, u_1, u_1} F (Atlas.Orthogonal.VectorD.{u_1} n F) F
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1} (Atlas.Orthogonal.Index n) (fun a => F) fun i =>
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Semiring.toAddCommMonoid.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Atlas.Orthogonal.Index n) F F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
          (@Semiring.toModule.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Atlas.Orthogonal.formB.{u_1} n F (@Field.toCommRing.{u_1} F inst)))
```

## C_n(q) / PSp(2n,q)

Model: `Atlas.Symplectic.PSp` ([source](Atlas/LinearGroups/Symplectic/Basic.lean)).

### Order

`Atlas.Symplectic.card_psp` — [source](Atlas/LinearGroups/Symplectic/ProjectiveOrder.lean).

```lean
@Atlas.Symplectic.card_psp.{u_1} : ∀ {n : Nat} {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Symplectic.PSp.{u_1} n F (@Field.toCommRing.{u_1} F inst)))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Atlas.Symplectic.orderNumerator n (Nat.card.{u_1} F))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simplicity

`Atlas.Symplectic.simple_of_good` — [source](Atlas/LinearGroups/Symplectic/Simplicity.lean).

```lean
@Atlas.Symplectic.simple_of_good.{u_1} : ∀ {n : Nat} {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F],
  Atlas.Symplectic.Good n (Nat.card.{u_1} F) →
    @IsSimpleGroup.{u_1} (@Atlas.Symplectic.PSp.{u_1} n F (@Field.toCommRing.{u_1} F inst))
      (@QuotientGroup.Quotient.group.{u_1} (@Atlas.Symplectic.Sp.{u_1} n F (@Field.toCommRing.{u_1} F inst))
        (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1} (Fin n) F (instDecidableEqFin n)
          (Fin.fintype n) (@Field.toCommRing.{u_1} F inst))
        (@Subgroup.center.{u_1} (@Atlas.Symplectic.Sp.{u_1} n F (@Field.toCommRing.{u_1} F inst))
          (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1} (Fin n) F
            (instDecidableEqFin n) (Fin.fintype n) (@Field.toCommRing.{u_1} F inst)))
        ⋯)
```

## D_n(q) / PΩ+(2n,q)

Model: `Atlas.Orthogonal.DPlus` ([source](Atlas/LinearGroups/Orthogonal/DFamily.lean)).

### Order

`Atlas.Orthogonal.DPlus_card` — [source](Atlas/LinearGroups/Orthogonal/DFamily.lean).

```lean
@Atlas.Orthogonal.DPlus_card.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Orthogonal.DPlus.{u_1} n F inst))
      (Atlas.Orthogonal.DPlus_order n (Nat.card.{u_1} F))
```

### Simplicity

`Atlas.Orthogonal.DPlus_simple` — [source](Atlas/LinearGroups/Orthogonal/DConstruction.lean).

```lean
@Atlas.Orthogonal.DPlus_simple.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    @IsSimpleGroup.{u_1} (@Atlas.Orthogonal.DPlus.{u_1} n F inst)
      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, u_1} F (Atlas.Orthogonal.VectorD.{u_1} n F) inst
        (@Pi.addCommGroup.{0, u_1} (Atlas.Orthogonal.Index n) (fun a => F) fun i =>
          @Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst)))
        (@Pi.Function.module.{0, u_1, u_1} (Atlas.Orthogonal.Index n) F F
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Semiring.toAddCommMonoid.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Semiring.toModule.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Atlas.Orthogonal.formD.{u_1} n F (@Field.toCommRing.{u_1} F inst)))
```

## G2(q)

Model: `Atlas.G2.Model` ([source](Atlas/LinearGroups/G2/Basic.lean)).

### Order

`Atlas.G2.card_Model` — [source](Atlas/LinearGroups/G2/Order.lean).

```lean
@Atlas.G2.card_Model.{u_1} : ∀ {K : Type u_1} [inst : Field.{u_1} K] [Finite.{u_1 + 1} K],
  @Eq.{1} Nat (Nat.card.{u_1} ↥(@Atlas.G2.Model.{u_1} K inst))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simplicity

`Atlas.G2.isSimple` — [source](Atlas/LinearGroups/G2/Simplicity.lean).

```lean
@Atlas.G2.isSimple.{u_1} : ∀ {K : Type u_1} [inst : Field.{u_1} K] [Finite.{u_1 + 1} K],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat.card.{u_1} K) →
    @IsSimpleGroup.{u_1} (↥(@Atlas.G2.Model.{u_1} K inst))
      (@Subgroup.toGroup.{u_1}
        (@LinearEquiv.{u_1, u_1, u_1, u_1} K K
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@RingHom.id.{u_1} K
            (@Semiring.toNonAssocSemiring.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
          (@RingHom.id.{u_1} K
            (@Semiring.toNonAssocSemiring.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
          ⋯ ⋯ (Atlas.SplitOctonion.Carrier.{u_1} K) (Atlas.SplitOctonion.Carrier.{u_1} K)
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a => K)
            fun i =>
            @Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a => K)
            fun i =>
            @Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
            (@Semiring.toModule.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
            (@Semiring.toModule.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
        (@LinearEquiv.automorphismGroup.{u_1, u_1} K (Atlas.SplitOctonion.Carrier.{u_1} K)
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a => K)
            fun i =>
            @Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
            (@Semiring.toModule.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
        (@Atlas.G2.Model.{u_1} K inst))
```

## Ree (2G2)

Model: `Atlas.ReeG2.Model` ([source](Atlas/LinearGroups/ReeG2/Generators.lean)).

### Order

`Atlas.ReeG2.order` — [source](Atlas/LinearGroups/ReeG2/Order.lean).

```lean
@Atlas.ReeG2.order.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [inst_1 : Finite.{u_1 + 1} F]
  [inst_2 :
    @CharP.{u_1} F
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} F
        (@Ring.toAddGroupWithOne.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  (m : Nat),
  @Eq.{1} Nat (Nat.card.{u_1} F)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.ReeG2.Model.{u_1} F inst inst_1 inst_2 m))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simplicity

`Atlas.ReeG2.simple` — [source](Atlas/LinearGroups/ReeG2/Simplicity.lean).

```lean
@Atlas.ReeG2.simple.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [inst_1 : Finite.{u_1 + 1} F]
  [inst_2 :
    @CharP.{u_1} F
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} F
        (@Ring.toAddGroupWithOne.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  (m : Nat),
  @Atlas.ReeG2.Parameters.{u_1} F inst inst_1 m →
    @IsSimpleGroup.{u_1} (@Atlas.ReeG2.Model.{u_1} F inst inst_1 inst_2 m)
      (@Subgroup.toGroup.{u_1} (@Atlas.ReeG2.Ambient.{u_1} F inst)
        (@Units.instGroup.{u_1}
          (Matrix.{0, 0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
          (@Semiring.toMonoid.{u_1}
            (Matrix.{0, 0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
            (@Matrix.semiring.{u_1, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F
              (@DivisionSemiring.toSemiring.{u_1} F
                (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
        (@Atlas.ReeG2.generated.{u_1} F inst inst_1 inst_2 m))
```

## M11

Model: `Atlas.Sporadic.Mathieu11.Model` ([source](Atlas/Sporadic/Mathieu11.lean)).

### Order

`Atlas.Sporadic.Mathieu11.card` — [source](Atlas/Sporadic/Mathieu11.lean).

```lean
Atlas.Sporadic.Mathieu11.card : ∀ (D : Atlas.Codes.Dodecad) (a : Atlas.Codes.Mathieu12Points D),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu11.Model D a)) Atlas.Sporadic.Mathieu11.order
```

### Simplicity

`Atlas.Sporadic.Mathieu11.isSimpleGroup` — [source](Atlas/Sporadic/Mathieu11.lean).

```lean
Atlas.Sporadic.Mathieu11.isSimpleGroup : ∀ (D : Atlas.Codes.Dodecad) (a : Atlas.Codes.Mathieu12Points D),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu11.Model D a)
    (@Subgroup.toGroup.{0} (↥(Atlas.Codes.Mathieu12DodecadModel D))
      (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
        (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
          Atlas.Codes.Mathieu24CodeModel)
        (Atlas.Codes.Mathieu12DodecadModel D))
      (Atlas.Codes.Mathieu11PointModel D a))
```

## M12

Model: `Atlas.Sporadic.Mathieu12.Model` ([source](Atlas/Sporadic/Mathieu12.lean)).

### Order

`Atlas.Sporadic.Mathieu12.card` — [source](Atlas/Sporadic/Mathieu12.lean).

```lean
Atlas.Sporadic.Mathieu12.card : ∀ (D : Atlas.Codes.Dodecad),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu12.Model D)) Atlas.Sporadic.Mathieu12.order
```

### Simplicity

`Atlas.Sporadic.Mathieu12.isSimpleGroup` — [source](Atlas/Sporadic/Mathieu12.lean).

```lean
Atlas.Sporadic.Mathieu12.isSimpleGroup : ∀ (D : Atlas.Codes.Dodecad),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu12.Model D)
    (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
      (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
        Atlas.Codes.Mathieu24CodeModel)
      (Atlas.Codes.Mathieu12DodecadModel D))
```

## M22

Model: `Atlas.Sporadic.Mathieu22.Model` ([source](Atlas/Sporadic/Mathieu22.lean)).

### Order

`Atlas.Sporadic.Mathieu22.card` — [source](Atlas/Sporadic/Mathieu22.lean).

```lean
Atlas.Sporadic.Mathieu22.card : ∀ (a : Atlas.Codes.Omega) (b : ↥(Atlas.Codes.Mathieu23Points a)),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu22.Model a b)) Atlas.Sporadic.Mathieu22.order
```

### Simplicity

`Atlas.Sporadic.Mathieu22.isSimpleGroup` — [source](Atlas/Sporadic/Mathieu22Simple.lean).

```lean
Atlas.Sporadic.Mathieu22.isSimpleGroup : ∀ (a : Atlas.Codes.Omega) (b : ↥(Atlas.Codes.Mathieu23Points a)),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu22.Model a b)
    (@Subgroup.toGroup.{0} (↥(Atlas.Codes.Mathieu23PointModel a))
      (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
        (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
          Atlas.Codes.Mathieu24CodeModel)
        (Atlas.Codes.Mathieu23PointModel a))
      (Atlas.Codes.Mathieu22PointModel a b))
```

## M23

Model: `Atlas.Sporadic.Mathieu23.Model` ([source](Atlas/Sporadic/Mathieu23.lean)).

### Order

`Atlas.Sporadic.Mathieu23.card` — [source](Atlas/Sporadic/Mathieu23.lean).

```lean
Atlas.Sporadic.Mathieu23.card : ∀ (a : Atlas.Codes.Omega),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu23.Model a)) Atlas.Sporadic.Mathieu23.order
```

### Simplicity

`Atlas.Sporadic.Mathieu23.isSimpleGroup` — [source](Atlas/Sporadic/Mathieu23.lean).

```lean
Atlas.Sporadic.Mathieu23.isSimpleGroup : ∀ (a : Atlas.Codes.Omega),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu23.Model a)
    (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
      (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
        Atlas.Codes.Mathieu24CodeModel)
      (Atlas.Codes.Mathieu23PointModel a))
```

## M24

Model: `Atlas.Sporadic.Mathieu24.Model` ([source](Atlas/Sporadic/Mathieu24.lean)).

### Order

`Atlas.Sporadic.Mathieu24.card` — [source](Atlas/Sporadic/Mathieu24Construction.lean).

```lean
Atlas.Sporadic.Mathieu24.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Mathieu24.Model)
  Atlas.Sporadic.Mathieu24.expectedOrder
```

### Simplicity

`Atlas.Sporadic.Mathieu24.isSimpleGroup` — [source](Atlas/Sporadic/Mathieu24Construction.lean).

```lean
Atlas.Sporadic.Mathieu24.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Mathieu24.Model
  (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
    Atlas.Codes.Mathieu24CodeModel)
```

## Co1

Model: `Atlas.Sporadic.Conway1.Model` ([source](Atlas/Sporadic/Conway1.lean)).

### Order

`Atlas.Sporadic.Conway1.card` — [source](Atlas/Sporadic/Conway1.lean).

```lean
Atlas.Sporadic.Conway1.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Conway1.Model) Atlas.Sporadic.Conway1.order
```

### Simplicity

`Atlas.Sporadic.Conway1.isSimpleGroup` — [source](Atlas/Sporadic/Conway1.lean).

```lean
Atlas.Sporadic.Conway1.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Conway1.Model
  (@QuotientGroup.Quotient.group.{0} Atlas.Lattices.LeechIsometryGroup
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
        (↥Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech))
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      Atlas.Lattices.leechIsometries)
    Atlas.Conway.leechCentralSigns Atlas.Conway.instNormalLeechIsometryGroupLeechCentralSigns)
```

## Co2

Model: `Atlas.Sporadic.Conway2.Model` ([source](Atlas/Sporadic/Conway2.lean)).

### Order

`Atlas.Sporadic.Conway2.card` — [source](Atlas/Sporadic/Conway2.lean).

```lean
Atlas.Sporadic.Conway2.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.Conway2.Model) Atlas.Sporadic.Conway2.order
```

### Simplicity

`Atlas.Sporadic.Conway2.isSimpleGroup` — [source](Atlas/Sporadic/Conway2Simplicity.lean).

```lean
Atlas.Sporadic.Conway2.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.Conway2.Model)
  (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
        (↥Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech))
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      Atlas.Lattices.leechIsometries)
    Atlas.Sporadic.Conway2.Model)
```

## Co3

Model: `Atlas.Sporadic.Conway3.Model` ([source](Atlas/Sporadic/Conway3.lean)).

### Order

`Atlas.Sporadic.Conway3.card` — [source](Atlas/Sporadic/Conway3.lean).

```lean
Atlas.Sporadic.Conway3.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.Conway3.Model) Atlas.Sporadic.Conway3.order
```

### Simplicity

`Atlas.Sporadic.Conway3.isSimpleGroup` — [source](Atlas/Sporadic/Conway3Simplicity.lean).

```lean
Atlas.Sporadic.Conway3.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.Conway3.Model)
  (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
        (↥Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech))
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      Atlas.Lattices.leechIsometries)
    Atlas.Sporadic.Conway3.Model)
```

## McL

Model: `Atlas.Sporadic.McLaughlin.Model` ([source](Atlas/Sporadic/McLaughlin.lean)).

### Order

`Atlas.Sporadic.McLaughlin.card` — [source](Atlas/Sporadic/McLaughlin.lean).

```lean
Atlas.Sporadic.McLaughlin.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.McLaughlin.Model)
  Atlas.Sporadic.McLaughlin.order
```

### Simplicity

`Atlas.Sporadic.McLaughlin.isSimpleGroup` — [source](Atlas/Sporadic/McLaughlinSimplicity.lean).

```lean
Atlas.Sporadic.McLaughlin.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.McLaughlin.Model)
  (@Subgroup.toGroup.{0} (↥Atlas.Sporadic.Conway3.Model)
    (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
      (@Subgroup.toGroup.{0}
        (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
          (↥Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech))
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        Atlas.Lattices.leechIsometries)
      Atlas.Sporadic.Conway3.Model)
    Atlas.Sporadic.McLaughlin.Model)
```

## HS

Model: `Atlas.Sporadic.HigmanSims.Model` ([source](Atlas/Sporadic/HigmanSimsConfiguration.lean)).

### Order

`Atlas.Sporadic.HigmanSims.card` — [source](Atlas/Sporadic/HigmanSims.lean).

```lean
Atlas.Sporadic.HigmanSims.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.HigmanSims.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 44352000) (instOfNatNat (nat_lit 44352000)))
```

### Simplicity

`Atlas.Sporadic.HigmanSims.isSimpleGroup` — [source](Atlas/Sporadic/HigmanSimsSimplicity.lean).

```lean
Atlas.Sporadic.HigmanSims.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.HigmanSims.Model)
  (@Subgroup.toGroup.{0}
    (↥(Atlas.Conway.fullVectorStabilizer (Atlas.Conway.normSixVector Atlas.Conway.co3MarkedCoordinate)))
    (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
      (@Subgroup.toGroup.{0}
        (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
          (↥Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech))
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        Atlas.Lattices.leechIsometries)
      (Atlas.Conway.fullVectorStabilizer (Atlas.Conway.normSixVector Atlas.Conway.co3MarkedCoordinate)))
    Atlas.Sporadic.HigmanSims.Model)
```

## Suz

Model: `Atlas.Sporadic.Suzuki.Model` ([source](Atlas/Sporadic/Suzuki.lean)).

### Order

`Atlas.Sporadic.Suzuki.card` — [source](Atlas/Sporadic/Suzuki.lean).

```lean
Atlas.Sporadic.Suzuki.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Suzuki.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 448345497600) (instOfNatNat (nat_lit 448345497600)))
```

### Simplicity

`Atlas.Sporadic.Suzuki.isSimpleGroup` — [source](Atlas/Sporadic/Suzuki.lean).

```lean
Atlas.Sporadic.Suzuki.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Suzuki.Model
  (@QuotientGroup.Quotient.group.{0} (↥Atlas.Conway.eisensteinCentralizer)
    (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
      (@Subgroup.toGroup.{0}
        (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
          (↥Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech))
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a => Int) fun i => Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        Atlas.Lattices.leechIsometries)
      Atlas.Conway.eisensteinCentralizer)
    Atlas.Conway.eisensteinCentralizerScalars Atlas.Conway.eisensteinCentralizerScalars_normal)
```

## J2

Model: `Atlas.Sporadic.Janko2.Model` ([source](Atlas/Sporadic/Janko2.lean)).

### Order

`Atlas.Sporadic.Janko2.card` — [source](Atlas/Sporadic/Janko2.lean).

```lean
Atlas.Sporadic.Janko2.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Janko2.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 604800) (instOfNatNat (nat_lit 604800)))
```

### Simplicity

`Atlas.Sporadic.Janko2.isSimpleGroup` — [source](Atlas/Sporadic/Janko2.lean).

```lean
Atlas.Sporadic.Janko2.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Janko2.Model
  (@QuotientGroup.Quotient.group.{0} (↥Atlas.Conway.icosianHermitianGroup)
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Rat Rat Rat.semiring Rat.semiring
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring))
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring)) ⋯ ⋯
        Atlas.Lattices.IcosianRationalCoordinates Atlas.Lattices.IcosianRationalCoordinates
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun a => Atlas.Algebra.IcosianQuaternion) fun i =>
          @Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun a => Atlas.Algebra.IcosianQuaternion) fun i =>
          @Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat
          Atlas.Algebra.IcosianQuaternion Rat.semiring
          (@Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
          (@Quaternion.instModule.{0, 0} Rat Atlas.Algebra.GoldenRational
            (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing)
            Rat.semiring
            (@QuadraticAlgebra.instModule.{0, 0} Rat Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.semiring
              (@Semiring.toAddCommMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Semiring.toModule.{0} Rat Rat.semiring))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat
          Atlas.Algebra.IcosianQuaternion Rat.semiring
          (@Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
          (@Quaternion.instModule.{0, 0} Rat Atlas.Algebra.GoldenRational
            (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing)
            Rat.semiring
            (@QuadraticAlgebra.instModule.{0, 0} Rat Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.semiring
              (@Semiring.toAddCommMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Semiring.toModule.{0} Rat Rat.semiring)))))
      (@LinearEquiv.automorphismGroup.{0, 0} Rat Atlas.Lattices.IcosianRationalCoordinates Rat.semiring
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun a => Atlas.Algebra.IcosianQuaternion) fun i =>
          @Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat
          Atlas.Algebra.IcosianQuaternion Rat.semiring
          (@Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
          (@Quaternion.instModule.{0, 0} Rat Atlas.Algebra.GoldenRational
            (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing)
            Rat.semiring
            (@QuadraticAlgebra.instModule.{0, 0} Rat Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.semiring
              (@Semiring.toAddCommMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Semiring.toModule.{0} Rat Rat.semiring)))))
      Atlas.Conway.icosianHermitianGroup)
    Atlas.Conway.icosianCentralSigns Atlas.Conway.icosianCentralSigns_normal)
```

## Fi22

Model: `Atlas.Sporadic.Fischer22.Model` ([source](Atlas/Sporadic/Fischer22.lean)).

### Order

`Atlas.Sporadic.Fischer22.card` — [source](Atlas/Sporadic/Fischer22.lean).

```lean
Atlas.Sporadic.Fischer22.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Fischer22.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 64561751654400) (instOfNatNat (nat_lit 64561751654400)))
```

### Simplicity

`Atlas.Sporadic.Fischer22.simple` — [source](Atlas/Sporadic/Fischer22.lean).

```lean
Atlas.Sporadic.Fischer22.simple : @IsSimpleGroup.{0} Atlas.Sporadic.Fischer22.Model
  (@QuotientGroup.Quotient.group.{0} (↥(Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer22Marking))
    (@Subgroup.toGroup.{0} (↥Atlas.Fischer.rootGeneratedRayGroup)
      (@Subgroup.toGroup.{0}
        (Equiv.Perm.{1} (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        (@Equiv.Perm.permGroup.{0}
          (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        Atlas.Fischer.rootGeneratedRayGroup)
      (Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer22Marking))
    (Atlas.Fischer.residueCentralElementary Atlas.Fischer.fischer22Marking) ⋯)
```

## Fi23

Model: `Atlas.Sporadic.Fischer23.Model` ([source](Atlas/Sporadic/Fischer23.lean)).

### Order

`Atlas.Sporadic.Fischer23.card` — [source](Atlas/Sporadic/Fischer23.lean).

```lean
Atlas.Sporadic.Fischer23.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Fischer23.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 4089470473293004800) (instOfNatNat (nat_lit 4089470473293004800)))
```

### Simplicity

`Atlas.Sporadic.Fischer23.simple` — [source](Atlas/Sporadic/Fischer23.lean).

```lean
Atlas.Sporadic.Fischer23.simple : @IsSimpleGroup.{0} Atlas.Sporadic.Fischer23.Model
  (@QuotientGroup.Quotient.group.{0} (↥(Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer23Marking))
    (@Subgroup.toGroup.{0} (↥Atlas.Fischer.rootGeneratedRayGroup)
      (@Subgroup.toGroup.{0}
        (Equiv.Perm.{1} (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        (@Equiv.Perm.permGroup.{0}
          (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        Atlas.Fischer.rootGeneratedRayGroup)
      (Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer23Marking))
    (Atlas.Fischer.residueCentralElementary Atlas.Fischer.fischer23Marking) ⋯)
```

## Fi24Prime

Model: `Atlas.Sporadic.Fischer24Prime.Model` ([source](Atlas/Sporadic/Fischer24Prime.lean)).

### Order

`Atlas.Sporadic.Fischer24Prime.card` — [source](Atlas/Sporadic/Fischer24Prime.lean).

```lean
Atlas.Sporadic.Fischer24Prime.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.Fischer24Prime.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 1255205709190661721292800) (instOfNatNat (nat_lit 1255205709190661721292800)))
```

### Simplicity

`Atlas.Sporadic.Fischer24Prime.simple` — [source](Atlas/Sporadic/Fischer24Prime.lean).

```lean
Atlas.Sporadic.Fischer24Prime.simple : @IsSimpleGroup.{0} (↥Atlas.Sporadic.Fischer24Prime.Model)
  (@Subgroup.toGroup.{0} (↥Atlas.Fischer.rootGeneratedRayGroup)
    (@Subgroup.toGroup.{0}
      (Equiv.Perm.{1} (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
      (@Equiv.Perm.permGroup.{0}
        (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
      Atlas.Fischer.rootGeneratedRayGroup)
    Atlas.Sporadic.Fischer24Prime.Model)
```

