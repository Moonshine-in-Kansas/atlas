# Explicit comparison interfaces

See [the aggregate theorem](../COMPARISON.md) for its 13-family scope and proof architecture.
Every row below retains its full field and rank assumptions.

| Models | Relation | Parameters | Declaration |
|---|---|---|---|
| B(1,F) / PSL(2,F) | isomorphism | F any field; natural quadratic dimension 3; PSL dimension 2; includes q=2,3 | [`Atlas.Comparisons.Classical.b1EquivA1`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| B(n,F) / C(n,F) | isomorphism | F finite, characteristic 2; n >= 1; natural dimensions 2n+1 and 2n | [`Atlas.Comparisons.Classical.evenBEquivC`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| B(2,F) / C(2,F) | isomorphism | F finite, every characteristic; natural dimensions 5 and 4 | [`Atlas.Comparisons.Classical.b2EquivC2`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| D+(2,F) / PSL(2,F) x PSL(2,F) | isomorphism | F any field; split quadratic dimension 4; PSL dimensions 2 and 2 | [`Atlas.Comparisons.Classical.d2EquivProduct`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| D+(3,F) / PSL(4,F) | isomorphism | F finite, every characteristic; split quadratic dimension 6; PSL dimension 4 | [`Atlas.Comparisons.Classical.d3EquivA3`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| B(n,F) / B(n,K) | isomorphism | F,K any fields; n any natural rank; explicit field isomorphism F ~= K | [`Atlas.Comparisons.Classical.bFieldEquiv`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| D+(n,F) / D+(n,K) | isomorphism | F,K any fields; n any natural rank; explicit field isomorphism F ~= K | [`Atlas.Comparisons.Classical.dFieldEquiv`](../Atlas/Comparisons/Classical/Orthogonal.lean) |
| B(n,F) / C(n,F) | same_order | F finite, odd characteristic; n >= 2; no isomorphism asserted | [`Atlas.Comparisons.Classical.oddB_card_eq_C`](../Atlas/Comparisons/Classical/OrthogonalOrder.lean) |
| B(n,F) / C(n,F) | nonisomorphism | F finite, odd characteristic; n >= 3; distinguished by proved involution-class counts | [`Atlas.Comparisons.Classical.oddB_not_equiv_C`](../Atlas/Comparisons/Classical/OrthogonalInvolutions.lean) |
| PSL(2,F) / A6 | isomorphism | F any finite field of cardinality 9; common faithful ten-point actions | [`Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6`](../Atlas/Comparisons/Exceptional/Order360.lean) |
| PSL(2,GaloisField 3 2) / A6 | isomorphism | Canonical pinned finite-field wrapper | [`Atlas.Comparisons.Exceptional.psl2NineEquivAlt6`](../Atlas/Comparisons/Exceptional/Order360.lean) |
| B(2,ZMod 2)' / C(2,ZMod 2)' | isomorphism | Actual commutator subgroups; restriction of the full B2/C2 comparison | [`Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived`](../Atlas/Comparisons/Exceptional/BinaryDerived.lean) |
| C(2,ZMod 2)' / A6 | isomorphism | Derived group of order 360; full C2(2) is not the endpoint | [`Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6`](../Atlas/Comparisons/Exceptional/BinaryDerived.lean) |
| PSL(2,F) / B(2,ZMod 2)' | isomorphism | F finite of cardinality 9; composition through actual A6 | [`Atlas.Comparisons.Exceptional.psl2Card9EquivB2BinaryDerived`](../Atlas/Comparisons/Exceptional/Order360.lean) |
| PSL(2,F) / C(2,ZMod 2)' | isomorphism | F finite of cardinality 9; composition through actual A6 | [`Atlas.Comparisons.Exceptional.psl2Card9EquivC2BinaryDerived`](../Atlas/Comparisons/Exceptional/Order360.lean) |
| A8 / D+(3,ZMod 2) | isomorphism | Actual binary deleted permutation quotient with explicit split isometry | [`Atlas.Comparisons.Exceptional.alt8EquivD3Two`](../Atlas/Comparisons/Exceptional/Order20160A8.lean) |
| PSL(4,ZMod 2) / A8 | isomorphism | Actual D3/A3 comparison composed with the faithful deleted-module action | [`Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8`](../Atlas/Comparisons/Exceptional/Order20160A8.lean) |
| PSL(4,ZMod 2) / PSL(3,F) | nonisomorphism | F finite of cardinality 4; Sylow-2 centers of cardinalities 2 and 4 | [`Atlas.Comparisons.Exceptional.psl4Two_not_equiv_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean) |
| A8 / PSL(3,F) | nonisomorphism | F finite of cardinality 4; transport of the proved Sylow-center obstruction | [`Atlas.Comparisons.Exceptional.alt8_not_equiv_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean) |
| PSL(4,ZMod 2) / PSL(3,F) | same_order | F finite of cardinality 4; both orders 20160 | [`Atlas.Comparisons.Exceptional.psl4Two_card_eq_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean) |
| A8 / PSL(3,F) | same_order | F finite of cardinality 4; both orders 20160 | [`Atlas.Comparisons.Exceptional.alt8_card_eq_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean) |
| PSL(2,F) / A5 | isomorphism | F any finite field of cardinality 4; natural projective-line action | [`Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5`](../Atlas/Comparisons/Exceptional/Order60Four.lean) |
| PSL(2,F) / A5 | isomorphism | F any finite field of cardinality 5; proved elementary order-60 recognition | [`Atlas.Comparisons.Exceptional.psl2Card5EquivAlt5`](../Atlas/Comparisons/Exceptional/Order60Five.lean) |
| PSL(2,ZMod 7) / PSL(3,ZMod 2) | isomorphism | Actual matrix models; common faithful action on eight points | [`Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two`](../Atlas/Comparisons/Exceptional/Order168.lean) |
| PSL(2,F) / PSL(2,ZMod 5) | isomorphism | F any finite field of cardinality 4; composition of the verified maps | [`Atlas.Comparisons.Exceptional.psl2Card4EquivPsl2Five`](../Atlas/Comparisons/Exceptional/Order60Five.lean) |
| C(1,F) / PSL(2,F) | isomorphism | F any field; Lie rank one, PSL dimension two | [`Atlas.Comparisons.Classical.c1EquivA1`](../Atlas/Comparisons/LowRank/Symplectic.lean) |
| PSU(2,K/F) / PSL(2,F) | isomorphism | F,K finite fields; Algebra F K; finrank F K = 2; PSL over base F | [`Atlas.Comparisons.Classical.psuTwoEquivA1`](../Atlas/Comparisons/LowRank/Unitary.lean) |
| PSU(2,K/F) / C(1,F) | isomorphism | F,K finite quadratic extension; all characteristics | [`Atlas.Comparisons.Classical.psuTwoEquivC1`](../Atlas/Comparisons/LowRank/Unitary.lean) |
| PSU(2,K/F) / B(1,F) | isomorphism | F,K finite quadratic extension; all characteristics | [`Atlas.Comparisons.Classical.psuTwoEquivB1`](../Atlas/Comparisons/LowRank/Unitary.lean) |
| DMinus(2,F,K) / PSL(2,K) | isomorphism | F,K finite quadratic extension; Lie rank two; PSL over extension K | [`Atlas.Comparisons.Classical.dMinusTwoEquivA1`](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean) |
| DMinus(3,F,K) / PSU(4,K/F) | isomorphism | F,K finite quadratic extension; Lie rank three, unitary dimension four | [`Atlas.Comparisons.Classical.dMinusThreeEquivUnitary`](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean) |
| PSU(d,K/F) / PSU(d,Kprime/Fprime) | isomorphism | Finite quadratic extensions; explicit base and extension field equivalences; actual Frobenius involutions | [`Atlas.Comparisons.Classical.unitaryFieldEquiv`](../Atlas/Comparisons/LowRank/FieldTransport.lean) |
| DMinus(n,F,K) / DMinus(n,Fprime,Kprime) | isomorphism | Finite quadratic extensions; explicit base/extension field equivalences with commuting algebraMap square | [`Atlas.Comparisons.Classical.dMinusFieldEquiv`](../Atlas/Comparisons/LowRank/FieldTransport.lean) |
| C(2,ZMod 2) / S6 | isomorphism | Full group of order720; compatible with existing derived A6 map | [`Atlas.Comparisons.Exceptional.c2BinaryEquivSymmetric`](../Atlas/Comparisons/Small/BinarySymplectic.lean) |
| C(2,F) / S6 | isomorphism | F any finite field of cardinality2; field transport of actual six-refinement action | [`Atlas.Comparisons.Exceptional.c2Card2EquivSymmetric`](../Atlas/Comparisons/Small/BinarySymplectic.lean) |
| B(2,F) / S6 | isomorphism | F any finite field of cardinality2; full B2/C2 comparison composed with transported six-point action | [`Atlas.Comparisons.Exceptional.b2Card2EquivSymmetric`](../Atlas/Comparisons/Small/BinarySymplectic.lean) |
| PSU(4,K/ZMod 2) / C(2,ZMod 3) | isomorphism | K finite; Algebra (ZMod 2) K; finrank (ZMod 2) K = 2; actual positive E6 Weyl reductions | [`Atlas.Comparisons.Exceptional.psu4BinaryEquivPSp4Ternary`](../Atlas/Comparisons/Exceptional/Order25920.lean) |
| PSU(4,L/F) / C(2,T) | isomorphism | F,L,T finite fields; Algebra F L; finrank F L = 2; \|F\|=2 and \|T\|=3; full-center projective models | [`Atlas.Comparisons.Exceptional.psu4Card2EquivPSp4Card3`](../Atlas/Comparisons/Exceptional/Order25920.lean) |
| DMinus(3,F,L) / C(2,T) | isomorphism | F,L,T finite fields; Algebra F L; finrank F L = 2; \|F\|=2 and \|T\|=3; retained minus/unitary map | [`Atlas.Comparisons.Exceptional.dMinus3Card2EquivPSp4Card3`](../Atlas/Comparisons/Exceptional/Order25920.lean) |
| PSU(4,L/F) / B(2,T) | isomorphism | F,L,T finite fields; Algebra F L; finrank F L = 2; \|F\|=2 and \|T\|=3; retained B2/C2 map | [`Atlas.Comparisons.Exceptional.psu4Card2EquivB2Card3`](../Atlas/Comparisons/Exceptional/Order25920.lean) |

[Chevalley identifications](REALIZATIONS.md) are additional concrete maps.
The outstanding order-6,048 and order-504 derived-group bridges are not inferred from order equality.
