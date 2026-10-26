# Uniform-theorem regression specializations

All rows are actual compiled theorems in `Atlas/LinearGroups/Symplectic/Checks.lean`,
selected by the full structural audit. Numerical simplification follows the uniform
order and exact-simplicity theorems; it does not enumerate any matrix group.

| Rank n | Field size q | Sp order | PSp order | PSp simple |
|---:|---:|---:|---:|---|
| 0 | 3 (indeed every finite field) | 1 | 1 | no |
| 1 | 2 | 6 | 6 | no |
| 1 | 3 | 24 | 12 | no |
| 1 | 4 | 60 | 60 | yes |
| 2 | 2 | 720 | 720 | no |
| 2 | 3 | 51840 | 25920 | yes |
| 2 | 4 | 979200 | 979200 | yes |
| 2 | 5 | 9360000 | 4680000 | yes |
| 3 | 2 | 1451520 | 1451520 | yes |
| 3 | 3 | 9170703360 | 4585351680 | yes |
| 4 | 2 | 47377612800 | 47377612800 | yes |

The rank-zero root is `Atlas.Symplectic.Checks.rank_zero`; the remaining names have
the form `Atlas.Symplectic.Checks.rankN_cardQ`. The additional `galois_four` theorem
uses the actual field `GaloisField 2 2`. `small_perfectness` specializes both required
small-field branches. The structural audit also selects the general symbolic
`Atlas.Symplectic.ternary_four_transvections` and `binary_seven_transvections` identities.
`binary_zero_counts` checks every one of sixteen refinements on sixteen vectors:
six zeros for the six odd forms, ten zeros for each of the other ten forms.

Exact elaborated statements are in the verbatim compiler extraction
`THEOREM_STATEMENTS.txt.gz`; corresponding proof closures are in the structure run.
