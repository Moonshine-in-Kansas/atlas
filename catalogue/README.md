# Catalogue data

`catalogue.json` contains the 33 completed entries, exact parameter conventions,
public declarations, auxiliary groups and evidence bindings. `realizations.json`
retains separate model records and explicit identification maps. `comparisons.json`
retains the 40 exposed comparison interfaces with their mathematical hypotheses.

Start with [Constructions and identification certificates](REALIZATIONS.md):
models of the same group, identifications between families, then the general
nonisomorphism certificate with its order and invariant proofs. The
[interface index](COMPARISONS.md) groups all 40 interfaces by purpose and retains
every parameter hypothesis. The [scope section](REALIZATIONS.md#comparison-scope)
collects the limits and unfinished comparisons.

The generated views display all 39 models of the 33 entries. Six entries retain
both original and Chevalley constructions. [ISOMORPHISMS.md](ISOMORPHISMS.md)
exposes the four registered A/B/C/D equivalences with exact source proofs,
compiled types and dependency certificates. G₂/F₄ model contracts are displayed
without silently promoting their pending realization registrations or comparison
scope. The same model inventory supplies the catalogue, CSV, statement pages,
comparison pages and navigation in every proof diagram.

Run `ruby catalogue/manage.rb refresh` after a reviewed data edit, then
`ruby catalogue/manage.rb check`. This deterministically produces the catalogue,
realization and comparison pages, CSV inventory and principal compiled signatures.
It checks diagram sources and registered interfaces; it does not run Lean or grant
new verification status. Use the [audit procedure](../AUDIT.md) for that.

The independent existence specifications retain exact source-bound mathematical
contracts. No separate nonabelian theorem rows are displayed in the catalogue;
those declarations remain in Lean and in the full verification target data.

`current-verification.json` binds these three registries to the 1,207-root
26 October compiled audit. The prior 1,167-reference catalogue check is preserved
as [dated evidence](../verification/catalogue/2026-10-19/original-current-verification.json);
its historical development paths and scope are not current release paths.
