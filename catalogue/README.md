# Catalogue data

`catalogue.json` contains the 33 completed entries, exact parameter conventions,
public declarations, auxiliary groups and evidence bindings. `realizations.json`
retains separate model records and explicit identification maps. `comparisons.json`
retains the 40 exposed comparison interfaces with their mathematical hypotheses.

Start with [Constructions and identification certificates](REALIZATIONS.md).
It has exactly three themes: isomorphisms between different models, exceptional
isomorphisms, and non-isomorphisms of all other cases by order or a further invariant.
Each result has separate Lean-statement and dated verification-certificate links.
The [complete statement index](COMPARISONS.md) follows the same three themes and
retains all 40 comparison interfaces with their full parameter hypotheses.
The 39-model inventory is an expandable reference list within the first theme;
full model descriptions, orders and simplicity domains remain in the catalogue.

The generated views display all 39 models of the 33 entries. Six entries retain
both original and Chevalley constructions. [ISOMORPHISMS.md](ISOMORPHISMS.md)
exposes the four registered A/B/C/D equivalences with exact source proofs,
compiled types and dependency certificates. G₂/F₄ retain their own model contracts
and the stated scope of the comparisons between them. The same model inventory supplies the catalogue, CSV, statement pages,
comparison pages and navigation in every proof diagram.

Run `ruby catalogue/manage.rb refresh` after a reviewed data edit, then
`ruby catalogue/manage.rb check`. This deterministically produces the catalogue,
realization and comparison pages, CSV inventory and principal compiled signatures.
It checks diagram sources and registered interfaces; it does not run Lean or grant
new verification status. Use the [audit procedure](../AUDIT.md) for that.

The independent existence specifications retain exact source-bound mathematical
contracts. The full internal theorem inventory remains available in Lean and the
verification target data.

`current-verification.json` binds these three registries to the 1,207-root
26 October compiled audit. The prior 1,167-reference catalogue check is preserved
as [dated evidence](../verification/catalogue/2026-10-19/original-current-verification.json);
its historical development paths and scope are not current release paths.
