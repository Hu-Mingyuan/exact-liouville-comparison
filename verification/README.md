# Verification and source provenance

## Current delivery boundary

The combined formalization was accepted at private Forgejo commit `e994427720c4af8d3915d86609c6fe0538f7c031`. This is a development provenance identifier, separate from the public GitHub commit history. This delivery retains all 191 mathematical Lean files byte-for-byte; [accepted-library.json](accepted-library.json) binds them. The [publication receipt](publication/receipt.json) records the separate successful build, consumer, and thirteen final-root axiom checks.

[GitHub Actions run 40055251963](https://github.com/Hu-Mingyuan/exact-liouville-comparison/actions/runs/40055251963) also passed using ordinary Lake at public commit `f51a6895cb4326c073650bcbd7f62cd5bbb5bcce`. Its downloaded receipt binds 199 compilation inputs and thirteen final-root axiom sets. Those inputs match the published sources; later documentation-only corrections leave them unchanged. The `lean-verification` artifact retains that run's receipt and logs for GitHub's artifact-retention period. The committed receipt above records the local managed checks; it is a separate record from the cloud artifact.

The root import exposes the accepted native integration and its proof assemblies. The additional publication consumers have their own exact-source receipt; earlier component receipts are not used to certify these additions automatically.

## Reproduce the public interface checks

From the repository root on Linux or Ubuntu under WSL, with Elan (`lake` on `PATH`), Git, Python 3, and Bash 4 or newer available:

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

`fetch-cache.sh` reuses the cluster project's cache workflow with this project's module path. It materializes locked dependency sources and obtains the imported pinned Mathlib cache. It does not request newer dependency revisions.

[FinalConsumer.lean](FinalConsumer.lean) checks that the default import exposes proof terms for `MainTarget`, `ManuscriptTarget`, complete comparison, cylindrical existence, prescribed extension, and the native quotient application. [PublicationAxioms.lean](PublicationAxioms.lean) prints transitive axiom sets for thirteen final roots, including the direct prescribed-kernel theorem. The verifier parses every expected result and fails on missing roots or axioms outside `propext`, `Classical.choice`, and `Quot.sound`.

On an already configured Horizon host, `python3 scripts/verify.py --managed` uses its normal build admission and shared caches. Ordinary readers use the default Lake commands. Results are written to `verification/publication/receipt.json`; its status and exact source hashes, rather than the existence of a log, determine whether the check passed.

This simple final-root audit is distinct from the broader module/declaration audits in the component receipts. Their declaration counts must not be added together or presented as the size of one combined audit.

## Source-bound development evidence

The existing `scripts/verify-*.py` scripts and their corresponding subdirectories retain the development checks, exact statement/input bindings, native consumers, transitive audits, and independent reviews. They use Horizon's managed environment; they are not the standalone installation requirement for a reader.

| Result | Evidence or exact import binding |
| --- | --- |
| General radial comparison | [main-comparison](main-comparison) |
| Finite-type and manuscript assembly | [manuscript-comparison](manuscript-comparison) |
| Native finite-type presentation | [finite-type-presentation](finite-type-presentation) |
| Global cylindrical construction | [cylindrical-compatibility/construction](cylindrical-compatibility/construction) |
| Relative metric extension | [metric-import.json](cylindrical-compatibility/continuation/metric-import.json) |
| Contact existence | [contact-import.json](cylindrical-compatibility/continuation/contact-import.json) |
| Combined native quotient, constructed reference and comparison | [native integration review](native-integration/final-review.md) |

A component's acceptance requires its exact source, successful snapshot-verified checks, permitted-only transitive axioms, and an independent review of that scope. A queued task, successful publication transport, or compiled target declaration alone does not establish the theorem.

## Final publication checks

The accepted native integration has three snapshot-verified checks, 3,029 permitted-only transitive declaration audits, and independent statement/proof review. Its 876-declaration type/definition inventory includes the actual native quotient, chosen metric, prescribed extension, and comparison endpoints. These counts describe that accepted integration receipt, not the smaller final-root publication check.

The three final publication checks passed with one verified source key, `8f1a301d1c35b2a72aea564e683a3e7f923e2a71061f2312b9b995d41edf9563`. Dependency revisions and cleanliness, all accepted mathematical source bytes, and all thirteen final-root axiom sets were checked. The [document check](document-check.json) records the seven-page theorem PDF and fourteen-page proof PDF, their source hashes, all-page visual inspection, and statement/proof correspondence.

A pending or failed GitHub Actions run is not successful verification. Runtime credentials, provider/session transcripts, and unrelated files are outside the final publication.
