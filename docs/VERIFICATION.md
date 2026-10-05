# Verification

The project pins Lean 4.24.0 and all mathematical dependencies in `lake-manifest.json`. `verification/library-provenance.json` records the complete fixed mathematical source inventory. `scripts/snapshot.py` hashes the current proof sources, comparison inputs and verification tools. A successful report is relevant only to that exact snapshot.

## Complete library

```sh
lake exe cache get
python3 scripts/verify.py
```

This performs a clean project build and checks every retained mathematical module. The axiom policy permits only `propext`, `Classical.choice` and `Quot.sound`. The proof library does not import specification placeholders. Additional executable regressions or contextual body checks are documented by the commands in `scripts/verify.py`.

The check reuses the pinned public Mathlib cache; it does not rebuild all public dependencies or verify the Lean compiler. Reports and logs are written to `.lake/publication-results/`, which is excluded from the source distribution.

## Official Comparator

The comparison covers **16 theorem targets**. 16 paper contracts are stated separately from their bridge proofs. The specification uses the documented concrete model definitions; the Comparator checks their declaration dependencies as well as the target types.

All official tools are pinned. Linux execution requires an unprivileged account, Landlock ABI 6 or newer, real Landrun, Go 1.24 or newer, and a working user systemd manager. The outer systemd process denies AF_UNIX sockets following upstream security guidance. A shell adapter preserves command argument separators; it does not change the official comparison or kernel code.

```sh
go install github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
export PATH="$(go env GOPATH)/bin:$PATH"
python3 scripts/compare.py
```

The driver fetches and builds the pinned official tools into an external cache. The positive comparison must finish both type checking and fresh kernel replay; a nonzero subprocess exit cannot count as a passed negative control. An added-premise case and an extra-axiom case must each produce the intended official diagnostic.

For reviewed local sources on macOS, `python3 scripts/compare.py --local` explicitly disables process isolation. That mode is useful for development but does not replace the sandboxed Linux CI result.

Comparator proves agreement with the checked specification, not that an informal paper was translated correctly. The paper map, definitions, hypotheses and any source corrections remain part of the mathematical review. The kernel used is Lean’s own default kernel; no external kernel is enabled.

The `Lean checks` workflow runs full library verification and official Comparator independently. Each job uploads its report and complete diagnostic logs, including on failure. Source reports must agree on the same source snapshot before release.
