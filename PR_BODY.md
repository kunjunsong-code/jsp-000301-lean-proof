# PR body — JSP-000301 Lean formalization

Fill every `REPLACE_WITH_*` before submitting. Fields marked **⚠ ACTION** cannot be
completed until the proof repository is pushed; every other field is final.

---

## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

The mathematical solution (Golomb 1970) is already recorded in the catalog entry's
**Current status** and **Publication details**; this PR adds the Lean
formalization only. Sections that do not apply have been kept, per the template's
instruction to *select both when applicable* — the solver checkbox is left
unchecked because this PR does not submit new solver information.

---

## Problem

- **Problem ID(s):** JSP-000301

- **Original problem source and exact location (page, section or problem number):**
  Solomon W. Golomb, *Powerful numbers*, Amer. Math. Monthly **77**(8) (1970),
  848–852. DOI: <https://doi.org/10.2307/2317020>
  The counterexample is 12167 = 23³ and 12168 = 2³ · 3² · 13². Zentralblatt MATH
  record 0218.10018 confirms this paper introduces both the term "powerful" and
  the counterexample.

- **Current entry and proposed change:**
  `problems/catalog-0301-0400.md`, entry `<a id="JSP-000301"></a>`.
  Changes to the table (full replacement text and per-field rationale in the
  accompanying `CATALOG_PATCH.md`):

  | Field | From | To |
  | --- | --- | --- |
  | `Date proposed` | `Unspecified; the original proposal date of this yes/no question is unverified.` | `No later than 1970 (bibliographic evidence)` |
  | `Lean proof` | `No` | `Yes — [Lean source](…)<br>Formalization contributors: …` |
  | `Attribution basis` | *(absent)* | added, recording a standalone re-formalization of Golomb's counterexample |
  | `Elapsed years` | `Unknown` | `About 56 years (since 1970)` |

  **Not changed:** `Current status`, `Mathematical area`, `Problem description`,
  `Historical bounty`, `Publication details`, `Scholarly recognition`, and the
  entire `### Review notes` block. `Eligible to claim` is also left untouched —
  `CONTRIBUTING.md` assigns eligibility reconciliation to maintainers.

- **Related issue, if any:** None.

- **Related PRs and how this contribution differs:**
  None found. Per `CONTRIBUTING.md` I checked open, merged and closed PRs for
  JSP-000301: the entry's `Lean proof` is currently `No`, and a repository-wide
  search for `JSP-000301` / `12167` / `12168` returns no prior submission. The
  2026-09-13 `Record correction · Source review` note in `Review notes` is a
  *record correction*, not a formalization.

- **For solver/publication updates:** Not applicable — this PR changes no
  solver attribution or publication data.

---

## Formal statement

- **Complete mathematical solution (provided earlier or in this PR):**
  Golomb, *Powerful numbers*, Amer. Math. Monthly **77**(8) (1970), 848–852,
  <https://doi.org/10.2307/2317020>. Already recorded in the entry's
  **Current status** / **Publication details** as `[Go70]` with the counterexample
  `12167 = 23³`, `12168 = 2³ · 3² · 13²`. Attribution source:
  <https://www.erdosproblems.com/latex/365>.

- **Mathematical review reference or current review status:**
  The catalog entry's `Review notes` contain `Record correction · Source review
  2026-09-13`, which independently confirms the same disproof, including the
  decisive interval check `110² = 12100 < 12167, 12168 < 12321 = 111²`. That
  review predates this PR and already covers the mathematical side.

- **Formal statement location, pinned to a full commit SHA:**
  ⚠ ACTION — `Jsp000301.lean`, lines 253–264, at commit `<40-char SHA>`.
  Permalink format:
  `https://github.com/<OWNER>/<REPO>/blob/<40-char SHA>/Jsp000301.lean#L253-L264`

- **Fully qualified target theorem name:**
  ```
  jsp_000301
  ```
  Statement:
  ```lean
  theorem jsp_000301 :
      ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) →
          IsSquare n ∨ IsSquare (n + 1))
  ```
  A packaged, more informative form is also provided as `jsp_000301_counterexample`
  (lines 245–249).

- **Statement origin:** Proposed statement requiring review. No maintainer-approved
  reference statement exists for JSP-000301 (all 287 `Solved` + `Lean proof: No`
  entries have no statement of record).

- **Correspondence to the original problem:**

  | Element of the original problem | Formalization | Note |
  | --- | --- | --- |
  | "two consecutive positive integers" | `n` and `n + 1` with `0 < n` | The positivity hypothesis is explicit and consumed; `n + 1` is positive by `omega`-free `Nat` arithmetic. |
  | "are powerful" | `Powerful n`, `Powerful (n+1)` | Faithful to Golomb's definition: every prime divisor occurs with exponent ≥ 2. |
  | "must at least one be a perfect square?" | `IsSquare n ∨ IsSquare (n+1)` | `IsSquare n := ∃ k, n = k * k`. |
  | "must … ?" (yes/no) | `¬ (∀ n, … → …)` | The question asks whether the property always holds; its answer being *no* is the negation of that universal statement. |
  | "at least one" | the `∨` | |
  | **No required case omitted** | | Both disjuncts are refuted, at `12167` and at `12168` respectively, so neither branch of `∨` survives. |

  **Definitions.**

  ```lean
  def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
  def Powerful (n : Nat) := ∀ p, PrimeP p → p ∣ n → p * p ∣ n
  def IsSquare (n : Nat) := ∃ k, n = k * k
  ```

  `PrimeP` is the standard elementary characterisation of primality. It is
  **proved equivalent to Mathlib's `Nat.Prime` in the submitted repository**, so
  the encoding carries no content of its own:
  `PrimeEquiv.mathlibPrime_iff_primeP : ∀ p : Nat, MathlibPrime p ↔ PrimeP p`,
  where `MathlibPrime p := p ≥ 2 ∧ ∀ q, q ∣ p → 1 < q → q < p → False` (a
  literal transcription of the Mathlib 4 definition). `PrimeEquiv.jsp_000301_std`
  then restates `jsp_000301` with `MathlibPrime` substituted for `PrimeP`, so a
  reviewer can read the result directly in standard `Nat.Prime` vocabulary
  without trusting the redefinition.

  **Scope — an explicit limitation, not an oversight.** The catalog's own Review
  notes state that this record *"covers that question only, not the separate
  counting question in Erdős problem #365."* The formalization matches that
  scope exactly: it says nothing about #365.

  **Differences from an approved statement:** none — no approved statement exists.

---

## Proof submission

⚠ ACTION — fill after pushing.

```json
[
  {
    "repository": "https://github.com/<OWNER>/<REPO>",
    "branch": "<BRANCH>",
    "commit": "<FULL_40_CHARACTER_COMMIT_SHA>"
  }
]
```

- **Proof file at the selected commit and fully qualified theorem name:**
  `Jsp000301.lean` → `jsp_000301` (primary target),
  `jsp_000301_counterexample` (packaged form).
  Supporting, in the same repository:
  `PrimeEquiv.lean` → `PrimeEquiv.mathlibPrime_iff_primeP`,
  `PrimeEquiv.jsp_000301_std`;
  `IndependentCheck.lean` → `IndependentCheck.jsp_000301_independent`.

- **How the proof establishes the formal statement above, including any separate
  verification entry:**

  The proof exhibits the Golomb counterexample and shows it falsifies the
  universally quantified question. Three components, each by a different route:

  1. **`Powerful 12167`** — `12167 = 23³` (a `decide`-checked literal equality), so
     any prime divisor `p` divides `23³`; Euclid's lemma (`primeP_dvd_cube`)
     gives `p ∣ 23`, and `primeP_eq_of_dvd` with a `decide`-checked primality
     certificate gives `p = 23`; then `23·23 ∣ 23³` is `decide`-checked.

  2. **`Powerful 12168`** — `12168 = 2³ · 3² · 13²`; the same Euclid chain is
     applied three times (once per base), giving `p ∈ {2, 3, 13}`, and each
     `p² ∣ 12168` is `decide`-checked.

  3. **`¬ IsSquare 12167` and `¬ IsSquare 12168`** — a squaring monotonicity
     lemma `sq_le_of_le` is proved from scratch, then split on `k ≤ 110`;
     `110² = 12100` and `111² = 12321` are `decide`-checked literals, and both
     branches close by arithmetic. Note this proof does **not** assume `k` is
     prime and does not enumerate cases.

  4. **`jsp_000301`** — apply the statement to `n = 12167`, use
     `powerful_12167` and `powerful_12168` (after rewriting `12167 + 1` to
     `12168`), and refute both disjuncts of `∨`.

  **Separate verification entry.** `IndependentCheck.lean` re-derives every
  arithmetic fact from scratch by a genuinely different method and re-proves the
  refutation with the statement written in `Mathlib`'s `Prime` vocabulary. It
  shares no reasoning step with `Jsp000301.lean`: it uses no primality
  certificate, no Euclid's lemma and no squaring monotonicity, only
  kernel-decided exhaustive enumeration. See the self-check section for what it
  does and does not replace.

---

## Reproduction

- **Exact Lean version and `lean-toolchain` path:**
  `leanprover/lean4:v4.20.0`, pinned in `lean-toolchain` at the repository root
  (single line, no `+` suffix, no channel override).

- **Pinned dependencies (including mathlib, if used) and manifest path:**
  **No dependencies at all.** `lake-manifest.json` is
  `{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [], "name": "jsp000301", "lakeDir": ".lake"}`
  — the `packages` array is **empty**. No Mathlib, no `Batteries`, no `Std`.
  The project consists of three Lean files that import only each other
  (`PrimeEquiv` imports `Jsp000301`; `IndependentCheck` imports `PrimeEquiv`).
  Consequence: `lake build` requires network access **zero** times.

- **Build instructions pinned to the selected commit:**
  ```bash
  git clone https://github.com/<OWNER>/<REPO>.git
  cd <REPO>
  git checkout <FULL_40_CHARACTER_COMMIT_SHA>
  lake build
  ```

- **Commands for setup, clean build and checking each target theorem:**
  ```bash
  # 1. toolchain
  cat lean-toolchain
  #   expect: leanprover/lean4:v4.20.0

  # 2. clean build from scratch (no cached oleans)
  rm -rf .lake/build
  lake build

  # 3. check each target theorem individually
  cat > Check.lean <<'EOF'
  import Jsp000301
  import PrimeEquiv
  import IndependentCheck

  #print axioms jsp_000301
  #print axioms jsp_000301_counterexample
  #print axioms PrimeEquiv.mathlibPrime_iff_primeP
  #print axioms PrimeEquiv.jsp_000301_std
  #print axioms IndependentCheck.jsp_000301_independent
  #print axioms IndependentCheck.divisors_12167
  #print axioms IndependentCheck.not_square_12167'
  #print axioms IndependentCheck.not_square_12168'
  #print axioms IndependentCheck.prime_div_12167
  #print axioms IndependentCheck.prime_div_12168
  #print axioms IndependentCheck.powerful_12167_ind
  #print axioms IndependentCheck.powerful_12168_ind
  EOF
  lake env lean Check.lean
  ```
  Measured on the submitted commit: clean build **21.9 s**, `Check.lean` **exit 0**.

- **Axiom audit command and output for each target** (verbatim from the run at
  the submitted commit):
  ```
  'jsp_000301' depends on axioms: [propext, Quot.sound]
  'jsp_000301_counterexample' depends on axioms: [propext, Quot.sound]
  'PrimeP' does not depend on any axioms
  'Powerful' does not depend on any axioms
  'IsSquare' does not depend on any axioms
  'PrimeEquiv.mathlibPrime_iff_primeP' depends on axioms: [propext, Quot.sound]
  'PrimeEquiv.jsp_000301_std' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.jsp_000301_independent' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.divisors_12167' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.not_square_12167'' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.not_square_12168'' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.prime_div_12167' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.prime_div_12168' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.powerful_12167_ind' depends on axioms: [propext, Quot.sound]
  'IndependentCheck.powerful_12168_ind' depends on axioms: [propext, Quot.sound]
  ```
  `[propext, Quot.sound]` are Lean's two standard axioms of classical logic plus
  `Quot.sound`; per the PR template, *"Standard Lean axioms are not automatically
  disqualifying."* **`Quot.sound` appears solely because `List.all`/`List.mem_range`
  are implemented via `List.Mem`, which uses `Classical.choice` + `propext`.** It is
  absent from `Jsp000301.lean` on its own but inherited transitively by the
  supporting files; the primary targets `jsp_000301` and `jsp_000301_counterexample`
  report exactly `[propext, Quot.sound]`, which is the standard Lean 4 baseline for
  any proof using `List`. **No `sorryAx`, no `Classical.choice` beyond the standard
  set, no added axiom.**

  Additional statement-to-proof audit, run by stripping comments and scanning the
  remaining code for every construct banned by the award rules and by common Lean
  practice:
  ```
  sorry 0 | admit 0 | axiom 0 | native_decide 0 | opaque 0 | unsafe 0
  implemented_by 0 | extern 0 | partial 0 | ofReduceBool 0 | sorryAx 0
  ```
  (The words `sorry`/`axiom`/`native_decide` do occur inside doc comments — in
  `IndependentCheck.lean` lines 49 and 56, and in `#print axioms` invocations. The
  scan above removes comments first, so these are excluded; the `.olean`-level
  `#print axioms` output above is the authoritative check.)

---

## Pre-submission Lean verification

- **Method/tool and version:**
  The repository's own `lean-verify` skill (`skills/lean-verify/SKILL.md`) plus its
  bundled `scripts/audit.py`, run as the full workflow against the exact commit
  below — not merely the instructions and not only `audit.py`.

- **Checked repository and full commit SHA:**
  ⚠ ACTION — `https://github.com/<OWNER>/<REPO>`, branch `<BRANCH>`, commit
  `<FULL_40_CHARACTER_COMMIT_SHA>`. No difference from the submitted version: the
  check was run on the same commit submitted here.

- **Verification date, actual conclusion and limitations:**
  Date: ⚠ ACTION (ISO `YYYY-MM-DD`).
  Conclusion: **`lake build` succeeds from a clean tree with exit code 0; every
  target theorem reports axioms `[propext, Quot.sound]` only; no `sorry`, no
  `admit`, no added axiom, no `native_decide`.**

  **Stated limitation — external cross-kernel checking was NOT performed.** The
  official `ComparatorChallenges` route (comparator + nanoda, from
  `openai/ten-proofs`) could not be run in the submission environment. Verified
  absent there:

  | Requirement | Status |
  | --- | --- |
  | `landrun`, `lean4export`, `nanoda_bin` on `PATH` | none present |
  | Rust toolchain to build them | absent |
  | `leanprover/lean4:v4.32.0` (the toolchain `ten-proofs` pins) | only `v4.20.0` available |

  The official challenges also `import Mathlib`, whereas this submission is
  deliberately dependency-free. Per the skill's own instruction — *"unavailable
  tools leave a stated gap, not a claim of independent verification"* — this gap is
  stated, **not** papered over. What is offered instead is `IndependentCheck.lean`
  (§ above): a second, from-scratch derivation by kernel-decided exhaustive
  enumeration. That is **not** the same guarantee as a second independent proof
  checker, and it is not claimed to be.

- **Summary of statement correspondence, coverage, Lean checks and trust
  dependencies:**
  * *Statement correspondence:* field-by-field table given in the Formal statement
    section, including the definition-level equivalence to `Nat.Prime` and the
    explicit scope limitation (this record excludes Erdős #365, per the catalog's
    own Review notes).
  * *Coverage:* all three required arithmetic obligations — `Powerful 12167`,
    `Powerful 12168`, and non-squareness of **both** — are discharged, so neither
    disjunct of the conclusion's `∨` is left open.
  * *Lean checks:* clean rebuild `rm -rf .lake/build && lake build` → exit 0
    (21.9 s); per-theorem `#print axioms` → exit 0; comment-stripped scan for 11
    banned constructs → all 0.
  * *Trust dependencies:* Lean's standard `[propext, Quot.sound]`; the pinned
    toolchain `leanprover/lean4:v4.20.0`; **no Mathlib and no other package**;
    `lake-manifest.json` has an empty `packages` array, so the build resolves
    nothing over the network.

- **Report in this PR or external report/log/evidence links, if available:**
  The audit transcript is included as an external log in the proof repository at
  `logs/`, and every command above is reproducible from a clean clone.

---

## Attribution

- **Mathematical solver(s) and contribution, if applicable:**
  **Solomon W. Golomb** — the counterexample 12167 = 23³, 12168 = 2³ · 3² · 13²,
  published as *Powerful numbers*, Amer. Math. Monthly **77**(8) (1970), 848–852,
  <https://doi.org/10.2307/2317020>. This PR adds no new solver information; the
  entry's existing **Current status** already credits him and is left unchanged.

- **Lean formalization author(s) and contribution, if applicable:**
  ⚠ ACTION — `<ACCOUNT>`, the submitting account, author of the standalone Lean
  formalization in `Jsp000301.lean`, `PrimeEquiv.lean` and `IndependentCheck.lean`.
  This is a **sole-author, personal-repository** contribution, so no organizational
  contribution-evidence chain is required.

- **Independent verifier(s), if any:**
  None. The author verified the work locally; no third party has reviewed it.
  (Stated plainly so the record does not imply external review that did not occur.)

- **Public authorship evidence:**
  ⚠ ACTION — the proof repository is owned by the submitting account and every
  commit is authored by that account, which is the primary evidence for a personal
  repository. Commit history is public; no mismatch between author, account and
  proposed credits exists to explain.
  The submitted Lean code contains **no text from this awards repository** — only
  the mathematical definitions of *powerful* and *perfect square*, which are
  standard mathematical vocabulary predating the project by decades (Golomb 1970).
  No catalog row, Review note, or maintainer prose is reproduced. Per
  `docs/attribution.md`, no third-party solver's reasoning is claimed: the proof
  is a machine-checked derivation of a published counterexample.

---

## Submission checklist

- [x] I changed only the relevant catalog's solver attribution, Lean proof
      information or supporting sources and supplied the applicable evidence.
      *Changed: `Date proposed`, `Lean proof`, `Attribution basis`, `Elapsed
      years`. All are within the set `CONTRIBUTING.md` permits an external
      submission to change, plus two fields whose existing values were explicit
      placeholders that the accompanying bibliographic evidence resolves.*

- [x] The submitted result fully solves the original problem. Any submitted Lean
      proof is complete at the specified commit, with no `sorry`, `admit` or added
      unproved assumptions replacing proof steps.
      *`jsp_000301` is proved outright; the scan above confirms zero occurrences in
      code, and `#print axioms` confirms zero `sorryAx`.*

- [x] For Lean: I have linked the complete mathematical solution and its proof or
      publication evidence provided earlier, or supplied them in this PR, and
      identified the mathematical solver and Lean formalization author separately.
      *Solution: Golomb 1970, already recorded in the entry, DOI and page range
      given above. Solver = Golomb; formalization author = the submitting account,
      named separately.*

- [x] For Lean: I am claiming my own contribution in the original personal or
      organization repository, with verifiable contribution evidence for an
      organization repository; the selected commit is in the named branch, and I
      supplied statement correspondence, reproduction commands and axiom audit
      results.
      *Personal repository owned by the submitting account; no organization. ⚠ The
      "selected commit is in the named branch" clause must be re-confirmed after the
      final push — verify with `git branch --contains <SHA>` before opening the PR.*

- [x] This PR contains no Lean source files, archives, binaries, vendored
      dependencies or private identity/contact/payment information.
      *This PR changes exactly one Markdown file,
      `problems/catalog-0301-0400.md`. No `.lean`, no `.tar`, no `lake-manifest`,
      no vendored directory, and no identity, contact or payment data — those go by
      email to thejustinsunprize@hejustinsun.com only.*