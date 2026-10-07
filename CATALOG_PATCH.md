# JSP-000301 — catalog patch (problems/catalog-0301-0400.md)

Target entry: `<a id="JSP-000301"></a>` in
`problems/catalog-0301-0400.md` of `TheJustinSunPrize/awards`.

Only the fields that `CONTRIBUTING.md` permits an external submission to change are
touched: **Lean proof** and **Attribution basis** (plus **Date proposed** /
**Elapsed years**, whose current values are placeholder "Unspecified" / "Unknown"
and which the accompanying evidence now pins down). **Current status** and
**Publication details** already record Golomb's counterexample and are left
exactly as they are. **Eligible to claim** is left as-is per the maintainer note in
`CONTRIBUTING.md` ("Maintainers reconcile the index and eligibility fields after
review").

---

## Replacement table

Replace the JSP-000301 table (the block from `| Date proposed |` through
`| Scholarly recognition |`) with:

```markdown
| Field | Content |
| --- | --- |
| Date proposed | No later than 1970 (bibliographic evidence) |
| Mathematical area | Number theory / Powerful numbers |
| Problem description | If two consecutive positive integers are powerful, must at least one be a perfect square? |
| Current status | Solved<br>Proof contributors: Solomon W. Golomb (counterexample in [Go70], 1970; [attribution source](https://www.erdosproblems.com/latex/365)). |
| Lean proof | Yes — [Lean source](REPLACE_WITH_RAW_URL_TO_Jsp000301.lean)<br>Formalization contributors: REPLACE_WITH_ACCOUNT. |
| Attribution basis | Lean credit follows REPLACE_WITH_ACCOUNT's standalone formalization of Solomon W. Golomb's counterexample in [Go70]. [Solver attribution source](https://www.erdosproblems.com/latex/365); [Lean attribution source](REPLACE_WITH_RAW_URL_TO_PRIMEQUIV.LEAN) |
| Eligible to claim | No |
| Historical bounty |  |
| Elapsed years | About 56 years (since 1970) |
| Publication details | &#91;Go70&#93; [Powerful numbers](https://doi.org/10.2307/2317020) — Amer. Math. Monthly 77(8) (1970), 848-852.<br>&#91;Wa76&#93; [Consecutive integer pairs of powerful numbers and related Diophantine equations](https://doi.org/10.1080/00150517.1976.12430562) — Fibonacci Quart. (1976), 111-116.<br>&#91;Gu04&#93; Unsolved problems in number theory — (2004), xviii+437. |
| Scholarly recognition | Independent scholarly review of this scoped record has not been verified. |
```

---

## Field-by-field rationale

### `Date proposed` — changed

Current value: `Unspecified; the original proposal date of this yes/no question is unverified.`

Proposed value follows the exact wording already used by JSP-000381
(`No later than 1970 (bibliographic evidence)`) and by the neighbouring records.

**Why 1970 and not 1976.** Zentralblatt MATH record 0218.10018 confirms that
Golomb's *Powerful numbers* (Amer. Math. Monthly 77(8), 1970, 848–852) is the
source that introduces the term "powerful" **and** supplies the counterexample in
the same paper. The question therefore cannot postdate its own answer: 1970 is an
upper bound on when the question was posed. This is deliberately the weakest
claim that is still true.

**Explicitly not claimed.** No pre-1970 written statement of the question has been
located. The two commonly cited later sources —
`[Er76d]` (1976, p. 31) and `[ErGr80]` (1980, p. 68), both listed at
`erdosproblems.com/365` — postdate the 1970 counterexample and so **cannot** be
used as the origin date.

**Consistency with the existing Review notes.** The entry's own
`Record correction · Source review 2026-09-13` row states: *"The previous
1976→2026 interval is removed because it does not establish the duration of the
stated question."* The proposed 1970 lower bound **establishes** the duration
(56 years), which is exactly what that note demanded; it does not reintroduce a
1976-based interval.

### `Elapsed years` — changed

Current value: `Unknown`. Proposed value: `About 56 years (since 1970)`, matching
the JSP-000381 format verbatim.

### `Lean proof` — changed

Current value: `No`. Proposed value follows the accepted-entry format:

```
Yes — [Lean source](<pinned raw URL>)<br>Formalization contributors: <account>.
```

The link must be a **commit-pinned raw or blob URL**, not a branch URL.

### `Attribution basis` — added

This field is absent from the current entry and present on accepted entries
(e.g. JSP-000381). It is added because this is a standalone re-formalization of an
existing published counterexample — the same attribution pattern the project has
already accepted, recorded on JSP-000381 as *"standalone re-formalization"*.

### `Current status`, `Publication details` — **unchanged**

Golomb's counterexample and its bibliographic record are already present and
correct. Nothing in this submission adds or removes mathematical content; it adds
a machine-checked formalization of the result that is already recorded.

### `Eligible to claim` — **unchanged (`No`)**

`CONTRIBUTING.md` states: *"Maintainers reconcile the index and eligibility fields
after review."* Leaving it `No` is correct — it flips to `Yes` only once
maintainers accept the proof, per `docs/award-process.md`: *"The catalog's shared
**Eligible to claim** flag is **Yes** only when **Current status** is **Solved**
and **Lean proof** is **Yes**."* Leaving it does not prejudice the outcome.

### `Review notes` — **unchanged**

Not modified. The existing 2026-09-13 source-review row is accurate and its scope
limitation ("covers that question only, not the separate counting question in
Erdős problem #365") is respected: the formalization proves exactly the yes/no
question and says nothing about #365.

### `Scholarly recognition` — **unchanged**

Left as `Independent scholarly review of this scoped record has not been
verified.` No claim of independent scholarly recognition is made, and none is
needed for a Lean contribution.

---

## Scope discipline

The submitted Lean code contains **no source of this catalog text**, no Markdown
table, and no data extracted from the awards repository. It states only the
mathematical definitions of *powerful* and *perfect square* and the refutation
`¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n+1) → IsSquare n ∨ IsSquare (n+1))`.
Per `docs/attribution.md`, this is a statement of a mathematical fact with
independent public provenance, not a reproduction of maintainers' prose.