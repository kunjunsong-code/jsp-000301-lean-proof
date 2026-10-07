# JSP-000301 — catalog field correction proposal

**Target file**: `problems/catalog-0301-0400.md#JSP-000301`
**Change type**: `Date proposed` / `Elapsed years`
**Prepared**: 2026-10-07
**Companion Lean evidence**: `Jsp000301.lean`, `PrimeEquiv.lean` (same repository, pinned commit)

---

## 1. Current catalog state

| Field | Current value |
| --- | --- |
| `Date proposed` | `Unspecified; the original proposal date of this yes/no question is unverified.` |
| `Elapsed years` | `Unknown` |
| `Scholarly recognition` | `Independent scholarly review of this scoped record has not been verified.` |

## 2. Why a correction is being proposed

`docs/grading.md:3` states that assessment considers **A — problem longevity**.
Of the eight contributions that have actually been awarded or are under public
review, all six awarded records carry a concrete `Elapsed years` value:

| Problem | Elapsed years |
| --- | --- |
| JSP-000305 | About 46 years (since 1980) |
| JSP-000371 | About 47 years (since 1979) |
| JSP-000381 | About 56 years (since 1970) |
| JSP-000526 | About 31 years (since 1995) |
| JSP-000866 | About 68 years (since 1958) |
| JSP-001001 | About 60 years (since 1966) |

JSP-000301 is the only candidate whose longevity is `Unknown`, which puts the
proposed contribution at a structural disadvantage on dimension A for reasons
that are independent of the quality of the Lean proof.

## 3. Investigation

### 3.1 The maintainers already considered and rejected a date

The `Review notes` for JSP-000301 record a correction dated **2026-09-13**:

> "This disproves the stated yes/no question. This record covers that question
> only, not the separate counting question in Erdős problem #365. **The previous
> 1976→2026 interval is removed because it does not establish the duration of the
> stated question.**"

So an earlier record asserted a 1976 → 2026 interval, and the maintainers
**deliberately removed it** because the cited evidence did not establish when the
*question* was posed. Any new proposal must therefore supply evidence that
actually bears on the posing of the question, not merely on its later discussion.

### 3.2 The source page does not supply a posing date

`https://www.erdosproblems.com/365` lists exactly two Erdős references,
`[Er76d, p.31]` and `[ErGr80, p.68]`. These are 1976 and 1980 — both **after**
Golomb's 1970 counterexample. Neither establishes a posing date, which is
exactly the reasoning the maintainers applied when removing the 1976→2026
interval.

### 3.3 The concept itself originates in 1970

The question is tied to the definition of *powerful numbers*, and that term was
introduced by Solomon W. Golomb in 1970:

- Zentralblatt MATH review **0218.10018**: *"Golomb, S. W. Powerful numbers. Am.
  Math. Mon. 77, 848–852 (1970). The author defines a positive integer (r) to be
  powerful if for every prime (p) dividing (r), (p²) also divides (r)."*
- MathWorld, *Powerful Number*: the term "powerful" traces to Golomb 1970.
- Wikipedia, *Powerful number*: *"Solomon W. Golomb named such numbers
  'powerful'."* — and attributes the study of them to Paul Erdős and George
  Szekeres.

The 1970 paper is the **first** appearance of the definition in print, and it is
also the source of the counterexample recorded for this problem:

> "The answer to the first question is no: Golomb observed that both 12167 and
> 12168 are powerful."

### 3.4 Conclusion

The term and the question are **contemporaneous with 1970** — the defining paper
and the counterexample appear in the same article. This is *earlier* than the
1976/1980 references the catalog previously relied on, so it is a stronger
basis for a longevity interval. It is nevertheless a **lower bound**: it
establishes that the question was already in circulation in 1970, not that it
was first asked in 1970.

## 4. Proposed replacement

Recommended, conservative wording that does not overclaim:

| Field | Proposed value |
| --- | --- |
| `Date proposed` | `No later than 1970 (the term "powerful" and the counterexample were both introduced by Golomb, [Go70], 1970; bibliographic evidence)` |
| `Elapsed years` | `About 56 years (since 1970)` |

`About 56 years` matches the phrasing convention already used by JSP-000381,
which is likewise anchored to 1970.

### Alternative if maintainers prefer strict accuracy

`Elapsed years` could be left as `At least 56 years`, which is logically
impeachable but may not fit the catalog's formatting convention. The applicant
defers to maintainer preference on this point.

## 5. What is *not* claimed

- This proposal does **not** claim to have located the first written statement
  of the question. No source earlier than 1970 has been found.
- This proposal does **not** touch `Scholarly recognition`, which remains
  unverified and should stay that way until independent review exists.
- The `Review notes` scoping decision (covering only the yes/no question, not
  the separate counting question in Erdős #365) is **unchanged** and is endorsed
  here. The Lean proof matches that scope exactly.

## 6. Evidence for the formalization (cross-reference)

The Lean contribution accompanying this proposal is a complete formalization of
the refutation. See the repository README for definitions, proof summary and
reproduction commands. Public evidence may be linked once the commit is pinned.

## 7. Sources consulted

| Source | Use |
| --- | --- |
| `problems/catalog-0301-0400.md#JSP-000301` | Current record, `Review notes` correction of 2026-09-13 |
| `https://www.erdosproblems.com/365` (accessed 2026-10-07) | Original statement, reference list `[Er76d]`, `[ErGr80]`, Golomb/Walker attribution |
| Zentralblatt MATH 0218.10018 | Golomb 1970 as the defining and first source of the term |
| MathWorld, *Powerful Number* | Term attribution to Golomb 1970 |
| Wikipedia, *Powerful number* | Golomb naming; Erdős–Szekeres earlier study |
| zbMATH review of Golomb, *Powerful numbers* | Contents of the 1970 paper, including the counterexample |