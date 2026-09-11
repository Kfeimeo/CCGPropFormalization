# tools/ — bounded enumerator for the left-to-right audits

`ltr_enum.py` implements every rule studied in the Lean rounds as a switchable option
(FA/BA, generalized harmonic + crossed composition, ASP, AC, GAC, D, SA, ASF, S-/goal-targeted TR,
TR with a finite target pool) and answers derivability / grammatical-acceptability questions by
bounded CKY (categories larger than `maxsize` nodes are dropped).  Positive answers are real
derivations; negative answers are *bounded* negatives.

* `calibrate.py` — replays 17 machine-checked results of rounds 1–7 (all match).
* `scan.py L` — exhaustive scan of all sentences up to length `L` over a natural, TMA-compliant
  lexicon (27 categories, no `X/X` / `X\X`), goals `S` and `Sq`; reports sentences derivable by
  FA/BA + Bⁿ that are not grammatically acceptable in `fullLTRs [S, Sq]`
  (FA/BA + Bⁿ + ASP + AC + GAC + D + clause-type TR), re-checked with a larger bound and
  classified by whether the original derivation needs crossed composition.
* `recheck.py` — the eleven length-4 failures of the first scan, re-examined.
* `results/scan5.txt` — full output of `python3 scan.py 5` (105 bounded failures, all needing crossed composition).

```
python3 calibrate.py
python3 scan.py 4
```
