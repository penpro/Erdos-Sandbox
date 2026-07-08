# PROVENANCE — Erdős #488 Sandbox Collaboration

> **Curation note (Claude-main, 2026-07-07).** Assembled by a provenance
> subagent from the shared chat, the workflow journals, file mtimes, and the
> subagent reports, then reviewed by me. Two later developments post-date it
> and live in `adversary_collab_chat.md`: (i) **Proposition 8''** — the charge
> argument generalizes to primitive sets of any size under a charge-positivity
> hypothesis (verified on 924 sets, sizes 3–6); (ii) a proposed |P|=4 boundary
> rescue conjecture was **falsified** (`{6,10,15,25}`). Standalone note:
> `writeup/erdos488_triples.{tex,pdf}`.

---


**Scope:** `D:\Erdos Sandbox` · **Date of work:** all events 2026-07-07 (local `-0700`) · **Compiled:** 2026-07-07

## 0. Sources and attribution method

Every row below is grounded in one of: (a) a dated, author-tagged entry in `adversary_collab_chat.md`; (b) a file mtime from `ls --time-style=full-iso`; (c) a subagent report `tmp/wf_result_*.md`; (d) the workflow journal `…/wf_046c451b-656/journal.jsonl` + `agent-*.jsonl` (model + task prompt). No timestamp is invented.

**Actors** (labels used throughout):

| Label | Identity | Model (evidence) |
|---|---|---|
| **Human** | Wes (`penpro`) | — |
| **Claude-main** | orchestrating Claude Code agent (ran the workflow, wrote corrections) | not recorded in the workflow journal (journal logs only subagents) |
| **Codex** | OpenAI Codex collaborator (chat tag `Codex`) | not recorded in these artifacts |
| **Sub:thread-audit** | `a30cf8a95fd7761e0` | `claude-fable-5` (agent jsonl) |
| **Sub:methods-survey** | `a0184db1f36725190` | `claude-fable-5` |
| **Sub:728-verify** | `a91f3a3e574e558ca` | `claude-fable-5` |
| **Sub:attack** | `a8eb4501afb88b28f` | `claude-fable-5` |
| **Sub:adversary-verify** | `a369bd6b9e2c62577` | `claude-fable-5` + `<synthetic>` — **crashed** ("API Error: Server error mid-response"); no journal `result` |

All five subagents were spawned by workflow `wf_046c451b-656` (all `.meta.json` mtime `14:21`; `journal.jsonl` records 5 `started`, only 4 `result`). Each `.meta.json` carries only `{"agentType":"workflow-subagent","spawnDepth":1}` — labels/models were recovered from each agent's first user prompt and `message.model` in `agent-*.jsonl`.

**Attribution caveat (honest):** some pre-workflow files are first-person and untagged. I split Codex vs Claude-main using the strongest available signals — chat tags, and the fact that `counterexample_search.py` (Claude-main) explicitly *preserved a pre-existing Codex script* as `codex_leftover_counterexample_search.py` before overwriting the filename (its own header note; the #728 verify report confirms that leftover is "codex's numeric check script"). Where authorship of an elementary lemma is genuinely shared, I say so rather than guess.

---

## 1. TIMELINE

| Time (2026-07-07) | Actor | What happened | Artifact (evidence) |
|---|---|---|---|
| 13:26:28 | Claude-main | First forum fetch of candidate comments | `scratch_comments.txt` (mtime) |
| 13:27:12 | Claude-main | Wrote problem-page fetch helper (browser-UA curl; plain fetch 403s) | `scripts_fetch.py` (mtime) |
| 13:27–13:38 | Claude-main | Fetched ~40 candidate problem pages (#129,#287,#375,#458,#488,#699,…) and ran recon probes | `scratch_problem_*.txt`, `scratch_probe.py` (13:30), `scratch_probe488.py` (13:32), `scratch_probe488b.py` (13:38) |
| 13:50:54 | Claude-main | **Problem selection.** Scanned ambiguous/falsifiable/AI-gap clusters; picked #488 as "true & tight ⇒ target is a proof" | `candidate_scan.md` (mtime; selection table) |
| 13:51:27 | Claude-main | **Statement + typo resolution.** Fixed the [Er61] non-multiples typo *independently from Erdős's own sharpness witness* (`A={a},n=2a−1,m=2a` ⇒ ratio→2 only under the multiples reading); logged singleton + dense-half + complement reduction as "Done" in the attack plan | `selected_problem.md` (mtime; "The typo, resolved independently") |
| 13:56:39 | Claude-main | Preserved a pre-existing **Codex** #728 script before reusing its filename | `codex_leftover_counterexample_search.py` (mtime; note in `counterexample_search.py` header) |
| 13:57:03 | Claude-main | **Singleton sharpness + large search + alternate-version disproof** driver: verify multiples (★) is true/tight, confirm `2−1/a`, disprove literal non-multiples version (`A=primes≤n,m=2n`, ratio→∞) | `counterexample_search.py` (mtime) |
| 13:57:28 | Claude-main | Exhaustive small-domain verifier (`A⊆{2..15}, |A|≤3, m≤200`) | `verify_exhaustive.py` (mtime) |
| 13:58:34 | Claude-main | Preserved Codex's old results file | `codex_leftover_computational_results.md` (mtime) |
| 13:59–14:00 | Codex | **#728 formulation audit** (later judged non-novel): degenerate large-`a,b` construction | `problem_728_formulation_audit/findings_728.tex` (13:59), `….pdf` (14:00) |
| 14:16:02 | Codex | **Min-3 certificates (Theorem 7).** Exact periodicity certificates for the 5 exceptional `{3,b,c}` triples (`{3,4,5},{3,4,7},{3,4,10},{3,4,11},{3,5,7}`) | `verify_min3_triples.py` (mtime); chat *Codex "Active target #488"* claim 5 |
| ~14:1x | Codex | **Reciprocal-sparse Theorem 6** (`Σ_{d∈P}1/d ≤ 2/min P ⇒ (★)`) written into the shared proof file, generalizing the public 2-element case | `proof_attempt.md` §3A; chat *Codex "Active target #488"* claim 4 |
| 14:21:16–18 | Human/Claude-main | Project rules committed (initial git commit `167aa33`) | `AGENTS.md` (14:21:16), `CLAUDE.md` (14:21:18) |
| **14:21** | Claude-main | **Workflow `wf_046c451b-656` launched 5 subagents** (thread-audit, methods-survey, 728-verify, attack, adversary-verify) | all `agent-*.meta.json` mtime 14:21; `journal.jsonl` 5×`started` |
| 14:21:28–14:29 | Sub:thread-audit | Fetched #488 page, 30-post forum thread, Chojecki note+Lean bundle, two MalekZ PDFs | `scratch_problem_488.txt` (14:21), `scratch_forum_488_parsed.txt` (14:22), `scratch_chojecki_488.txt` (14:23), `scratch_malekz_note.txt` (14:26), `scratch_malekz_tripod.txt` (14:29) |
| ~14:24 | Sub:adversary-verify | **Crashed mid-response** (server error); produced no result and no artifact | `agent-a369bd6b9e2c62577.jsonl` last text = "API Error…"; absent from journal `result`s |
| 14:30:56 | Claude-main | Independent criterion sweep tool (`δ ≥ S/2` and per-period `B(n) > nS/2` over triples and 4-sets) | `sweep_criterion.py` (mtime); chat *Claude "Audit of verify_triples_min_leq.py"* |
| 14:32:45 | Sub:methods-survey | **AI-methods survey delivered.** Catalog of AI-solved Erdős problems; deep dives on #728/#650/#690/#1026; **Idea 1 = two-sided Bonferroni + finite exceptional region (template #690)** | `tmp/wf_result_a0184db1f36725190.md` (mtime) |
| 14:32:45 | Sub:thread-audit | **Public-priority audit delivered** (Chojecki/MalekZ/Tao/Blair; 30-post catalog; item-by-item PUBLIC verdicts) | `tmp/wf_result_a30cf8a95fd7761e0.md` (mtime) |
| 14:42:09 | Codex | **Bounded-triple certificate (Theorem 8).** `verify_triples_min_leq.py 20` → 6944 reciprocal-heavy triples PASS; worst `{19,20,21}` β/α=666/361 | `verify_triples_min_leq.py` (mtime); chat *Codex "Bounded primitive triples certified"* |
| 14:43:56 | Sub:728-verify | **#728 verify delivered.** Codex's audit is arithmetically correct but is a restatement of the AlphaProof caveat already on the #728 page (since 2025-10-20); #728 proved (Lean) Jan 2026 | `tmp/wf_result_a91f3a3e574e558ca.md` (mtime) |
| 14:46 | Codex/Claude-main | #728 findings md finalized (Claude addendum noting it's the page's own caveat) | `problem_728_formulation_audit/findings_728.md` (mtime) |
| 14:48:36 | Claude-main | **Literature notes + CORRECTION section** absorbing the thread audit (dense-half, union-bound, 2∈A, periodicity, witness-typo all PUBLIC; Chojecki Cor 4.7 = size-≤3, Lean modulo one `sorry`) | `literature_notes.md` (mtime; "CORRECTION … materially incomplete") |
| 14:48 | Claude-main | Adversarial review of Codex's four requests; confirms Thm 6/7/8 sound; flags subsumption by Chojecki Lemma 6.3 / Cor 4.7 | chat *Claude "Adversarial review of the four requests"* |
| 15:02:32 | Sub:attack | **Attack verification code lands** — general triple proof engine (charge decomposition + two-sided Bonferroni) | `attack_triples.py` (mtime) |
| 15:04:07 | Sub:attack | **General Theorem 9 delivered.** (★) for every primitive core `|P|≤3` via `2B(n) > nS` (Lemmas 1–5, Thm 8, Cor 8'); verified at scale | `tmp/wf_result_a8eb4501afb88b28f.md` (mtime) |
| 15:10:20 | Claude-main | Rigorous writeup of Theorem 9 (Lemmas 1–5, Thm 8, Cor 8', Thm 9, sharpness, `|P|≥4` open) | `triples_writeup.md` (mtime) |
| 15:10:59 | Claude-main | **Chat finalized:** logs `PROVED` |P|≤3 (line-by-line audit + independent re-runs), the two `PUBLIC` Corrections, the `BROKEN` `|P|≥4` conjecture, the #488-two-element and #728 Codex entries | `adversary_collab_chat.md` (mtime) |
| 15:11:32 | Claude-main | Marked consecutive-triples lead `SUPERSEDED` by Theorem 9 | `consecutive_triples_notes.md` (mtime) |
| 15:11:48 | Claude-main | proof_attempt.md status update + inline audit/priority notes (Thm 9 subsumes §2/Cor 5/§3A/§3B; `2B(n)>nS` false in general) | `proof_attempt.md` (mtime) |
| 15:12:21 | Claude-main | Final report: verdict "partial result", corrected-framing, direction-(a)-DONE update, `|P|≥4` counterexample recorded | `final_report.md` (mtime) |
| 15:12:48 | Claude-main | Computational results ledger (R1–R10) finalized | `computational_results.md` (mtime) |

---

## 2. ATTRIBUTION LEDGER

Claim → first in-sandbox producer → public-priority status (tags pulled from `adversary_collab_chat.md` Corrections + `tmp/wf_result_a30cf8a95fd7761e0.md`).

| # | Mathematical claim | First produced in-sandbox by | Public-priority status | Citation |
|---|---|---|---|---|
| 1 | Intended version is *multiples* (typo resolved via Erdős's own sharpness witness) | Claude-main | **PUBLIC** — BorisAlexeev posts 1860–1865 (27 Nov 2025) made the same witness argument first | `selected_problem.md`; thread-audit §1; `literature_notes.md` correction |
| 2 | Singleton case sharp: ratio `2−1/a`, extremal family unique | Claude-main (Prop 1) | **PUBLIC** — Chojecki Thm 3.1 (Lean, no sorry) | `proof_attempt.md` §2; thread-audit §2 |
| 3 | Dense half: `B(n) ≥ n/2 ⇒ (★)` (complement form `2C(n)/n − C(m)/m < 1`) | Claude-main (Thm 3, Lemma 2) | **PUBLIC** — Chojecki Prop 6.1 (`Dense.lean`); inline in MalekZ 5163 | `proof_attempt.md` §3; thread-audit §3(a) |
| 4 | Union-bound / single-time criterion `B(n) > nS/2 ⇒ (★) at n` | Claude-main / Codex (implicit in Thm 6; tooled in `sweep_criterion.py`) | **PUBLIC** — Chojecki Lemma 6.3 + Prop 5.1 (`UnionBound.lean`, Lean) | thread-audit §3(b) |
| 5 | `2 ∈ A` case | Claude-main (Cor 5, clean proof replacing an earlier sketch) | **PUBLIC** — MalekZ post 5163 (31 Mar 2026) | `proof_attempt.md` Cor 5 note; thread-audit §3(c); chat *Codex "#488 two-element case is public"* |
| 6 | Reciprocal-sparse **Theorem 6** (`Σ1/d ≤ 2/min P ⇒ (★)`) | **Codex** | **thin-novelty** — not stated publicly, but a 2-line corollary of public Lemma 6.3 + `B(n)≥⌊n/a⌋+1`; its `|A|=2` case is Will Blair post 6864 (06 Jun 2026). Must cite both | `proof_attempt.md` §3A; chat *Codex "Active target"* claim 4 + *Claude review R1*; thread-audit §3(f) |
| 7 | **Theorem 7** — 5 `{3,b,c}` periodicity certificates complete | **Codex** | **independent-verification** — subsumed by Chojecki Cor 4.7 (claimed, Lean modulo one `sorry`); method (periodicity) PUBLIC (MalekZ 5089/5101) | `proof_attempt.md` §3B; `verify_min3_triples.py`; chat *Claude review R2/R3* |
| 8 | **Theorem 8** — exact certificate, all primitive triples `min ≤ 20` | **Codex** | **independent-verification** — same subsumption as Thm 7; certificate-lemma phrasing internal only | `proof_attempt.md` §3C; `verify_triples_min_leq.py`; chat *Codex "Bounded…"* + *Claude "Audit of verify_triples_min_leq.py"* |
| 9 | **Theorem 9** — (★) for every primitive core `|P| ≤ 3`, sorry-free, via charge decomposition `s(n)−2P(n)=X_a+X_b+X_c ≥ 3` ⇒ `2B(n) > nS` | **Sub:attack** (`a8eb4501`, claude-fable-5); audited + written up by Claude-main | **independent, sorry-free elementary proof of a CLAIMED result — NOT a new result, NOT a new method.** RESULT is Chojecki Cor 4.7 (Lean modulo one `sorry`; community treats `|A|≥3` open); method backbone is classical (Heilbronn–Rohrbach); only the finitary charge-integrality packaging is candidate-new (low weight) | `tmp/wf_result_a8eb4501afb88b28f.md`; `triples_writeup.md`; chat *Claude "PROVED … size ≤ 3"* (tag `PROVED`/`NOVEL?`) |
| 10 | `δ ≥ S/2` per-`A` decision + necessary condition `inf g ≥ δ/2` | Claude-main / Codex | **thin-novelty** — not explicitly public; "small novelty at most" | `proof_attempt.md` §4; thread-audit §3(e) |
| 11 | Alternate (non-multiples) version is **false**, ratio→∞ | Claude-main | **PUBLIC** — Cambie/Alexeev/Aristotle counterexamples on #488 page | `counterexample_search.py` job III; `literature_notes.md` |
| 12 | Universal conjecture "`2B(n) > nS` for every primitive `P`" | (drafted in `triples_writeup.md` §7 by Sub:attack) | **BROKEN** — see Honesty Ledger #H4 | chat *Claude "BROKEN…"* (tag `BROKEN`) |
| 13 | #728 degenerate-solution construction | Codex (`findings_728.*`) | **PUBLIC / BROKEN-AS-NOVEL** — verbatim the AlphaProof caveat on the #728 page since 2025-10-20; #728 proved (Lean) Jan 2026 | `problem_728_formulation_audit/findings_728.md`; `tmp/wf_result_a91f3a3e574e558ca.md`; chat *Codex "#728 is not publishable"* |

---

## 3. METHOD PROVENANCE

**Periodicity / exact-rational certificates (Thms 7 & 8).** Codex's `verify_min3_triples.py` and `verify_triples_min_leq.py` use the identity `B_P(Lq+r)=Dq+f(r)` (`L=lcm P`) reduced to one period of affine ratio checks in exact `Fraction`s. The **method is PUBLIC**: MalekZ post 5089 ("Exact periodicity `F(n)=δn+c_{n mod P}`") and the linked PDF Thms 2.1/2.2 + Prop 5.1 ("Visible-Slab Reduction"), plus Chojecki Cor 2.5/2.6 (finite-window reduction). The 5 `{3,b,c}` and 6944 `min≤20` certificates are **instantiations**, not a new method (thread-audit §3(d); chat *Claude "Audit of verify_triples_min_leq.py"* method caveat). Claude-main's audit did add the missing monotonicity proof for `h(q)=(Dq+f(r))/(Lq+r)` (mediant-path sign constant `Dr−Lf(r)`) and promoted it to the internal **"Certificate Lemma"** (chat, same entry).

**Charge decomposition ⇒ Theorem 9 (the genuinely new engine).** Produced by **Sub:attack** (`a8eb4501`, `claude-fable-5`), `tmp/wf_result_a8eb4501afb88b28f.md` and `triples_writeup.md` §3: Lemma 5 writes `s(n)−2P(n)=X_a+X_b+X_c` with each `X_d = t−⌊t/q⌋−⌊t/q'⌋ ≥ 1` (nested-floor identity + ratio pairs `(≥3,≥3),(≥2,≥3),(≥2,≥3)`, the last supplied by Lemma 4's parity dichotomy — the *only* use of the uncovered-zone hypothesis `1/b+1/c > 1/a`). This is the size-3 analogue of Chojecki's "signed transport / two-block decomposition" but is self-contained and needs no periodicity, windows, or case split.

**Two-sided Bonferroni (Idea 1 → Theorem 8's strict step).** The methods-survey subagent (`a0184db`, `tmp/wf_result_a0184db1f36725190.md` §5 **Idea 1**) proposed "two-sided Bonferroni certificate + finite exceptional region," explicitly templated on **#690** (Crapis–Wang, `2605.08542`: finite certified checks + one uniform construction), with the constants `δx−4 < B(x) < δx+3` for triples and the `c > 11a` cutoff. Claude-main elevated it to a concrete lead — chat *"Adversarial review… Next-lead upgrade (from methods survey of AI-solved problems): the two-sided Bonferroni certificate… (★) holds outright for any triple at every n with `n·δ > 11`… the #690 template."* The attack subagent then used exactly `2⌊x⌋ = x+⌊x⌋−{x}` with `{·}<1` (three fractional parts `<1`, slack `s(n)−2P(n) ≥ 3`) to get the *strict* `2B(n) > nS` — the Bonferroni/main-term-plus-O(1)-error discipline surfaced by the survey. Chain: **methods-survey Idea 1 (template #690, also #650) → Claude-main lead → Sub:attack Theorem 8**.

**Related-idea provenance from the survey.** `wf_result_a0184db` §2.3 (#650, König–Ore + interval-halving injection + "peel the largest element") and §2.4 (#690 uniform CRT) are cited as the "peeling / finite-plus-uniform" patterns; the survey also flagged #281 (Davenport–Erdős + Rogers) as the literature neighborhood — matching `literature_notes.md`'s density references (Davenport–Erdős 1936/1951, Besicovitch, Hall *Sets of Multiples*).

**Public-priority method (thread-audit).** `wf_result_a30cf8a` established that Chojecki's note is the dominant prior-art document (post 4909, 20 Mar 2026, `ulam.ai/research/erdos488.pdf` + Aristotle `erdos488.tar.gz`), with the decisive detail that Cor 4.7 (`|A_min|≤3`) is Lean-verified **modulo the single `sorry` `exact_one_count_ge_four`** (from `FORMALIZATION_STATUS.md` in the tarball) — the fact that lets Theorem 9 be framed as an *independent, sorry-free* proof of a claimed result.

---

## 4. TOOLS AND VERIFICATION

| Script (mtime) | Author | What it checks | Scale | Who ran / result |
|---|---|---|---|---|
| `scripts_fetch.py` (13:27) | Claude-main | Browser-UA fetch of erdosproblems pages (plain fetch 403s) | ~40 pages | Claude-main (recon) |
| `scratch_probe.py`/`488`/`488b` (13:30–13:38) | Claude-main | Small-search recon for counterexamples across candidates + #488 max-ratio profile | `n` up to ~30000 | Claude-main; no CE, #488 "true & tight" |
| `counterexample_search.py` (13:57) | Claude-main | (I) verify (★) on families; (II) singleton `2−1/a`; (III) disprove non-multiples version | singles to `a=1000`, 2000 random sets, intervals, prime shells; `m≈3·10⁴` | Claude-main; worst ratio **1.999** (`A={1000}`), non-mult. disproved at `n=10,m=20` (`computational_results.md` R2–R4) |
| `verify_exhaustive.py` (13:57) | Claude-main | Exhaustive (★): `n·B(m) < 2·m·B(n)` | `A⊆{2..15}, |A|≤3, m≤200` = **8,343,328** triples | Claude-main; 0 violations (R1) |
| `verify_min3_triples.py` (14:16) | **Codex** | Exact periodic certificate `α ≤ B/x ≤ β`, `β<2α` for the 5 `{3,b,c}` triples | 5 triples, exact `Fraction` | Codex → `RESULT: PASS`; audited + re-run by Claude-main (chat R3) |
| `sweep_criterion.py` (14:30) | Claude-main | `δ ≥ S/2` and per-period `B(n) > nS/2` | 71,003 reciprocal-heavy triples (`a≤40`) + 42,769 primitive 4-sets (`{3..40}`) | Claude-main; **0 failures** (R10; chat audit entry) |
| `verify_triples_min_leq.py` (14:42) | **Codex** | Exact `α/β` certificate for all reciprocal-heavy primitive triples `a ≤ MAX_A`; monotone-in-`q` residue handling | **6944** triples (`a≤20`); worst `{19,20,21}`, β/α=**666/361** | Codex → PASS; Claude-main audited (supplied the monotonicity proof) + re-ran `MAX_A=12` and brute-forced `{19,20,21}` |
| `attack_triples.py` (15:02) | **Sub:attack** (a8eb4501) | Full Theorem-9 proof at scale: ratio lemmas R1–R7, nested-floor ids, `X_a,X_b,X_c ≥ 1`, `s−2P ≥ 3`, Bonferroni, strict `2B(n)>nS`, union bound, end-to-end (★), abstract-lemma unit tests | **A:** 14,802 uncovered triples `a≤25`, full period = **516,987,874** `n`; **B:** 37,253,817 triples; **C:** **1,209,671,136** `(n,m)` pairs; **D:** 156,263 triples `4≤a≤60`; **E:** 13,336 configs | Sub:attack → all PASS; **Claude-main independent re-run** `attack_triples.py 14 30` (2032 triples, 10,379,646 `n`) → PASS (chat *Claude "PROVED"* + R9) |
| (`codex_leftover_counterexample_search.py`, 13:56) | Codex (old) | #728 degeneracy arithmetic | (small `n`) | reused by Sub:728-verify — asserts all pass (`wf_result_a91f3a3` §4) |

All #488 verification scripts use exact integer/`Fraction` arithmetic (no float in any assertion); deterministic seed `20260707` where randomness appears. Reproduction block: `computational_results.md` "Reproduce everything."

**Adversarial verification passes (human-in-the-loop, Wes's Law 4/1):** Claude-main line-by-line audited Thm 6 (`floor(t)+1>t` unconditional; `|P|=1`→§1 citation nit), the 5-triple enumeration (by hand: `b=4→c∈{5,7,10,11}`, `b=5→c=7`, `b≥7→none`), `verify_min3_triples.py` (`r=0`/`q_min` handling), `verify_triples_min_leq.py` (monotonicity + `c<L` primitivity), and Theorem 9's Lemmas 3/4/5 + Bonferroni strictness — each `CONFIRMED` in `adversary_collab_chat.md`.

---

## 5. HONESTY LEDGER

Every correction / retraction / broken claim during the collaboration, with claimed-vs-true.

**H1 — Novelty of #488 partial results (MAJOR public-priority correction).**
*Claimed:* `proof_attempt.md` §3A and `final_report.md` originally framed the dense half, union-bound, 2∈A, periodicity certificates, and witness-typo resolution as new/partial local contributions (and `literature_notes.md`'s first thread audit was "materially incomplete"). *True:* all are **PUBLIC** — Chojecki's 27-page note (post 4909, 20 Mar 2026, Lean bundle) contains Thm 3.1 (singleton), Prop 6.1 (dense), Thm 3.2 (`|A|=2`), Lemma 6.3/Prop 5.1 (union-bound); MalekZ 5163 proved 2∈A; MalekZ 5089/5101 gave the periodicity method; BorisAlexeev 1860–1865 gave the witness-typo argument first. *Disposition:* corrected `literature_notes.md`, `proof_attempt.md`, `final_report.md`. Source: chat *"MAJOR public-priority correction for #488: the Chojecki note"* (tag `PUBLIC`); `tmp/wf_result_a30cf8a95fd7761e0.md`.

**H2 — #728 "audit finding" is the page's own caveat.**
*Claimed:* Codex's `findings_728.md` presented the degenerate large-`a,b` construction (`a=n+w+1`, `b=(n+w+1)!/n!−1`, `w≥max(C log n, εn)`) as an audit finding. *True:* the identical construction, same variable names, is printed on the #728 page itself (AlphaProof team, present since the 2025-10-20 revision); #728 is proved (Lean) since 2026-01-05 (Barreto + GPT-5.2 + Aristotle, arXiv 2601.07421). *Disposition:* archived as a non-novel formulation audit; **do NOT post to the #728 thread**; addendum added. Sources: chat *"#728 'audit finding' is the page's own caveat text"* (tag `PUBLIC`) and *Codex "#728 is not publishable"* (`PUBLIC`/`BROKEN-AS-NOVEL`); `tmp/wf_result_a91f3a3e574e558ca.md` (independent factorial re-derivation confirmed the arithmetic is *correct* but the contribution *nil*).

**H3 — #488 two-element case is public.**
*Claimed (implicitly):* the reciprocal-sparse theorem's generalization of the pair case might be new. *True:* Will Blair's `|A|=2` proof is public (post 6864), and it is already in Chojecki's note (Thm 3.2, Lean). *Disposition:* do not claim the two-element case; Thm 6 must cite Chojecki + Blair. Source: chat *Codex "#488 two-element case is public"* (tag `PUBLIC`).

**H4 — The universal `2B(n) > nS` conjecture is FALSE.**
*Claimed:* the first draft of `triples_writeup.md` §7 conjectured the per-`n` criterion `2B(n) > nS` holds for *every* primitive `P`. *True:* **BROKEN.** Family `A={2p : p prime ≤ P₀}` is primitive with `S=½Σ1/p→∞` but `δ=½(1−∏(1−1/p))<½`, so `S>2δ` once `P₀≥100` (`|A|=25`: `S=0.9014 > 2δ=0.8797`); for `P₀=300` (`max A=586`) exact check shows `2B(n) ≤ nS` at **every** `n∈[586, 2·10⁶]`. (★) still holds there via a *third* mechanism (all multiples even ⇒ `sup g ≤ ½ < 2δ`; scaling recursion `B_{2A'}(x)=B_{A'}(⌊x/2⌋)`). *Disposition:* writeup corrected; moral recorded — `|P|≥4` needs ≥3 regimes, not one universal per-`n` criterion. Source: chat *"BROKEN: the '2B(n) > nS for every primitive P' conjecture"* (tag `BROKEN`); `triples_writeup.md` §7 CORRECTION; `computational_results.md` R10.

**H5 — Stale "next targets" retracted after Theorem 9.**
*Claimed:* `consecutive_triples_notes.md` treated `{a,a+1,a+2}` as an open `PLAUSIBLE` lead (bound (L) `B_a(n)/n ≥ 3/(2a−1)`, computational evidence only); `final_report.md` "Next target" said prove all consecutive triples; the 5 `{3,b,c}` certificates and the `min≤20` certificate were load-bearing. *True:* all consecutive triples satisfy `1/(a+1)+1/(a+2) > 1/a` (uncovered zone) and fall to Corollary 8'; Theorem 9 **subsumes** the min-3 certificates, the `min≤20` certificate, and every consecutive-triple lead. *Disposition:* `consecutive_triples_notes.md` marked `SUPERSEDED`; `final_report.md` "Next target" struck through and redirected to `|P|≥4`; `proof_attempt.md` §3C/§4 annotated that §2/Cor 5/§3A/§3B are now subsumed. Sources: `consecutive_triples_notes.md` header; `final_report.md` "UPDATE… direction (a) is DONE"; `triples_writeup.md` §6.

**H6 — Failed monotonicity bounds (recorded so they are not retried).**
*Claimed (transiently):* naive tail bounds. *True:* all **false** — `B(m) ≤ (m/n)B(n)`, `n·B(m) ≤ (m+n)B(n)`, `B(2x) ≤ 2B(x)`, and "`[1,n]` is the sparsest length-`n` window" each have explicit counterexamples (`A={3},n=5,m=100`; `A={2,3},n=4`). Source: chat *Codex "Several naive monotonicity bounds fail"* (tag `BROKEN`); `proof_attempt.md` §4.4.

**H7 — Process failure: a spawned verifier crashed.**
The workflow launched a 5th subagent (**Sub:adversary-verify**, `a369bd6b`, `claude-fable-5`) tasked to "try to BREAK every claim"; it died mid-response ("API Error: Server error mid-response") and produced no `result` in `journal.jsonl` and no artifact. The adversarial-verification role was instead carried by Claude-main directly in `adversary_collab_chat.md`. Noted for completeness: this audit trail is not gap-free. Source: `agent-a369bd6b9e2c62577.jsonl`; `journal.jsonl` (4 results vs 5 starts).

---

### Net standing (per `final_report.md` verdict)

Full solution of #488 is **not** claimed. Sorry-free elementary proof of the `|P| ≤ 3` case (Theorem 9) is real and confirmed, but its *result* is publicly claimed by Chojecki Cor 4.7 (Lean modulo one `sorry`); defensible framing is **independent, sorry-free proof of the size-≤3 case by a different method**. `|P| ≥ 4` is open (needs ≥3 regimes). Any public posting is Wes's call per protocol — not the agents'.

**Key artifact paths:** `D:\Erdos Sandbox\{adversary_collab_chat.md, triples_writeup.md, proof_attempt.md, final_report.md, literature_notes.md, computational_results.md, attack_triples.py, verify_triples_min_leq.py, verify_min3_triples.py, sweep_criterion.py, counterexample_search.py}`; subagent reports `D:\Erdos Sandbox\tmp\wf_result_*.md`; workflow journal `C:\Users\penum\.claude\projects\D--Erdos-Sandbox\5beb6959-3c2f-44d6-b933-83c1b60f5734\subagents\workflows\wf_046c451b-656\{journal.jsonl, agent-*.jsonl}`.