# How to hand this off — a plain-English guide

You don't need to understand the math. Everything is prepared. This is the whole
job, in order.

## What you actually have (in one paragraph)

We wrote a short, correct proof of one (already-known) case of a famous open
problem (Erdős #488), checked it by computer on many cases and by several AI
review passes, and started a machine-checked ("Lean") version — the substantive
ordered primitive-triple statement is now covered in Claude's Lean files; the
remaining wrapper work is singleton/pair cleanup plus primitive-core
bookkeeping. It's all public at **https://github.com/penpro/Erdos-Sandbox**. It's
an honest, modest contribution: we are **not** claiming a new theorem, a new
method, or a solution to #488 — just a clean, correct,
computer-checkable proof of a case where the experts are currently stuck.

## Current research thread after posting

**Status update (2026-07-18).** The size-`≤4` result is now sorry-free in Lean.
For size 5, the density and C-B covering theorems are proved, and the reviewed
W-FIN argument proves the C-B residual is finite. The universal source-owned
cutoff is below `2.562 * 10^12`; the residual-specific `CRIT` audit and exact
bad-edge cofactors cut this to `2.494 * 10^6`. Full size 5 is still open because
SPREAD covers every primitive quintuple with `max/min >= 7`; the
remaining compact residual box has `min < 3054109696/1225`, `max/min < 7`, and
`max < 17452056`, still beyond direct enumeration. The exact v3 slot-matrix
certificate passes all 906 normalized bad triples having at least two internal
strong edges (`869` vacuous). The remaining edge classes now have independent
finite reductions: corrected `oneedgebankcheck` finds exactly 19 compact
one-edge residuals and direct-bank certifies all 19; `zeroedgebankcheck` proves
a finite rational-template reduction and finds exactly four zero-edge residuals,
all direct-bank positive (and independently v3-positive). Claude's first
`bank1edge` draft is retracted because it used `1/k` where the charge is `1/c`,
included three noncompact tuples, and omitted `D=[30,52,78,130,195]`. The
minimum-good lemma excludes five-bad residuals. For four bads, cutoff-free
spanning-tree/two-pair enumeration recovers exactly 174 necessary-filter shapes,
and `shape4` certifies all 174. This gives a candidate complete compact-box
partition at paper-plus-certificate tier. Full size 5 is **not yet claimed
solved**: both agents' internal hostile passes now hold, but a second independent
external review of the v3/shape4 package and W-FIN plus final consolidation
remain. Start with `REFEREE_SIZE5_CANDIDATE.md`, then
`REFEREE_WFIN.md`, Sections 22-26 of `cbfin_reduction_notes.md`, and the latest entry in
`adversary_collab_chat.md`. The older narrative below is retained as history.

The public update has been posted. The active internal frontier is now:
audit the local `|P|<=4` proof candidate, then push toward `|P|>=5`.

Claude started `fastcheck/` as a Rust bounded-window searcher, and Codex added
an exact periodic-certificate layer (`classify`, `cert`, `sweep-quad-cert`).
The strongest new computation so far:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quad-cert 150 3000000
```

This checked 15,591,140 primitive quadruples with entries `<=150`. The new note
`quadruple_charge_notes.md` now gives a local proof of the size-4 case: every
primitive quadruple has at least two good charges, and two good charges plus
exact four-set inclusion-exclusion prove `2B(n)>nS` for all `n>=max(P)`.
The sweep agrees:

```text
two-good-charge rescue condition applies: 15,591,140
residual after those regimes: 0
```

Next mathematical task: continue the external audit. Codex's first local audit
passed (`REFEREE_QUADRUPLES.md`, `audit_quadruple_charge.py`), checking the
five-shape classification when `b` is bad, the `a`-term reductions in the five
estimates for `charge(c)`, and the pointwise weight table in the
two-good-charge proposition. The proof still needs Claude/human review and a
literature/thread audit before anyone calls it new. See
`quadruple_charge_notes.md`, `adversary_collab_chat.md`, and
`computational_results.md` R11/R12.

First size-5 lead: `quintuple_charge_notes.md` shows three good charges would
suffice for a primitive quintuple, but the naive claim that every primitive
quintuple has three good charges is false. Codex added `sweep-quint-cert`; up to
entries `<=100`, after the `2 in A`/sparse/three-good symbolic regimes and
thirty-three exact scaled-family audits, 950 residual quintuples exact-certify and still
satisfy the union-bound separator. The scaled-family audits live in
`audit_scaled_quint_families.py` and `quintuple_charge_notes.md`; the current
worst remaining residual is `{40,48,60,72,90}` with ratio `1883/1440`. The next
tool/proof upgrade should classify the remaining structural size-5 regimes.

## What "handing off" means

The people who can finish the Lean and vet the math are already gathered in one
place: the discussion thread for problem 488 on erdosproblems.com (this includes
an active thread with several number theorists). "Handing off" = posting a short comment there that
points them to the repo. That's it. They take it from there.

## The steps (about 5 minutes)

1. **Open the discussion page:**
   https://www.erdosproblems.com/forum/discuss/488
   (or go to https://www.erdosproblems.com/488 and scroll to the comments.)

2. **Sign in.** Look for a "Sign in" button (top-right area). The site uses
   **Google sign-in** — use whichever Google account you're comfortable posting
   under. (If you don't see it, click around "Forum" / the menu; it's a normal
   JavaScript site so the button appears once the page loads.)

3. **Start a reply / new comment.** There's a comment/reply box on the discussion.

4. **Paste the prepared comment.** Open the file
   `writeup/thread_comment_488.md` in this repo (or on GitHub). Copy the text
   **between the two `---` lines** (skip the `<!-- ... -->` note and the
   "Pre-post checklist" at the bottom — those are just instructions to you).
   Replace `—[your name/handle]` at the end with your name or a handle.

5. **Post it.** Done. The links in the comment already point to the public repo,
   the PDF, the verification script, and the Lean.

## What to expect after

- Someone may reply with a question, a correction, or "I'll finish the Lean." If
  they ask something technical, **copy their reply back to me** and I'll draft
  your response — you don't have to answer math yourself.
- Nobody may reply for a while. That's normal and fine; the repo stands on its own.
- If someone points out a genuine error, that's a good outcome — bring it to me and
  we fix it. (Several independent AI checks found none, but a human hasn't
  refereed it, so a real error is still possible — that's how this works.)

## If you'd rather not post publicly yet

Totally fine. Two lower-key options:
- **Just share the repo link** (https://github.com/penpro/Erdos-Sandbox) with any
  specific person you'd like to look at it. The README explains itself.
- **Do nothing outward-facing.** The work is committed and safe; you can post any
  time later.

## Honesty note (so you know what you're putting your name to)

The comment is deliberately modest and honest: it credits the prior work
(Chojecki's), notes the method is classical (Heilbronn–Rohrbach, 1937), does not
overclaim, and discloses the AI assistance. You are not claiming to have "solved"
#488 — only to have given a clean, correct, partially-formalized proof of a
sub-case. That is an accurate and defensible thing to put your name to.

## The one thing only an expert (or a Lean prover) can do next

Finish the Lean proof: the "counting" half + assembly, documented precisely in
`lean/ep488/README.md`. That's the natural thing the hand-off invites someone to
pick up — or that a specialized AI prover (the thread mentions "Aristotle") could
close. You don't need to do this; posting the hand-off is what puts it in reach.
