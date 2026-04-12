---
description: Force a full Cascade Series review against the mandatory protocol in CLAUDE.md
---

# Full Cascade Series review

Run the complete mandatory review protocol against the Cascade Series in this repository. This is a user-invocable reinforcement of the protocol in `CLAUDE.md` — it is designed to be invoked on fresh-context sessions where the user wants an explicit guarantee that the full review fires before any substantive answer.

## Operating rules

You are performing an independent review of the Cascade Series research program. You have no memory of prior reviews in this or any other session. Prior ratings, prior conclusions, and prior corrections are unavailable to you, and that is intentional — the user specifically clears context between sessions to remove the pro-paper drift that accumulates in long conversations. Treat the freshness of your context as a virtue, not a limitation.

Every check in `CLAUDE.md` §"Mandatory Review Protocol" is active. You may not skip any of them, and you may not self-declare a question "trivial enough to bypass the protocol." The protocol runs every time.

## Specific instructions for this command

1. **Start by reading `CLAUDE.md` directly.** Do not rely on your prior knowledge of what it contains. Read it as the first action of this command.

2. **Then read the cover sheet directly** (`src/cascade-series-cover-sheet.tex`). It contains the hypothesis, the thought experiment, and the predictions table. Do not paraphrase it; quote it when you refer to its content.

3. **Then read the Prelude directly** (`src/cascade-series-prelude.tex`). It contains the derivation chain from `0 ≠ 1` to `B^∞`. Verify each step is marked as a theorem or definition and that the chain closes.

4. **Survey the remaining parts by glob, not by sub-agent.** Use `Glob src/cascade-series-part*.tex` to list them. For any claim you intend to make about what a Part paper derives, read the relevant section of that Part paper directly using `Read` or `Grep` on the file. Do not dispatch a sub-agent to "audit" a Part paper and report findings — sub-agents produce systematic false negatives on this material, and the user has explicitly disallowed that workflow.

5. **Follow the six checks in `CLAUDE.md` §"Mandatory Review Protocol".** Each check is mandatory. Report which checks you have run in your first response.

6. **Categorize every defect you flag** as either (a) already in `CLAUDE.md` §"Known Quantitative Issues" or Tier 5 of the predictions table, or (b) novel. Only (b) is a review finding. State the category explicitly.

7. **Quote, don't paraphrase.** When you make a claim about what a source says, produce the sentence. If you cannot produce the sentence, you may not make the claim.

8. **Do not conclude that a derivation is missing** unless you have read the specific section where the derivation should live and have confirmed by direct reading that it is not there. "I did not find it in the section I sampled" is not a valid finding; it is a reading failure.

## Output format

Your response should contain, in order:

1. **Protocol confirmation line.** Exactly this text: "Running mandatory review protocol. Checks 1–6 active."

2. **Sources read.** A short list of the files you read directly, with line ranges. This is the audit trail; without it, the rest of your review is not verifiable.

3. **The user's question.** Restate it.

4. **The review.** Answer the question, following all six checks. Every logical-gap claim must cite `file:line`. Every textual claim must quote the sentence. Every defect must be categorized (a) or (b). Grade individual predictions on the same scale the prior reviews used (A, A-, B+, B, B-, C+, C, F) if and only if the user asks for a rating; otherwise focus on the specific question asked.

5. **Errors made in this session.** At the end of the response, if you made any paraphrase errors or logical-gap overreaches that were caught mid-answer, list them explicitly. Honest self-reporting of mid-session errors is a review feature, not a cost.

## Calibration note

The base rate for real defects in this program is lower than reviewer intuition suggests. Prior sessions have produced at least three "the text does not derive X" claims that collapsed under direct reading (Gleason, Lovelock "circularity," and a black-hole evaporation paraphrase error). Every novel defect of that type that you are tempted to raise should be verified twice against the source before you commit to it. At the same time, real acknowledged gaps exist and should be flagged in their correct category — this is not a reason to go easy on the program, only a reason to aim your scepticism at the places where it is quantitatively warranted.
