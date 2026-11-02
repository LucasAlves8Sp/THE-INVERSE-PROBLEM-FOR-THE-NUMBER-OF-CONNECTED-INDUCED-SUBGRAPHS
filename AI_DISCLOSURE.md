# AI disclosure

This is the AI disclosure of the paper *The inverse problem for the number of connected induced
subgraphs*, as it appears there.

Artificial intelligence was used extensively in this work, both to obtain the results and to check
them.

**Solving and proving.** The main model used to solve the problem and to prove the theorems was
Claude Opus 5.5 (Anthropic). In an iterative process directed by the author, it:
- carried out most of the exploratory proof development, including the near-cones of Section 4
  and the arguments of Section 3;
- wrote and ran the programs of Section 9;
- carried out the literature search of Section 1.2;
- generated most of the first draft of the manuscript and of the Lean 4 formalization of
  Section 8.

**Reading and checking.** ChatGPT-Astra (OpenAI) was used, together with the author, to read the
manuscript and check the arguments. AI was used extensively for proofreading and proof checking,
and for repeated rounds of checking the arguments and comparing the proofs with one another. Two
examples are the two proofs of Proposition 3.2 and the two exclusions of 16 on five vertices. In
each round, the author and ChatGPT-Astra reviewed the text, the proofs and the supplementary
material and sent feedback, and Claude revised them.

**The author's role.** The author:
- formulated the problem, which arose from Questions 3.5 and 3.21 of Camargo, Ordoñez and Ramírez;
- provided the mathematical context and constraints, and steered the iterations through prompts
  and feedback;
- supplied ideas and suggested strategies;
- selected and revised the outputs, and reviewed the final arguments.

**Verification.** Programs check the explicit finite counts (Section 9), and the results listed in
Table 7 of the paper are formally verified in Lean (Section 8). No independent expert has yet
verified the proofs. The author takes full responsibility for the content.
