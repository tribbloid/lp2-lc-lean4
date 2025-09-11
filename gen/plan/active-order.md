# Active Coq sources: size ranking and suggested order

Ranked by size (ascending), per prompt/Define.md step 1.

- Fsub.v — 1,478 lines
- FsubL_alt.v — 1,713 lines
- Dsub.v — 1,774 lines
- Dsubsup.v — 1,800 lines
- Ddia.v — 1,886 lines

Notes:
- Ddia and Fsub modules already exist in Lp2lc/Active. The remaining to scaffold are Dsub, Dsubsup, and FsubL_alt.
- We’ll proceed smallest-first among the remaining files: FsubL_alt → Dsub → Dsubsup.
- If dependency edges appear during conversion, we will adjust the order locally for the impacted declarations, while keeping modules independent per FileStructure.md.
