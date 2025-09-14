You are tasked with writing multiple prompts files from a template, in a very safe, sandboxed environment:

- Scan all Coq sources under `Lp2lc_coq/Active` and rank them by size (in ascending order)
- For each Coq source: Reify the [prompt template](__Template.md) into a concrete prompts and save it into `prompt/instruct/<index_number>_<coq_source>.md`

No planning is required