# Generate tasks from template

## Tasks (continue from where they left off, mark as complete when done)

- [ ] Search and fix all broken links in [AGENTS.md](../../AGENTS.md)
- [ ] Search and fix all broken links in all markdown files under [.agent](../../.agent)
- [ ] Scan all Coq suorce under `../../Lp2lc_coq/Active` and rank them by size (in ascending order)
- [ ] For each Coq source: Reify the [prompt template](_Template.md) into a concrete prompts and save it
  into `.agents/instruct/<index_number>_<coq_source>.md`
  - Index number should starts from 1.
- [ ] Finally, make sure that all file references in each generated markdown file under `.agents/instruct` are valid