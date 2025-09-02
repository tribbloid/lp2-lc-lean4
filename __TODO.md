
Open questions for you
•  Path/namespace: Keep “Active” capitalized (Lp2lc/Active/Fsub.lean, module Lp2lc.Active.Fsub) or convert to lower-case directory names?
•  Comments: Is it OK to keep the big Coq banner at the top and then restrict all additional comments to “-- line NNN” only?
•  Proof effort: Do you want me to keep absolutely everything as sorry initially, or try to discharge some of the easier constructor-style lemmas (with aesop) as a quick win?
•  Env and ok: Some Coq lemmas reference ok E from LibEnv. I can define a minimal ok : env → Prop and keep statements typechecking. Do you want a more faithful “no duplicate keys” implementation now, or leave it abstract for later proofs?

Pending prompt:

- should always write into the same file
