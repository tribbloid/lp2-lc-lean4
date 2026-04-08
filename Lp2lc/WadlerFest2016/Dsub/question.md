# Dsub questions and notes

- Names: Coq “type”/“term” are renamed to def_type/def_term to avoid conflicts and match Fsub conventions.
- Environments: env := List (Var × typ). Binding E & x ~ T is represented as (x, T) :: E. dom via Shared.Env.domOf. binds via List.lookup equalities.
- Opening/substitution: Follow Coq’s argument order strictly. open_t/open_e operate at de Bruijn index 0.
- Splitting combined lemmas: Use _t (types) and _e (terms) suffixes for P /\ Q splits.
- ok predicate: Use abstract ok from Shared if/when required in later lemmas.
- Divergences from Coq: We use Bool for typ_mem’s boolean flag; check any downstream pattern matches for exact vs upper-bound.
- Next steps: Continue scaffolding all theorems in Proof.lean in source order, then progressively prove helper lemmas without introducing axioms.
