# Demo Steps

(All Scala code are in version 3.3 LTS)

## Locate Coq proof file

## List Coq types as Scala objects

- Convert each Coq type definition into an empty Scala sub object.
- Do not break existing format.

## Writing Scala Examples

- In each Scala object, explain the Scala language feature defined in Coq.
- Follow existing format and pattern.
- Do not translate Coq directly into Scala.
- Search https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc and other coq documents for symbols you don't
  know.

## Verify

- Doublecheck that:
    -[ ] Each Coq types have a demo in Scala code.
    -[ ] gradle can compile Scala code without error.
