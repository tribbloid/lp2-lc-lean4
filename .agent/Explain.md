# Explain Steps

## Locate Coq proof file

## Explain Theorems

- For each theorem in the proof file, explain it in Scala code in the following format:
```scala
object `<theorem name>` {
  /**
   * full name: ...
   * 
   * purpose: ...
   */
  
  // Scala example that can be successfully compiled, if necessary.
}
```

- Ensure that each theorem in coq or lean file is explained in `Glossary.md`.
- The explanation should be clear and concise, and contains at least its term/symbol name (as used in the code), its
  full name, and its meaning/purpose.
- If the subject is a primary conclusive theorem and not a lemma, you should also explain why it entails the soundness
  of the type system.
- Doublecheck that:

## Verify
    -[ ] All theorems in coq file are explained
