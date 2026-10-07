# PL semantics

This module uses untyped De Bruijn serials and context embedding.

- Functional binders receive contractible serial proxies, so their bodies are uniform over inputs at a fixed context.
- Each binder accepts only the proxy for its next De Bruijn serial.
