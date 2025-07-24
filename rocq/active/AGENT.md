# AGENT.md - Coq Type Soundness Proofs Project

## Project Overview
This directory contains Coq formalization of type soundness proofs with definitional interpreters from the POPL 2017 paper. The project includes multiple type systems (STLC, F<:, D<:>, DOT) implemented in Coq.

## Frequently Used Commands

### Build Commands
- `make` - Compile all Coq files (uses Coq 8.4pl6 syntax)
- `make clean` - Remove compiled files (.vo, .vi, .glob, etc.)
- `coqc <file>.v` - Compile individual Coq file
- `make validate` - Validate all compiled proofs

### Documentation Generation
- `make html` - Generate HTML documentation
- `make all.pdf` - Generate PDF documentation

### Development Commands
- `coqtop` - Interactive Coq toplevel
- `coqdep -slash $(COQLIBS) <file>.v` - Check dependencies

## Project Structure

### Core Files
- `SfLib.v` - Support library (upgrade this first)
- `stlc.v` - Simply Typed Lambda Calculus
- `fsub.v` - System F with subtyping (F<:)
- `fsub_equiv.v` - F<: equivalence with small-step
- `fsub_mut.v` - F<: with mutable references
- `fsub_exn.v` - F<: with exceptions
- `fsubsup.v` - F<:> from System D Square
- `dsubsup.v` - D<:> from System D Square  
- `dot.v` - DOT calculus in big-step

### Generated Files
- `*.vo` - Compiled Coq objects
- `*.glob` - Global information files
- `*.v.d` - Dependency files

## Upgrade Notes (Coq 8.4 → 8.18)
- LibLN imports need TLC prefix: `Require Import TLC.LibLN.`
- All Hint definitions must be added to `core` hint database
- Upgrade order: Start with SfLib.v, then shortest to longest files
- Compile individually, not with makefile during upgrade
- Test compilation frequently with `coqc`

## Development Workflow
1. Always start changes with SfLib.v
2. Compile individual files during development
3. Use `make validate` to check proof validity
4. Run `make clean` before major changes

## Coq Version
- Original: Coq 8.4pl6 (July 2015)
- Target: Coq 8.18 with TLC library
