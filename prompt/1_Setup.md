# Task Definition

## Overview

You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting
proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan

- Scan all Coq sources and rank them by size (in ascending order).
- Read the Lean build file [here](../lakefile.lean)

### 2. File Structure Setup

For each Coq source file:

- Create (if not exists) the corresponding file structure as defined in [this](CodeStructure.md), including Lean directory/modules, module aggregators, markdown reports and sections.
- Do not delete existing file or directory.
- Do not remove any file contents.

### 3. Checklist
Check the following criteria, ensure that:

[ ] Each Coq source file have a corresponding Lean module.
[ ] Each Lean module have a module aggregator file.
[ ] Each Lean module have the proper file structure as defined in [this](CodeStructure.md)?

If any of the above is unmet, go to previous step and fix it.

## Rules

see [this](ConversionRules.md)