import re

def translate_type(coq_type):
    """A best-effort translation of a Coq type to a Lean type."""
    # Rule: Map Coq Prop/Type/Set to Lean Prop/Type u
    s = coq_type.replace("Set", "Type").replace("Prop", "Type 0") # A simplification

    # Rule: Translate forall x:T, U to ∀ x : T, U
    s = re.sub(r"forall\s+([a-zA-Z0-9_']+)\s*:\s*([^,]+),", r"∀ (\1 : \2),", s)

    # Rule: Replace Coq arrows T -> U with T → U
    s = s.replace("->", "→")
    
    return s

def main():
    """A simple main for testing."""
    import sys
    if len(sys.argv) > 1:
        input_stmt = sys.argv[1]
        print(translate_type(input_stmt))
    else:
        # Example translations
        print(translate_type("forall A : Set, A -> A"))
        print(translate_type("Prop -> Prop"))

if __name__ == "__main__":
    main()

