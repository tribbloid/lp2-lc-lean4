import re
import json
import argparse
import os

def strip_comments(text):
    """
    Removes Coq's block comments `(* ... *)`.
    This function handles nested comments.
    """
    pattern = r'\(\*.*?\*\)'
    # This is a simplification; a robust implementation would need to handle nesting.
    # For now, we'll do a simple iterative replacement.
    while re.search(pattern, text, re.DOTALL):
        text = re.sub(pattern, '', text, flags=re.DOTALL)
    return text

def scan_coq_file(filepath):
    """
    Scans a Coq file to extract definitions and proofs.
    """
    if "draft" in filepath.split(os.sep):
        return None # Ignore files in draft directories

    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    content_no_comments = strip_comments(content)
    lines = content_no_comments.splitlines()

    # Regex for definitions and proofs
    def_pattern = re.compile(
        r'^\s*(Definition|Inductive|CoInductive|Record|Class|Fixpoint|CoFixpoint|Axiom|Parameter|Notation|Reserved Notation)\b'
    )
    proof_pattern = re.compile(
        r'^\s*(Lemma|Theorem|Corollary|Proposition|Fact)\b'
    )

    defs = []
    proofs = []
    
    # This logic needs to be more robust to find the *end* of a statement, which is a period.
    # A simple line-by-line scan is not enough for multi-line statements.
    
    for i, line in enumerate(lines):
        # We need to find the start of a definition or proof.
        def_match = def_pattern.match(line)
        proof_match = proof_pattern.match(line)

        # Simplified extraction: find the start, then scan for the terminating '.'
        if def_match:
            kind = def_match.group(1)
            # Find the full statement
            full_statement, end_line = find_full_statement(lines, i)
            name = extract_name(full_statement, kind)
            defs.append({
                "name": name,
                "kind": kind,
                "start_line": i + 1,
                "end_line": end_line + 1,
                "raw_statement": full_statement
            })

        elif proof_match:
            kind = proof_match.group(1)
            # Find the full statement up to 'Proof.' or '.'
            full_statement, end_line = find_full_statement(lines, i, proof_terminator=True)
            name = extract_name(full_statement, kind)
            proofs.append({
                "name": name,
                "kind": kind,
                "start_line": i + 1,
                "end_line": end_line + 1,
                "raw_statement": full_statement
            })


    return {"defs": defs, "proofs": proofs}

def find_full_statement(lines, start_index, proof_terminator=False):
    """
    Starting from start_index, finds the full statement which ends with a ".".
    If proof_terminator is True, it can also be terminated by "Proof.".
    """
    buffer = ""
    current_index = start_index
    while current_index < len(lines):
        line_part = lines[current_index]
        buffer += line_part + " "
        if "." in line_part:
            # Simplistic check for termination
            stripped_line = line_part.strip()
            if stripped_line.endswith('.') or (proof_terminator and "Proof." in stripped_line):
                return buffer.strip(), current_index
        current_index += 1
    return buffer.strip(), current_index # Reaches end of file

def extract_name(statement, kind):
    """
    Extracts the name of the definition or proof.
    E.g., "Definition foo :=" -> "foo"
    E.g., "Lemma bar:" -> "bar"
    """
    parts = statement.split()
    try:
        kind_index = parts.index(kind)
        name = parts[kind_index + 1]
        # remove trailing ':' or ' ' or '('
        name = re.sub(r'[:(].*$', '', name)
        return name
    except (ValueError, IndexError):
        return "unnamed"


def main():
    parser = argparse.ArgumentParser(description="Scan Coq files to extract definitions and proofs.")
    parser.add_argument("file", help="The Coq file to scan.")
    parser.add_argument("--output", help="The JSON file to write the output to.", default=None)
    args = parser.parse_args()

    result = scan_coq_file(args.file)
    if result is None:
        print(f"Skipping file in draft directory: {args.file}")
        return

    output_json = json.dumps(result, indent=2)

    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(output_json)
        print(f"Scan results written to {args.output}")
    else:
        print(output_json)

if __name__ == "__main__":
    main()

