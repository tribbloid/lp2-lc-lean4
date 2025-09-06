import sys

if len(sys.argv) != 4:
    print("Usage: python add_line_comment.py <file> <start> <end>")
    sys.exit(1)

file = sys.argv[1]
start = sys.argv[2]
end = sys.argv[3]

print(f"-- Coq: {file}:L{start}-L{end}")

