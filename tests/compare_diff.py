import sys


def main(argv):
    if len(argv) != 3:
        print("usage: compare_diff.py C_DIFF AGDA_DIFF")
        return 2
    with open(argv[1]) as handle:
        c_lines = handle.read().splitlines()
    with open(argv[2]) as handle:
        a_lines = handle.read().splitlines()

    for i in range(max(len(c_lines), len(a_lines))):
        c_line = c_lines[i] if i < len(c_lines) else ""
        a_line = a_lines[i] if i < len(a_lines) else ""
        c_parts = c_line.split()
        a_parts = a_line.split()
        if (len(c_parts) < 2 or len(a_parts) < 2
                or c_parts[0] != a_parts[0] or c_parts[1] != a_parts[1]):
            print("differential test: fail at line %d: c=%r agda=%r"
                  % (i, c_line, a_line))
            return 1

    print("differential test: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
