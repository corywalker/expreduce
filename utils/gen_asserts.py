import re, sys

p = re.compile(ur'In\[(\d+)\]:= ([^\n]+)\n\nOut\[\1\]= ([^\n]+)')
test_str = sys.stdin.read()

for num, instr, outstr in re.findall(p, test_str):
    print('CasAssertSame(t, es, "{}", "{}")'.format(outstr, instr))
