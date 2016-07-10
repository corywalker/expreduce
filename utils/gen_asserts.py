import re, sys
import argparse

desc = 'Generate assertions from pasted examples'
parser = argparse.ArgumentParser(description=desc)
parser.add_argument('--assert_str', dest='assert_str', action='store_true',
                    default=False,
                    help='Assert string result, not expression equality')

args = parser.parse_args()

p = re.compile(ur'In\[(\d+)\]:= ([^\n]+)\n\nOut\[\1\]= ([^\n]+)')
test_str = sys.stdin.read()

if args.assert_str:
    format_str = 'assert.Equal(t, "{}", EasyRun("{}", es))'
else:
    format_str = 'CasAssertSame(t, es, "{}", "{}")'
for num, instr, outstr in re.findall(p, test_str):
    print(format_str.format(outstr, instr))
