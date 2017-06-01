import re, sys
import argparse

desc = 'Generate assertions from pasted examples'
parser = argparse.ArgumentParser(description=desc)
parser.add_argument('--assert_str', dest='assert_str', action='store_true',
                    default=False,
                    help='Assert string result, not expression equality')

args = parser.parse_args()

# When copying directly:
# p = re.compile(r'In\[(\d+)\]:= ([^\n]+)\n\n(?:Out\[\1\]= ([^\n]+)|)')
# When copying as plain text
p = re.compile(r'In\[(\d+)\]:= ([^\n]+)\n(?:Out\[\1\]= ([^\n]+)|)')
test_str = sys.stdin.read()

if args.assert_str:
    format_str = 'assert.Equal(t, "{}", EasyRun("{}", es))'
else:
    format_str = '&SameTest{{"{}", "{}"}},'
for num, instr, outstr in re.findall(p, test_str):
    if outstr == '':
        outstr = 'Null'
    print(format_str.format(outstr, instr))
