import re, sys, string
import argparse

desc = 'Generate assertions from pasted examples'
parser = argparse.ArgumentParser(description=desc)
parser.add_argument('--type', dest='test_type', default='mtest',
                    help='Type of test')

args = parser.parse_args()

# When copying directly:
# p = re.compile(r'In\[(\d+)\]:= ([^\n]+)\n\n(?:Out\[\1\]= ([^\n]+)|)')
# When copying as plain text
p = re.compile(r'In\[(\d+)\]:= ([^\n]+)\n(?:Out\[\1\]= ([^\n]+)|)')
test_str = sys.stdin.read()

if args.test_type == "string":
    format_str = 'assert.Equal(t, "{}", EasyRun("{}", es))'
elif args.test_type == "same":
    format_str = '&SameTest{{"{}", "{}"}},'
else:
    format_str = 'ESameTest[{}, {}],'
for num, instr, outstr in re.findall(p, test_str):
    if outstr == '':
        outstr = 'Null'
    to_print = format_str.format(outstr, instr)
    to_print = string.replace(to_print, '\[Pi]', 'Pi')
    print(to_print)
