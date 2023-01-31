from parser import read_input
from intersection import find_intersection
import argparse

parser = argparse.ArgumentParser(description="")
parser.add_argument("-i", "--input_path", type=str, default="./tests/test1.txt", help="Specify path to input file")
parser.add_argument("-cfg", "--cfg", action=argparse.BooleanOptionalAction, help="Show CFG")
parser.add_argument("-dfa", "--dfa", action=argparse.BooleanOptionalAction, help="Show DFA")

args = parser.parse_args()
c, d = read_input(args.input_path)

if args.cfg:
    print("CFG:")
    print(c)

if args.dfa:
    print("DFA:")
    print(d)

intersection = find_intersection(c, d)
print("Intersection:")
for a in intersection:
    print(a)
