from parser import read_input
from intersection import find_intersection
from new_intersection import *
import argparse

parser = argparse.ArgumentParser(description="")
parser.add_argument("-i", "--input_path", type=str, default="./tests/test1.txt", help="Specify path to input file")
parser.add_argument("-cfg", "--cfg", action=argparse.BooleanOptionalAction, help="Show CFG")
parser.add_argument("-dfa", "--dfa", action=argparse.BooleanOptionalAction, help="Show DFA")
parser.add_argument("-deb", "--debug", action=argparse.BooleanOptionalAction, help="Show debug")

args = parser.parse_args()
c, d = read_input(args.input_path)

if args.cfg:
    print("CFG:")
    print(c)

if args.dfa:
    print("DFA:")
    print(d)

if args.debug:
    print("DEBUG ACTIVE")

intersection = make_intersection(c, d, args.debug)
# intersection = find_intersection(c, d)
# print(intersection)
# print("Intersection:")
for a in intersection:
    print(a)
