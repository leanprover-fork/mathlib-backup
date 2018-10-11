
import sys
from os.path import relpath, abspath

for x in sys.stdin:
    print relpath(x)
