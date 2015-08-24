#!/usr/bin/env python

import sys
import os

if __name__ == "__main__":
    sys.path[0] = os.path.join(sys.path[0], 'runtests')
    from runtests.main import Runtests
    Runtests().main()
