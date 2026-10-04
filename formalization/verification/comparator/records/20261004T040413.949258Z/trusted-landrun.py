#!/usr/bin/env python3
"""Explicit TRUSTED-LOCAL adapter: executes a command WITHOUT sandboxing.

Only installed by reproduce.py --trusted-local; never an automatic fallback.
Accepts exactly the argument grammar emitted by the pinned comparator.
"""
import os
import sys

args = sys.argv[1:]
while args:
    flag = args[0]
    if flag in ("--best-effort", "-ldd", "-add-exec"):
        args = args[1:]
    elif flag in ("--env", "--ro", "--rw", "--rwx", "--rox"):
        if len(args) < 2:
            sys.exit("missing comparator sandbox option value")
        args = args[2:]
    elif flag.startswith("-"):
        sys.exit("unsupported comparator sandbox option: " + flag)
    else:
        break
if not args:
    sys.exit("missing comparator command")
os.execvp(args[0], args)
