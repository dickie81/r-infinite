"""The tower's dependency tracer (round 399, F399-A1/B1/B2/C1: the
F269-3 class, its fourth round -- code a member runs that its static
key does not bind).

run_tower.py puts this directory first on PYTHONPATH for every live
member run and names a trace file in CASCADE_TRACE. Python then imports
this module at startup, in the member and in every Python process the
member spawns (the environment is inherited), and an audit hook appends
one line per event to the trace file:

  R <path>              a file opened for reading (source files read by
                        the import system included -- io.open_code
                        raises the same "open" event)
  X <cwd> <arg>...      a process spawned (subprocess.Popen, os.system,
                        os.exec*, os.posix_spawn, os.spawn*): its
                        working directory and each argument, so a
                        script named on a command line is recorded even
                        when the child does not load this module

The driver turns the trace into the run's dependency set and stores it,
hashed, with the cached PASS; a later cache hit requires every recorded
file unchanged. Recording is observation, not a sandbox: a process that
removes the hook, clears the environment for its children or starts
Python in isolated mode is out of scope (round 279), though such a
child's script is still recorded from its parent's spawn event.

After installing the hook, this module runs the next sitecustomize on
sys.path (the system one), so the member's interpreter behaves as it
would without the tracer.
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_OUT = os.environ.get("CASCADE_TRACE")
_SPAWN = {"subprocess.Popen", "os.system", "os.exec", "os.posix_spawn",
          "os.spawn"}

if _OUT:
    _busy = [False]
    _fd = [None]

    def _emit(line):
        _busy[0] = True
        try:
            if _fd[0] is None:
                _fd[0] = os.open(_OUT, os.O_WRONLY | os.O_APPEND | os.O_CREAT,
                                 0o600)
            os.write(_fd[0], (line.replace("\n", " ") + "\n").encode(
                "utf-8", "surrogateescape"))
        except OSError:
            pass
        finally:
            _busy[0] = False

    def _text(x):
        if isinstance(x, bytes):
            return x.decode("utf-8", "surrogateescape")
        if isinstance(x, os.PathLike):
            return _text(os.fspath(x))
        return x if isinstance(x, str) else None

    def _hook(event, args):
        if _busy[0]:
            return
        if event == "open":
            path, mode, flags = (tuple(args) + (None, None, None))[:3]
            path = _text(path)
            if path is None:
                return
            if isinstance(mode, str):
                reading = "r" in mode or "+" in mode
            else:
                acc = (flags or 0) & os.O_ACCMODE
                reading = acc in (os.O_RDONLY, os.O_RDWR)
            if reading:
                _emit("R " + os.path.abspath(path))
        elif event in _SPAWN:
            if event == "os.system":
                argv = [args[0]]
                cwd = None
            elif event == "subprocess.Popen":
                exe, argv, cwd = args[0], args[1], args[2]
                if isinstance(argv, (str, bytes, os.PathLike)):
                    argv = [argv]
                argv = [exe] + list(argv or [])
            elif event == "os.spawn":
                argv = [args[1]] + list(args[2] or [])
                cwd = None
            else:
                argv = [args[0]] + list(args[1] or [])
                cwd = None
            words = []
            for a in argv:
                t = _text(a)
                if t:
                    words += t.split()
            _emit("X " + " ".join([os.path.abspath(_text(cwd) or os.getcwd())]
                                  + words))

    sys.addaudithook(_hook)

# chain to the next sitecustomize on the path (the system one)
import importlib.machinery as _mach
import importlib.util as _util
_spec = _mach.PathFinder.find_spec(
    "sitecustomize",
    [p for p in sys.path if os.path.abspath(p or os.curdir) != _HERE])
if _spec is not None and _spec.loader is not None:
    _mod = _util.module_from_spec(_spec)
    _spec.loader.exec_module(_mod)
