"""The tower's dependency tracer (round 399, F399-A1/B1/B2/C1: the
F269-3 class, its fourth round -- code a member runs that its static
key does not bind; widened at round 400, F400-B1..B5/C1..C5).

run_tower.py puts this directory first on PYTHONPATH for every live
member run and names a trace file in CASCADE_TRACE. Python then imports
this module at startup, in the member and in every Python process the
member spawns that keeps the environment and loads site (a child started
with -I, -E or -S, with a cleared environment or with its PYTHONPATH
replaced, does not), and an
audit hook appends one line per event to the trace file:

  R <path>      a file opened for reading (a trace that cannot be
                written ends the process with status 97, round 401
                F401-B2): open(), os.open() and
                io.open_code() (the import system's reads); a bytecode
                cache is written as its source when it has one (round
                400 F400-B1/C1: with a valid cache CPython never opens
                the .py), mapped here with this process's own pycache
                prefix (the round-400 sweep's pre-landing check: a cache
                under PYTHONPYCACHEPREFIX lies outside __pycache__); a
                cache with no source is written as itself
  L <dir>       a directory listed (os.listdir, os.scandir; glob,
                os.walk and pathlib go through them), except by the
                import system itself -- the driver hashes the listing,
                so a file a glob would pick up later changes the record
                (round 400 F400-B2); a listing by file descriptor is not
                recorded
  X <json>      a process spawned through subprocess.Popen (os.popen
                included), os.system, os.exec*, os.posix_spawn or
                os.spawn*: {"cwd": ..., "argv": [...]}, the argument
                list kept whole, so the driver can resolve quoted
                paths, "-m" specs and a "cd" written as its own word
                inside a shell string

An audit event fires before its operation, so a read or listing that
finds nothing is recorded too; the driver keeps such a path under the
repository as missing. The driver turns the trace into the run's
dependency set and stores it, hashed, with the cached PASS; a later
cache hit requires every recorded file and listing unchanged and every
missing path still absent. Recording is observation, not a sandbox: a
process that removes the hook or starts children that drop it is out of
scope (round 279); such a child's script is still resolved from its
parent's spawn line where the spawn went through one of the calls above
(multiprocessing's own spawn raises no audit event of these kinds).

The hook's re-entry guard is per thread (round 400 F400-B4/C2: a flag
shared by the process dropped other threads' reads while one thread
wrote). After installing the hook, this module runs the next
sitecustomize on sys.path (the system one), so the member's interpreter
behaves as it would without the tracer.
"""
import importlib.util as _util
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_OUT = os.environ.get("CASCADE_TRACE")
_SPAWN = {"subprocess.Popen", "os.system", "os.exec", "os.posix_spawn",
          "os.spawn"}
_LIST = {"os.listdir", "os.scandir"}

if _OUT:
    import json as _json
    import threading as _threading
    _local = _threading.local()
    _fd = [None]

    def _emit(line):
        _local.busy = True
        try:
            if _fd[0] is None:
                _fd[0] = os.open(_OUT, os.O_WRONLY | os.O_APPEND | os.O_CREAT,
                                 0o600)
            data = (line.replace("\n", " ") + "\n").encode(
                "utf-8", "surrogateescape")
            if os.write(_fd[0], data) != len(data):
                raise OSError("short write")
        except OSError:
            # round 401 F401-B2: a trace that cannot be written would be
            # cached as a complete record; fail closed instead
            try:
                os.write(2, b"reach_trace: the trace could not be written\n")
            except OSError:
                pass
            os._exit(97)
        finally:
            _local.busy = False

    def _text(x):
        if isinstance(x, bytes):
            return x.decode("utf-8", "surrogateescape")
        if isinstance(x, os.PathLike):
            return _text(os.fspath(x))
        return x if isinstance(x, str) else None

    def _source(pyc):
        try:
            src = _util.source_from_cache(pyc)
        except (ValueError, NotImplementedError):
            return pyc
        return src if os.path.isfile(src) else pyc

    def _hook(event, args):
        if getattr(_local, "busy", False):
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
                path = os.path.abspath(path)
                if path.endswith(".pyc"):
                    path = _source(path)
                _emit("R " + path)
        elif event in _LIST:
            # the import system's own listings (its path finder caches a
            # sys.path directory's names) are left to the static walk,
            # which resolves imports against the code roots: a file that
            # would shadow an import written in a reach file rotates the
            # key there; one that shadows a library's own import is not
            # bound by either (round 401 F401-B6/C2)
            caller = sys._getframe(1)
            if caller.f_code.co_filename.startswith("<frozen importlib"):
                return
            path = _text(args[0]) if args else None
            if path is None and args and args[0] is not None:
                return
            _emit("L " + os.path.abspath(path or os.curdir))
        elif event in _SPAWN:
            if event == "os.system":
                argv, cwd = [args[0]], None
            elif event == "subprocess.Popen":
                exe, argv, cwd = args[0], args[1], args[2]
                if isinstance(argv, (str, bytes, os.PathLike)):
                    argv = [argv]
                argv = ([exe] if exe is not None else []) + list(argv or [])
            elif event == "os.spawn":
                argv, cwd = [args[1]] + list(args[2] or []), None
            else:
                argv, cwd = [args[0]] + list(args[1] or []), None
            argv = [t for t in (_text(a) for a in argv) if t]
            _emit("X " + _json.dumps({
                "cwd": os.path.abspath(_text(cwd) or os.getcwd()),
                "argv": argv}))

    sys.addaudithook(_hook)

# chain to the next sitecustomize on the path (the system one)
import importlib.machinery as _mach
_spec = _mach.PathFinder.find_spec(
    "sitecustomize",
    [p for p in sys.path if os.path.abspath(p or os.curdir) != _HERE])
if _spec is not None and _spec.loader is not None:
    _mod = _util.module_from_spec(_spec)
    _spec.loader.exec_module(_mod)
