#!/usr/bin/env python3
"""Live VerseVM conformance: probe sources for UEFN, OpenVerse runs, UEFN log
parsing and the comparison report (docs/research/versevm-live-conformance.md).

Python 3 standard library only; the generate, parse and compare commands run
the same on Linux and Windows.

  ovprobe.py generate [--mode single|batch] [--layout driver|devices] [--out DIR]
                      [--header FILE] [--marker WORD] [--exclude ID]...
                      [--exclude-refused PARSED.json] [--exclude-done PARSED.json]
                      [--risky-last OV.json] PROBE...
      single: OUT/<id>/openverse_probe.verse for each probe, byte for byte the
      runbook's `cat device.verse.header; printf '\\n'; cat PROBE`. Use it to
      test compile admission one probe at a time: an error in one file can
      hide errors in others.
      batch, driver layout (default): OUT/ovprobes/openverse_probe_driver.verse,
      one inline module per probe (`ovp_<ident> := module:`, the body indented)
      with a public entry, and one device, openverse_probe_driver, that runs
      the entries in order. Every line is tagged with the probe id:
      `OVPROBE <id> begin|...|end`. One device to place, one session per batch.
      batch, devices layout: OUT/ovprobes/ovp_<ident>/ovp_<ident>.verse, one
      folder (one Verse module) per probe, each with its own device class.
      A Verse runtime error ends the session's Verse, so batch only admitted
      probes, put the risky ones last (--risky-last), and after each session
      generate the rest with --exclude-done.
      Every mode writes OUT/manifest.json, which `parse` uses to attribute
      lines and diagnostics.

  ovprobe.py openverse [--openverse BIN] [--cverse BIN] [--modes LIST]
                       [--json OUT] [--tsv OUT] PROBE...
      run every probe with the Lean interpreter (`openverse run --emit`) and,
      when bytecode was written, with the C runtime, in each mode (`default`,
      and `signal-rollback`, the legacy transactional mode, #515; also
      `signal-no-rollback`, the default's old opt-in name, which older
      result files use); record stdout, stderr and exit status.

  ovprobe.py parse [--manifest M | --single ID] [--marker WORD]
                   [--line-regex RE] [--diag-regex RE] [--runtime-error-regex RE]
                   [--out PARSED.json] LOG...
      extract the ordered OVPROBE lines of every probe run, Verse compiler
      diagnostics, runtime error lines and build identification from UEFN
      editor, build or session logs (UTF-8, with or without a byte order
      mark, or UTF-16), and diagnostics from JSON build results (uefn_mcp.py's
      admission records, or UEFN's BuildAll output).

  ovprobe.py compare --openverse OV.json --epic PARSED.json... [--expectations TSV]...
                     [--tsv OUT] [--md OUT]
      per-probe verdicts: agree, differ, epic-refuses, openverse-refuses or
      inconclusive, with the raw evidence, against each OpenVerse mode, and
      Epic and OpenVerse each against the Book's expectation where one exists.

PROBE is a .verse probe body or a directory of them (not recursive). A probe's
id is its file name without `.verse`; `X-control.verse` is the paired control
of `X.verse`. An `expectations.tsv` beside the probes gives the Book's
expectation (columns probe, book_case, book_outcome, book_lines).
"""

import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
HEADER = os.path.join(HERE, "device.verse.header")
MARKER = "OVPROBE"
SINGLE_FILE = "openverse_probe.verse"
SINGLE_CLASS = "openverse_probe"
BATCH_ROOT = "ovprobes"
DRIVER_FILE = "openverse_probe_driver.verse"
DRIVER_CLASS = "openverse_probe_driver"
DRIVER_ID = "ovprobe-driver"
ENTRY = "RunOVProbe"
OV_DRIVER_FN = "Main"
MODES = ("default", "signal-rollback", "signal-no-rollback")
# (the modes `openverse` runs unless told: the default, Epic's admission of
# an event's Signal, and the legacy transactional mode, #515)
DEFAULT_MODES = ("default", "signal-rollback")
OUTCOMES_RUN = ("ran", "runtime-error", "failed", "limit")
VERDICTS = ("agree", "differ", "epic-refuses", "openverse-refuses", "inconclusive")
ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")


# ---------------------------------------------------------------------------
# Probes
# ---------------------------------------------------------------------------

def read_bytes(path):
    with open(path, "rb") as fh:
        return fh.read()


def rel(path):
    """A path relative to the repository root, with forward slashes."""
    try:
        return os.path.relpath(os.path.abspath(path), ROOT).replace(os.sep, "/")
    except ValueError:   # another drive on Windows
        return os.path.abspath(path).replace(os.sep, "/")


def find_probes(paths):
    """[(id, path)] of the probe bodies named by files and directories, in order."""
    out = []
    for p in paths:
        if os.path.isdir(p):
            out += [os.path.join(p, f) for f in sorted(os.listdir(p)) if f.endswith(".verse")]
        elif p.endswith(".verse") and os.path.isfile(p):
            out.append(p)
        else:
            raise SystemExit("ovprobe: not a probe file or directory: %s" % p)
    probes, seen = [], {}
    for path in out:
        pid = os.path.basename(path)[:-len(".verse")]
        if not ID_RE.match(pid):
            raise SystemExit("ovprobe: probe id %r has characters other than letters, digits, '_', '.', '-'" % pid)
        if pid in seen:
            raise SystemExit("ovprobe: two probes have the id %s: %s and %s" % (pid, seen[pid], path))
        seen[pid] = path
        probes.append((pid, path))
    return probes


def control_of(pid, ids):
    """The paired control's id (`X-control` for `X`), when it is among ids."""
    c = pid + "-control"
    return c if c in ids else None


def ident(pid):
    """The Verse identifier of a probe's module: ovp_ plus the id in snake case."""
    return "ovp_" + re.sub(r"[^a-z0-9]+", "_", pid.lower()).strip("_")


def tag_markers(text, marker, pid):
    """The text with every string literal that starts with `MARKER ` tagged
    `MARKER <pid> `. Refuses a marker anywhere else, where tagging could not
    be done reliably."""
    word = re.escape(marker)
    total = len(re.findall(r"(?<![A-Za-z0-9_])%s(?![A-Za-z0-9_])" % word, text))
    tagged, n = re.subn(r'(?<=")%s(?= )' % word, "%s %s" % (marker, pid), text)
    if n != total:
        raise SystemExit("ovprobe: %s: %d use(s) of %s are not at the start of a string literal "
                         "followed by a space; batch mode cannot tag them" % (pid, total - n, marker))
    return tagged


def single_source(header, body):
    """The runbook's single-probe device source: header, a newline, the body."""
    return header + b"\n" + body


def body_first_line(prefix):
    return prefix.count(b"\n") + 1


def header_parts(header):
    """The header's `using` lines."""
    text = header.decode("utf-8")
    usings = [l for l in text.split("\n") if re.match(r"\s*using\b", l)]
    if not usings:
        raise SystemExit("ovprobe: the header has no using lines")
    return usings


def check_reserved(body, pid, marker):
    for word in ("begin", "end"):
        if re.search(r'"%s %s %s"' % (re.escape(marker), re.escape(pid), word), body):
            raise SystemExit("ovprobe: %s prints the reserved marker %r" % (pid, word))


def device_source(header, body, pid, marker):
    """A probe's source in the devices layout: the header with its own device
    class and tagged markers, a newline, the tagged body."""
    h = header.decode("utf-8")
    cls = ident(pid) + "_device"
    pat = r"(?m)^%s(?=\s*:=)" % re.escape(SINGLE_CLASS)
    h, n = re.subn(pat, cls, h)
    if n != 1:
        raise SystemExit("ovprobe: the header must define the class %s once" % SINGLE_CLASS)
    h = tag_markers(h, marker, pid)
    for word in ("begin", "end"):
        if '"%s %s %s"' % (marker, pid, word) not in h:
            raise SystemExit("ovprobe: the header must print \"%s %s\"" % (marker, word))
    b = tag_markers(body.decode("utf-8"), marker, pid)
    check_reserved(b, pid, marker)
    return (h.encode("utf-8") + b"\n", b.encode("utf-8")), cls


def indent_block(text, n):
    return "\n".join((" " * n + l) if l.strip() else "" for l in text.split("\n"))


def driver_source(header, probes, marker, host="uefn"):
    """The driver layout: one file, one inline module per probe, each with a
    public entry that prints the begin and end markers around the probe's
    Main, and one device class that calls the entries in order. Returns the
    source and, per probe, the file lines of its body. With host "openverse"
    the device class is a top-level Main()<suspends> and the Fortnite modules
    are not used, so `openverse run FILE` runs the same batch: a check of the
    layout and of the demultiplexing. (Epic's compiler is not asked to accept
    that Main beside the modules' own.)"""
    usings = header_parts(header)
    out = []
    if host == "openverse":
        out += [u for u in usings if "/Fortnite.com" not in u] + [""]
        out += ["# Generated by tests/conformance/versevm/ovprobe.py (driver layout, OpenVerse host).",
                "%s()<suspends>:void =" % OV_DRIVER_FN]
        pad = "    "
    else:
        out += list(usings) + [""]
        out += ["# Generated by tests/conformance/versevm/ovprobe.py (driver layout).",
                "%s := class(creative_device):" % DRIVER_CLASS,
                "    OnBegin<override>()<suspends>:void ="]
        pad = "        "
    out += ['%sPrint("%s %s begin")' % (pad, marker, DRIVER_ID)]
    out += ["%s%s.%s()" % (pad, ident(pid), ENTRY) for pid, _ in probes]
    out += ['%sPrint("%s %s end")' % (pad, marker, DRIVER_ID), ""]
    spans = {}
    for pid, body in probes:
        b = tag_markers(body.decode("utf-8"), marker, pid)
        check_reserved(b, pid, marker)
        b = b.rstrip("\n")
        if "\t" in b:
            raise SystemExit("ovprobe: %s has tabs; the driver layout indents bodies with spaces" % pid)
        out += ["%s := module:" % ident(pid),
                "    %s<public>()<suspends>:void =" % ENTRY,
                '        Print("%s %s begin")' % (marker, pid),
                "        Main()",
                '        Print("%s %s end")' % (marker, pid), ""]
        first = len(out) + 1
        out += indent_block(b, 4).split("\n")
        spans[pid] = (first, len(out))
        out.append("")
    return ("\n".join(out) + "\n").encode("utf-8"), spans


def write_file(path, data):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "wb") as fh:   # binary: no newline translation on Windows
        fh.write(data)


def load_json(path):
    with open(path, "rb") as fh:
        return json.loads(decode_log(fh.read()))


def load_jsons(paths):
    """The JSON documents of files, a directory standing for its *.json files."""
    out = []
    for p in paths or []:
        files = [os.path.join(p, f) for f in sorted(os.listdir(p)) if f.endswith(".json")] \
            if os.path.isdir(p) else [p]
        out += [load_json(f) for f in files]
    return out


def refused_ids(parsed):
    return {pid for pid, p in parsed.get("probes", {}).items()
            if any(d["severity"] == "error" for d in p.get("diagnostics", []))}


def done_ids(parsed):
    """Probes a parsed session has an answer for: refused, or begun (complete
    or aborted). A Verse runtime error ends the session's Verse, so the probes
    after an aborted one never begin and are left for the next session."""
    return refused_ids(parsed) | {pid for pid, p in parsed.get("probes", {}).items()
                                  if any(r["begun"] for r in p.get("runs", []))}


def risky_ids(ov_json):
    """Probes whose OpenVerse run (Lean, any mode) ends in a runtime error, a
    resource limit or a timeout: in a batch they go last."""
    return {r["probe"] for r in load_json(ov_json)["records"]
            if r["runtime"] == "lean" and r["outcome"] in ("runtime-error", "limit", "timeout")}


def cmd_generate(a):
    header = read_bytes(a.header)
    probes = find_probes(a.probes)
    skip = set(a.exclude or [])
    for d in load_jsons(a.exclude_refused):
        skip |= refused_ids(d)
    for d in load_jsons(a.exclude_done):
        skip |= done_ids(d)
    probes = [(pid, path) for pid, path in probes if pid not in skip]
    if a.risky_last:
        risky = risky_ids(a.risky_last)
        probes = [p for p in probes if p[0] not in risky] + [p for p in probes if p[0] in risky]
    if not probes:
        raise SystemExit("ovprobe: no probes to generate")
    idents = {}
    for pid, _ in probes:
        k = ident(pid)
        if k in idents:
            raise SystemExit("ovprobe: %s and %s have the same Verse identifier %s" % (idents[k], pid, k))
        idents[k] = pid
    ids = {pid for pid, _ in probes}
    bodies = [(pid, read_bytes(path)) for pid, path in probes]
    entries = []
    for (pid, path), (_, body) in zip(probes, bodies):
        entries.append({"id": pid, "source": rel(path), "sha256": hashlib.sha256(body).hexdigest(),
                        "control": control_of(pid, ids)})
    layout = a.layout if a.mode == "batch" else "single"
    if layout == "driver":
        src, spans = driver_source(header, bodies, a.marker, a.host)
        out = "%s/%s" % (BATCH_ROOT, DRIVER_FILE)
        write_file(os.path.join(a.out, *out.split("/")), src)
        for e in entries:
            first, last = spans[e["id"]]
            e.update(file=out, module=ident(e["id"]), device_class=DRIVER_CLASS,
                     body_first_line=first, body_last_line=last, indent=4)
    for e, (pid, body) in zip(entries, bodies):
        if layout == "single":
            write_file(os.path.join(a.out, pid, SINGLE_FILE), single_source(header, body))
            e.update(file="%s/%s" % (pid, SINGLE_FILE), device_class=SINGLE_CLASS,
                     body_first_line=body_first_line(header + b"\n"))
        elif layout == "devices":
            (h, b), cls = device_source(header, body, pid, a.marker)
            name = ident(pid)
            out = "%s/%s/%s.verse" % (BATCH_ROOT, name, name)
            write_file(os.path.join(a.out, *out.split("/")), h + b)
            e.update(file=out, module=name, device_class=cls, body_first_line=body_first_line(h))
    manifest = {"tool": "ovprobe.py generate", "mode": a.mode, "layout": layout,
                "host": a.host if layout == "driver" else "uefn",
                "marker": a.marker, "header": rel(a.header),
                "header_sha256": hashlib.sha256(header).hexdigest(),
                "driver_id": DRIVER_ID if layout == "driver" else None, "probes": entries}
    write_file(os.path.join(a.out, "manifest.json"),
               (json.dumps(manifest, indent=2) + "\n").encode("utf-8"))
    print("ovprobe: wrote %d probe(s), %s layout, and manifest.json under %s"
          % (len(entries), layout, a.out))
    if layout == "driver" and a.host == "openverse":
        print("  run: openverse run %s" % os.path.join(a.out, BATCH_ROOT, DRIVER_FILE))
    elif layout == "driver":
        print("  copy the folder %s into the UEFN project's Verse folder, build Verse, and place"
              % BATCH_ROOT)
        print("  one %s device; it runs the probes in this order:" % DRIVER_CLASS)
        for e in entries:
            print("    %s" % e["id"])
    elif layout == "devices":
        print("  copy the folder %s into the UEFN project's Verse folder, build Verse," % BATCH_ROOT)
        print("  and place one instance of each device class:")
        for e in entries:
            print("    %-48s %s" % (e["device_class"], e["id"]))
    else:
        print("  copy one %s at a time into the UEFN project (see the runbook)" % SINGLE_FILE)
    return 0


# ---------------------------------------------------------------------------
# OpenVerse runs
# ---------------------------------------------------------------------------

COMPILER_PATHS = ["OpenVerse", "OpenVerse.lean", "Main.lean", "runtime", "lakefile.toml",
                  "lean-toolchain", "lake-manifest.json"]


def git(*args):
    try:
        p = subprocess.run(["git", "-C", ROOT] + list(args), stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)
        return p.stdout.decode("utf-8", "replace").strip() if p.returncode == 0 else None
    except OSError:
        return None


def run_cmd(cmd, timeout):
    try:
        p = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout)
        return p.returncode, p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return None, "", "timeout after %ds\n" % timeout


def ov_outcome(rc):
    return {0: "ran", 1: "failed", 2: "runtime-error", 3: "limit", 4: "refused",
            None: "timeout"}.get(rc, "crash")


def split_warnings(err, path):
    """The compiler's leading `PATH:L:C: warning:` lines, and the rest."""
    lines = err.split("\n")
    k = 0
    while k < len(lines) and lines[k].startswith(path + ":") and ": warning: " in lines[k]:
        k += 1
    return lines[:k], "\n".join(lines[k:])


def cmd_openverse(a):
    probes = find_probes(a.probes)
    modes = [m.strip() for m in a.modes.split(",") if m.strip()]
    for m in modes:
        if m not in MODES:
            raise SystemExit("ovprobe: unknown mode %s (modes: %s)" % (m, ", ".join(MODES)))
    for exe in (a.openverse, a.cverse):
        if not os.path.isfile(exe):
            raise SystemExit("ovprobe: %s not found: build OpenVerse first (lake build; make -C runtime)" % exe)
    records = []
    with tempfile.TemporaryDirectory() as tmp:
        for pid, path in probes:
            src = rel(path)
            sha = hashlib.sha256(read_bytes(path)).hexdigest()
            for mode in modes:
                vbc = os.path.join(tmp, "%s.%s.vbc" % (pid, mode))
                flags = ["--" + mode] if mode in ("signal-rollback", "signal-no-rollback") else []
                cmd = [a.openverse, "run", src] + flags + ["--emit", vbc]
                rc, out, err = run_cmd(cmd, a.timeout)
                warnings, _ = split_warnings(err, src)
                lean = {"probe": pid, "path": src, "sha256": sha, "mode": mode, "runtime": "lean",
                        "command": " ".join(["openverse"] + cmd[1:-1] + ["PROBE.vbc"]),
                        "exit": rc, "stdout": out, "stderr": err, "outcome": ov_outcome(rc),
                        "warnings": warnings}
                records.append(lean)
                c = {"probe": pid, "path": src, "sha256": sha, "mode": mode, "runtime": "c",
                     "command": "cverse PROBE.vbc"}
                if os.path.exists(vbc):
                    crc, cout, cerr = run_cmd([a.cverse, vbc], a.timeout)
                    c.update(exit=crc, stdout=cout, stderr=cerr, outcome=ov_outcome(crc))
                    os.remove(vbc)
                else:
                    c.update(exit=None, stdout="", stderr="", outcome="not-run")
                records.append(c)
    head = git("rev-parse", "HEAD")
    compiler = git("log", "-1", "--format=%H", "--", *COMPILER_PATHS)
    changed = git("status", "--porcelain", "--untracked-files=no", "--", *COMPILER_PATHS)
    doc = {"tool": "ovprobe.py openverse", "head": head, "compiler_revision": compiler,
           "compiler_sources_modified": bool(changed),
           "date_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
           "modes": modes, "records": records}
    if a.json:
        write_file(a.json, (json.dumps(doc, indent=1) + "\n").encode("utf-8"))
    if a.tsv:
        cols = ["probe", "mode", "runtime", "exit", "outcome", "stdout", "stderr", "path", "sha256"]
        rows = ["\t".join(cols)] + ["\t".join(tsv_cell(r.get(k)) for k in cols) for r in records]
        write_file(a.tsv, ("\n".join(rows) + "\n").encode("utf-8"))
    summary = summarize_openverse(doc)
    print(summary)
    return 0


def tsv_cell(v):
    if v is None:
        return ""
    s = str(v)
    return s.replace("\\", "\\\\").replace("\t", "\\t").replace("\r", "\\r").replace("\n", "\\n")


def summarize_openverse(doc):
    by = {}
    for r in doc["records"]:
        by.setdefault((r["probe"], r["mode"]), {})[r["runtime"]] = r
    out = ["OpenVerse %s (compiler sources %s%s)" % (
        (doc.get("head") or "?")[:12], (doc.get("compiler_revision") or "?")[:12],
        ", modified" if doc.get("compiler_sources_modified") else "")]
    for (pid, mode), rs in by.items():
        lean, c = rs.get("lean"), rs.get("c")
        agree = c is None or c["outcome"] == "not-run" or (
            (lean["exit"], lean["stdout"]) == (c["exit"], c["stdout"]))
        out.append("  %-34s %-19s lean %-13s c %-13s %s" % (
            pid, mode, lean["outcome"], c["outcome"] if c else "-",
            "" if agree else "LEAN/C DISAGREE"))
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Log parsing
# ---------------------------------------------------------------------------

# `[2026.11.18-10.22.33:123][ 42]LogVerse: : text`: the timestamp and frame
# prefix of an Unreal log line, then the category. Verse's Print goes to
# LogVerse with an empty channel field (the Book's API reference, `log`).
UE_CATEGORY = re.compile(r"^(?:\[[^\]]*\])*\s*(Log[A-Za-z0-9_]+|VerseBuild)\s*:")
ROLLBACK = re.compile(r"\(\s*Rolling\s+Back\s*\)", re.I)
# A Verse compiler diagnostic, as UEFN's log writes it:
#   VerseBuild: Error: C:/path/f.verse(25,17, 25,31): Script error 3506: Unknown identifier
# The path may hold spaces and a drive letter; the (L,C[, L2,C2]) range is optional.
DIAG = (r"(?P<path>(?:[A-Za-z]:)?[^():\"<>|]*?\.verse)\s*"
        r"\((?P<line>\d+)\s*,\s*(?P<col>\d+)(?:\s*,\s*(?P<eline>\d+)\s*,\s*(?P<ecol>\d+))?\)\s*:\s*"
        r"(?P<kind>(?:Script\s+)?(?:error|warning))\s*(?P<code>\d+)?\s*:\s*(?P<message>.*)")
# one without a location: `Script error 3100: ...`
DIAG_BARE = re.compile(r"\bScript\s+(?P<kind>error|warning)\s*(?P<code>\d+)?\s*:\s*(?P<message>.*)", re.I)
DIAG_GUARD = re.compile(r"(?i)\bscript\s+(?:error|warning)\b|\.verse\s*\(\d+\s*,\s*\d+")
RUNTIME_ERROR = (r"(?i)verse\s*runtime\s*error|runtime\s+error|ErrRuntime|unrecoverable\s+error"
                 r"|VerseRuntimeErrors")
BUILD_INFO = re.compile(r"(?i)\b(?:LogInit|LogVerse\w*|LogUEFN\w*)\b.*?\b(Build|Engine Version|Net CL|"
                        r"Compatible Engine Version|Changelist|BuildVersion)\s*:\s*(.+)$")
BACKEND = re.compile(r"(?i)verse\s*vm|\bBPVM\b|blueprint\s*vm|UseVerseVM")
# The diagnostics of a JSON build result (UEFN's MCP BuildAll, saved by
# uefn_mcp.py): objects with a message and a severity or code.
JSON_PATH_KEYS = ("filePath", "file", "path", "uri", "sourcePath")
JSON_LINE_KEYS = ("startLine", "line", "Line", "StartLine")
JSON_COL_KEYS = ("startColumn", "startCol", "column", "col", "Column", "StartColumn")


def decode_log(data):
    if data.startswith(b"\xef\xbb\xbf"):
        return data[3:].decode("utf-8", "replace")
    if data.startswith(b"\xff\xfe") or data.startswith(b"\xfe\xff"):
        return data.decode("utf-16", "replace")
    # UTF-16 without a byte order mark: every other byte zero
    if len(data) >= 4 and data[1:2] == b"\x00" and data[3:4] == b"\x00":
        return data.decode("utf-16-le", "replace")
    return data.decode("utf-8", "replace")


def json_diagnostics(doc):
    """Every object in a JSON document that looks like a diagnostic."""
    out = []

    def walk(x):
        if isinstance(x, dict):
            if isinstance(x.get("message"), str) and ("severity" in x or "code" in x):
                out.append(x)
                return
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
        elif isinstance(x, str) and x.lstrip()[:1] in ("[", "{"):
            try:     # MCP tool results carry JSON as text content
                walk(json.loads(x))
            except ValueError:
                pass
    walk(doc)
    return out


def first_key(d, keys):
    for k in keys:
        if k in d and d[k] is not None:
            return d[k]
    return None


class Parser:
    def __init__(self, marker=MARKER, manifest=None, single=None, line_regex=None,
                 diag_regex=None, runtime_error_regex=None, header=HEADER,
                 json_zero_based=True):
        self.marker = marker
        self.single = single
        self.manifest = manifest
        self.json_zero_based = json_zero_based
        self.ids = {e["id"] for e in manifest["probes"]} if manifest else set()
        if manifest and manifest.get("driver_id"):
            self.ids.add(manifest["driver_id"])
        if single:
            self.ids.add(single)
        word = re.escape(marker)
        self.line_re = re.compile(line_regex) if line_regex else re.compile(
            r"(?P<pre>.*?)(?<![A-Za-z0-9_\"'])%s(?![A-Za-z0-9_\"'])[ \t]*(?P<rest>.*?)\s*$" % word)
        self.diag_re = re.compile(diag_regex or DIAG, re.I)
        self.rt_re = re.compile(runtime_error_regex or RUNTIME_ERROR)
        self.probes = {}
        self.unattributed = []
        self.diag_unattributed = []
        self.runtime_errors = []
        self.build_info = []
        self.backend = []
        self.verse_errors = []
        self.files = []
        self.file_index = {}
        for e in (manifest or {}).get("probes", []):
            self.file_index.setdefault(os.path.basename(e["file"]).lower(), []).append(e)
        # the runbook's single-probe file: the header, a newline, the body
        self.single_offset = body_first_line(read_bytes(header) + b"\n") if single else None

    def probe(self, pid):
        return self.probes.setdefault(pid, {"runs": [], "diagnostics": [], "admission": []})

    def open_runs(self):
        return [(pid, p["runs"][-1]) for pid, p in self.probes.items()
                if p["runs"] and p["runs"][-1]["begun"] and not p["runs"][-1]["ended"]]

    def attribute_diag(self, path, line):
        """(probe id, its manifest entry or None) of a diagnostic's file and line."""
        if not path:
            return None, None
        base = re.split(r"[\\/]", path.strip())[-1].lower()
        for e in self.file_index.get(base, []):
            last = e.get("body_last_line")
            if last is None or (line is not None and e["body_first_line"] <= line <= last):
                return e["id"], e
        if base in self.file_index and len(self.file_index[base]) > 1:
            return None, None     # the driver's own lines
        if self.single and base == SINGLE_FILE:
            return self.single, {"body_first_line": self.single_offset}
        return None, None

    def add_diagnostic(self, d, pid=None, entry=None):
        if pid is None:
            pid, entry = self.attribute_diag(d.get("path"), d.get("line"))
        if pid and entry and d.get("line") is not None and entry.get("body_first_line"):
            d["body_line"] = d["line"] - entry["body_first_line"] + 1
            if d.get("col") is not None and entry.get("indent"):
                d["body_col"] = d["col"] - entry["indent"]
        if pid:
            self.probe(pid)["diagnostics"].append(d)
        else:
            self.diag_unattributed.append(d)

    def feed_file(self, path):
        text = decode_log(read_bytes(path))
        head = text.lstrip()[:1]
        if head in ("{", "["):
            try:
                doc = json.loads(text)
            except ValueError:
                doc = None
            if doc is not None:
                self.feed_json(doc, path)
                return
        self.feed(text, path)

    def feed_json(self, doc, fname):
        """A JSON build result: uefn_mcp.py's admission record ({"kind":
        "verse-admission", "results": [{probe, body_first_line, diagnostics,
        ...}]}) or any JSON holding diagnostics (BuildAll's entries:
        severity, code, message, filePath, span with 0-based lines)."""
        self.files.append(fname)
        if isinstance(doc, dict) and doc.get("kind") == "verse-admission":
            zero = doc.get("zero_based", self.json_zero_based)
            slot = str(doc.get("slot") or SINGLE_FILE).lower()
            for k, r in enumerate(doc.get("results", [])):
                pid = r.get("probe")
                diags = [self.json_diag(x, "%s#%d" % (fname, k), zero)
                         for x in json_diagnostics(r.get("diagnostics", []))]
                if not pid:
                    for d in diags:
                        self.add_diagnostic(d)
                    continue
                entry = {"body_first_line": r.get("body_first_line") or self.single_offset}
                p = self.probe(pid)
                p["admission"].append({"at": "%s#%d" % (fname, k), "build_ok": r.get("build_ok"),
                                       "errors": sum(1 for d in diags if d["severity"] == "error")})
                for d in diags:
                    base = re.split(r"[\\/]", (d.get("path") or "").strip())[-1].lower()
                    if base in ("", slot):
                        self.add_diagnostic(d, pid, entry)
                    else:     # another file of the project
                        self.diag_unattributed.append(d)
            return
        zero = doc.get("zero_based", self.json_zero_based) if isinstance(doc, dict) \
            else self.json_zero_based
        for k, x in enumerate(json_diagnostics(doc)):
            self.add_diagnostic(self.json_diag(x, "%s#%d" % (fname, k), zero))

    def json_diag(self, x, at, zero):
        sev = x.get("severity", x.get("type"))
        if isinstance(sev, (int, float)):     # VerseWorkflowServer: 1 error, 2 warning
            sev = "error" if int(sev) == 1 else "warning" if int(sev) == 2 else "info"
        sev = str(sev or "error").lower()
        sev = "error" if "err" in sev else "warning" if "warn" in sev else sev
        span = x.get("span") or x.get("range") or {}
        if isinstance(span, dict) and isinstance(span.get("start"), dict):
            span = dict(span["start"], **{k: v for k, v in span.items() if k != "start"})
        line = first_key(span, JSON_LINE_KEYS) if isinstance(span, dict) else None
        line = line if line is not None else first_key(x, JSON_LINE_KEYS)
        col = first_key(span, JSON_COL_KEYS) if isinstance(span, dict) else None
        col = col if col is not None else first_key(x, JSON_COL_KEYS)
        add = 1 if zero else 0
        return {"at": at, "category": "json", "severity": sev,
                "code": str(x["code"]) if x.get("code") is not None else None,
                "path": first_key(x, JSON_PATH_KEYS),
                "line": int(line) + add if line is not None else None,
                "col": int(col) + add if col is not None else None,
                "message": x.get("message", ""), "raw": json.dumps(x, sort_keys=True)}

    def feed(self, text, fname):
        self.files.append(fname)
        for n, raw in enumerate(text.splitlines(), 1):
            line = raw.rstrip("\r\n")
            at = "%s:%d" % (fname, n)
            cat = UE_CATEGORY.match(line)
            category = cat.group(1) if cat else ""
            if DIAG_GUARD.search(line):
                m = self.diag_re.search(line) or DIAG_BARE.search(line)
                if m:
                    self.add_text_diag(m, line, at, category)
                    continue
            m = self.line_re.match(line)
            if m and m.groupdict().get("rest") is not None:
                self.add_marker(m, line, at, category)
                continue
            if self.rt_re.search(line):
                opens = self.open_runs()
                ev = {"at": at, "category": category, "raw": line,
                      "open_probes": [pid for pid, _ in opens]}
                for _, run in opens:
                    run["runtime_errors"].append(ev)
                self.runtime_errors.append(ev)
                continue
            b = BUILD_INFO.search(line)
            if b and len(self.build_info) < 50:
                self.build_info.append({"at": at, "key": b.group(1), "value": b.group(2).strip(),
                                        "raw": line})
            if BACKEND.search(line) and len(self.backend) < 50:
                self.backend.append({"at": at, "raw": line})
            if category.startswith("LogVerse") and re.search(r"\bError\b", line) \
                    and len(self.verse_errors) < 200:
                self.verse_errors.append({"at": at, "raw": line})

    def add_text_diag(self, m, line, at, category):
        g = m.groupdict()
        kind = (g.get("kind") or "").lower()
        self.add_diagnostic({
            "at": at, "category": category, "severity": "warning" if "warning" in kind else "error",
            "code": g.get("code"), "path": (g.get("path") or "").strip() or None,
            "line": int(g["line"]) if g.get("line") else None,
            "col": int(g["col"]) if g.get("col") else None,
            "message": (g.get("message") or "").strip(), "raw": line})

    def add_marker(self, m, line, at, category):
        g = m.groupdict()
        pre, rest = g.get("pre") or "", g.get("rest") or ""
        # Epic prints the lines of a rolled-back transaction all the same, each
        # prefixed with `(Rolling Back)` (the Book's API reference, `log`)
        rolled = bool(ROLLBACK.search(pre))
        if g.get("id") is not None:
            pid, text = g["id"], rest
        elif self.single:
            pid, text = self.single, rest
        else:
            parts = rest.split(None, 1)
            pid, text = (parts[0] if parts else ""), (parts[1] if len(parts) > 1 else "")
            if self.ids and pid not in self.ids:
                self.unattributed.append({"at": at, "raw": line})
                return
        item = {"text": text, "at": at, "category": category, "rolled_back": rolled, "raw": line}
        p = self.probe(pid)
        cur = p["runs"][-1] if p["runs"] and not p["runs"][-1]["ended"] else None
        if text == "begin" and not rolled:
            p["runs"].append(new_run(True, item))
        elif text == "end" and not rolled:
            if cur is None:
                cur = new_run(False, None)
                p["runs"].append(cur)
            cur["ended"] = True
            cur["end_at"], cur["end_raw"] = item["at"], item["raw"]
        else:
            if cur is None:
                cur = new_run(False, None)
                p["runs"].append(cur)
            cur["lines"].append(item)

    def result(self):
        for pid, p in self.probes.items():
            p["summary"] = summarize_epic(p)
        return {"tool": "ovprobe.py parse", "marker": self.marker, "files": self.files,
                "single": self.single,
                "manifest_ids": sorted(self.ids) if self.manifest else None,
                "build_info": self.build_info, "backend_evidence": self.backend,
                "probes": self.probes, "unattributed_lines": self.unattributed,
                "unattributed_diagnostics": self.diag_unattributed,
                "runtime_errors": self.runtime_errors, "verse_errors": self.verse_errors}


def new_run(begun, item):
    return {"begun": begun, "ended": False, "begin_at": item["at"] if item else None,
            "begin_raw": item["raw"] if item else None, "end_at": None, "end_raw": None,
            "lines": [], "runtime_errors": []}


def run_lines(run, keep_rolled_back=False):
    return [l["text"] for l in run["lines"] if keep_rolled_back or not l["rolled_back"]]


def summarize_epic(p, keep_rolled_back=False):
    """Epic's outcome for a probe from its parsed runs and diagnostics:
    {outcome, lines, notes}. outcome is refused (a compile error), ran (begin
    and end markers), runtime-error (begun, no end, a runtime error line while
    it ran), aborted (begun, no end, no runtime error line recognized: a
    runtime error ends the session's Verse, and so would a hang), admitted
    (compiled without errors, never run), inconsistent (complete runs that
    printed different lines), partial (lines without a begin marker), conflict
    (compile errors and runs) or missing."""
    errs = [d for d in p.get("diagnostics", []) if d["severity"] == "error"]
    runs = p.get("runs", [])
    notes = []
    if errs and runs:
        return {"outcome": "conflict", "lines": None,
                "notes": ["compile errors and run output for the same probe (different builds?)"]}
    if errs:
        return {"outcome": "refused", "lines": None, "notes": []}
    if not runs:
        if any(a.get("build_ok") is not False for a in p.get("admission", [])):
            return {"outcome": "admitted", "lines": None, "notes": ["compiled; no run in the logs"]}
        return {"outcome": "missing", "lines": None, "notes": []}
    complete = [r for r in runs if r["begun"] and r["ended"]]
    rolled = sum(1 for r in runs for l in r["lines"] if l["rolled_back"])
    if rolled:
        notes.append("%d (Rolling Back) line(s) %s" % (
            rolled, "kept" if keep_rolled_back else "left out of the comparison"))
    if len(runs) > 1:
        notes.append("%d runs, %d complete" % (len(runs), len(complete)))
    if complete:
        seqs = {tuple(run_lines(r, keep_rolled_back)) for r in complete}
        if len(seqs) > 1:
            return {"outcome": "inconsistent", "lines": None,
                    "notes": notes + ["complete runs printed different lines"]}
        return {"outcome": "ran", "lines": list(next(iter(seqs))), "notes": notes}
    with_err = [r for r in runs if r["runtime_errors"]]
    if with_err:
        r = with_err[0]
        if any(len(e["open_probes"]) > 1 for e in r["runtime_errors"]):
            notes.append("the runtime error was logged while other probes were running")
        return {"outcome": "runtime-error", "lines": run_lines(r, keep_rolled_back),
                "notes": notes}
    r = runs[-1]
    if not r["begun"]:
        return {"outcome": "partial", "lines": None,
                "notes": notes + ["lines without a begin marker (a log cut short?)"]}
    return {"outcome": "aborted", "lines": run_lines(r, keep_rolled_back),
            "notes": notes + ["begun with no end marker and no runtime error line recognized"]}


def cmd_parse(a):
    manifest = load_json(a.manifest) if a.manifest else None
    if manifest and a.marker == MARKER and manifest.get("marker"):
        a.marker = manifest["marker"]
    if not manifest and not a.single:
        print("ovprobe: no --manifest or --single: the word after the marker is taken as the probe id",
              file=sys.stderr)
    p = Parser(a.marker, manifest, a.single, a.line_regex, a.diag_regex, a.runtime_error_regex,
               a.header, not a.json_one_based)
    for f in a.logs:
        p.feed_file(f)
    res = p.result()
    if a.out:
        write_file(a.out, (json.dumps(res, indent=1) + "\n").encode("utf-8"))
    for pid in sorted(res["probes"]):
        s = res["probes"][pid]["summary"]
        print("  %-40s %-14s %s" % (pid, s["outcome"], " | ".join(s["lines"] or [])))
    print("ovprobe: %d probe(s), %d unattributed marker line(s), %d unattributed diagnostic(s), "
          "%d runtime error line(s), %d build info line(s)" % (
              len(res["probes"]), len(res["unattributed_lines"]),
              len(res["unattributed_diagnostics"]), len(res["runtime_errors"]),
              len(res["build_info"])))
    return 0


# ---------------------------------------------------------------------------
# Comparison
# ---------------------------------------------------------------------------

def strip_marker(line, marker):
    if line.startswith(marker + " "):
        return line[len(marker) + 1:]
    return line[len(marker):] if line == marker else line


def ov_view(lean, c, marker):
    """OpenVerse's outcome in one mode: {outcome, lines, evidence, lean_c}."""
    out = [strip_marker(l, marker) for l in lean["stdout"].split("\n") if l != ""]
    _, err = split_warnings(lean["stderr"], lean["path"])
    first = next((l for l in err.split("\n") if l.strip()), "")
    lean_c = "n/a"
    if c and c.get("outcome") != "not-run":
        lean_c = "agree" if (c["exit"], c["stdout"]) == (lean["exit"], lean["stdout"]) else "DISAGREE"
    return {"outcome": lean["outcome"],
            "lines": out if lean["outcome"] in OUTCOMES_RUN else None,
            "evidence": "exit %s%s" % (lean["exit"], ("; " + first) if first else ""),
            "lean_c": lean_c}


def load_expectations(paths):
    exp = {}
    for path in paths:
        with open(path, encoding="utf-8") as fh:
            rows = [l.rstrip("\r\n") for l in fh if l.strip() and not l.startswith("#")]
        if not rows:
            continue
        cols = rows[0].split("\t")
        for r in rows[1:]:
            d = dict(zip(cols, r.split("\t")))
            if d.get("probe"):
                exp[d["probe"]] = d
    return exp


def split_lines(s):
    return [x for x in (s or "").split("|") if x != ""] if s not in (None, "", "-") else []


# Epic outcomes that settle nothing; an aborted run counts as a runtime error
EPIC_UNSETTLED = ("missing", "partial", "inconsistent", "conflict", "admitted")


def outcome_class(o):
    return "runtime-error" if o == "aborted" else o


def same_outcome(x, y):
    """Whether two outcomes ({outcome, lines}) are the same observable result."""
    if x["outcome"] == "refused" or y["outcome"] == "refused":
        return x["outcome"] == y["outcome"]
    return outcome_class(x["outcome"]) == outcome_class(y["outcome"]) and \
        (x["lines"] or []) == (y["lines"] or [])


def book_view(e):
    if not e or not e.get("book_outcome") or e["book_outcome"] in ("-", "unspecified"):
        return None
    o = e["book_outcome"]
    return {"outcome": o, "lines": None if o == "refused" else split_lines(e.get("book_lines"))}


def verdict(epic, ov, control_epic):
    """(verdict, reason) of Epic's outcome against OpenVerse's."""
    eo = epic["outcome"]
    if eo in EPIC_UNSETTLED:
        return "inconclusive", "Epic: %s" % eo
    if control_epic is not None and control_epic["outcome"] != "ran":
        return "inconclusive", "paired control did not run on Epic (%s)" % control_epic["outcome"]
    oo = ov["outcome"]
    if oo not in OUTCOMES_RUN + ("refused",):
        return "inconclusive", "OpenVerse: %s" % oo
    if eo == "refused" and oo == "refused":
        return "agree", "both refuse"
    if eo == "refused":
        return "epic-refuses", "Epic refuses; OpenVerse %s" % oo
    if oo == "refused":
        return "openverse-refuses", "OpenVerse refuses; Epic %s" % eo
    if eo == "aborted" and oo != "runtime-error":
        return "inconclusive", ("Epic aborted (no end marker, no runtime error line recognized) "
                                "where OpenVerse %s: a runtime error, a hang or a log cut short" % oo)
    if same_outcome(epic, ov):
        if eo == "aborted":
            return "agree", "same lines; Epic aborted (no end marker), OpenVerse runtime error"
        return "agree", "same outcome (%s) and lines" % eo
    if outcome_class(eo) != oo:
        return "differ", "Epic %s, OpenVerse %s" % (eo, oo)
    return "differ", "different lines"


def against_book(x, book):
    if book is None or x is None or x["outcome"] in EPIC_UNSETTLED:
        return "n/a"
    if outcome_class(x["outcome"]) not in OUTCOMES_RUN + ("refused",):
        return "n/a"
    return "agree" if same_outcome(x, book) else "differ"


def show(x):
    if x is None:
        return "-"
    if x.get("lines") is None:
        return x["outcome"]
    return "%s: %s" % (x["outcome"], " | ".join(x["lines"]) if x["lines"] else "(no lines)")


def epic_evidence(p, limit=6):
    ev = []
    for d in p.get("diagnostics", [])[:limit]:
        loc = " (body line %d)" % d["body_line"] if d.get("body_line") else ""
        ev.append("%s%s: %s" % (d["severity"], loc, d["raw"].strip()))
    for r in p.get("runs", [])[:3]:
        if r.get("begin_raw"):
            ev.append(r["begin_raw"].strip())
        for l in r["lines"][:limit]:
            ev.append(l["raw"].strip())
        for e in r["runtime_errors"][:2]:
            ev.append(e["raw"].strip())
        ev.append(r["end_raw"].strip() if r.get("end_raw") else "(no end marker)")
    return ev


def merge_parsed(docs):
    """Several parse results as one: each probe's runs, diagnostics and
    admission records in the order given, and the global lists joined."""
    out = {"tool": "ovprobe.py compare (merged)", "marker": docs[0].get("marker", MARKER),
           "files": [], "probes": {}}
    for k in ("build_info", "backend_evidence", "unattributed_lines", "unattributed_diagnostics",
              "runtime_errors", "verse_errors"):
        out[k] = [x for d in docs for x in d.get(k, [])]
    for d in docs:
        out["files"] += d.get("files", [])
        for pid, p in d.get("probes", {}).items():
            q = out["probes"].setdefault(pid, {"runs": [], "diagnostics": [], "admission": []})
            for k in ("runs", "diagnostics", "admission"):
                q[k] += p.get(k, [])
    return out


def cmd_compare(a):
    ov = load_json(a.openverse)
    docs = load_jsons(a.epic)
    if not docs:
        raise SystemExit("ovprobe: no parse results in %s" % ", ".join(a.epic))
    epic = merge_parsed(docs)
    marker = epic.get("marker") or MARKER
    recs = {}
    for r in ov["records"]:
        recs.setdefault(r["probe"], {}).setdefault(r["mode"], {})[r["runtime"]] = r
    exp_paths = list(a.expectations or [])
    if not exp_paths:
        dirs = sorted({os.path.dirname(os.path.join(ROOT, r["path"])) for r in ov["records"]})
        exp_paths = [os.path.join(d, "expectations.tsv") for d in dirs
                     if os.path.isfile(os.path.join(d, "expectations.tsv"))]
    exp = load_expectations(exp_paths)
    ids = list(recs)
    modes = [m for m in MODES if any(m in recs[p] for p in ids)]
    eprobes = epic.get("probes", {})
    summaries = {pid: summarize_epic(eprobes.get(pid, {}), a.keep_rolled_back) for pid in ids}
    rows = []
    for pid in ids:
        e = summaries[pid]
        ctl = control_of(pid, set(ids))
        book = book_view(exp.get(pid))
        for mode in modes:
            if mode not in recs[pid]:
                continue
            v = ov_view(recs[pid][mode]["lean"], recs[pid][mode].get("c"), marker)
            verd, why = verdict(e, v, summaries[ctl] if ctl else None)
            notes = list(e.get("notes", []))
            if v["lean_c"] == "DISAGREE":
                notes.append("OpenVerse Lean and C disagree")
            rows.append({
                "probe": pid, "openverse_mode": mode, "verdict": verd, "reason": why,
                "epic": show(e), "openverse": show(v), "openverse_evidence": v["evidence"],
                "lean_c": v["lean_c"], "control": ctl or "",
                "book_case": (exp.get(pid) or {}).get("book_case", ""),
                "book": show(book) if book else "", "epic_vs_book": against_book(e, book),
                "openverse_vs_book": against_book(v, book), "notes": "; ".join(notes),
                "epic_evidence": " || ".join(epic_evidence(eprobes.get(pid, {})))})
    cols = ["probe", "openverse_mode", "verdict", "reason", "epic", "openverse", "book",
            "epic_vs_book", "openverse_vs_book", "book_case", "control", "lean_c", "notes",
            "openverse_evidence", "epic_evidence"]
    if a.tsv:
        lines = ["\t".join(cols)] + ["\t".join(tsv_cell(r[k]) for k in cols) for r in rows]
        write_file(a.tsv, ("\n".join(lines) + "\n").encode("utf-8"))
    md = markdown_report(rows, modes, ov, epic, exp_paths, summaries)
    if a.md:
        write_file(a.md, md.encode("utf-8"))
    counts = {}
    for r in rows:
        counts.setdefault(r["openverse_mode"], {}).setdefault(r["verdict"], 0)
        counts[r["openverse_mode"]][r["verdict"]] += 1
    for mode in modes:
        print("%-19s %s" % (mode, ", ".join("%s %d" % (k, counts.get(mode, {}).get(k, 0))
                                             for k in VERDICTS)))
    return 0


def md_cell(s):
    return (s or "").replace("|", "\\|").replace("\n", " ")


def markdown_report(rows, modes, ov, epic, exp_paths, summaries):
    out = ["# OpenVerse and Epic's Verse VM: live probe comparison", ""]
    out.append("- OpenVerse: HEAD `%s`, compiler sources at `%s`%s." % (
        ov.get("head"), ov.get("compiler_revision"),
        " (modified)" if ov.get("compiler_sources_modified") else ""))
    out.append("- Epic logs: %s." % (", ".join("`%s`" % f for f in epic.get("files", [])) or "none"))
    builds = epic.get("build_info", [])
    if builds:
        seen = []
        for b in builds:
            s = "%s: %s" % (b["key"], b["value"])
            if s not in seen:
                seen.append(s)
        out.append("- Epic build lines: %s." % "; ".join("`%s`" % md_cell(s) for s in seen[:8]))
    else:
        out.append("- Epic build lines: none found in the logs; record the editor and session builds by hand.")
    back = epic.get("backend_evidence", [])
    out.append("- Backend evidence lines: %d%s." % (
        len(back), (" (first: `%s`)" % md_cell(back[0]["raw"].strip())) if back else
        "; the Verse VM backend is not confirmed by the logs"))
    if exp_paths:
        out.append("- Book expectations: %s." % ", ".join("`%s`" % rel(p) for p in exp_paths))
    out.append("")
    out.append("| Mode | " + " | ".join(VERDICTS) + " |")
    out.append("| --- |" + " ---: |" * len(VERDICTS))
    for mode in modes:
        rs = [r for r in rows if r["openverse_mode"] == mode]
        out.append("| %s | %s |" % (mode, " | ".join(
            str(sum(1 for r in rs if r["verdict"] == v)) for v in VERDICTS)))
    out.append("")
    out.append("| Probe | %s | Epic | %s | Book | Epic vs Book |" % (
        " | ".join("Verdict (%s)" % m for m in modes),
        " | ".join("OpenVerse (%s)" % m for m in modes)))
    out.append("| --- |" + " --- |" * (2 * len(modes) + 3))
    by = {}
    for r in rows:
        by.setdefault(r["probe"], {})[r["openverse_mode"]] = r
    for pid, rs in by.items():
        any_r = next(iter(rs.values()))
        out.append("| `%s` | %s | %s | %s | %s | %s |" % (
            pid,
            " | ".join(md_cell(rs[m]["verdict"]) if m in rs else "-" for m in modes),
            md_cell(any_r["epic"]),
            " | ".join(md_cell(rs[m]["openverse"]) if m in rs else "-" for m in modes),
            md_cell(any_r["book"] or "-"), md_cell(any_r["epic_vs_book"])))
    out.append("")
    glob = [("Diagnostics not attributed to a probe", epic.get("unattributed_diagnostics", [])),
            ("Runtime error lines", epic.get("runtime_errors", [])),
            ("Marker lines not attributed to a probe", epic.get("unattributed_lines", [])),
            ("Other LogVerse error lines", epic.get("verse_errors", []))]
    for title, items in glob:
        if items:
            out.append("%s (%d):" % (title, len(items)))
            out.append("")
            out.append("```text")
            out.extend("%s  %s" % (x["at"], x["raw"].strip()) for x in items[:20])
            out.append("```")
            out.append("")
    out.append("## Evidence")
    out.append("")
    for pid, rs in by.items():
        any_r = next(iter(rs.values()))
        out.append("### `%s`" % pid)
        out.append("")
        if any_r["book_case"]:
            out.append("Book case: %s." % md_cell(any_r["book_case"]))
        if any_r["control"]:
            out.append("Paired control: `%s` (Epic: %s)." % (
                any_r["control"], summaries[any_r["control"]]["outcome"]))
        for m in modes:
            if m in rs:
                r = rs[m]
                out.append("- %s: **%s** (%s); OpenVerse %s, Lean/C %s." % (
                    m, r["verdict"], md_cell(r["reason"]), md_cell(r["openverse_evidence"]),
                    r["lean_c"]))
        if any_r["notes"]:
            out.append("- Notes: %s." % md_cell(any_r["notes"]))
        ev = any_r["epic_evidence"]
        out.append("")
        out.append("```text")
        out.extend(ev.split(" || ") if ev else ["(no Epic log lines for this probe)"])
        out.append("```")
        out.append("")
    return "\n".join(out)


# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter,
                                 epilog=__doc__.split("\n\n", 1)[1])
    sub = ap.add_subparsers(dest="cmd")
    g = sub.add_parser("generate", help="UEFN device sources from probe bodies")
    g.add_argument("probes", nargs="+")
    g.add_argument("--mode", choices=("single", "batch"), default="single")
    g.add_argument("--layout", choices=("driver", "devices"), default="driver",
                   help="batch: one driver device calling every probe (default), or a device per probe")
    g.add_argument("--host", choices=("uefn", "openverse"), default="uefn",
                   help="driver layout: for UEFN (default) or for OpenVerse, to check the batch")
    g.add_argument("--out", default="ovprobe-out")
    g.add_argument("--header", default=HEADER)
    g.add_argument("--marker", default=MARKER)
    g.add_argument("--exclude", action="append", metavar="ID")
    g.add_argument("--exclude-refused", action="append", metavar="PARSED",
                   help="leave out the probes with compile errors in a parse result "
                   "(a file, or a directory of them)")
    g.add_argument("--exclude-done", action="append", metavar="PARSED",
                   help="leave out the probes a parse result has refused or begun (ran or aborted)")
    g.add_argument("--risky-last", metavar="OV.json",
                   help="put the probes OpenVerse ends with a runtime error, limit or timeout last")
    o = sub.add_parser("openverse", help="run the probes with OpenVerse (Lean and C)")
    o.add_argument("probes", nargs="+")
    o.add_argument("--openverse", default=os.path.join(ROOT, ".lake", "build", "bin", "openverse"))
    o.add_argument("--cverse", default=os.path.join(ROOT, "runtime", "build", "cverse"))
    o.add_argument("--modes", default=",".join(DEFAULT_MODES))
    o.add_argument("--timeout", type=int, default=120)
    o.add_argument("--json")
    o.add_argument("--tsv")
    p = sub.add_parser("parse", help="extract probe lines and diagnostics from UEFN logs")
    p.add_argument("logs", nargs="+")
    p.add_argument("--manifest")
    p.add_argument("--single", metavar="ID", help="every marker line and openverse_probe.verse "
                   "diagnostic belongs to this probe (the runbook's one-probe builds)")
    p.add_argument("--marker", default=MARKER)
    p.add_argument("--header", default=HEADER, help="the header of --single builds (for body line numbers)")
    p.add_argument("--line-regex", help="a marker line regex with groups rest (and optionally pre, id)")
    p.add_argument("--diag-regex", help="a compiler diagnostic regex with groups path, line, col, "
                   "kind, code, message")
    p.add_argument("--runtime-error-regex")
    p.add_argument("--json-one-based", action="store_true",
                   help="lines and columns in JSON diagnostics count from 1 (BuildAll's count from 0)")
    p.add_argument("--out")
    c = sub.add_parser("compare", help="verdicts and the report")
    c.add_argument("--openverse", required=True)
    c.add_argument("--epic", required=True, action="append",
                   help="a parse result, or a directory of them; several are merged "
                   "(one per single-probe build, say)")
    c.add_argument("--expectations", action="append")
    c.add_argument("--keep-rolled-back", action="store_true",
                   help="compare Epic's (Rolling Back) lines too (OpenVerse rolls back output)")
    c.add_argument("--tsv")
    c.add_argument("--md")
    a = ap.parse_args(argv)
    if a.cmd == "generate":
        return cmd_generate(a)
    if a.cmd == "openverse":
        return cmd_openverse(a)
    if a.cmd == "parse":
        if a.manifest and a.single:
            ap.error("--manifest and --single cannot be combined")
        return cmd_parse(a)
    if a.cmd == "compare":
        return cmd_compare(a)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    sys.exit(main())
