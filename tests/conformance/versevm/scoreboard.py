#!/usr/bin/env python3
"""Where OpenVerse stands against Epic's recorded results (#724).

Every probe under tests/conformance/versevm that Epic's compiler or Verse VM
has answered (UEFN 43.12) is compared with what this checkout does now, and
each difference must be listed, with its reason, in known-differences.tsv.

  scoreboard.py (--run | --openverse OV.json) [--md FILE] [--tsv FILE] [--check]

--run runs every probe with this checkout's build (Lean and C, default mode);
--openverse takes the JSON of an earlier `ovprobe.py openverse <every probe
directory> --json OV.json`. --md rewrites the parts of FILE between the
`<!-- scoreboard:begin -->` and `<!-- scoreboard:end -->` lines, and between the
`scoreboard-summary` ones (with --check
it only compares, and fails if FILE is out of date). Epic's answer for a probe is taken, in this order,
from its directory's expectations.tsv (epic_outcome, epic_lines), from
results/epic-43.12-runs.tsv (Verse VM sessions) and from
results/epic-43.12-compile.tsv (compiler verdicts); a probe compiled or run
more than once counts with its last record.

Verdicts:
  agree         both refuse; or both run and print the same lines; or both
                stop with a runtime error after the same lines
  agree-admit   Epic's compiler admitted the probe and no Verse VM run is
                recorded; OpenVerse admits it too (what it prints is unchecked)
  differ        anything else, with a kind: openverse-refuses, epic-refuses,
                lines, outcome
  unanswered    no Epic record

A line Epic's log labels "(Rolling Back)" is a Print inside a failed context:
the Verse VM logs it with that label and OpenVerse drops it (LANGUAGE.md), so
such lines are left out of Epic's side before the comparison.

--check exits 1 if a difference is not in known-differences.tsv, if a listed
probe no longer differs, or if Lean and C disagree on any probe.

Python 3 standard library only.
"""
import argparse
import collections
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROLLING = "(Rolling Back) "
SUMMARY = collections.OrderedDict([
    ("bug", "openverse bugs: it runs the program and prints something else than the Verse VM"),
    ("gap", "gaps: Verse that Epic admits and runs, and openverse refuses because the form is not "
            "implemented. openverse says so at compile time; it does not run these programs wrongly"),
    ("epic-defect", "where Epic stops with an internal error or stalls, and openverse computes the result"),
    ("book-ahead", "where openverse has a form of the Book of Verse that 43.12 does not ship yet"),
    ("restricted-name", "library names Epic keeps internal or restricted, which openverse lets a program use"),
    ("kept", "kept on purpose, where Epic's behaviour is unspecified or not worth imitating"),
    ("harness", "caused by the probe's form, not the language"),
])


def set_block(text, name, body, path):
    """text with the lines between `<!-- name:begin -->` and `<!-- name:end -->` replaced by body."""
    begin, end = "<!-- %s:begin -->\n" % name, "<!-- %s:end -->" % name
    try:
        head, rest = text.split(begin, 1)
        _, tail = rest.split(end, 1)
    except ValueError:
        raise SystemExit("scoreboard: %s has no %s ... %s part" % (path, begin.strip(), end))
    return head + begin + body + end + tail
CATEGORIES = collections.OrderedDict([
    ("bug", "OpenVerse does something else than the Verse VM, and is to be fixed"),
    ("gap", "Verse that UEFN 43.12 admits and runs, and OpenVerse refuses: not implemented yet"),
    ("book-ahead", "OpenVerse has a form of the Book of Verse that UEFN 43.12 does not have yet"),
    ("restricted-name", "A library name UEFN 43.12 keeps internal or restricted; OpenVerse lets a program use it"),
    ("kept", "OpenVerse's behaviour is kept on purpose, where Epic's is unspecified or not worth imitating"),
    ("epic-defect", "Epic stops or stalls where the language defines a result; OpenVerse computes it"),
    ("harness", "The probe's form, not the language: it uses a name only the UEFN device wrapper has"),
])


def read_tsv(path):
    with open(path, encoding="utf-8") as fh:
        rows = [l.rstrip("\r\n") for l in fh if l.strip() and not l.startswith("#")]
    if not rows:
        return []
    cols = rows[0].split("\t")
    return [dict(zip(cols, r.split("\t"))) for r in rows[1:]]


def split_lines(s):
    """A cell's lines, `|`-separated; `\\t` in a cell is a tab (a raw one would split the row)."""
    if s in (None, "", "-"):
        return []
    return [x.replace("\\t", "\t") for x in s.split("|") if x != ""]


def probe_dirs():
    out = [HERE]
    for name in sorted(os.listdir(HERE)):
        d = os.path.join(HERE, name)
        if os.path.isdir(d) and name != "results" and any(f.endswith(".verse") for f in os.listdir(d)):
            out.append(d)
    return out


def probes():
    """{probe id: directory name ('' for the original probes)}"""
    found = collections.OrderedDict()
    for d in probe_dirs():
        for f in sorted(os.listdir(d)):
            if f.endswith(".verse"):
                pid = f[:-len(".verse")]
                if pid in found:
                    raise SystemExit("scoreboard: probe %s is in two directories" % pid)
                found[pid] = os.path.relpath(d, HERE) if d != HERE else "original"
    return found


def epic_records():
    """{probe: {outcome, lines, source, detail}}; outcome: refused, admitted, ran,
    runtime-error, stalled, cook-error."""
    epic = {}
    for r in read_tsv(os.path.join(HERE, "results", "epic-43.12-compile.tsv")):
        if r["verdict"] == "refused":
            epic[r["probe"]] = {"outcome": "refused", "lines": None, "source": "compile",
                                "detail": "error " + r.get("error_codes", "")}
        else:
            epic[r["probe"]] = {"outcome": "admitted", "lines": None, "source": "compile", "detail": ""}
    for r in read_tsv(os.path.join(HERE, "results", "epic-43.12-runs.tsv")):
        if r["vm"] != "verse-vm":
            continue
        if epic.get(r["probe"], {}).get("outcome") == "refused":
            continue  # a later rewrite's verdict stands; compile rows are in order
        o = {"completed": "ran", "runtime-error": "runtime-error", "no-end-marker": "stalled",
             "no-output": "stalled", "server-cook-error": "cook-error"}[r["outcome"]]
        detail = r.get("error", "")
        epic[r["probe"]] = {"outcome": o, "lines": split_lines(r.get("lines")), "source": "run",
                            "detail": "" if detail == "-" else detail}
    for d in probe_dirs():
        path = os.path.join(d, "expectations.tsv")
        if not os.path.isfile(path):
            continue
        for r in read_tsv(path):
            o = r.get("epic_outcome", "")
            if o in ("", "-"):
                continue
            lines = r.get("labelled_lines") if "labelled_lines" in r else r.get("epic_lines")
            o = {"no-output": "stalled", "no-end": "stalled"}.get(o, o)
            epic[r["probe"]] = {"outcome": o, "lines": None if o in ("refused", "admitted") else split_lines(lines),
                                "source": "expectations", "detail": ""}
    return epic


def openverse_records(path):
    with open(path, encoding="utf-8") as fh:
        doc = json.load(fh)
    by = {}
    for r in doc["records"]:
        if r["mode"] != "default":
            continue
        by.setdefault(r["probe"], {})[r["runtime"]] = r
    out = {}
    for pid, rs in by.items():
        lean, c = rs["lean"], rs.get("c")
        lines = [l[len("OVPROBE "):] if l.startswith("OVPROBE ") else l
                 for l in lean["stdout"].split("\n") if l != ""]
        err = next((l for l in lean["stderr"].split("\n") if l.strip() and ": warning: " not in l), "")
        lean_c = True
        if c and c.get("outcome") != "not-run":
            lean_c = (c["exit"], c["stdout"]) == (lean["exit"], lean["stdout"])
        out[pid] = {"outcome": lean["outcome"], "lines": lines, "exit": lean["exit"], "error": err,
                    "lean_c": lean_c}
    return doc, out


def verdict(e, o):
    """(verdict, kind) of Epic's record against OpenVerse's."""
    if e is None:
        return "unanswered", ""
    eo, oo = e["outcome"], o["outcome"]
    if eo in ("refused", "cook-error"):
        # (a cook error is the Verse VM's link step refusing the module: no line is printed)
        return ("agree", "") if oo == "refused" else ("differ", "epic-refuses")
    if oo == "refused":
        return "differ", "openverse-refuses"
    if eo == "admitted":
        return "agree-admit", ""
    kept = [l for l in e["lines"] if not l.startswith(ROLLING)]
    if eo == "stalled":
        return "differ", "outcome"
    if eo == "runtime-error":
        if oo != "runtime-error":
            return "differ", "outcome"
        return ("agree", "") if kept == o["lines"] else ("differ", "lines")
    if oo != "ran":
        return "differ", "outcome"
    return ("agree", "") if kept == o["lines"] else ("differ", "lines")


def show(rec):
    if rec is None:
        return "-"
    if rec["outcome"] in ("refused", "admitted", "cook-error"):
        d = rec.get("detail") or rec.get("error") or ""
        return rec["outcome"] + ((": " + d) if d else "")
    lines = " \\| ".join(rec["lines"] or []) or "(no lines)"
    return "%s: %s" % (rec["outcome"], lines)


def cell(s, limit=220):
    s = s.replace("\n", " ")
    return s if len(s) <= limit else s[:limit - 1] + "…"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--openverse", help="JSON of `ovprobe.py openverse`")
    ap.add_argument("--run", action="store_true", help="run the probes with this checkout's build")
    ap.add_argument("--md", help="rewrite the generated part of this Markdown file")
    ap.add_argument("--tsv", help="write one row per probe")
    ap.add_argument("--check", action="store_true", help="fail on an unlisted or a stale difference")
    a = ap.parse_args(argv)

    if a.run == bool(a.openverse):
        ap.error("give one of --run and --openverse")
    where = probes()
    epic = epic_records()
    if a.run:
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "ov.json")
            cmd = [sys.executable, "-I", os.path.join(HERE, "ovprobe.py"), "openverse"] + probe_dirs() + \
                ["--modes", "default", "--json", path]
            done = subprocess.run(cmd, cwd=os.path.dirname(os.path.dirname(os.path.dirname(HERE))),
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if done.returncode != 0:
                sys.stdout.write(done.stdout)
                return done.returncode
            doc, ov = openverse_records(path)
    else:
        doc, ov = openverse_records(a.openverse)
    known = {r["probe"]: r for r in read_tsv(os.path.join(HERE, "known-differences.tsv"))}
    problems = []
    rows = []
    for pid, d in where.items():
        if pid not in ov:
            problems.append("%s: no OpenVerse record (run ovprobe.py openverse on every directory)" % pid)
            continue
        v, kind = verdict(epic.get(pid), ov[pid])
        rows.append({"probe": pid, "set": d, "verdict": v, "kind": kind, "epic": epic.get(pid), "ov": ov[pid]})
        if not ov[pid]["lean_c"]:
            problems.append("%s: Lean and C disagree" % pid)
        if v == "differ" and pid not in known:
            problems.append("%s: differs from Epic (%s) and is not in known-differences.tsv" % (pid, kind))
        if v != "differ" and pid in known:
            problems.append("%s: listed in known-differences.tsv but is now %s" % (pid, v))
    for pid, k in known.items():
        if pid not in where:
            problems.append("%s: in known-differences.tsv but no such probe" % pid)
        elif k.get("category") not in CATEGORIES:
            problems.append("%s: unknown category %r" % (pid, k.get("category")))

    count = collections.Counter(r["verdict"] for r in rows)
    answered = [r for r in rows if r["verdict"] != "unanswered"]
    by_set = collections.OrderedDict()
    for r in rows:
        by_set.setdefault(r["set"], collections.Counter())[r["verdict"]] += 1

    if a.tsv:
        with open(a.tsv, "w", encoding="utf-8") as fh:
            fh.write("probe\tset\tverdict\tkind\tcategory\tepic\topenverse\n")
            for r in rows:
                fh.write("\t".join([r["probe"], r["set"], r["verdict"], r["kind"],
                                    known.get(r["probe"], {}).get("category", ""),
                                    show(r["epic"]).replace("\\|", "|"),
                                    show(r["ov"]).replace("\\|", "|")]) + "\n")
    if a.md:
        out = []
        w = out.append
        w("| | Probes |")
        w("| --- | ---: |")
        w("| Probes Epic has answered | %d |" % len(answered))
        w("| Same result (refused by both, or the same lines, or the same lines then a runtime error) | %d |" % count["agree"])
        w("| Admitted by both, not run on Epic | %d |" % count["agree-admit"])
        w("| Different | %d |" % count["differ"])
        w("| Not asked of Epic | %d |" % count["unanswered"])
        w("")
        cats = collections.Counter(known[r["probe"]]["category"] for r in rows
                                   if r["verdict"] == "differ" and r["probe"] in known)
        w("The %d differences by cause (each is listed below):" % count["differ"])
        w("")
        w("| Cause | Probes | Meaning |")
        w("| --- | ---: | --- |")
        for c, meaning in CATEGORIES.items():
            if cats[c]:
                w("| %s | %d | %s |" % (c, cats[c], meaning))
        w("")
        w("### By probe set")
        w("")
        w("A set is a directory of `tests/conformance/versevm` (`original`: the directory itself).")
        w("")
        w("| Set | Probes | Same | Admitted by both | Different | Not asked |")
        w("| --- | ---: | ---: | ---: | ---: | ---: |")
        for s, c in by_set.items():
            w("| `%s` | %d | %d | %d | %d | %d |" % (s, sum(c.values()), c["agree"], c["agree-admit"],
                                                 c["differ"], c["unanswered"]))
        w("")
        w("### Every difference")
        w("")
        w("Lines are separated by `|`. Epic's column is the Verse VM's output, or its compiler's verdict.")
        w("")
        for c, meaning in CATEGORIES.items():
            sel = [r for r in rows if r["verdict"] == "differ" and known.get(r["probe"], {}).get("category") == c]
            if not sel:
                continue
            w("#### `%s` (%d)" % (c, len(sel)))
            w("")
            w(meaning + ".")
            w("")
            w("| Probe | Epic's Verse VM | OpenVerse | Why |")
            w("| --- | --- | --- | --- |")
            for r in sel:
                w("| `%s` | %s | %s | %s |" % (r["probe"], cell(show(r["epic"])), cell(show(r["ov"])),
                                              known[r["probe"]].get("reason", "")))
            w("")
        unl = [r for r in rows if r["verdict"] == "differ" and r["probe"] not in known]
        if unl:
            w("**Unlisted** (%d)." % len(unl))
            w("")
            for r in unl:
                w("- `%s` (%s): Epic %s; OpenVerse %s" % (r["probe"], r["kind"], show(r["epic"]), show(r["ov"])))
            w("")
        summary = ["Epic's shipped compiler and Verse VM (UEFN 43.12) have answered %d probe programs. openverse"
                   % len(answered),
                   "gives the same answer on %d of them and a different one on %d:"
                   % (count["agree"] + count["agree-admit"], count["differ"]),
                   ""]
        summary += ["- **%d** %s." % (cats[c], SUMMARY[c]) for c in SUMMARY if cats[c]]
        summary.append("")
        with open(a.md, encoding="utf-8") as fh:
            text = fh.read()
        new = set_block(text, "scoreboard-summary", "\n".join(summary), a.md)
        new = set_block(new, "scoreboard", "\n".join(out), a.md)
        if new != text:
            if a.check:
                problems.append("%s is out of date: run scoreboard.py --run --md %s" % (a.md, a.md))
            else:
                with open(a.md, "w", encoding="utf-8") as fh:
                    fh.write(new)

    print("scoreboard: %d probes, %d answered by Epic: %d same, %d admitted by both, %d different, %d not asked" % (
        len(rows), len(answered), count["agree"], count["agree-admit"], count["differ"], count["unanswered"]))
    for p in problems:
        print("scoreboard: " + p)
    return 1 if (a.check and problems) else 0


if __name__ == "__main__":
    sys.exit(main())
