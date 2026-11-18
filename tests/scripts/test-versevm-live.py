#!/usr/bin/env python3
"""The live VerseVM conformance tools (tests/conformance/versevm/ovprobe.py and
uefn_mcp.py): generation, log parsing and comparison on synthetic UEFN logs, a
mock of UEFN's MCP server, and an end-to-end batch run on OpenVerse itself."""
import contextlib
import http.server
import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
VM = ROOT / "tests" / "conformance" / "versevm"


def load(name):
    spec = importlib.util.spec_from_file_location(name, VM / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ov = load("ovprobe")
mcp = load("uefn_mcp")
HEADER = (VM / "device.verse.header").read_bytes()

PROBES = {
    "alpha": 'Main():void =\n    Print("OVPROBE one")\n    Print("OVPROBE two")\n',
    "beta": 'Helper()<computes>:int = 1\n\nMain():void =\n    Print("OVPROBE value {Helper()}")\n',
    "beta-control": 'Main():void =\n    Print("OVPROBE control")\n',
    "gamma": 'Main():void =\n    Print("OVPROBE before")\n    X := 1\n',
    "delta": 'Main():void =\n    Print("OVPROBE never")\n',
    "epsilon": 'Main():void =\n    Foo()\n    Print("OVPROBE after foo")\n',
    "zeta": 'Main():void =\n    Print("OVPROBE zeta ran")\n',
    "eta": 'Main():void =\n    Print("OVPROBE eta ran")\n',
    "theta": 'Main():void =\n    Print("OVPROBE theta ran")\n',
    "theta-control": 'Main():void =\n    Print("OVPROBE theta control")\n',
}


def quiet(fn, *args):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return fn(*args)


class Tmp(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="ovprobe-test-"))
        self.probes = self.tmp / "probes"
        self.probes.mkdir()
        for pid, body in PROBES.items():
            (self.probes / (pid + ".verse")).write_bytes(body.encode())

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def generate(self, *args):
        out = self.tmp / ("gen-%d" % len(list(self.tmp.iterdir())))
        quiet(ov.main, ["generate", "--out", str(out)] + list(args))
        return out, json.loads((out / "manifest.json").read_text())


class Generate(Tmp):
    def test_single_is_the_runbook_concatenation(self):
        dirs = [VM, VM / "book", VM / "fingerprint"]
        out = self.tmp / "single"
        quiet(ov.main, ["generate", "--mode", "single", "--out", str(out)] + [str(d) for d in dirs])
        n = 0
        for d in dirs:
            for f in sorted(d.glob("*.verse")):
                got = (out / f.stem / "openverse_probe.verse").read_bytes()
                self.assertEqual(got, HEADER + b"\n" + f.read_bytes(), f.name)
                n += 1
        self.assertGreaterEqual(n, 15 + 30)
        m = json.loads((out / "manifest.json").read_text())
        self.assertEqual({e["body_first_line"] for e in m["probes"]}, {HEADER.count(b"\n") + 2})

    def test_driver_layout(self):
        out, m = self.generate("--mode", "batch", str(self.probes))
        self.assertEqual(m["layout"], "driver")
        src = (out / "ovprobes" / "openverse_probe_driver.verse").read_text()
        lines = src.split("\n")
        for u in HEADER.decode().split("\n"):
            if u.startswith("using"):
                self.assertIn(u, lines)
        self.assertIn("openverse_probe_driver := class(creative_device):", lines)
        calls = [l.strip() for l in lines if l.strip().endswith(".RunOVProbe()")]
        self.assertEqual(calls, ["%s.RunOVProbe()" % ov.ident(e["id"]) for e in m["probes"]])
        for e in m["probes"]:
            self.assertIn("%s := module:" % e["module"], lines)
            body = PROBES[e["id"]].rstrip("\n").split("\n")
            span = lines[e["body_first_line"] - 1:e["body_last_line"]]
            self.assertEqual([l[4:] if l else l for l in span],
                             [b.replace('"OVPROBE ', '"OVPROBE %s ' % e["id"]) for b in body])
            self.assertIn('        Print("OVPROBE %s begin")' % e["id"], lines)
            self.assertIn('        Print("OVPROBE %s end")' % e["id"], lines)
        self.assertNotIn('"OVPROBE one"', src)
        self.assertEqual(m["probes"][0]["control"], None)
        self.assertEqual({e["id"]: e["control"] for e in m["probes"]}["beta"], "beta-control")

    def test_devices_layout(self):
        out, m = self.generate("--mode", "batch", "--layout", "devices", str(self.probes))
        e = next(x for x in m["probes"] if x["id"] == "alpha")
        src = (out / e["file"]).read_bytes()
        self.assertTrue(src.startswith(HEADER.replace(b"openverse_probe :=", b"ovp_alpha_device :=")
                                       .replace(b'"OVPROBE ', b'"OVPROBE alpha ') + b"\n"))
        self.assertTrue(src.endswith(PROBES["alpha"].replace('"OVPROBE ', '"OVPROBE alpha ').encode()))
        self.assertEqual(src.split(b"\n")[e["body_first_line"] - 1], b"Main():void =")

    def test_ordering_and_exclusion(self):
        ovj = self.tmp / "ov.json"
        ovj.write_text(json.dumps({"records": [
            {"probe": "alpha", "runtime": "lean", "outcome": "runtime-error"},
            {"probe": "beta", "runtime": "lean", "outcome": "ran"}]}))
        parsed = self.tmp / "parsed.json"
        parsed.write_text(json.dumps({"probes": {
            "gamma": {"runs": [{"begun": True, "ended": False}], "diagnostics": []},
            "delta": {"runs": [], "diagnostics": [{"severity": "error"}]},
            "zeta": {"runs": [], "diagnostics": [{"severity": "warning"}]}}}))
        _, m = self.generate("--mode", "batch", "--risky-last", str(ovj),
                             "--exclude-done", str(parsed), "--exclude", "eta", str(self.probes))
        ids = [e["id"] for e in m["probes"]]
        self.assertEqual(ids[-1], "alpha")
        for gone in ("gamma", "delta", "eta"):
            self.assertNotIn(gone, ids)
        self.assertIn("zeta", ids)

    def test_refusals(self):
        bad = self.tmp / "bad"
        bad.mkdir()
        (bad / "a-b.verse").write_text(PROBES["alpha"])
        (bad / "a_b.verse").write_text(PROBES["alpha"])
        with self.assertRaises(SystemExit):
            quiet(ov.main, ["generate", "--mode", "batch", "--out", str(self.tmp / "o1"), str(bad)])
        (bad / "a_b.verse").unlink()
        (bad / "late.verse").write_text('Main():void =\n    Print("late OVPROBE")\n')
        with self.assertRaises(SystemExit):
            quiet(ov.main, ["generate", "--mode", "batch", "--out", str(self.tmp / "o2"), str(bad)])
        (bad / "late.verse").write_text('Main():void =\n    Print("OVPROBE end")\n')
        with self.assertRaises(SystemExit):
            quiet(ov.main, ["generate", "--mode", "batch", "--out", str(self.tmp / "o3"), str(bad)])


def ue(text):
    """Synthetic Unreal log lines: timestamp and frame prefixes on each line."""
    return "".join("[2026.11.18-12.00.%02d:%03d][%3d]%s\n" % (k % 60, k, k, l)
                   for k, l in enumerate(text.strip("\n").split("\n")))


class Logs:
    def batch_log(self, m):
        eps = next(e for e in m["probes"] if e["id"] == "epsilon")
        path = "C:/Users/someone/Documents/Fortnite Projects/P/Plugins/P/Content/ovprobes/" \
               "openverse_probe_driver.verse"
        line = eps["body_first_line"] + 1
        build = ue("""LogInit: Build: ++Fortnite+Release-43.10-CL-60458657
LogInit: Engine Version: 5.7.0-60458657+++Fortnite+Release-43.10
VerseBuild: Error: %s(%d,5, %d,8): Script error 3506: Unknown identifier `Foo`.
VerseBuild: Error: %s(4,9, 4,30): Script error 3506: Unknown identifier in Print("OVPROBE alpha one")
LogVerse: Warning: something mentions OVPROBE"quoted"
""" % (path, line, line, path))
        session = ue("""LogVerse: : OVPROBE ovprobe-driver begin
LogVerse: : OVPROBE alpha begin
LogVerse: : OVPROBE alpha one
LogVerse: : OVPROBE alpha two
LogVerse: : OVPROBE alpha end
LogVerse: : OVPROBE beta-control begin
LogVerse: : OVPROBE beta-control control
LogVerse: : OVPROBE beta-control end
LogVerse: : OVPROBE beta begin
LogVerse: : (Rolling Back) OVPROBE beta rolled
LogVerse: : OVPROBE beta value 1
LogVerse: : OVPROBE beta end
LogVerse: : OVPROBE nobody stray
LogVerse: : OVPROBE gamma begin
LogVerse: : OVPROBE gamma before
LogVerse: Error: VerseRuntimeErrors: Verse unrecoverable error: integer overflow
LogVerse: : OVPROBE zeta begin
LogVerse: : OVPROBE zeta zeta ran
LogVerse: : OVPROBE zeta end
LogVerse: : OVPROBE eta begin
LogVerse: : OVPROBE eta eta ran
LogVerse: : OVPROBE theta begin
LogVerse: : OVPROBE theta theta ran
LogVerse: : OVPROBE theta end
LogVerse: : OVPROBE theta-control begin
LogVerse: : OVPROBE theta-control theta control
""")
        return build + session

    def parse(self, m, data, *extra):
        f = self.tmp / ("log-%d" % len(list(self.tmp.iterdir())))
        f.write_bytes(data)
        man = self.tmp / "m.json"
        man.write_text(json.dumps(m))
        out = self.tmp / "parsed.json"
        quiet(ov.main, ["parse", "--manifest", str(man), "--out", str(out), str(f)] + list(extra))
        return json.loads(out.read_text())


class Parse(Logs, Tmp):
    def test_batch_log(self):
        _, m = self.generate("--mode", "batch", str(self.probes))
        text = self.batch_log(m)
        res = self.parse(m, b"\xef\xbb\xbf" + text.encode())
        p = res["probes"]
        s = {k: v["summary"] for k, v in p.items()}
        self.assertEqual(s["alpha"], {"outcome": "ran", "lines": ["one", "two"], "notes": []})
        self.assertEqual(s["beta"]["outcome"], "ran")
        self.assertEqual(s["beta"]["lines"], ["value 1"])
        self.assertTrue(p["beta"]["runs"][0]["lines"][0]["rolled_back"])
        self.assertEqual(s["gamma"]["outcome"], "runtime-error")
        self.assertEqual(s["gamma"]["lines"], ["before"])
        self.assertEqual(s["epsilon"]["outcome"], "refused")
        d = p["epsilon"]["diagnostics"][0]
        self.assertEqual((d["code"], d["body_line"], d["body_col"]), ("3506", 2, 1))
        self.assertTrue(d["path"].startswith("C:/Users/someone/Documents/Fortnite Projects/"))
        self.assertEqual(s["eta"]["outcome"], "aborted")
        self.assertEqual(s["theta-control"]["outcome"], "aborted")
        self.assertEqual(s["ovprobe-driver"]["outcome"], "runtime-error")
        self.assertNotIn("delta", p)
        self.assertEqual(len(res["unattributed_lines"]), 1)
        self.assertEqual(len(res["unattributed_diagnostics"]), 1)   # the driver's own line 4
        self.assertEqual(res["build_info"][0]["value"], "++Fortnite+Release-43.10-CL-60458657")
        self.assertEqual(len(res["runtime_errors"]), 1)
        self.assertEqual(res["runtime_errors"][0]["open_probes"], ["ovprobe-driver", "gamma"])
        # the same log with CRLF, and in UTF-16
        crlf = self.parse(m, text.replace("\n", "\r\n").encode())
        u16 = self.parse(m, text.encode("utf-16"))
        u16le = self.parse(m, text.encode("utf-16-le"))
        for other in (crlf, u16, u16le):
            self.assertEqual({k: v["summary"] for k, v in other["probes"].items()}, s)

    def test_single_log(self):
        f = self.tmp / "single.log"
        f.write_text(ue("""LogVerse: : OVPROBE begin
LogVerse: : OVPROBE after
LogVerse: : OVPROBE end
VerseBuild: Warning: D:\\P\\Content\\openverse_probe.verse(13,4, 13,9): Script warning 2000: Unreachable
"""))
        out = self.tmp / "p.json"
        quiet(ov.main, ["parse", "--single", "signal-direct", "--out", str(out), str(f)])
        p = json.loads(out.read_text())["probes"]["signal-direct"]
        self.assertEqual(p["summary"]["outcome"], "ran")
        self.assertEqual(p["summary"]["lines"], ["after"])
        d = p["diagnostics"][0]
        self.assertEqual((d["severity"], d["line"], d["body_line"]), ("warning", 13, 3))

    def test_json_diagnostics(self):
        _, m = self.generate("--mode", "batch", str(self.probes))
        eps = next(e for e in m["probes"] if e["id"] == "epsilon")
        entry = {"severity": "Error", "code": 3506, "message": "Unknown identifier `Foo`.",
                 "filePath": "C:/P/Content/ovprobes/openverse_probe_driver.verse",
                 "span": {"startLine": eps["body_first_line"], "startColumn": 4,
                          "endLine": eps["body_first_line"], "endColumn": 7}}
        build = {"content": [{"type": "text", "text": json.dumps([entry])}]}
        res = self.parse(m, json.dumps(build).encode())
        d = res["probes"]["epsilon"]["diagnostics"][0]
        self.assertEqual((d["line"], d["body_line"], d["col"], d["body_col"]),
                         (eps["body_first_line"] + 1, 2, 5, 1))
        self.assertEqual(res["probes"]["epsilon"]["summary"]["outcome"], "refused")

    def test_admission_record(self):
        adm = {"kind": "verse-admission", "zero_based": True, "slot": "openverse_probe.verse",
               "results": [
                   {"probe": "alpha", "body_first_line": 11, "build_ok": True, "diagnostics": []},
                   {"probe": "epsilon", "body_first_line": 11, "build_ok": False, "diagnostics": [
                       {"severity": "Error", "code": "3506", "message": "Unknown identifier",
                        "filePath": "C:/P/Content/openverse_probe.verse", "span": {"startLine": 11}},
                       {"severity": "Error", "code": "3100", "message": "stale",
                        "filePath": "C:/P/Content/other.verse", "span": {"startLine": 0}}]}]}
        f = self.tmp / "adm.json"
        f.write_text(json.dumps(adm))
        out = self.tmp / "p.json"
        quiet(ov.main, ["parse", "--out", str(out), str(f)])
        res = json.loads(out.read_text())
        self.assertEqual(res["probes"]["alpha"]["summary"]["outcome"], "admitted")
        self.assertEqual(res["probes"]["epsilon"]["summary"]["outcome"], "refused")
        self.assertEqual(res["probes"]["epsilon"]["diagnostics"][0]["body_line"], 2)
        self.assertEqual(len(res["unattributed_diagnostics"]), 1)


def record(pid, mode, rc, out="", err=""):
    o = ov.ov_outcome(rc)
    lean = {"probe": pid, "path": "probes/%s.verse" % pid, "sha256": "", "mode": mode,
            "runtime": "lean", "exit": rc, "stdout": out, "stderr": err, "outcome": o}
    c = dict(lean, runtime="c")
    if rc == 4:
        c.update(exit=None, stdout="", stderr="", outcome="not-run")
    return [lean, c]


class Compare(Logs, Tmp):
    def test_verdicts(self):
        _, m = self.generate("--mode", "batch", str(self.probes))
        res = self.parse(m, self.batch_log(m).encode())
        recs = []
        for mode in ("default", "signal-no-rollback"):
            recs += record("alpha", mode, 0, "OVPROBE one\nOVPROBE two\n")
            recs += record("beta", mode, 0, "OVPROBE value 2\n")
            recs += record("beta-control", mode, 0, "OVPROBE control\n")
            recs += record("gamma", mode, 2, "OVPROBE before\n", "error: overflow\n")
            recs += record("delta", mode, 0, "OVPROBE never\n")
            recs += record("epsilon", mode, 0, "OVPROBE after foo\n")
            recs += record("zeta", mode, *((4, "", "x: refused\n") if mode == "default"
                                           else (0, "OVPROBE zeta ran\n")))
            recs += record("eta", mode, 2, "OVPROBE eta ran\n", "error: overflow\n")
            recs += record("theta", mode, 0, "OVPROBE theta ran\n")
            recs += record("theta-control", mode, 0, "OVPROBE theta control\n")
        ovj, epj = self.tmp / "ov.json", self.tmp / "epic.json"
        ovj.write_text(json.dumps({"head": "h", "compiler_revision": "c", "records": recs}))
        epj.write_text(json.dumps(res))
        exp = self.tmp / "exp.tsv"
        exp.write_text("# comment\nprobe\tbook_case\tbook_outcome\tbook_lines\n"
                       "alpha\tT:1\tran\tone|two\nbeta\tT:2\tran\tvalue 2\n"
                       "epsilon\tT:3\trefused\t\n")
        tsv, md = self.tmp / "c.tsv", self.tmp / "c.md"
        quiet(ov.main, ["compare", "--openverse", str(ovj), "--epic", str(epj),
                        "--expectations", str(exp), "--tsv", str(tsv), "--md", str(md)])
        rows = [l.split("\t") for l in tsv.read_text().strip().split("\n")]
        cols = rows[0]
        got = {(r[0], r[1]): dict(zip(cols, r)) for r in rows[1:]}
        # beta: its control ran, its line differs; gamma: a runtime error after
        # the same line; eta: aborted after the same line as OpenVerse's
        # runtime error; theta: its control aborted; theta-control: aborted
        # where OpenVerse ran (a log cut short looks the same)
        want = {"alpha": "agree", "beta": "differ", "beta-control": "agree",
                "gamma": "agree", "delta": "inconclusive", "epsilon": "epic-refuses",
                "eta": "agree", "theta": "inconclusive", "theta-control": "inconclusive"}
        for pid, v in want.items():
            self.assertEqual(got[(pid, "default")]["verdict"], v, pid)
        self.assertEqual(got[("zeta", "default")]["verdict"], "openverse-refuses")
        self.assertEqual(got[("zeta", "signal-no-rollback")]["verdict"], "agree")
        self.assertEqual(got[("alpha", "default")]["epic_vs_book"], "agree")
        self.assertEqual(got[("alpha", "default")]["openverse_vs_book"], "agree")
        self.assertEqual(got[("epsilon", "default")]["epic_vs_book"], "agree")
        self.assertEqual(got[("epsilon", "default")]["openverse_vs_book"], "differ")
        self.assertIn("Rolling Back", got[("beta", "default")]["notes"])
        text = md.read_text()
        self.assertIn("| Probe | Verdict (default) | Verdict (signal-no-rollback) |", text)
        self.assertIn("### `epsilon`", text)
        self.assertIn("++Fortnite+Release-43.10-CL-60458657", text)
        self.assertIn("Unknown identifier `Foo`", text)

    def test_merge(self):
        a = {"marker": "OVPROBE", "files": ["a.log"], "build_info": [{"key": "Build"}], "probes": {
            "alpha": {"runs": [], "diagnostics": [{"severity": "error"}], "admission": []}}}
        b = {"files": ["b.log"], "probes": {
            "alpha": {"runs": [], "diagnostics": [], "admission": []},
            "beta": {"runs": [{"begun": True, "ended": True, "lines": [], "runtime_errors": []}],
                     "diagnostics": []}}}
        d = self.tmp / "parsed"
        d.mkdir()
        (d / "a.json").write_text(json.dumps(a))
        (d / "b.json").write_text(json.dumps(b))
        m = ov.merge_parsed(ov.load_jsons([str(d)]))
        self.assertEqual(m["files"], ["a.log", "b.log"])
        self.assertEqual(ov.summarize_epic(m["probes"]["alpha"])["outcome"], "refused")
        self.assertEqual(ov.summarize_epic(m["probes"]["beta"])["outcome"], "ran")
        self.assertEqual(len(m["build_info"]), 1)

    def test_differ_and_control(self):
        p = {"diagnostics": [], "admission": [], "runs": [
            {"begun": True, "ended": True, "lines": [{"text": "x", "rolled_back": False}],
             "runtime_errors": []}]}
        epic = ov.summarize_epic(p)
        self.assertEqual(ov.verdict(epic, {"outcome": "ran", "lines": ["y"]}, None)[0], "differ")
        self.assertEqual(ov.verdict(epic, {"outcome": "runtime-error", "lines": ["x"]}, None)[0],
                         "differ")
        self.assertEqual(ov.verdict(epic, {"outcome": "ran", "lines": ["x"]},
                                    {"outcome": "refused"})[0], "inconclusive")
        self.assertEqual(ov.verdict(epic, {"outcome": "refused", "lines": None}, None)[0],
                         "openverse-refuses")


class Mock(http.server.BaseHTTPRequestHandler):
    """UEFN's MCP server as reported: meta-tools, BuildAll in a toolset."""
    content = None
    seen_sessions = []

    def log_message(self, *a):
        pass

    def reply(self, code, body=b"", ctype="application/json", sid=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        if sid:
            self.send_header("Mcp-Session-Id", sid)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self):
        msg = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        Mock.seen_sessions.append(self.headers.get("Mcp-Session-Id"))
        if "id" not in msg:
            return self.reply(202)
        meth, mid = msg["method"], msg["id"]
        if meth == "initialize":
            res = {"protocolVersion": "2025-03-26", "capabilities": {"tools": {}}}
            return self.reply(200, json.dumps({"jsonrpc": "2.0", "id": mid, "result": res}).encode(),
                              sid="session-1")
        if meth == "tools/list":
            res = {"tools": [{"name": n} for n in ("list_toolsets", "describe_toolset", "call_tool")]}
        else:
            args = msg["params"]["arguments"]
            assert (args["toolset_name"], args["tool_name"]) == mcp.BUILD
            slot = (Path(Mock.content) / "openverse_probe.verse").read_text()
            diags = []
            if "Foo()" in slot:
                line = slot.split("\n").index("    Foo()")
                diags.append({"severity": "Error", "code": 3506, "message": "Unknown identifier",
                              "filePath": str(Path(Mock.content) / "openverse_probe.verse"),
                              "span": {"startLine": line, "startColumn": 4}})
            res = {"content": [{"type": "text", "text": json.dumps(diags)}]}
        data = "event: message\ndata: %s\n\n" % json.dumps({"jsonrpc": "2.0", "id": mid, "result": res})
        self.reply(200, data.encode(), ctype="text/event-stream")


class McpClient(Tmp):
    def test_admission_through_mock_server(self):
        content = self.tmp / "Content"
        content.mkdir()
        Mock.content, Mock.seen_sessions = str(content), []
        srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Mock)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        try:
            out, m = self.generate("--mode", "single", str(self.probes / "alpha.verse"),
                                   str(self.probes / "epsilon.verse"))
            adm = self.tmp / "admission.json"
            url = "http://127.0.0.1:%d/mcp" % srv.server_address[1]
            rc = quiet(mcp.main, ["--url", url, "admit", "--manifest", str(out / "manifest.json"),
                                  "--content", str(content), "--out", str(adm)])
        finally:
            srv.shutdown()
            srv.server_close()
        self.assertEqual(rc, 0)
        self.assertEqual(Mock.seen_sessions[0], None)
        self.assertTrue(all(s == "session-1" for s in Mock.seen_sessions[1:]))
        doc = json.loads(adm.read_text())
        self.assertEqual([(r["probe"], r["build_ok"]) for r in doc["results"]],
                         [("alpha", True), ("epsilon", False)])
        self.assertEqual((content / "openverse_probe.verse").read_bytes(), mcp.EMPTY_SLOT)
        parsed = self.tmp / "p.json"
        quiet(ov.main, ["parse", "--out", str(parsed), str(adm)])
        res = json.loads(parsed.read_text())["probes"]
        self.assertEqual(res["alpha"]["summary"]["outcome"], "admitted")
        self.assertEqual(res["epsilon"]["summary"]["outcome"], "refused")
        self.assertEqual(res["epsilon"]["diagnostics"][0]["body_line"], 2)


OPENVERSE = ROOT / ".lake" / "build" / "bin" / "openverse"
CVERSE = ROOT / "runtime" / "build" / "cverse"


@unittest.skipUnless(OPENVERSE.exists() and CVERSE.exists(), "OpenVerse is not built")
class EndToEnd(Tmp):
    def test_openverse_batch_matches_single_runs(self):
        """The original probes OpenVerse admits, run one by one and as one
        driver batch on OpenVerse, demultiplex to the same results."""
        probes = [str(p) for p in sorted(VM.glob("*.verse")) if "subscribe" not in p.name]
        ovj = self.tmp / "ov.json"
        quiet(ov.main, ["openverse", "--modes", "default", "--json", str(ovj)] + probes)
        out, m = self.generate("--mode", "batch", "--host", "openverse", "--risky-last", str(ovj),
                               *probes)
        self.assertEqual(m["probes"][-1]["id"], "int-overflow")
        p = subprocess.run([str(OPENVERSE), "run", str(out / "ovprobes" / "openverse_probe_driver.verse")],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        self.assertEqual(p.returncode, 2)          # int-overflow, last, ends the batch
        log = self.tmp / "batch.log"
        log.write_bytes(p.stdout)
        parsed = self.tmp / "parsed.json"
        quiet(ov.main, ["parse", "--manifest", str(out / "manifest.json"), "--out", str(parsed),
                        str(log)])
        tsv = self.tmp / "c.tsv"
        quiet(ov.main, ["compare", "--openverse", str(ovj), "--epic", str(parsed), "--tsv", str(tsv)])
        rows = [l.split("\t") for l in tsv.read_text().strip().split("\n")[1:]]
        self.assertEqual(len(rows), len(probes))
        self.assertEqual({r[2] for r in rows}, {"agree"}, rows)


if __name__ == "__main__":
    r = unittest.main(argv=[sys.argv[0], "-v"] if "-v" in sys.argv else [sys.argv[0]], exit=False)
    sys.exit(0 if r.result.wasSuccessful() else 1)
