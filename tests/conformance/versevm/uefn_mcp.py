#!/usr/bin/env python3
"""Drive a running UEFN editor for the live probes: Verse builds, compile
admission one probe at a time, sessions and their OVPROBE lines.

UNTESTED AGAINST A LIVE EDITOR. The endpoints, toolset and tool names below are
community reports for UEFN 42.x/43.00, not Epic documentation; every name can be
overridden on the command line, and `tools` lists what the editor offers.
Python 3 standard library only (runs on the Windows host).

UEFN's MCP server (streamable HTTP, default http://127.0.0.1:8000/mcp) offers
meta-tools: list_toolsets, describe_toolset and call_tool{toolset_name,
tool_name, arguments}. When the server lists a tool directly, it is called
directly instead.

  uefn_mcp.py tools [--describe]
      list the MCP tools, and the toolsets with --describe
  uefn_mcp.py call TOOLSET TOOL [JSON-ARGUMENTS]
      call one tool and print its result
  uefn_mcp.py build [--out BUILD.json]
      build all Verse (VerseToolset.VerseToolset BuildAll); the JSON is input
      for `ovprobe.py parse` (BuildAll's lines count from 0)
  uefn_mcp.py admit --manifest SINGLE/manifest.json --content DIR [--slot NAME]
                    [--only ID]... --out ADMISSION.json
      for each probe of an `ovprobe.py generate --mode single` output: write
      its source over DIR/NAME (default openverse_probe.verse), build, record
      the diagnostics; then leave the slot file holding only a comment. The
      project's other files stay as they are, so an error elsewhere shows up
      in every build (`ovprobe.py parse` keeps such diagnostics apart).
  uefn_mcp.py session start|status|game|stop-game|stop
      the session tools (ValkyrieFortniteToolset.SessionToolset)
  uefn_mcp.py logs [--category LogVerse] [--pattern OVPROBE] [--max N] --out LOG.txt
      the editor's log entries (ConsoleToolset.LogsToolset GetLogEntries), one
      per line, input for `ovprobe.py parse`; with --verse-output, the
      session's Verse output (GetVerseOutput) instead
  uefn_mcp.py compile-socket [--host H] [--port 1962] --out BUILD.json
      ask the VerseWorkflowServer socket (Content-Length framed JSON) to
      compile the project, and record its messages until the build state
"""

import argparse
import json
import os
import re
import shutil
import socket
import sys
import time
import urllib.error
import urllib.request

URL = "http://127.0.0.1:8000/mcp"
BUILD = ("VerseToolset.VerseToolset", "BuildAll")
SESSION = "ValkyrieFortniteToolset.SessionToolset"
SESSION_TOOLS = {"start": "StartSession", "status": "GetSessionStatus", "game": "StartGame",
                 "stop-game": "StopGame", "stop": "StopSession"}
VERSE_OUTPUT = "GetVerseOutput"
LOGS = ("ConsoleToolset.LogsToolset", "GetLogEntries")
SLOT = "openverse_probe.verse"
EMPTY_SLOT = b"# openverse probe slot: empty between admission builds\n"


class McpError(Exception):
    pass


class Mcp:
    """A minimal MCP client over streamable HTTP (JSON-RPC 2.0 POSTs; replies
    as JSON or as a server-sent event stream; the session id in the
    Mcp-Session-Id header)."""

    def __init__(self, url=URL, timeout=600):
        self.url, self.timeout, self.sid, self.n = url, timeout, None, 0

    def post(self, msg, reply=True):
        req = urllib.request.Request(self.url, data=json.dumps(msg).encode("utf-8"), method="POST",
                                     headers={"Content-Type": "application/json",
                                              "Accept": "application/json, text/event-stream"})
        if self.sid:
            req.add_header("Mcp-Session-Id", self.sid)
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as r:
                self.sid = r.headers.get("Mcp-Session-Id") or self.sid
                ctype = r.headers.get("Content-Type", "")
                body = r.read().decode("utf-8", "replace")
        except urllib.error.URLError as e:
            raise McpError("cannot reach %s: %s" % (self.url, e))
        return pick_reply(body, ctype, msg.get("id")) if reply else None

    def request(self, method, params=None):
        self.n += 1
        return self.post({"jsonrpc": "2.0", "id": self.n, "method": method, "params": params or {}})

    def initialize(self):
        r = self.request("initialize", {"protocolVersion": "2025-03-26", "capabilities": {},
                                        "clientInfo": {"name": "openverse-ovprobe", "version": "0.1"}})
        self.post({"jsonrpc": "2.0", "method": "notifications/initialized"}, reply=False)
        return r


def pick_reply(body, ctype, mid):
    msgs = []
    if "text/event-stream" in ctype:
        for block in re.split(r"\r?\n\r?\n", body):
            data = "\n".join(l[5:].lstrip() for l in block.splitlines() if l.startswith("data:"))
            if data.strip():
                msgs.append(json.loads(data))
    elif body.strip():
        x = json.loads(body)
        msgs = x if isinstance(x, list) else [x]
    for m in msgs:
        if isinstance(m, dict) and m.get("id") == mid:
            if "error" in m:
                raise McpError("error from the server: %s" % json.dumps(m["error"]))
            return m.get("result")
    raise McpError("no reply to request %s in: %s" % (mid, body[:500]))


def unwrap(result):
    """A tool result's content: structuredContent, or its text parts read as
    JSON where they are JSON."""
    if not isinstance(result, dict):
        return result
    if result.get("isError"):
        raise McpError("the tool failed: %s" % json.dumps(result)[:2000])
    if "structuredContent" in result:
        return result["structuredContent"]
    parts = []
    for c in result.get("content", []):
        if c.get("type") == "text":
            try:
                parts.append(json.loads(c["text"]))
            except ValueError:
                parts.append(c["text"])
        else:
            parts.append(c)
    return parts[0] if len(parts) == 1 else parts


class Uefn:
    def __init__(self, url, timeout):
        self.mcp = Mcp(url, timeout)
        self.mcp.initialize()
        self.names = {t.get("name") for t in self.mcp.request("tools/list").get("tools", [])}

    def tool(self, name, args=None):
        return unwrap(self.mcp.request("tools/call", {"name": name, "arguments": args or {}}))

    def call(self, toolset, name, args=None):
        if "call_tool" in self.names:
            return self.tool("call_tool", {"toolset_name": toolset, "tool_name": name,
                                           "arguments": args or {}})
        if name in self.names:
            return self.tool(name, args)
        raise McpError("the server offers neither call_tool nor %s (tools: %s)"
                       % (name, ", ".join(sorted(n for n in self.names if n))))


def dump(path, doc):
    data = (json.dumps(doc, indent=1) + "\n").encode("utf-8")
    if path:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        with open(path, "wb") as fh:
            fh.write(data)
    else:
        sys.stdout.write(data.decode("utf-8"))


def is_error(d):
    s = d.get("severity", d.get("type"))
    if isinstance(s, (int, float)):
        return int(s) == 1
    return "err" in str(s or "").lower()


def diagnostics_of(x):
    """The diagnostic-like objects of a build result (see ovprobe.json_diagnostics)."""
    out = []

    def walk(v):
        if isinstance(v, dict):
            if isinstance(v.get("message"), str) and ("severity" in v or "code" in v):
                out.append(v)
                return
            for w in v.values():
                walk(w)
        elif isinstance(v, list):
            for w in v:
                walk(w)
    walk(x)
    return out


def cmd_tools(u, a):
    print("MCP tools: %s" % ", ".join(sorted(n for n in u.names if n)))
    if "list_toolsets" in u.names:
        sets = u.tool("list_toolsets")
        print(json.dumps(sets, indent=1))
        if a.describe and "describe_toolset" in u.names:
            names = re.findall(r'"([A-Za-z0-9_]+\.[A-Za-z0-9_.]+)"', json.dumps(sets))
            for n in sorted(set(names)):
                print("== %s" % n)
                print(json.dumps(u.tool("describe_toolset", {"toolset_name": n}), indent=1))
    return 0


def build(u, a):
    t0 = time.time()
    res = u.call(a.build_toolset, a.build_tool)
    return res, time.time() - t0


def cmd_build(u, a):
    res, secs = build(u, a)
    diags = diagnostics_of(res)
    dump(a.out, {"tool": "uefn_mcp.py build", "kind": "verse-build", "zero_based": True,
                 "seconds": round(secs, 1), "errors": sum(1 for d in diags if is_error(d)),
                 "result": res})
    print("build: %d diagnostic(s), %d error(s), %.0f s" % (
        len(diags), sum(1 for d in diags if is_error(d)), secs), file=sys.stderr)
    return 0


def cmd_admit(u, a):
    with open(a.manifest, encoding="utf-8") as fh:
        manifest = json.load(fh)
    if manifest.get("layout", manifest.get("mode")) != "single":
        raise SystemExit("uefn_mcp: admit takes the manifest of ovprobe.py generate --mode single")
    base = os.path.dirname(os.path.abspath(a.manifest))
    slot = os.path.join(a.content, a.slot)
    results = []
    try:
        for e in manifest["probes"]:
            if a.only and e["id"] not in a.only:
                continue
            shutil.copyfile(os.path.join(base, *e["file"].split("/")), slot)
            res, secs = build(u, a)
            diags = diagnostics_of(res)
            mine = [d for d in diags
                    if os.path.basename(str(d.get("filePath") or d.get("file") or "")).lower()
                    in ("", a.slot.lower())]
            ok = not any(is_error(d) for d in mine)
            print("%-44s %s (%d diagnostic(s), %.0f s)" % (
                e["id"], "admitted" if ok else "REFUSED", len(mine), secs), file=sys.stderr)
            results.append({"probe": e["id"], "sha256": e["sha256"],
                            "body_first_line": e["body_first_line"], "build_ok": ok,
                            "seconds": round(secs, 1), "diagnostics": diags})
            dump(a.out, {"tool": "uefn_mcp.py admit", "kind": "verse-admission",
                         "zero_based": True, "slot": a.slot, "results": results})
    finally:
        with open(slot, "wb") as fh:
            fh.write(EMPTY_SLOT)
    return 0


def cmd_session(u, a):
    print(json.dumps(u.call(a.session_toolset, SESSION_TOOLS[a.action]), indent=1))
    return 0


def entry_line(x):
    if isinstance(x, str):
        return x
    if isinstance(x, dict):
        msg = next((x[k] for k in ("message", "Message", "text", "line", "Line") if k in x), None)
        if msg is None:
            return json.dumps(x, sort_keys=True)
        cat = next((x[k] for k in ("category", "Category") if k in x), None)
        return "%s: %s" % (cat, msg) if cat and not str(msg).startswith(str(cat)) else str(msg)
    return json.dumps(x)


def cmd_logs(u, a):
    if a.verse_output:
        res = u.call(a.session_toolset, VERSE_OUTPUT)
    else:
        args = {"maxEntries": a.max}
        if a.category:
            args["category"] = a.category
        if a.pattern:
            args["pattern"] = a.pattern
        res = u.call(a.logs_toolset, a.logs_tool, args)
    entries = res
    if isinstance(res, dict):
        entries = next((res[k] for k in ("entries", "Entries", "lines", "logs", "output")
                        if isinstance(res.get(k), list)), [res])
    if isinstance(entries, str):
        entries = entries.splitlines()
    lines = [entry_line(x) for x in (entries if isinstance(entries, list) else [entries])]
    data = ("\n".join(lines) + "\n").encode("utf-8")
    with open(a.out, "wb") as fh:
        fh.write(data)
    print("logs: %d line(s) to %s" % (len(lines), a.out), file=sys.stderr)
    return 0


def frame(msg):
    body = json.dumps(msg).encode("utf-8")
    return b"Content-Length: %d\r\n\r\n" % len(body) + body


def read_frames(sock, deadline):
    buf = b""
    while time.time() < deadline:
        sock.settimeout(max(0.1, deadline - time.time()))
        try:
            chunk = sock.recv(65536)
        except socket.timeout:
            break
        if not chunk:
            break
        buf += chunk
        while True:
            head, sep, rest = buf.partition(b"\r\n\r\n")
            if not sep:
                break
            m = re.search(rb"Content-Length:\s*(\d+)", head, re.I)
            if not m:
                raise McpError("a frame without Content-Length: %r" % head[:200])
            n = int(m.group(1))
            if len(rest) < n:
                break
            yield json.loads(rest[:n].decode("utf-8", "replace"))
            buf = rest[n:]


def cmd_compile_socket(a):
    msgs = []
    with socket.create_connection((a.host, a.port), timeout=10) as s:
        s.sendall(frame({"seq": 1, "type": 1, "command": "compileProject", "params": {}}))
        for m in read_frames(s, time.time() + a.timeout):
            msgs.append(m)
            if "updateBuildState" in json.dumps(m):
                break
    diags = diagnostics_of(msgs)
    dump(a.out, {"tool": "uefn_mcp.py compile-socket", "kind": "verse-build", "zero_based": False,
                 "messages": msgs})
    print("compile-socket: %d message(s), %d diagnostic(s)" % (len(msgs), len(diags)),
          file=sys.stderr)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter,
                                 epilog=__doc__.split("\n\n", 1)[1])
    ap.add_argument("--url", default=URL)
    ap.add_argument("--timeout", type=int, default=900, help="seconds per MCP request")
    ap.add_argument("--build-toolset", default=BUILD[0])
    ap.add_argument("--build-tool", default=BUILD[1])
    ap.add_argument("--session-toolset", default=SESSION)
    ap.add_argument("--logs-toolset", default=LOGS[0])
    ap.add_argument("--logs-tool", default=LOGS[1])
    sub = ap.add_subparsers(dest="cmd")
    t = sub.add_parser("tools")
    t.add_argument("--describe", action="store_true")
    c = sub.add_parser("call")
    c.add_argument("toolset")
    c.add_argument("tool")
    c.add_argument("arguments", nargs="?", default="{}")
    b = sub.add_parser("build")
    b.add_argument("--out")
    m = sub.add_parser("admit")
    m.add_argument("--manifest", required=True)
    m.add_argument("--content", required=True, help="the project's Verse folder (Plugins/<P>/Content)")
    m.add_argument("--slot", default=SLOT)
    m.add_argument("--only", action="append")
    m.add_argument("--out", required=True)
    s = sub.add_parser("session")
    s.add_argument("action", choices=sorted(SESSION_TOOLS))
    g = sub.add_parser("logs")
    g.add_argument("--category", default="LogVerse")
    g.add_argument("--pattern", default="OVPROBE")
    g.add_argument("--max", type=int, default=20000)
    g.add_argument("--verse-output", action="store_true")
    g.add_argument("--out", required=True)
    k = sub.add_parser("compile-socket")
    k.add_argument("--host", default="127.0.0.1")
    k.add_argument("--port", type=int, default=1962)
    k.add_argument("--timeout", type=int, default=900)
    k.add_argument("--out")
    a = ap.parse_args(argv)
    if a.cmd is None:
        ap.print_help()
        return 2
    try:
        if a.cmd == "compile-socket":
            return cmd_compile_socket(a)
        u = Uefn(a.url, a.timeout)
        if a.cmd == "tools":
            return cmd_tools(u, a)
        if a.cmd == "call":
            print(json.dumps(u.call(a.toolset, a.tool, json.loads(a.arguments)), indent=1))
            return 0
        return {"build": cmd_build, "admit": cmd_admit, "session": cmd_session,
                "logs": cmd_logs}[a.cmd](u, a)
    except McpError as e:
        print("uefn_mcp: %s" % e, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    sys.exit(main())
