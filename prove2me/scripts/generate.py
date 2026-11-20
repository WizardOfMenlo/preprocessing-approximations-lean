#!/usr/bin/env python3
"""Plan and generate the Prove2Me platform tree from the ported `LatticePrepro` sources.

Inputs (produced by ExtractDecls.lean / ExtractSyntax.lean): out/decl_graph.jsonl and
out/syntax/<Module>.jsonl. Output: workspace/{Definitions,Theorems,Solutions}/ and out/plan.json.

Every generated file is the original source minus the spans of unselected commands ("skeleton
subtraction"), so namespaces, sections, `variable` lines and proofs survive byte for byte.

* Definitions/Def_<Module>.lean : the module's definitions, plus the theorems that definitions or
  theorem statements cite, or that carry attributes (`@[simp]`, ...), with their proofs.
* Theorems/Thm_<slug>.lean      : `preamble` + `formal_statement` of a node, ending in `by sorry`.
* Solutions/Sol_<slug>.lean     : the node's proof. Small helper lemmas are inlined; other nodes
  are imported as `Theorems.Thm_*`. The original theorem is kept in its namespace as a `private`
  declaration and the top-level `theorem solution` applies it.

Published items are immutable. `published/` holds a verbatim copy of every published file and of
the plan they were generated with; those files are copied, never regenerated. Definitions of a
module that a new statement needs and that its published bundle lacks go to an extension bundle
(`Def_<Module>_Ext`, then `_Ext2`, ...) that imports the published one.
"""
import collections
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.dirname(HERE)
WS = os.path.join(P, "workspace")
OUT = os.path.join(P, "out")
PREFIX = "LatticePrepro"

CFG = json.load(open(os.path.join(P, "targets.json")))
TARGETS = CFG["targets"]
NODE_MIN = CFG["node_min_lines"]
PROMOTE_MIN = CFG["promote_min_lines"]
OVERRIDES = json.load(open(os.path.join(P, "overrides.json"))) if os.path.exists(
    os.path.join(P, "overrides.json")) else {}
FORCE_INLINE = set(OVERRIDES.get("force_inline", []))
FORCE_NODE = set(OVERRIDES.get("force_node", []))
FORCE_EMBED = set(OVERRIDES.get("force_embed", []))
EXTRA_DEF_ROOTS = set(OVERRIDES.get("extra_def_roots", []))
WRAPPER_ARGS = OVERRIDES.get("wrapper_args", {})

PUB = os.path.join(P, "published")
PUB_PLAN = (json.load(open(os.path.join(PUB, "plan.json")))
            if os.path.exists(os.path.join(PUB, "plan.json")) else {"definitions": [], "nodes": []})
PUB_DEFS = {d["definition_name"]: d for d in PUB_PLAN["definitions"]}
PUB_NODES = {n["theorem_name"]: n for n in PUB_PLAN["nodes"]}

ASCII_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")
K = "Lean.Parser.Command."
THM_KW = {K + "theorem", "group"}  # `group` is Mathlib's `lemma`
LOCAL_CTX = {K + "variable", K + "open", K + "include", K + "omit", K + "universe",
             K + "set_option"}
SCOPE = {K + "namespace", K + "section", K + "end"}


def die(msg):
    print("ERROR:", msg, file=sys.stderr)
    sys.exit(1)


# --------------------------------------------------------------------------- load

class Cmd:
    __slots__ = ("mod", "idx", "f", "kind", "a", "b", "cls", "consts", "stack", "ns", "open_idx",
                 "fullname", "main", "tdeps", "vdeps", "deps", "plines")

    def __init__(self, mod, idx, f):
        self.mod, self.idx, self.f = mod, idx, f
        self.kind = f["kind"]
        self.a, self.b = f["range"]
        self.consts = []
        self.stack = []      # indices of the enclosing scope-opening commands
        self.ns = ""         # current namespace
        self.open_idx = None  # for `end`: the command it closes
        self.fullname = None
        self.main = None
        self.tdeps, self.vdeps, self.deps = set(), set(), set()
        self.plines = 0
        if f.get("decl"):
            self.cls = "thm" if (f["kw"] in THM_KW) else "def"
        elif self.kind in SCOPE:
            self.cls = "scope"
        elif self.kind in LOCAL_CTX:
            self.cls = "local"
        elif self.kind == K + "moduleDoc":
            self.cls = "doc"
        else:
            self.cls = "global"

    def key(self):
        return (self.mod, self.idx)


class Module:
    def __init__(self, name):
        self.name = name
        self.path = os.path.join(WS, *name.split(".")) + ".lean"
        self.src = open(self.path, "rb").read()
        rows = [json.loads(l) for l in open(os.path.join(OUT, "syntax", name + ".jsonl"))]
        self.header = rows[0]["range"]
        self.cmds = [Cmd(name, i, f) for i, f in enumerate(rows[1:])]
        head = self.src[self.header[0]:self.header[1]].decode()
        imps = re.findall(r"^import\s+(\S+)", head, flags=re.M)
        self.proj_imports = [i for i in imps if i.startswith(PREFIX + ".")]
        self.ext_imports = [i for i in imps if not i.startswith(PREFIX + ".")]
        self.line_starts = [0]
        for m in re.finditer(b"\n", self.src):
            self.line_starts.append(m.end())

    def text(self, a, b):
        return self.src[a:b].decode()

    def offset(self, line, col):
        ls = self.line_starts[line - 1]
        le = self.line_starts[line] if line < len(self.line_starts) else len(self.src)
        return ls + len(self.src[ls:le].decode()[:col].encode())

    def line_of(self, off):
        import bisect
        return bisect.bisect_right(self.line_starts, off)


mod_names = [l.strip()[:-5].replace("/", ".") for l in open(os.path.join(OUT, "files.txt"))]
MODS = {n: Module(n) for n in mod_names}

# transitive project imports, and a topological order
_trans = {}


def trans_imports(m):
    if m not in _trans:
        acc = []
        for i in MODS[m].proj_imports:
            for j in trans_imports(i) + [i]:
                if j not in acc:
                    acc.append(j)
        _trans[m] = acc
    return _trans[m]


TOPO = []
for _m in mod_names:
    for _j in trans_imports(_m) + [_m]:
        if _j not in TOPO:
            TOPO.append(_j)
TOPO_IDX = {m: i for i, m in enumerate(TOPO)}


def ext_imports_closure(mods):
    acc = set()
    for m in mods:
        for j in trans_imports(m) + [m]:
            acc.update(MODS[j].ext_imports)
    return sorted(acc)


# scopes
for M in MODS.values():
    stack, ns_stack = [], [""]
    for c in M.cmds:
        if c.kind == K + "end":
            if not stack:
                die(f"unbalanced end in {M.name}")
            c.open_idx = stack.pop()
            opener = M.cmds[c.open_idx]
            if opener.kind == K + "namespace":
                ns_stack.pop()
            c.stack, c.ns = list(stack), ns_stack[-1]
        elif c.kind in (K + "namespace", K + "section"):
            c.stack = list(stack)
            stack.append(c.idx)
            if c.kind == K + "namespace":
                ns_stack.append((ns_stack[-1] + "." if ns_stack[-1] else "") + c.f["name"])
            c.ns = ns_stack[-1]
        else:
            c.stack, c.ns = list(stack), ns_stack[-1]
    if stack:
        die(f"unclosed scope in {M.name}")

# graph
ROWS = {}
for l in open(os.path.join(OUT, "decl_graph.jsonl")):
    r = json.loads(l)
    ROWS[r["name"]] = r

CONST_CMD = {}
for name, r in ROWS.items():
    if r["range"] is None:
        continue
    M = MODS[r["module"]]
    off = M.offset(r["range"][0], r["range"][1])
    for c in M.cmds:
        if c.a <= off < c.b:
            CONST_CMD[name] = c
            c.consts.append(name)
            break
unassigned = []
for name, r in ROWS.items():
    if name in CONST_CMD:
        continue
    parts = name.split(".")
    for k in range(len(parts) - 1, 0, -1):
        pre = ".".join(parts[:k])
        if pre in CONST_CMD:
            CONST_CMD[name] = CONST_CMD[pre]
            CONST_CMD[pre].consts.append(name)
            break
    else:
        unassigned.append(name)

# full names, main constants, dependencies
for M in MODS.values():
    for c in M.cmds:
        if c.cls not in ("thm", "def"):
            continue
        if c.cls == "thm":
            did = M.text(*c.f["declId"])
            c.fullname = (c.ns + "." if c.ns else "") + did
            if c.fullname not in ROWS or ROWS[c.fullname]["kind"] != "theorem":
                die(f"cannot find theorem constant for {c.fullname} in {M.name}")
            c.main = c.fullname
            c.plines = M.line_of(c.b) - M.line_of(c.f["valStart"])

            def closure(seed):
                res, seen, work = set(), set(), list(seed)
                while work:
                    x = work.pop()
                    if x in seen or x == c.main:
                        continue
                    seen.add(x)
                    cx = CONST_CMD.get(x)
                    if cx is None:
                        continue
                    if cx is c:
                        work.extend(ROWS[x]["typeDeps"] + ROWS[x]["valueDeps"])
                    else:
                        res.add(cx.key())
                return res
            c.tdeps = closure(ROWS[c.main]["typeDeps"])
            c.vdeps = closure(ROWS[c.main]["valueDeps"])
            c.deps = c.tdeps | c.vdeps
        else:
            if c.f.get("declId"):
                c.fullname = (c.ns + "." if c.ns else "") + M.text(*c.f["declId"])
            for x in c.consts:
                for d in ROWS[x]["typeDeps"] + ROWS[x]["valueDeps"]:
                    cd = CONST_CMD.get(d)
                    if cd is not None and cd is not c:
                        c.deps.add(cd.key())


def cmd(key):
    return MODS[key[0]].cmds[key[1]]


# Source references. Proof terms miss what is elaborated away (lemmas `simp` applies by `rfl`,
# definitions that are only unfolded), so every identifier of the source counts as a dependency.
for M in MODS.values():
    starts = [c.a for c in M.cmds]
    import bisect
    for l in open(os.path.join(OUT, "refs", M.name + ".jsonl")):
        if not l.strip():
            continue
        r = json.loads(l)
        i = bisect.bisect_right(starts, r["pos"]) - 1
        if i < 0 or not (M.cmds[i].a <= r["pos"] < M.cmds[i].b):
            continue
        c, target = M.cmds[i], CONST_CMD.get(r["name"])
        if target is None or target is c:
            continue
        if c.cls == "thm":
            (c.tdeps if r["pos"] < c.f["valStart"] else c.vdeps).add(target.key())
        c.deps.add(target.key())


BY_NAME = {c.fullname: c for M in MODS.values() for c in M.cmds if c.cls == "thm"}
for t in TARGETS:
    if t not in BY_NAME:
        die(f"target {t} not found")

# --------------------------------------------------------------------------- plan

roots = [BY_NAME[t].key() for t in TARGETS]
for M in MODS.values():
    for c in M.cmds:
        if c.cls == "def" and (c.f["kw"] == K + "instance" or c.fullname in EXTRA_DEF_ROOTS):
            roots.append(c.key())
REACH, work = set(), list(roots)
while work:
    k = work.pop()
    if k in REACH:
        continue
    REACH.add(k)
    work.extend(cmd(k).deps)

thms = [cmd(k) for k in REACH if cmd(k).cls == "thm"]
defs = [cmd(k) for k in REACH if cmd(k).cls == "def"]

users = collections.defaultdict(set)
for t in thms:
    for k in t.vdeps:
        users[k].add(t.key())

# Candidate nodes, by size and reuse. Theorems carrying attributes (`@[simp]`, ...) stay out:
# a stub cannot carry the attribute, and later proofs rely on it.
CAND = set()
skipped_non_ascii, skipped_attr = [], []
for t in thms:
    k = t.key()
    if t.fullname in TARGETS or t.fullname in FORCE_NODE or t.fullname in PUB_NODES:
        CAND.add(k)
        continue
    if t.fullname in FORCE_INLINE or t.fullname in FORCE_EMBED:
        continue
    cross = any(u[0] != t.mod for u in users[k])
    want = t.plines > NODE_MIN or (t.plines > PROMOTE_MIN and (cross or len(users[k]) >= 2))
    if want and not ASCII_NAME.match(t.fullname):
        skipped_non_ascii.append(t.fullname)
        want = False
    if want and t.f.get("attrs") is not None:
        skipped_attr.append(t.fullname)
        want = False
    if want:
        CAND.add(k)

# Theorems carrying attributes are used implicitly (`simp` applies a `@[simp]` lemma without
# naming it, and a `rfl` lemma leaves no trace in the proof term), so they go wherever the
# definitions they talk about go.
ATTR_THMS = [c for M in MODS.values() for c in M.cmds
             if c.cls == "thm" and c.f.get("attrs") is not None]

INSTANCES = [c.key() for M in MODS.values() for c in M.cmds
             if c.cls == "def" and c.key() in REACH and c.f["kw"] == K + "instance"]


def bundle_material(nodes):
    """Definitions that node statements need (with everything those definitions need), and the
    theorems cited by such definitions or by node statements (with everything their proofs need).
    These live in the Definitions bundles, proofs included."""
    sdef, emb, work = set(), set(), list(INSTANCES)
    for k in nodes:
        work.extend(cmd(k).tdeps)
    for t in thms:
        if t.fullname in FORCE_EMBED:
            work.append(t.key())
    def run():
        while work:
            k = work.pop()
            c = cmd(k)
            if c.cls == "def":
                if k not in sdef:
                    sdef.add(k)
                    work.extend(c.deps)
            elif c.cls == "thm":
                if k not in emb:
                    emb.add(k)
                    work.extend(c.deps)
    run()
    changed = True
    while changed:
        changed = False
        for a in ATTR_THMS:
            k = a.key()
            if k in emb:
                continue
            td = [j for j in a.tdeps if cmd(j).cls in ("def", "thm")]
            if all((j in sdef) if cmd(j).cls == "def" else (j in emb) for j in td):
                work.append(k)
                run()
                changed = True
    return sdef, emb


NODES = set(CAND)
while True:
    SDEF, EMB = bundle_material(NODES)
    clash = NODES & EMB
    if not clash:
        break
    for k in clash:
        if cmd(k).fullname in TARGETS or cmd(k).fullname in PUB_NODES:
            die(f"node {cmd(k).fullname} is cited by a definition or a statement")
    NODES -= clash

slugs = collections.Counter(cmd(k).fullname.replace(".", "_") for k in NODES)
dups = [s for s, n in slugs.items() if n > 1]
if dups:
    die(f"slug collisions: {dups}")


def slug(c):
    return c.fullname.replace(".", "_")


def inline_closure(t):
    """Proof-side material of a node: the helper lemmas and definitions pasted into its solution,
    and the nodes it imports."""
    inl, nd, seen, work = [], set(), set(), list(t.vdeps)

    def run():
        while work:
            k = work.pop()
            if k in seen:
                continue
            seen.add(k)
            c = cmd(k)
            if c.cls not in ("thm", "def") or k in EMB or k in SDEF or k == t.key():
                continue
            if k in NODES:
                nd.add(k)
            else:
                inl.append(k)
                work.extend(c.deps)
    run()
    changed = True
    while changed:
        changed = False
        have = set(inl)
        for a in ATTR_THMS:
            k = a.key()
            if k in EMB or k in NODES or k in have:
                continue
            td = [j for j in a.tdeps if cmd(j).cls in ("def", "thm")]
            if any(j in have for j in td) and all(j in SDEF or j in EMB or j in have for j in td):
                seen.discard(k)
                work.append(k)
                run()
                changed = True
    return inl, nd


# a global command (`attribute [instance] ...`) goes wherever the definition before it goes
for M in MODS.values():
    last = None
    for c in M.cmds:
        if c.cls == "def":
            last = c.idx
        elif c.cls == "global":
            same = sorted(k[1] for k in c.deps if k[0] == M.name and cmd(k).cls == "def")
            c.open_idx = same[0] if same else last

# bundles: for each module, the files that carry its definitions, as (name, command indices,
# published?). A published file keeps exactly the declarations it was published with.
def norm_ws(s):
    return re.sub(r"\n{3,}", "\n\n", re.sub(r"[ \t]+\n", "\n", s))


def bundle_file_names(mod):
    base = "Def_" + mod.replace(".", "_")
    yield base
    yield base + "_Ext"
    k = 2
    while True:
        yield f"{base}_Ext{k}"
        k += 1


BUNDLES = {}
for M in MODS.values():
    rest = {c.idx for c in M.cmds if (c.cls == "def" and c.key() in SDEF)
            or (c.cls == "thm" and c.key() in EMB)}
    if not rest:
        continue
    files = []
    for fname in bundle_file_names(M.name):
        if fname[4:] in PUB_DEFS:
            ftext = norm_ws(open(os.path.join(PUB, "Definitions", fname + ".lean")).read())
            got = {i for i in rest if norm_ws(M.text(M.cmds[i].a, M.cmds[i].b)) in ftext}
            files.append((fname, got, True))
            rest -= got
        else:
            if rest:
                files.append((fname, rest, False))
            break
    BUNDLES[M.name] = files
_have = {f[4:] for fs in BUNDLES.values() for f, _, pub in fs if pub}
if set(PUB_DEFS) - _have:
    die(f"published bundles without a module: {sorted(set(PUB_DEFS) - _have)}")
if set(PUB_NODES) - {cmd(k).fullname for k in NODES}:
    die(f"published theorems that are no longer nodes: "
        f"{sorted(set(PUB_NODES) - {cmd(k).fullname for k in NODES})}")


def bundle_closure(mods):
    acc = set()
    for m in mods:
        for j in trans_imports(m) + [m]:
            if j in BUNDLES:
                acc.add(j)
    return sorted(acc, key=lambda m: TOPO_IDX[m])


def bundle_names(mods):
    """The bundle files of the given modules, in import order."""
    return [f for m in mods for f, _, _ in BUNDLES[m]]


# --------------------------------------------------------------------------- generate

def tidy(s):
    s = re.sub(r"[ \t]+\n", "\n", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip() + "\n"


def skeleton(M, keep, edits=None):
    """Source of `M` minus the header and the commands not in `keep` (a set of indices).
    `edits` maps a command index to a list of (offset, delete_len, insert_bytes)."""
    out, pos = [], M.header[1]
    for c in M.cmds:
        if c.idx in keep:
            if edits and c.idx in edits:
                p = pos
                for off, dl, ins in sorted(edits[c.idx]):
                    out.append(M.src[p:off])
                    out.append(ins)
                    p = off + dl
                out.append(M.src[p:c.b])
            else:
                out.append(M.src[pos:c.b])
        else:
            out.append(M.src[pos:c.a])
        pos = c.b
    out.append(M.src[pos:])
    return b"".join(out).decode()


def scope_keep(M, kept_decls, with_docs, avail):
    """Indices to keep: the given declarations, the scopes that contain one of them, and the
    context commands of those scopes whose own references are available (`avail`: a predicate
    on command keys for what the imports provide)."""
    def ok(c):
        return all((k[0] == M.name and k[1] in kept_decls) or avail(k) for k in c.deps)
    keep = set(kept_decls)
    for c in M.cmds:
        if c.cls == "global" and c.open_idx in kept_decls and ok(c):
            keep.add(c.idx)
    live = set()
    for i in keep:
        live.update(M.cmds[i].stack)
    for c in M.cmds:
        if c.kind in (K + "namespace", K + "section"):
            if c.idx in live:
                keep.add(c.idx)
        elif c.kind == K + "end":
            if c.open_idx in live:
                keep.add(c.idx)
        elif c.cls == "local" or (c.cls == "doc" and with_docs):
            if all(s in live for s in c.stack) and ok(c):
                keep.add(c.idx)
    return keep


def provided_namespaces(bundle_mods):
    """Namespaces that the given definition bundles already declare something in."""
    acc = set()
    for k in SDEF | EMB:
        if k[0] in bundle_mods:
            for x in cmd(k).consts:
                parts = x.split(".")
                for i in range(1, len(parts)):
                    acc.add(".".join(parts[:i]))
    return acc


def shims(names, provided=frozenset()):
    """`open X` fails when no declaration of the file or its imports lives in `X`; registering
    the namespace makes it a no-op instead."""
    ns = sorted({n for n in names if (n == PREFIX or n.startswith(PREFIX + ".")) and n not in provided})
    return "".join(f"namespace {n} end {n}\n" for n in ns)


def opened_by(M, keep):
    return [n for c in M.cmds if c.idx in keep for n in c.f.get("openResolved", [])]


def bundle_avail(mods):
    bm = set(bundle_closure(mods))
    return lambda k: k[0] in bm and (k in SDEF or k in EMB)


def statement_context(M, t, avail, provided=None):
    """The `open`/`variable`/... lines in scope at theorem `t`, flattened to top level, and the
    project namespaces they open."""
    lines, opened = [], []
    frames = [[None, []]]  # (namespace name or None, context commands)
    for c in M.cmds[:t.idx]:
        if c.kind == K + "namespace":
            frames.append([c.ns, []])
        elif c.kind == K + "section":
            frames.append([None, []])
        elif c.kind == K + "end":
            frames.pop()
        elif c.cls == "local" and all(avail(k) for k in c.deps):
            res = [n for n in c.f.get("openResolved", []) if n == PREFIX or n.startswith(PREFIX + ".")]
            if (c.kind == K + "open" and provided is not None and res
                    and len(res) == len(c.f.get("openResolved", []))
                    and not any(n in provided for n in res)):
                continue  # opens only project namespaces the stub's imports leave empty
            frames[-1][1].append(c)
    for ns, ctx in frames:
        # the theorem's dotted name opens its own namespaces; an explicit `open` is only useful
        # when the imports declare something there
        if ns and (provided is None or ns in provided):
            lines.append(f"open {ns}")
            opened.append(ns)
        for c in ctx:
            lines.append(M.text(c.a, c.b))
            opened.extend(c.f.get("openResolved", []))
    for a, b in t.f["inPrefixes"]:
        lines.append(M.text(a, b))
    opened.extend(t.f.get("openResolved", []))
    return lines, opened


def signature(M, t):
    return M.text(t.f["declIdFull"][1], t.f["valStart"]).rstrip()


def wrapper_args(t):
    if t.fullname in WRAPPER_ARGS:
        return WRAPPER_ARGS[t.fullname]
    binders = ROWS[t.main]["binders"]
    n = len(binders) - t.f["conclLead"]
    sig = t.f["sigBinders"]
    if n < len(sig):
        die(f"binder count mismatch for {t.fullname}")
    for s, b in zip(sig, binders[n - len(sig):n]):
        if s != "_" and s != b["name"]:
            die(f"binder name mismatch for {t.fullname}: {s} vs {b['name']}")
    args = []
    for b in binders[:n]:
        if b["bi"] == "inst":
            args.append("_")
        elif b["hyg"]:
            args.append("‹_›" if b["bi"] == "explicit" else "_")
        else:
            args.append(b["name"])
    return " ".join(args)


def import_block(ext, bundle_mods, node_keys=(), more=()):
    lines = [f"import {i}" for i in ext]
    lines += [f"import Definitions.{f}" for f in bundle_names(bundle_mods) + list(more)]
    lines += sorted(f"import Theorems.Thm_{slug(cmd(k))}" for k in node_keys)
    return "\n".join(lines)


for sub in ("Definitions", "Theorems", "Solutions"):
    d = os.path.join(WS, sub)
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        if f.endswith(".lean"):
            os.remove(os.path.join(d, f))

def published_file(sub, name):
    return open(os.path.join(PUB, sub, name)).read()


# published bundles first (verbatim, in their published order), then the new ones
plan = {"definitions": list(PUB_PLAN["definitions"]), "nodes": []}
for d in PUB_PLAN["definitions"]:
    fn = f"Def_{d['definition_name']}.lean"
    open(os.path.join(WS, "Definitions", fn), "w").write(published_file("Definitions", fn))

for m in TOPO:
    M = MODS[m]
    for bi, (fname, decls, pub) in enumerate(BUNDLES.get(m, [])):
        if pub:
            continue
        earlier = [f for f, _, _ in BUNDLES[m][:bi]]
        earlier_idx = set().union(*[s for _, s, _ in BUNDLES[m][:bi]]) if bi else set()
        deps = bundle_closure(trans_imports(m))
        base_av = bundle_avail(trans_imports(m))

        def avail(k, m=m, earlier_idx=earlier_idx, base_av=base_av):
            return base_av(k) or (k[0] == m and k[1] in earlier_idx)
        keep = scope_keep(M, decls, with_docs=(bi == 0), avail=avail)
        body = skeleton(M, keep)
        note = "" if bi == 0 else (
            f"/-! Further definitions from `{m.replace('.', '/')}.lean`, continuing "
            f"`{earlier[0]}`. -/\n\n")
        text = (import_block(ext_imports_closure([m]), deps, more=earlier) + "\n\n" + note
                + shims(opened_by(M, keep)) + tidy(body))
        open(os.path.join(WS, "Definitions", fname + ".lean"), "w").write(text)
        plan["definitions"].append({
            "definition_name": fname[4:], "module": m,
            "imports": [f[4:] for f in bundle_names(deps) + earlier],
            "defs": sorted(c.fullname or "(instance)" for c in M.cmds
                           if c.idx in decls and c.cls == "def"),
            "embedded_theorems": sorted(c.fullname for c in M.cmds
                                        if c.idx in decls and c.cls == "thm"),
            "lines": text.count("\n")})

# nodes
node_list = sorted((cmd(k) for k in NODES), key=lambda c: (TOPO_IDX[c.mod], c.idx))
for t in node_list:
    M = MODS[t.mod]
    if t.fullname in PUB_NODES:
        for sub, pre in (("Theorems", "Thm_"), ("Solutions", "Sol_")):
            fn = f"{pre}{slug(t)}.lean"
            open(os.path.join(WS, sub, fn), "w").write(published_file(sub, fn))
        plan["nodes"].append(PUB_NODES[t.fullname])
        continue
    inl, nd = inline_closure(t)
    stub_provided = provided_namespaces(set(bundle_closure([t.mod])))
    ctx, ctx_opened = statement_context(M, t, bundle_avail([t.mod]), stub_provided)
    sig = signature(M, t)
    # stub
    preamble = import_block(ext_imports_closure([t.mod]), bundle_closure([t.mod]))
    if ctx or ctx_opened:
        preamble += "\n\n" + shims(ctx_opened, stub_provided) + "\n".join(ctx)
    statement = f"theorem {t.fullname}{sig} := by sorry"
    open(os.path.join(WS, "Theorems", f"Thm_{slug(t)}.lean"), "w").write(
        preamble + "\n\n" + statement + "\n")
    # solution
    by_mod = collections.defaultdict(set)
    for k in inl:
        by_mod[k[0]].add(k[1])
    by_mod[t.mod].add(t.idx)
    mods = sorted(by_mod, key=lambda m: TOPO_IDX[m])
    parts, opened = [], list(ctx_opened)
    inl_set = set(inl) | {t.key()}
    b_av = bundle_avail(mods)

    def avail(k):
        return b_av(k) or k in nd or k in inl_set
    for m in mods:
        Mm = MODS[m]
        keep = scope_keep(Mm, by_mod[m], with_docs=False, avail=avail)
        opened.extend(opened_by(Mm, keep))
        edits = None
        if m == t.mod:
            vis = t.f.get("visibility")
            if vis is not None:
                edits = {t.idx: [(vis[0], vis[1] - vis[0], b"private")]}
            else:
                edits = {t.idx: [(t.f["kwPos"], 0, b"private ")]}
        parts.append(tidy(skeleton(Mm, keep, edits)))
    wrapper = "\n".join(ctx + [f"theorem solution{sig} :=\n  @{t.fullname} {wrapper_args(t)}"])
    sol = (import_block(ext_imports_closure(mods), bundle_closure(mods), nd) + "\n\n"
           + shims(opened) + "\n" + "\n".join(parts) + "\n" + wrapper + "\n")
    open(os.path.join(WS, "Solutions", f"Sol_{slug(t)}.lean"), "w").write(sol)
    plan["nodes"].append({
        "theorem_name": t.fullname, "slug": slug(t), "module": t.mod,
        "source_lines": [M.line_of(t.a), M.line_of(t.b - 1)],
        "proof_lines": t.plines, "is_target": t.fullname in TARGETS,
        "preamble": preamble, "formal_statement": statement,
        "definition_imports": [f[4:] for f in bundle_names(bundle_closure(mods))],
        "node_deps": sorted(cmd(k).fullname for k in nd),
        "inlined": sorted(cmd(k).fullname or "(instance)" for k in inl),
        "inlined_defs": sum(cmd(k).cls == "def" for k in inl),
        "solution_lines": sol.count("\n")})

json.dump(plan, open(os.path.join(OUT, "plan.json"), "w"), indent=1, ensure_ascii=False)

# --------------------------------------------------------------------------- report

emb = [cmd(k) for k in EMB]
inl_all = set()
for t in node_list:
    inl_all.update(inline_closure(t)[0])
print(f"published: {len(PUB_DEFS)} bundles and {len(PUB_NODES)} theorems copied verbatim; new: "
      f"{len(plan['definitions']) - len(PUB_DEFS)} bundles and {len(NODES) - len(PUB_NODES)} theorems")
print(f"constants: {len(ROWS)} (unassigned: {len(unassigned)})")
print(f"reachable: {len(thms)} theorems, {len(defs)} definitions "
      f"(of {sum(c.cls == 'thm' for M in MODS.values() for c in M.cmds)} / "
      f"{sum(c.cls == 'def' for M in MODS.values() for c in M.cmds)})")
print(f"bundles: {sum(len(v) for v in BUNDLES.values())} ({len(PUB_DEFS)} published) with "
      f"{len(SDEF)} definitions and {len(emb)} embedded theorems "
      f"(longest embedded proof: {max((c.plines for c in emb), default=0)} lines)")
print(f"nodes: {len(NODES)}; inlined into solutions: "
      f"{sum(cmd(k).cls == 'thm' for k in inl_all)} theorems, {sum(cmd(k).cls == 'def' for k in inl_all)} definitions")
lost = [c.fullname for c in thms if c.key() not in EMB and c.key() not in NODES and c.key() not in inl_all]
print(f"reachable theorems in no output: {len(lost)} {lost[:5]}")
big = sorted(plan["nodes"], key=lambda n: -n["solution_lines"])[:6]
print("largest solutions:", [(n["slug"], n["solution_lines"]) for n in big])
print("largest bundles:", sorted(((d["definition_name"], d["lines"]) for d in plan["definitions"]),
                                 key=lambda x: -x[1])[:5])
print("embedded with long proofs:", sorted(((c.fullname, c.plines) for c in emb if c.plines > 20),
                                           key=lambda x: -x[1])[:12])
print("candidates that had to stay embedded:", sorted(cmd(k).fullname for k in CAND - NODES))
if skipped_non_ascii:
    print("not nodes (non-ASCII or primed name):", skipped_non_ascii)
if skipped_attr:
    print("not nodes (carry attributes):", skipped_attr)
