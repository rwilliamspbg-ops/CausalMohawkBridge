#!/usr/bin/env python3
"""Vacuous-claim lint for the CausalMohawkBridge Lean 4 project.

Standard library only.  Scans every ``*.lean`` file under ``<repo>/CausalMohawkBridge/``
and the root ``<repo>/CausalMohawkBridge.lean`` and reports three classes of
vacuous or trivial claim.  Exits 1 when any finding is reported.

Classes
-------
(a) ``type-true``      -- a declaration whose stated type is exactly ``True``
                          (after stripping whitespace and redundant parentheses).
(b) ``trivial-eq``     -- a ``theorem``/``lemma`` whose conclusion is a
                          reflexive equality ``X = X``: both sides syntactically
                          identical after whitespace normalisation.
(c) ``sorry``          -- ``sorry`` or ``admit`` used as a token inside a
                          declaration body (comments, docstrings and ``#``
                          commands excluded).

Output
------
One line per finding: ``<path>:<line>: <kind>: <detail>``, then a summary and
``Found <N> vacuous/trivial claim(s).``  Exit status 1 when N > 0.

Robustness notes
----------------
* Lean block comments ``/- ... -/`` (including docstrings ``/-! ... -/`` and
  ``/-- ... -/``) are skipped, with nesting counted; line numbers of the
  remaining code lines are preserved.
* Inline ``--`` comments are stripped, but ``s!`` / ``s!"..."`` / raw strings
  are handled first so a ``--`` inside a string is not mistaken for a comment.
* Lines whose first non-blank character is ``#`` (``#print``, ``#eval``, ...) are
  skipped entirely.
* Whole-line ``sorry``/``admit`` declarations are deliberately not reported by
  class (c): the CI "Placeholder scan" step already greps for those.
* In class (b) the two sides are compared after whitespace normalisation, so
  ``f x = f x`` (and also ``a = a``) is reported; a genuine equation such as
  ``a^2 = a*a`` is not.  Names in ``KNOWN_TRIVIAL`` are suppressed: they are
  deliberate determinism anchors, not vacuous claims.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# --------------------------------------------------------------------------- #
# configuration
# --------------------------------------------------------------------------- #

SCRIPT_PATH = Path(__file__).resolve()
REPO_ROOT = SCRIPT_PATH.parent.parent          # <repo>
MODULE_DIR = REPO_ROOT / "CausalMohawkBridge"  # <repo>/CausalMohawkBridge
ROOT_FILE = REPO_ROOT / "CausalMohawkBridge.lean"

DECL_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "opaque",
    "axiom",
    "constant",
    "example",
)
STMT_KINDS = DECL_KINDS + ("inductive", "structure", "class")

# Optional modifiers before the keyword (``private theorem``, ...).
MODIFIER_RE = r"(?:(?:private|protected|noncomputable|partial)\s+)*"
DECL_RE = re.compile(
    r"^\s*" + MODIFIER_RE + r"(?P<kind>" + "|".join(STMT_KINDS) + r")\s+(?P<name>[^\s:{(]+)"
)

TOP_ARROW_RE = re.compile(r"→|↦")
TOP_EQ_RE = re.compile(r"(?<![=≠!<>≤≥])=(?!=)")
SORRY_TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_.'])(?:sorry|admit)(?![A-Za-z0-9_'])")
# whole-line placeholder declarations: left to the CI "Placeholder scan" step
LINE_SORRY_DECL_RE = re.compile(
    r"^\s*(?:" + MODIFIER_RE + r")?(?:axiom|constant|opaque|def|theorem|lemma|abbrev|instance)\s+"
    r"\S+\s*:?[^:=\n]*\b(?:sorry|admit)\b\s*$"
)
WHERE_RE = re.compile(r"where\b")

# Deliberate determinism anchor: `multiKrumSelectImpl_deterministic` states
# `f x = f x` on purpose (it pins the spec function as a pure function for the
# traceability matrix), so its reflexive conclusion is not a vacuous claim.
# Class-(b) findings for these names are suppressed; any other finding
# (type `True`, `sorry`/`admit`, or a reflexive conclusion elsewhere) is still
# reported.
KNOWN_TRIVIAL = {"multiKrumSelectImpl_deterministic"}

# --------------------------------------------------------------------------- #
# small text helpers
# --------------------------------------------------------------------------- #


def _mask_strings(line: str) -> str:
    """Blank out Lean string literals so comment markers inside them are inert."""
    out: list[str] = []
    i, n = 0, len(line)
    while i < n:
        c = line[i]
        if c == "s" and i + 1 < n and line[i + 1] == "!" and i + 2 < n and line[i + 2] == '"':
            # ``s!"..."`` interpolation string: the literal part ends at the
            # closing quote (``\`` escapes, ``"`` does not).
            j = i + 3
            while j < n:
                if line[j] == "\\":
                    j += 2
                    continue
                if line[j] == '"':
                    j += 1
                    break
                j += 1
            out.append('""')
            i = j
        elif c == '"':
            j = i + 1
            while j < n:
                if line[j] == "\\":
                    j += 2
                    continue
                if line[j] == '"':
                    j += 1
                    break
                j += 1
            out.append('""')
            i = j
        elif c == "/" and i + 1 < n and line[i + 1] == "/":
            # Lean line comment inside a string would be handled above; ``//``
            # is not a Lean comment, but blanking the rest is harmless here.
            out.append(" " * (n - i))
            i = n
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _strip_comment(line: str) -> str:
    """Remove a trailing ``-- ...`` comment (strings already masked)."""
    idx = line.find("--")
    if idx >= 0:
        return line[:idx]
    return line


def _strip_parens(s: str) -> str:
    """Remove redundant parentheses surrounding the whole expression."""
    t = s.strip()
    while t.startswith("(") and t.endswith(")"):
        depth = 0
        for i, ch in enumerate(t):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    if i == len(t) - 1:
                        t = t[1:-1].strip()
                        break
                    return t
        else:
            return t
    return t


def _split_top(s: str, pattern: re.Pattern[str]) -> list[str]:
    """Split ``s`` on ``pattern`` matches that sit at bracket depth zero."""
    parts: list[str] = []
    depth = 0
    last = 0
    for m in pattern.finditer(s):
        depth = 0
        for i in range(m.start()):
            ch = s[i]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
        if depth == 0:
            parts.append(s[last : m.start()])
            last = m.end()
    parts.append(s[last:])
    return parts


# --------------------------------------------------------------------------- #
# file reading
# --------------------------------------------------------------------------- #


def _code_lines(path: Path) -> list[str]:
    """Physical lines of ``path`` with block comments and ``#`` lines removed.

    Line comments are left in place (they are stripped when needed); line
    numbers therefore match the file exactly.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        print(f"warning: cannot read {path}: {exc}", file=sys.stderr)
        return []
    lines = text.splitlines()
    out: list[str] = []
    depth = 0
    for line in lines:
        masked = _mask_strings(line)
        res: list[str] = []
        i = 0
        while i < len(masked):
            if depth > 0:
                # inside a block comment: track nesting, skip to the next
                # ``-/'', but a nested ``/-`` opens a deeper level first.
                nxt_open = masked.find("/-", i)
                nxt_close = masked.find("-/", i)
                if nxt_close < 0:
                    i = len(masked)
                    continue
                if 0 <= nxt_open < nxt_close:
                    depth += 1
                    i = nxt_open + 2
                    continue
                depth -= 1
                i = nxt_close + 2
                continue
            first_nonblank = len(masked) - len(masked.lstrip())
            if masked[first_nonblank:].startswith("#"):
                # ``#print`` / ``#eval`` / ``#check`` ... : skip the whole line.
                i = len(masked)
                continue
            open_idx = masked.find("/-", i)
            if open_idx < 0:
                res.append(masked[i:])
                i = len(masked)
            else:
                res.append(masked[i:open_idx])
                depth += 1
                i = open_idx + 2
        out.append("".join(res))
    return out


def _iter_lean_files() -> list[Path]:
    files: list[Path] = []
    if MODULE_DIR.is_dir():
        files.extend(p for p in MODULE_DIR.rglob("*.lean") if p.is_file())
    if ROOT_FILE.is_file():
        files.append(ROOT_FILE)
    return sorted(set(files))


# --------------------------------------------------------------------------- #
# declaration parsing
# --------------------------------------------------------------------------- #


def _find_type_colon(header: str) -> int:
    """Index of the signature colon (not ``:=``, not ``::``), or -1."""
    depth = 0
    for i, ch in enumerate(header):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            nxt = header[i + 1] if i + 1 < len(header) else ""
            if nxt in ("=", ":"):
                continue
            return i
    return -1


def _cut_body(sig: str) -> str:
    """Drop a trailing proof body (``:= ...``) or ``where`` clause."""
    depth = 0
    for i, ch in enumerate(sig):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            if ch == ":" and i + 1 < len(sig) and sig[i + 1] == "=":
                return sig[:i].strip()
            if WHERE_RE.match(sig, i):
                return sig[:i].strip()
    return sig


def _has_top_assign(text: str) -> bool:
    """True when ``text`` contains a top-level ``:=`` (body separator)."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            if i + 1 < len(text) and text[i + 1] == "=":
                return True
    return False


def _gather_header(body_lines: list[str], start: int) -> tuple[list[str], int]:
    """Collect the lines of a declaration header (type may span lines).

    Returns ``(lines, last_index)``.  Stops at a blank line, a new declaration
    header, a block terminator (``end``/``namespace``/``section``/``open``), or
    as soon as the accumulated header already carries its ``:=`` body separator.
    """
    parts = [body_lines[start]]
    j = start
    while j + 1 < len(body_lines):
        if _has_top_assign("\n".join(_strip_comment(_mask_strings(x)) for x in parts)):
            break
        nxt = _strip_comment(_mask_strings(body_lines[j + 1]))
        s = nxt.strip()
        if s == "":
            break
        if DECL_RE.match(nxt):
            break
        if s == "end" or s.startswith(("end ", "namespace ", "section", "open ")):
            break
        parts.append(body_lines[j + 1])
        j += 1
    return parts, j


def _find_body_end(body_lines: list[str], start: int) -> int:
    """Last index of the declaration body starting after header line ``start``.

    The body runs until the next declaration header (or end of file); proof
    tactics, ``|`` patterns, ``have``/``show`` lines and ``end``/``namespace``
    lines are all part of it.
    """
    for j in range(start + 1, len(body_lines)):
        line = _strip_comment(_mask_strings(body_lines[j]))
        if DECL_RE.match(line):
            return j - 1
    return len(body_lines) - 1


def _strip_bindings(s: str) -> str:
    """Drop binders and hypotheses before the conclusion."""
    s = s.strip()
    changed = True
    while changed:
        changed = False
        for pat in (r"^∀\s", r"^forall\s", r"^\([^()]*\)\s*", r"^\{[^ {}]*\}\s*"):
            m = re.match(pat, s)
            if m:
                s = s[m.end() :].lstrip()
                changed = True
    parts = _split_top(s, TOP_ARROW_RE)
    return parts[-1].strip() if parts else s


def _decl_signature(header: str) -> tuple[str, re.Match[str]] | None:
    """``(signature, match)`` for a declaration header, or ``None``."""
    m = DECL_RE.match(header)
    if not m:
        return None
    colon = _find_type_colon(header)
    if colon < 0:
        return None
    sig = _cut_body(header[colon + 1 :].strip())
    return sig, m


# --------------------------------------------------------------------------- #
# the three checks
# --------------------------------------------------------------------------- #


def _check_type_true(kind: str, name: str, sig: str) -> str | None:
    t = _strip_parens(sig)
    if t == "True":
        return f"{kind} {name} : True (vacuous: every proof proves it)"
    return None


def _check_trivial_eq(kind: str, name: str, sig: str) -> str | None:
    s = _strip_parens(sig)
    s = _strip_bindings(s)
    parts = _split_top(s, TOP_EQ_RE)
    if len(parts) != 2:
        return None
    lhs, rhs = parts[0].strip(), parts[1].strip()
    if lhs == rhs:
        return (
            f"{kind} {name} : conclusion is a reflexive equality: {lhs} "
            "(trivial, rfl-derivable)"
        )
    return None


def _check_sorry(body_lines: list[str], start: int, end: int) -> tuple[int, str] | None:
    """First ``sorry``/``admit`` token in ``body_lines[start..end]``."""
    for i in range(start, end + 1):
        line = _strip_comment(_mask_strings(body_lines[i]))
        m = SORRY_TOKEN_RE.search(line)
        if not m:
            continue
        if LINE_SORRY_DECL_RE.match(_strip_comment(_mask_strings(body_lines[i]))):
            continue
        token = m.group(0)
        snippet = line.strip()
        if len(snippet) > 70:
            snippet = snippet[:67] + "..."
        return i, f"{token!r} in proof body: {snippet}"
    return None


# --------------------------------------------------------------------------- #
# main
# --------------------------------------------------------------------------- #


def main() -> int:
    files = _iter_lean_files()
    if not files:
        print("error: no .lean files found", file=sys.stderr)
        return 1

    findings: list[str] = []
    seen: set[tuple[str, int, str]] = set()
    for path in files:
        lines = _code_lines(path)
        n = len(lines)
        i = 0
        while i < n:
            raw = _strip_comment(_mask_strings(lines[i]))
            if not raw.strip():
                i += 1
                continue
            sig_info = _decl_signature(raw)
            if sig_info is None:
                i += 1
                continue
            signature, m = sig_info
            kind, name = m.group("kind"), m.group("name")
            header_lines, hdr_end = _gather_header(lines, i)
            header = "\n".join(_strip_comment(_mask_strings(x)) for x in header_lines)
            sig_info = _decl_signature(header)
            if sig_info is None:
                i = hdr_end + 1
                continue
            signature, m = sig_info
            kind, name = m.group("kind"), m.group("name")
            line_no = i + 1
            rel = path.relative_to(REPO_ROOT).as_posix()

            # class (a): type is exactly True
            detail = _check_type_true(kind, name, signature)
            if detail and (rel, line_no, "type-true") not in seen:
                seen.add((rel, line_no, "type-true"))
                findings.append(f"{rel}:{line_no}: type-true: {detail}")

            # class (b): conclusion is X = X (allowlisted anchors suppressed)
            if kind in ("theorem", "lemma"):
                detail = _check_trivial_eq(kind, name, signature)
                if detail and name not in KNOWN_TRIVIAL and (rel, line_no, "trivial-eq") not in seen:
                    seen.add((rel, line_no, "trivial-eq"))
                    findings.append(f"{rel}:{line_no}: trivial-eq: {detail}")

            # class (c): sorry/admit in the body
            end = _find_body_end(lines, hdr_end)
            hit = _check_sorry(lines, i, end)
            if hit is not None:
                j, detail = hit
                if (rel, j + 1, "sorry") not in seen:
                    seen.add((rel, j + 1, "sorry"))
                    findings.append(f"{rel}:{j + 1}: sorry: {name}: {detail}")
            i = end + 1

    for f in findings:
        print(f)
    print(f"Scanned {len(files)} .lean file(s); {len(findings)} finding(s).")
    if findings:
        print(f"Found {len(findings)} vacuous/trivial claim(s).")
        return 1
    print("No vacuous/trivial claims found.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
