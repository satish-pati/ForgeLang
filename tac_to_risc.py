import re
import sys
import json
import os
_var_types = {}
_symtab_array_sizes = {}   
_symtab_var_types   = {}   
_global_scalars     = {}   
_global_arrays      = set()  
_local_var_names    = set()  
_BASE_TYPE_MAP = {
    'int':          'int',
    'long':         'long',
    'short':        'short',
    'char':         'char',
    'float':        'float',
    'double':       'double',
    'const int':    'int',
    'const long':   'long',
    'const short':  'short',
    'const char':   'char',
    'const float':  'float',   # Bug fix 1: fixed @float constants were normalised to 'int'
    'const double': 'double',  # Bug fix 1: same for double
}
def load_symtab_json(path="symtab.json"):
    global _symtab_array_sizes, _symtab_var_types, _global_scalars, _global_arrays, _local_var_names
    if not os.path.exists(path):
        return
    try:
        with open(path) as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        return
    for scope in data.get("scopes", []):
        scope_id    = scope.get("scope_id", scope.get("id", -1))
        scope_label = scope.get("label", scope.get("name", "")).lower()
        is_global   = (scope_id == 0 or scope_label in ("global", "[global]"))
        for sym in scope.get("symbols", []):
            name      = sym.get("name", "")
            base_type = sym.get("base_type", "int").lower().strip()
            category  = sym.get("category", "scalar")
            dim_count = sym.get("dim_count", 0)
            dims      = sym.get("dimensions", [])
            normalised = _BASE_TYPE_MAP.get(base_type, base_type if base_type.startswith('ptr:') else 'int')
            _symtab_var_types[name] = normalised
            if dim_count > 0 and dims:
                total = 1
                for d in dims:
                    total *= d
                _symtab_array_sizes[name] = total
                if is_global:
                    _global_arrays.add(name)
            elif category in ("array", "multi-dim array"):
                elem_size   = sym.get("elem_size", 4) or 4
                total_bytes = sym.get("total_bytes", 0)
                if total_bytes > 0 and elem_size > 0:
                    _symtab_array_sizes[name] = total_bytes // elem_size
                if is_global:
                    _global_arrays.add(name)
            elif is_global and category == "scalar":
                _global_scalars[name] = normalised
            elif not is_global and category == "scalar":
                _local_var_names.add(name)
def set_type(var, typ):
    _var_types[var] = typ
def get_type(var):
    return _var_types.get(var, 'int')
def is_long_type(var):
    return get_type(var) == 'long'
def is_short_type(var):
    return get_type(var) == 'short'
def is_char_type(var):
    return get_type(var) == 'char'
def is_float_type(var):
    return get_type(var) in ('float', 'double')
def is_double_type(var):
    return get_type(var) == 'double'
def load_ins(var):
    t = get_type(var)
    if t == 'long':            return 'ld'
    if t == 'short':           return 'lh'
    if t == 'char':            return 'lb'
    if t.startswith('ptr:'):   return 'ld'   
    return 'lw'
def store_ins(var):
    t = get_type(var)
    if t == 'long':            return 'sd'
    if t == 'short':           return 'sh'
    if t == 'char':            return 'sb'
    if t.startswith('ptr:'):   return 'sd'   
    return 'sw'
def print_fmt(var):
    t = _global_scalars.get(var, get_type(var))
    if t == 'long':            return '.fmt_long'
    if t in ('float','double'): return '.fmt_float'
    if t == 'char':             return '.fmt_char'
    return '.fmt_int'
def scan_fmt(var):
    t = _global_scalars.get(var, get_type(var))
    if t == 'long':             return '.fmt_scan_long'
    if t in ('float','double'): return '.fmt_scan_float'
    return '.fmt_scan_int'
def is_int_literal(v):
    try:
        int(v)
        return True
    except (ValueError, TypeError):
        return False
def is_num_literal(v):
    try:
        float(v)
        return True
    except (ValueError, TypeError):
        return False
def to_int(v):
    return int(float(v))
def fits_in_32bit(v): 
    try:
        n = int(v)
        return -2147483648 <= n <= 2147483647
    except (ValueError, TypeError):
        return True
def int_to_double_ins(val_str, src_type=None):
    if is_int_literal(val_str) and not fits_in_32bit(val_str):
        return "fcvt.d.l"
    return "fcvt.d.w"
def int_to_float_ins(val_str, src_type=None):
    if is_int_literal(val_str) and not fits_in_32bit(val_str):
        return "fcvt.s.l"
    return "fcvt.s.w"
def parse_line(raw):
    raw = raw.strip()
    m = re.match(r'^(\d+)\s+(.*)', raw)
    return (int(m.group(1)), m.group(2).strip()) if m else (None, raw)
def _extract_defs_uses(instr):
    KEYWORDS = {'BeginFunc','EndFunc','PopParam','PushParam','Return',
                'Call','goto','if','int','float','char','double',
                'long','short',
                'printint','printfloat','printchar','printstring',
                'inputint','inputfloat','inputchar','inputstring',
                'rtz','main','eq','ne','lt','le','gt','ge','true','false'}
    defs, uses = set(), set()
    def is_var(t):
        return bool(re.match(r'^[A-Za-z_]\w*$', t)) and t not in KEYWORDS
    m = re.match(r'^(\w+)\s*=\s*ref\s+(\w+)$', instr)
    if m:
        defs.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*deref\s+(\w+)$', instr)
    if m:
        defs.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        return defs, uses
    m = re.match(r'^deref\s+(\w+)\s*=\s*(\S+)$', instr)
    if m:
        if is_var(m.group(1)): uses.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*ALLOC\s+(\w+)\s*\*\s*(\w+)$', instr)
    if m:
        defs.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        if is_var(m.group(3)): uses.add(m.group(3))
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*CALLOC\s+(\w+)\s*,\s*(\w+)$', instr)
    if m:
        defs.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        if is_var(m.group(3)): uses.add(m.group(3))
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*REALLOC\s+(\w+)\s*,\s*(\w+)\s*\*\s*(\w+)$', instr)
    if m:
        defs.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        if is_var(m.group(3)): uses.add(m.group(3))
        if is_var(m.group(4)): uses.add(m.group(4))
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*REALLOC\s+(\w+)\s*,\s*(\w+)$', instr)
    if m:
        defs.add(m.group(1))
        if is_var(m.group(2)): uses.add(m.group(2))
        if is_var(m.group(3)): uses.add(m.group(3))
        return defs, uses
    m = re.match(r'^FREE\s+(\S+)$', instr)
    if m:
        tok = m.group(1)
        if is_var(tok): uses.add(tok)
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*\(ptr:[^)]+\)\s*(\S+)$', instr)
    if m:
        defs.add(m.group(1))
        tok = m.group(2)
        if is_var(tok): uses.add(tok)
        return defs, uses
    if re.match(r'^(BeginFunc|EndFunc)\b', instr):
        return defs, uses
    m = re.match(r'^PopParam\s+(\w+)$', instr)
    if m:
        defs.add(m.group(1)); return defs, uses
    m = re.match(r'^Return\s+(\S+)$', instr)
    if m:
        tok = m.group(1)
        if is_var(tok): uses.add(tok)
        return defs, uses
    m = re.match(r'^PushParam\s+(.+)$', instr)
    if m:
        raw = m.group(1).strip()
        cast_m = re.match(r'^\(\w+\)\s*(.+)$', raw)
        tok = cast_m.group(1).strip() if cast_m else raw
        if tok.startswith('&'):
            tok = tok[1:].strip()
        if is_var(tok): uses.add(tok)
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*Call\s+\w+$', instr)
    if m:
        defs.add(m.group(1)); return defs, uses
    if re.match(r'^Call\s+\w+$', instr):
        return defs, uses
    m = re.match(r'^(?:print|input)\w+\s+(\S+)$', instr)
    if m:
        tok = m.group(1)
        if is_var(tok): uses.add(tok)
        return defs, uses
    m = re.match(r'^if\s+(\S+)\s+\S+\s+(\S+)\s+goto\s+\d+$', instr)
    if m:
        for tok in (m.group(1), m.group(2)):
            if is_var(tok):
                uses.add(tok)
            else:
                am = re.match(r'^(\w+)\[(\w+)\]$', tok)
                if am:
                    if is_var(am.group(1)): uses.add(am.group(1))
                    if is_var(am.group(2)): uses.add(am.group(2))
        return defs, uses
    if re.match(r'^goto\s+\d+$', instr):
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*(\S+)\s*(<=|>=|==|!=|<<|>>|[+\-*/%&|^<>])\s*(\S+)$', instr)
    if m:
        op1 = m.group(2)
        if not (re.match(r'^[A-Za-z_]\w*(\[\w+\])?$', op1) or is_num_literal(op1)):
            m = None
    if m:
        defs.add(m.group(1))
        for tok in (m.group(2), m.group(4)):
            arr_m = re.match(r'^(\w+)\[(\w+)\]$', tok)
            if arr_m:
                for t in (arr_m.group(1), arr_m.group(2)):
                    if is_var(t): uses.add(t)
            elif is_var(tok):
                uses.add(tok)
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*(\w+)\[(\w+)\]$', instr)
    if m:
        defs.add(m.group(1))
        for tok in (m.group(2), m.group(3)):
            if is_var(tok): uses.add(tok)
        return defs, uses
    m = re.match(r'^(\w+)\[(\w+)\]\s*=\s*(\S+)$', instr)
    if m:
        for tok in (m.group(1), m.group(2)):
            if is_var(tok): uses.add(tok)
        rhs = m.group(3)
        rhs_arr_m = re.match(r'^(\w+)\[(\w+)\]$', rhs)
        if rhs_arr_m:
            for tok in (rhs_arr_m.group(1), rhs_arr_m.group(2)):
                if is_var(tok): uses.add(tok)
        elif is_var(rhs):
            uses.add(rhs)
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*\(\w+\)\s*(\S+)$', instr)
    if m:
        defs.add(m.group(1))
        tok = m.group(2)
        if is_var(tok): uses.add(tok)
        return defs, uses
    m = re.match(r'^(\w+)\s*=\s*(\S+)$', instr)
    if m:
        defs.add(m.group(1))
        tok = m.group(2)
        if is_var(tok): uses.add(tok)
        return defs, uses
    return defs, uses
def _liveness_analysis(instrs):
    n = len(instrs)
    if n == 0:
        return [], []
    lnum_to_idx = {lnum: i for i, (lnum, _) in enumerate(instrs)}
    succ = [[] for _ in range(n)]
    for i, (lnum, instr) in enumerate(instrs):
        if i + 1 < n:
            succ[i].append(i + 1)
        for m in re.finditer(r'goto\s+(\d+)', instr):
            tgt = int(m.group(1))
            if tgt in lnum_to_idx:
                succ[i].append(lnum_to_idx[tgt])
        if re.match(r'^goto\s+\d+$', instr.strip()):
            tgt = int(re.search(r'\d+', instr).group())
            succ[i] = [lnum_to_idx[tgt]] if tgt in lnum_to_idx else []
    defs_list  = []
    uses_list  = []
    for _, instr in instrs:
        d, u = _extract_defs_uses(instr)
        defs_list.append(d)
        uses_list.append(u)
    live_in  = [set() for _ in range(n)]
    live_out = [set() for _ in range(n)]
    changed = True
    while changed:
        changed = False
        for i in range(n - 1, -1, -1):
            new_out = set()
            for s in succ[i]:
                new_out |= live_in[s]
            new_in  = uses_list[i] | (new_out - defs_list[i])
            if new_in != live_in[i] or new_out != live_out[i]:
                live_in[i]  = new_in
                live_out[i] = new_out
                changed = True
    return live_in, live_out
def _compute_live_across_calls(instrs):
    if not instrs:
        return set()
    live_in, live_out = _liveness_analysis(instrs)
    def _is_call_site(instr):
        s = instr.strip()
        return (re.match(r'^(print|input)\w+', s) or
                re.match(r'^\w+\s*=\s*Call\b', s) or
                re.match(r'^Call\b', s) or
                re.match(r'^FREE\b', s) or
                re.search(r'\b(ALLOC|CALLOC|REALLOC)\b', s))
    live_across = set()
    for i, (_, instr) in enumerate(instrs):
        if _is_call_site(instr):
            live_across |= live_out[i]
    return live_across
class RegAlloc:
    SAVED_POOL  = ["s1","s2","s3","s4","s5",
                   "s6","s7","s8","s9","s10","s11"]
    CALLER_POOL = ["t0","t1","t2","t3"]
    DEAD_POOL   = ["t4","t5","t6"]
    FP_CALLER_POOL = ["ft0","ft1","ft2","ft3","ft4","ft5","ft6","ft7",
                      "ft8","ft9","ft10","ft11"]
    FP_SAVED_POOL  = ["fs0","fs1","fs2","fs3","fs4","fs5","fs6","fs7",
                      "fs8","fs9","fs10","fs11"]
    K              = len(SAVED_POOL) + len(CALLER_POOL) + len(DEAD_POOL)
    SREG_SAVE_BASE = 16
    SREG_SLOTS     = 11
    TEMP_SCRATCH_MAP = {
        "t0": "t0", "t1": "t1", "t2": "t2", "t3": "t3",
    }
    def __init__(self):
        self._map         = {}
        self._spill       = {}
        self.spill_slots  = 0
        self.used_sregs   = []
        self.used_fp_sregs = []
        self._float_vars  = set()
        self._string_vars = set()
        self._array_names = set()
        self._safe_scratch     = set()
        self._no_call_crossing = set()
        self._fp_no_call_crossing = set()
        self._spill_base  = 16 + 11 * 8
        self._shadow_locals = set() 
    def set_safe_scratch_temps(self, instrs):
        if instrs and isinstance(instrs[0], str):
            pairs = list(enumerate(instrs))
        else:
            pairs = list(instrs)
        if not pairs:
            self._safe_scratch     = set(self.TEMP_SCRATCH_MAP.keys())
            self._no_call_crossing = set()
            return
        all_vars = set()
        for _, instr in pairs:
            d, u = _extract_defs_uses(instr)
            all_vars |= d | u
        all_vars -= (set(_global_scalars.keys()) - self._shadow_locals)
        live_across = _compute_live_across_calls(pairs)
        safe_from_calls = all_vars - live_across
        all_tac_temps = set(self.TEMP_SCRATCH_MAP.keys())
        self._safe_scratch = (safe_from_calls & all_tac_temps) - {
            v for v in all_tac_temps if get_type(v) in ('float', 'double')
        }
        self._no_call_crossing = {
            v for v in safe_from_calls
            if not re.match(r'^t\d+$', v)
            and get_type(v) not in ('float','double')
            and v not in self._array_names
        }
        self._fp_no_call_crossing = {
            v for v in safe_from_calls
            if get_type(v) in ('float', 'double')
            and v not in self._array_names
        }
    @staticmethod
    def _compute_dead_after_def(instrs):
        if not instrs:
            return set()
        live_in, live_out = _liveness_analysis(instrs)
        def_site = {}
        for i, (_, instr) in enumerate(instrs):
            defs, _ = _extract_defs_uses(instr)
            for v in defs:
                def_site[v] = i
        used_anywhere = set()
        for _, instr in instrs:
            _, uses = _extract_defs_uses(instr)
            used_anywhere |= uses
        dead_after_def = set()
        for v, i in def_site.items():
            if v not in used_anywhere or v not in live_out[i]:
                dead_after_def.add(v)
        return dead_after_def
    def run_graph_coloring(self, instrs):
        if not instrs:
            return
        live_in, live_out = _liveness_analysis(instrs)
        dead_after_def = self._compute_dead_after_def(instrs)
        all_vars = set()
        for _, instr in instrs:
            d, u = _extract_defs_uses(instr)
            all_vars |= d | u
        all_vars -= (set(_global_scalars.keys()) - self._shadow_locals)
        forced_spill = set()
        for v in all_vars:
            is_tac_temp  = bool(re.match(r'^t\d+$', v))
            is_fp_var    = get_type(v) in ('float', 'double') and v not in self._array_names
            in_safe_scratch   = v in self._safe_scratch
            in_fp_no_crossing = v in self._fp_no_call_crossing
            in_fp_saved_ok    = is_fp_var and not in_fp_no_crossing
            if is_tac_temp and not in_safe_scratch and not is_fp_var:
                pass
            elif is_tac_temp and is_fp_var and not in_fp_no_crossing:
                forced_spill.add(v)
            elif is_fp_var and not is_tac_temp and not in_fp_no_crossing and not in_fp_saved_ok:
                pass
        self._float_vars = {v for v in forced_spill
                            if get_type(v) in ('float', 'double')}
        colorable = sorted(all_vars - forced_spill)
        colorable_set = set(colorable)
        adj = {v: set() for v in colorable}
        def add_edge(a, b):
            if a != b and a in adj and b in adj:
                adj[a].add(b)
                adj[b].add(a)
        for i, (_, instr) in enumerate(instrs):
            live_out_i = live_out[i] & colorable_set
            defs, _    = _extract_defs_uses(instr)
            copy_m = re.match(r'\A(\w+)\s*=\s*([A-Za-z_]\w*)\s*\Z', instr)
            copy_dst = copy_m.group(1) if copy_m else None
            copy_src = copy_m.group(2) if copy_m else None
            for d in (defs & colorable_set):
                for v in live_out_i:
                    if d == copy_dst and v == copy_src:
                        continue
                    add_edge(d, v)
            lv = list(live_out_i)
            for ii in range(len(lv)):
                for jj in range(ii + 1, len(lv)):
                    add_edge(lv[ii], lv[jj])
            live_in_i = live_in[i] & colorable_set
            li2 = list(live_in_i)
            for ii in range(len(li2)):
                for jj in range(ii + 1, len(li2)):
                    a, b = li2[ii], li2[jj]
                    if copy_dst and copy_src:
                        if (a == copy_dst and b == copy_src) or \
                           (a == copy_src and b == copy_dst):
                            continue
                    add_edge(a, b)
        for arr_var in self._array_names:
            if arr_var in colorable_set:
                for other in colorable_set:
                    add_edge(arr_var, other)
        stack            = []
        optimistic_spill = set()
        remaining        = set(colorable)
        def _sorted_remaining():
            return sorted(remaining, key=lambda v: (len(adj[v] & remaining), v))
        last_use = {}
        for i, (_, instr) in enumerate(instrs):
            _, uses = _extract_defs_uses(instr)
            for v in uses:
                last_use[v] = i
        def _spill_score(v):
            if v not in last_use:
                return (float('inf'), len(adj[v] & remaining), v)
            return (last_use[v], len(adj[v] & remaining), v)
        while remaining:
            candidate = next(
                (v for v in _sorted_remaining() if len(adj[v] & remaining) < self.K),
                None
            )
            if candidate is None:
                candidate = max(_sorted_remaining(), key=_spill_score)
                optimistic_spill.add(candidate)
            remaining.remove(candidate)
            stack.append((candidate, adj[candidate] & remaining))
        color   = {}
        spilled = set()
        while stack:
            v, neighbors = stack.pop()
            used = {color[n] for n in adj[v] if n in color}
            is_array_base    = (v in self._array_names)
            is_tac_safe_temp = (v in self._safe_scratch)
            if not is_tac_safe_temp:
                for n in adj[v]:
                    if n in self._safe_scratch and n in self.TEMP_SCRATCH_MAP:
                        used.add(self.TEMP_SCRATCH_MAP[n])
            crosses_call     = (v not in self._no_call_crossing
                                and not is_tac_safe_temp)
            if is_tac_safe_temp:
                color[v] = self.TEMP_SCRATCH_MAP.get(v, v)
                continue
            is_fp_var = (get_type(v) in ('float', 'double') and v not in self._array_names)
            if is_fp_var:
                if v in self._fp_no_call_crossing:
                    assigned = next(
                        (r for r in self.FP_CALLER_POOL if r not in used), None)
                    if assigned is None:
                        assigned = next(
                            (r for r in self.FP_SAVED_POOL if r not in used), None)
                else:
                    assigned = next(
                        (r for r in self.FP_SAVED_POOL if r not in used), None)
                if assigned:
                    color[v] = assigned
                else:
                    spilled.add(v)
                continue
            if crosses_call or is_array_base:
                assigned = next(
                    (r for r in self.SAVED_POOL if r not in used), None)
            else:
                assigned = next(
                    (r for r in self.CALLER_POOL if r not in used), None)
                if assigned is None and v in dead_after_def:
                    assigned = next(
                        (r for r in self.DEAD_POOL if r not in used), None)
                if assigned is None:
                    assigned = next(
                        (r for r in self.SAVED_POOL if r not in used), None)
            if assigned:
                color[v] = assigned
            else:
                spilled.add(v)
        used_regs_set = set()
        used_fp_sregs_set = set()
        for v, reg in color.items():
            if v not in spilled:
                self._map[v] = reg
                if reg in self.SAVED_POOL:
                    used_regs_set.add(reg)
                elif reg in self.FP_SAVED_POOL:
                    used_fp_sregs_set.add(reg)
                if get_type(v) in ('float', 'double') and v not in spilled:
                    self._float_vars.discard(v)
        for v in all_vars:
            if v in self._safe_scratch and v in self.TEMP_SCRATCH_MAP:
                self._map[v] = self.TEMP_SCRATCH_MAP[v]
        self.used_sregs = [r for r in self.SAVED_POOL if r in used_regs_set]
        self.used_fp_sregs = [r for r in self.FP_SAVED_POOL if r in used_fp_sregs_set]
        self._recompute_spill_base()
        for v in sorted(forced_spill):
            self.spill_slots += 1
            self._spill[v] = -(self._spill_base + self.spill_slots * 8)
        for v in sorted(spilled):
            if v not in self._spill:
                self.spill_slots += 1
                self._spill[v] = -(self._spill_base + self.spill_slots * 8)
    def _recompute_spill_base(self):
        header = 16
        self._spill_base = header + len(self.used_sregs) * 8 + len(self.used_fp_sregs) * 8
    def _alloc(self, var):
        if var in self._safe_scratch and var in self.TEMP_SCRATCH_MAP:
            hw = self.TEMP_SCRATCH_MAP[var]
            self._map[var] = hw
            return hw
        if re.match(r'^t\d+$', var) and var not in self._safe_scratch:
            self.spill_slots += 1
            off = -(self._spill_base + self.spill_slots * 8)
            self._spill[var] = off
            return None
        if (get_type(var) in ('float', 'double') and var not in self._array_names):
            used = set(self._map.values())
            if var in self._fp_no_call_crossing:
                for reg in self.FP_CALLER_POOL:
                    if reg not in used:
                        self._map[var] = reg
                        return reg
                for reg in self.FP_SAVED_POOL:
                    if reg not in used:
                        self._map[var] = reg
                        if reg not in self.used_fp_sregs:
                            self.used_fp_sregs.append(reg)
                        return reg
            else:
                for reg in self.FP_SAVED_POOL:
                    if reg not in used:
                        self._map[var] = reg
                        if reg not in self.used_fp_sregs:
                            self.used_fp_sregs.append(reg)
                        return reg
            self.spill_slots += 1
            off = -(self._spill_base + self.spill_slots * 8)
            self._spill[var] = off
            if get_type(var) in ('float', 'double'):
                self._float_vars.add(var)
            return None
        used = set(self._map.values())
        is_array_base = (var in self._array_names)
        crosses_call  = (var not in self._no_call_crossing)
        if not re.match(r'^t\d+$', var) and not crosses_call and not is_array_base:
            for tac_tmp, hw in self.TEMP_SCRATCH_MAP.items():
                if tac_tmp in self._safe_scratch:
                    used.add(hw)
        if crosses_call or is_array_base:
            for reg in self.SAVED_POOL:
                if reg not in used:
                    self._map[var] = reg
                    if reg not in self.used_sregs:
                        self.used_sregs.append(reg)
                    return reg
        else:
            for reg in self.CALLER_POOL:
                if reg not in used:
                    self._map[var] = reg
                    return reg
            for reg in self.SAVED_POOL:
                if reg not in used:
                    self._map[var] = reg
                    if reg not in self.used_sregs:
                        self.used_sregs.append(reg)
                    return reg
        self.spill_slots += 1
        off = -(self._spill_base + self.spill_slots * 8)
        self._spill[var] = off
        return None
    def reg(self, var):
        if var not in self._map and var not in self._spill:
            self._alloc(var)
        return self._map.get(var)
    def is_spilled(self, var):
        if var not in self._map and var not in self._spill:
            self._alloc(var)
        return var in self._spill
    def spill_offset(self, var):
        return self._spill[var]
    def ensure(self, var):
        if var not in self._map and var not in self._spill:
            self._alloc(var)
    def force_spill(self, var):
        if var in self._spill:
            return self._spill[var]
        if var in self._map:
            freed = self._map.pop(var)
            if freed in self.used_sregs:
                self.used_sregs.remove(freed)
        self.spill_slots += 1
        off = -(self._spill_base + self.spill_slots * 8)
        self._spill[var] = off
        return off
def _copy_propagate(tac):
    KEYWORDS = {'BeginFunc','EndFunc','PopParam','PushParam','Return',
                'Call','goto','if','int','float','char','double',
                'long','short',
                'printint','printfloat','printchar','printstring',
                'inputint','inputfloat','inputchar','inputstring',
                'rtz','main','eq','ne','lt','le','gt','ge','true','false'}
    def _is_plain_var(tok):
        return bool(re.match(r'^[A-Za-z_]\w*$', tok)) and tok not in KEYWORDS
    _ref_param_vars: set = set()
    instrs_only = [instr for _, instr in tac]
    for idx, instr in enumerate(instrs_only):
        pm = re.match(r'^PushParam\s+&([A-Za-z_]\w*)\s*$', instr.strip())
        if not pm:
            continue
        push_group = []
        for k in range(idx, -1, -1):
            pp = re.match(r'^PushParam\s+(.+)$', instrs_only[k].strip())
            if pp:
                push_group.insert(0, pp.group(1).strip())
            elif re.match(r'^(BeginFunc|EndFunc)\b', instrs_only[k].strip()):
                break
            elif k < idx and re.match(r'^(?:\w+\s*=\s*)?Call\b', instrs_only[k].strip()):
                break
        call_fname = None
        for k in range(idx + 1, len(instrs_only)):
            cm = re.match(r'^(?:\w+\s*=\s*)?Call\s+(\w+)\s*$', instrs_only[k].strip())
            if cm:
                call_fname = cm.group(1)
                break
            if not re.match(r'^PushParam\b', instrs_only[k].strip()):
                break
        if not call_fname:
            continue
        ref_positions = {i for i, a in enumerate(push_group) if a.startswith('&')}
        in_callee = False
        pop_idx_c = 0
        for k, ci in enumerate(instrs_only):
            bm = re.match(rf'^BeginFunc\s+{re.escape(call_fname)}\b', ci.strip())
            if bm:
                in_callee = True
                pop_idx_c = 0
                continue
            if in_callee:
                if re.match(r'^EndFunc\b', ci.strip()):
                    break
                ppm = re.match(r'^PopParam\s+(\w+)\s*$', ci.strip())
                if ppm:
                    if pop_idx_c in ref_positions:
                        _ref_param_vars.add(ppm.group(1))
                    pop_idx_c += 1
    changed = True
    while changed:
        changed = False
        lnums  = [lnum  for lnum, _ in tac]
        instrs = [instr for _, instr in tac]
        n      = len(instrs)
        jump_targets = set()
        for instr in instrs:
            for m in re.finditer(r'goto\s+(\d+)', instr):
                jump_targets.add(int(m.group(1)))
        remove      = set()
        new_instrs  = list(instrs)
        for i in reversed(range(n)):
            instr = new_instrs[i]
            m = re.match(r'^(\w+)\s*=\s*([A-Za-z_]\w*)\s*$', instr)
            if not m:
                continue
            dst, src = m.group(1), m.group(2)
            if not (_is_plain_var(dst) and _is_plain_var(src)):
                continue
            if dst in _ref_param_vars or src in _ref_param_vars:
                continue
            if dst == src:
                if lnums[i] not in jump_targets:
                    remove.add(i)
                    changed = True
                continue
            if lnums[i] in jump_targets:
                continue
            dst_uses      = []
            src_kill_idx  = None
            has_back_edge = False
            dst_redefined_after = False
            dst_redef_idx = None
            for j in range(i + 1, n):
                defs_j, uses_j = _extract_defs_uses(new_instrs[j])
                if dst in defs_j:
                    dst_redefined_after = True
                    dst_redef_idx = j
                    break
                if src_kill_idx is None and src in defs_j:
                    src_kill_idx = j
                if dst in uses_j:
                    dst_uses.append(j)
                for bm in re.finditer(r'goto\s+(\d+)', new_instrs[j]):
                    tgt = int(bm.group(1))
                    if tgt <= lnums[i]:
                        has_back_edge = True
            if has_back_edge:
                continue
            bypass_unsafe = False
            if dst_uses:
                def_lnum = lnums[i]
                for k in range(n):
                    if k == i:
                        continue
                    for bm in re.finditer(r'goto\s+(\d+)', new_instrs[k]):
                        goto_lnum = int(bm.group(1))
                        src_lnum  = lnums[k]

                        if src_lnum < def_lnum and goto_lnum > def_lnum:
                            bypass_unsafe = True
                            break
                    if bypass_unsafe:
                        break
            if bypass_unsafe:
                continue
            if dst_redefined_after and dst_uses:
                last_use_lnum = lnums[dst_uses[-1]]
                redef_lnum    = lnums[dst_redef_idx]
                unsafe = False
                for k in range(i, n):
                    for bm in re.finditer(r'goto\s+(\d+)', new_instrs[k]):
                        tgt_lnum = int(bm.group(1))
                        if lnums[i] < tgt_lnum <= last_use_lnum:
                            unsafe = True
                            break
                        if tgt_lnum <= lnums[i]:
                            unsafe = True
                            break
                        if k < dst_redef_idx and tgt_lnum > redef_lnum:
                            unsafe = True
                            break
                    if unsafe:
                        break
                if unsafe:
                    continue
            if not dst_uses:
                remove.add(i)
                changed = True
                continue
            if src_kill_idx is not None and src_kill_idx <= max(dst_uses):
                continue
            src_is_temp = bool(re.match(r'^t\d+$', src))
            safe_uses = []
            unsafe_found = False
            for j in dst_uses:
                instr_j = new_instrs[j]
                if src_is_temp:
                    arr_write_m = re.match(r'^(\w+)\[(\w+)\]\s*=\s*(.+)$', instr_j)
                    if arr_write_m and arr_write_m.group(2) == dst:
                        unsafe_found = True
                        break
                    arr_read_m = re.match(r'^(\w+)\s*=\s*(\w+)\[(\w+)\]$', instr_j)
                    if arr_read_m and arr_read_m.group(3) == dst:
                        unsafe_found = True
                        break
                safe_uses.append(j)
            if unsafe_found:
                continue
            any_skipped = False
            for j in safe_uses:
                old = new_instrs[j]
                if re.match(r'^print(float|double)\s+' + re.escape(dst) + r'$', old):
                    src_type = get_type(src) if re.match(r'^[A-Za-z_]\w*$', src) else 'int'
                    if src_type not in ('float', 'double'):
                        any_skipped = True
                        continue  
                if re.match(r'^PushParam\s+&', old):
                    any_skipped = True
                    continue
                new_instr = re.sub(r'\b' + re.escape(dst) + r'\b', src, old)
                if new_instr != old:
                    new_instrs[j] = new_instr
                    changed = True
            if not any_skipped:
                remove.add(i)
                changed = True
        tac = [(lnum, instr)
               for i, (lnum, instr) in enumerate(zip(lnums, new_instrs))
               if i not in remove]
    return tac
FRAME = 512
def _compute_frame(n_sregs, n_spill_slots, needs_ra, needs_fp):
    if n_spill_slots > 0:
        needs_fp = True  
    header = (8 if needs_ra else 0) + (8 if needs_fp else 0)
    ra_s0_slots = 16          
    min_for_spills = ra_s0_slots + n_sregs * 8 + n_spill_slots * 8
    size = max(header + n_sregs * 8 + n_spill_slots * 8, min_for_spills)
    if size % 16:
        size += 16 - (size % 16)
    return max(size, 16)
class TACtoRISCV:
    BRANCH_MAP = {
        '==': ("beq", False), 'eq': ("beq", False),
        '!=': ("bne", False), 'ne': ("bne", False),
        '<' : ("blt", False), 'lt': ("blt", False),
        '>=': ("bge", False), 'ge': ("bge", False),
        '>' : ("blt", True),  'gt': ("blt", True),
        '<=': ("bge", True),  'le': ("bge", True),
    }
    BINOP_MAP = {
        '+' : ("add",  "addi"),
        '-' : ("sub",  None),
        '*' : ("mul",  None),
        '/' : ("div",  None),
        '%' : ("rem",  None),
        '&' : ("and",  "andi"),
        '|' : ("or",   "ori"),
        '^' : ("xor",  "xori"),
        '<<': ("sll",  "slli"),
        '>>': ("sra",  "srai"),
    }
    def __init__(self):
        self.out          = []
        self.tac          = []
        self.jump_targets = set()
        self.tac_line_set = set()
        self.str_lits     = []
        self.flt_lits     = []
        self._used_externs = set()
        self._used_fmts    = set()
        self.fname            = ""
        self.ra_alloc         = RegAlloc()
        self.param_q          = []
        self.pop_idx = 0
        self.int_pop_idx = 0
        self.float_pop_idx = 0
        self.epilogue_lbl     = ""
        self.in_main          = False
        self._fn_tac_lines    = []
        self._fn_targets  = set()
        self._fn_lines    = set()
        self._global_targets = set()
        self._global_lines   = set()
        self._in_function    = False
        self._cross_scope_emitted = set()  
        self._arrays      = {}
        self._array_order = []
        self._local_arrays = {}  
        self._fn_shadow_locals = set()  
        self._locally_defined  = set()  
        self._fn_return_types = {}
        self._fn_param_types  = {}
        self._fn_scoped_types = {}
        self._dead_const_vals = {}   
        self._ref_params: dict = {}
        self._ref_param_indices: set = set()
    def e(self, line=""):
        self.out.append(line)
    def lbl(self, name):
        self.out.append(f"{name}:")
    def ins(self, op, *args):
        arg = ", ".join(str(a) for a in args)
        self.out.append(f"    {op:<8} {arg}".rstrip())
    def _is_global_scalar(self, var):    
        if var in self._fn_shadow_locals:        
            return var not in self._locally_defined
        return var in _global_scalars
    def _is_global_scalar_write(self, var):
        if var in self._fn_shadow_locals:
            return False
        return var in _global_scalars
    def _load_global(self, var, dst_reg):
        if var in self._dead_const_vals:
            self.ins("li", dst_reg, self._dead_const_vals[var])
            t = _global_scalars.get(var, 'int')
            if t == 'long' and not fits_in_32bit(self._dead_const_vals[var]):
                pass  
            elif t == 'int' and not fits_in_32bit(self._dead_const_vals[var]):
                self.ins("addiw", dst_reg, dst_reg, "0")
            elif t == 'short':
                self.ins("slli", dst_reg, dst_reg, "48")
                self.ins("srai", dst_reg, dst_reg, "48")
            elif t == 'char':
                self.ins("slli", dst_reg, dst_reg, "56")
                self.ins("srai", dst_reg, dst_reg, "56")
            return
        self.ins("la", "t6", var)
        t = _global_scalars.get(var, 'int')
        if t == 'long' or t.startswith('ptr:'):
            self.ins("ld", dst_reg, f"0(t6)")
        elif t == 'short':
            self.ins("lh", dst_reg, f"0(t6)")
        elif t == 'char':
            self.ins("lb", dst_reg, f"0(t6)")
        elif t == 'double':
            self.ins("fld", dst_reg, f"0(t6)")
        elif t == 'float':
            self.ins("flw", "ft1", f"0(t6)")
            self.ins("fcvt.d.s", dst_reg, "ft1")
        else:
            self.ins("lw", dst_reg, f"0(t6)")
    def _store_global(self, var, src_reg):
        self.ins("la", "t6", var)
        t = _global_scalars.get(var, 'int')
        if t == 'long' or t.startswith('ptr:'):
            self.ins("sd", src_reg, f"0(t6)")
        elif t == 'short':
            self.ins("sh", src_reg, f"0(t6)")
        elif t == 'char':
            self.ins("sb", src_reg, f"0(t6)")
        elif t == 'double':
            self.ins("fsd", src_reg, f"0(t6)")
        elif t == 'float':
            self.ins("fcvt.s.d", "ft1", src_reg)
            self.ins("fsw", "ft1", f"0(t6)")
        else:
            self.ins("sw", src_reg, f"0(t6)")
    def _is_fp_reg(self, var):
        r = self.ra_alloc._map.get(var)
        if r and (r in RegAlloc.FP_CALLER_POOL or r in RegAlloc.FP_SAVED_POOL):
            return r
        return None
    def _load_float_var_into(self, var, fa_reg):
        if self._is_global_scalar(var):
            t = _global_scalars.get(var, 'float')
            self.ins("la", "t6", var)
            if t == 'double':
                self.ins("fld", fa_reg, "0(t6)")
            elif t == 'float':
                self.ins("flw", "ft1", "0(t6)")
                self.ins("fcvt.d.s", fa_reg, "ft1")
            elif t == 'long':
                self.ins("ld",       "t4",    "0(t6)")
                self.ins("fcvt.d.l", fa_reg, "t4")
            else:
                ld_map = {'short': 'lh', 'char': 'lb'}
                ld = ld_map.get(t, 'lw')
                self.ins(ld,         "t4",    "0(t6)")
                self.ins("fcvt.d.w", fa_reg, "t4")
            return
        # Bug fix 1: shadowed global float — _is_global_scalar() returns False when
        # the variable is both in _global_scalars and in _locally_defined (i.e. it was
        # written to inside main/a function).  The value still lives in the global .data
        # label as a single-precision word, so we must use flw/fld, NOT lw+fcvt.d.w.
        if var in _global_scalars and _global_scalars[var] in ('float', 'double'):
            t = _global_scalars[var]
            self.ins("la", "t6", var)
            if t == 'double':
                self.ins("fld", fa_reg, "0(t6)")
            else:
                self.ins("flw", "ft1", "0(t6)")
                self.ins("fcvt.d.s", fa_reg, "ft1")
            return
        fp_r = self._is_fp_reg(var)
        if fp_r:
            if fp_r != fa_reg:
                self.ins("fmv.d", fa_reg, fp_r)
        elif self.ra_alloc.is_spilled(var):
            t = get_type(var)
            if t == 'float' and var not in self.ra_alloc._float_vars:
                # Spilled as single-precision; load with flw and widen to double.
                # NOTE: if the var is in _float_vars it was stored via fsd (8-byte
                # double) by _handle_ptr_read — in that case fall through to fld.
                self.ins("flw", "ft1", f"{self.ra_alloc.spill_offset(var)}(s0)")
                self.ins("fcvt.d.s", fa_reg, "ft1")
            elif t == 'double' or t == 'float' or var in self.ra_alloc._float_vars:
                self.ins("fld", fa_reg, f"{self.ra_alloc.spill_offset(var)}(s0)")
            elif t == 'long':
                self.ins("ld",  "t4", f"{self.ra_alloc.spill_offset(var)}(s0)")
                self.ins("fcvt.d.l", fa_reg, "t4")
            elif t == 'short':
                self.ins("lh",  "t4", f"{self.ra_alloc.spill_offset(var)}(s0)")
                self.ins("fcvt.d.w", fa_reg, "t4")
            elif t == 'char':
                self.ins("lb",  "t4", f"{self.ra_alloc.spill_offset(var)}(s0)")
                self.ins("fcvt.d.w", fa_reg, "t4")
            else:
                self.ins("lw",  "t4", f"{self.ra_alloc.spill_offset(var)}(s0)")
                self.ins("fcvt.d.w", fa_reg, "t4")
        else:
            r = self.ra_alloc.reg(var)
            t = get_type(var)
            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
            if r and r in _fp_regs:
                if r != fa_reg:
                    self.ins("fmv.d", fa_reg, r)
            else:
                if t == 'long':
                    cvt = "fcvt.d.l"
                else:
                    cvt = "fcvt.d.w"
                self.ins(cvt, fa_reg, r if r else "zero")
    def _store_float_result(self, fa_reg, dst_var):
        if self._is_global_scalar_write(dst_var):
            t = _global_scalars.get(dst_var, 'float')
            self.ins("la", "t6", dst_var)
            if t == 'double':
                self.ins("fsd", fa_reg, "0(t6)")
            else:
                self.ins("fcvt.s.d", "ft1", fa_reg)
                self.ins("fsw", "ft1", "0(t6)")
            return
        fp_r = self._is_fp_reg(dst_var)
        if fp_r:
            if fp_r != fa_reg:
                self.ins("fmv.d", fp_r, fa_reg)
        else:
            off = self.ra_alloc.force_spill(dst_var)
            self.ins("fsd", fa_reg, f"{off}(s0)")
    def use_extern(self, sym):
        self._used_externs.add(sym)
    def use_fmt(self, fmt):
        self._used_fmts.add(fmt)
    def _fn_has_calls(self, instrs):
        for s in instrs:
            if re.search(r'\bCall\b', s):          return True
            if re.match(r'^print', s.strip()):    return True
            if re.match(r'^input', s.strip()):    return True
            stripped = s.strip()
            if re.match(r'^FREE\b', stripped):     return True
            if re.search(r'\bALLOC\b', stripped):  return True
            if re.search(r'\bCALLOC\b', stripped): return True
            if re.search(r'\bREALLOC\b', stripped):return True
        return False
    @staticmethod
    def _tac_needs_fp(instrs, ra_alloc=None):
        if ra_alloc is not None and ra_alloc.spill_slots:
            return True
        for raw in instrs:
            instr = re.sub(r'^//.*', '', raw).strip()
            if not instr:
                continue
            if re.match(r'^\w+\s*=\s*\((float|double)\)\s*\S+', instr):
                return True
            if re.search(r'\bCall\b', instr):
                return True
            if re.match(r'^FREE\b', instr):
                return True
            if re.search(r'\b(ALLOC|CALLOC|REALLOC)\b', instr):
                return True
            if re.match(r'^(print|input)\w+', instr):
                return True
            m = re.match(r'^\w+\s*=\s*(\S+)$', instr)
            if m:
                val = m.group(1)
                if is_num_literal(val) and not is_int_literal(val):
                    return True
            m = re.match(
                r'^\w+\s*=\s*(\S+)\s*(?:<=|>=|==|!=|<<|>>|[+\-*/%])\s*(\S+)$',
                instr)
            if m:
                for tok in (m.group(1), m.group(2)):
                    if is_num_literal(tok) and not is_int_literal(tok):
                        return True
                    if re.match(r'^[A-Za-z_]\w*$', tok) and \
                            get_type(tok) in ('float', 'double'):
                        return True
        return False
    def _fn_needs_fp(self, ra_alloc):
        fn_instrs = getattr(self, '_fn_tac_lines', [])
        return self._tac_needs_fp(fn_instrs, ra_alloc)
    def load(self, val, dst):
        if is_int_literal(val):
            self.ins("li", dst, to_int(val))
        elif is_num_literal(val):
            lname = f".flt{len(self.flt_lits)}"
            self.flt_lits.append((lname, val))
            self.ins("la",  "t6", lname)
            self.ins("fld", dst, f"0(t6)")
        elif val in self._ref_params:
            ptr_off = self._ref_params[val]
            self.ins("ld", "t6", f"{ptr_off}(s0)")
            self.ins(load_ins(val), dst, "0(t6)")
        elif self._is_global_scalar(val):
            self._load_global(val, dst)
        elif self.ra_alloc.is_spilled(val):
            ins = load_ins(val)
            self.ins(ins, dst, f"{self.ra_alloc.spill_offset(val)}(s0)")
        else:
            r = self.ra_alloc.reg(val)
            if r and r != dst:
                _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                if r in _fp_regs and dst in _fp_regs:
                    self.ins("fmv.d", dst, r)
                elif r in _fp_regs:
                    self.ins("fmv.x.d", dst, r)
                else:
                    self.ins("mv", dst, r)
    def store_var(self, var, src):
        if var in self._ref_params:
            ptr_off = self._ref_params[var]
            self.ins("ld", "t6", f"{ptr_off}(s0)")
            self.ins(store_ins(var), src, "0(t6)")
        elif self._is_global_scalar_write(var):
            self._store_global(var, src)
        elif self.ra_alloc.is_spilled(var):
            ins = store_ins(var)
            self.ins(ins, src, f"{self.ra_alloc.spill_offset(var)}(s0)")
        else:
            r = self.ra_alloc.reg(var)
            if r and r != src:
                _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                if r in _fp_regs and src in _fp_regs:
                    self.ins("fmv.d", r, src)
                elif src in _fp_regs:
                    self.ins("fmv.x.d", r, src)
                else:
                    self.ins("mv", r, src)
    def var_reg_or_load(self, var, scratch):
        if is_int_literal(var):
            self.ins("li", scratch, to_int(var))
            return scratch
        if self._is_global_scalar(var):
            self._load_global(var, scratch)
            return scratch
        if var in self._ref_params:
            ptr_off = self._ref_params[var]
            self.ins("ld", "t6", f"{ptr_off}(s0)")
            self.ins(load_ins(var), scratch, "0(t6)")
            return scratch
        if self.ra_alloc.is_spilled(var):
            ins = load_ins(var)
            self.ins(ins, scratch, f"{self.ra_alloc.spill_offset(var)}(s0)")
            return scratch
        r = self.ra_alloc.reg(var)
        return r if r else scratch
    def dst_reg(self, var):
        if self._is_global_scalar_write(var):
            return "t4"
        if self.ra_alloc.is_spilled(var):
            return "t4"
        r = self.ra_alloc.reg(var)
        return r if r else "t4"
    def flush_dst(self, var, reg):
        if var in self._ref_params:
            ptr_off = self._ref_params[var]
            self.ins("ld", "t6", f"{ptr_off}(s0)")
            self.ins(store_ins(var), reg, "0(t6)")
        elif self._is_global_scalar_write(var):
            self._store_global(var, reg)
        elif self.ra_alloc.is_spilled(var):
            ins = store_ins(var)
            self.ins(ins, reg, f"{self.ra_alloc.spill_offset(var)}(s0)")
    def operand(self, val, scratch):
        if is_int_literal(val):
            self.ins("li", scratch, to_int(val))
            return scratch
        if self._is_global_scalar(val):
            self._load_global(val, scratch)
            return scratch
        if val in self._ref_params:
            ptr_off = self._ref_params[val]
            self.ins("ld", "t6", f"{ptr_off}(s0)")
            self.ins(load_ins(val), scratch, "0(t6)")
            return scratch
        if self.ra_alloc.is_spilled(val):
            self.ins(load_ins(val), scratch, f"{self.ra_alloc.spill_offset(val)}(s0)")
            return scratch
        r = self.ra_alloc.reg(val)
        return r if r else scratch
    def tac_lbl(self, n):
        return f".L{n}"
    def collect_targets(self):
        in_fn = False
        fn_targets = set()
        fn_lines   = set()
        self._fn_scope_list = []
        for lnum, instr in self.tac:
            self.tac_line_set.add(lnum)
            for m in re.finditer(r'goto\s+(\d+)', instr):
                self.jump_targets.add(int(m.group(1)))
            if re.match(r'^BeginFunc', instr):
                in_fn      = True
                fn_targets = set()
                fn_lines   = set()
                fn_lines.add(lnum)
            elif re.match(r'^EndFunc', instr):
                fn_lines.add(lnum)
                self._fn_scope_list.append((fn_targets, fn_lines))
                in_fn = False
            else:
                if in_fn:
                    fn_lines.add(lnum)
                    for m in re.finditer(r'goto\s+(\d+)', instr):
                        fn_targets.add(int(m.group(1)))
                else:
                    self._global_lines.add(lnum)
                    for m in re.finditer(r'goto\s+(\d+)', instr):
                        self._global_targets.add(int(m.group(1)))
        self._fn_scope_iter = iter(self._fn_scope_list)
        self._array_stride = {}
        self._array_nelems = {}
        self._array_declared_size = dict(_symtab_array_sizes)
        seen_order = []
        arr_offsets = {}  
        for _, instr in self.tac:
            for m in re.finditer(r'\b([A-Za-z_]\w*)\[(\d+)\]', instr):
                aname, byte_off = m.group(1), int(m.group(2))
                if aname not in self._arrays:
                    self._arrays[aname] = byte_off
                    seen_order.append(aname)
                    arr_offsets[aname] = set()
                else:
                    self._arrays[aname] = max(self._arrays[aname], byte_off)
                arr_offsets[aname].add(byte_off)
        for _, instr in self.tac:
            for m in re.finditer(r'\b([A-Za-z_]\w*)\[([A-Za-z_]\w*)\]', instr):
                aname = m.group(1)
                if aname not in self._arrays:
                    self._arrays[aname] = 0
                    seen_order.append(aname)
                    arr_offsets[aname] = set()
        arr_multiply_strides = {}   
        for _, instr in self.tac:
            mult_m = (re.match(r'^(\w+)\s*=\s*\w+\s*\*\s*(\d+)$', instr) or
                      re.match(r'^(\w+)\s*=\s*(\d+)\s*\*\s*\w+$', instr))
            if not mult_m:
                continue
            tmp = mult_m.group(1)
            factor = int(mult_m.group(2))
            if factor == 0:
                continue
            for _, instr2 in self.tac:
                for am in re.finditer(r'\b([A-Za-z_]\w*)\[' + re.escape(tmp) + r'\]', instr2):
                    aname = am.group(1)
                    arr_multiply_strides.setdefault(aname, set()).add(factor)
        from math import gcd
        from functools import reduce
        def _gcd_list(vals):
            if not vals:
                return 4
            return reduce(gcd, vals)
        _TYPE_STRIDE = {'char': 1, 'short': 2, 'int': 4,
                        'float': 4, 'double': 8, 'long': 8}
        for aname in list(self._arrays.keys()):
            offsets = arr_offsets.get(aname, set())
            nonzero = sorted(o for o in offsets if o > 0)
            if aname in _symtab_var_types:
                sym_type = _symtab_var_types[aname]
                stride = _TYPE_STRIDE.get(sym_type, 4)
                set_type(aname, sym_type)  
            elif aname in arr_multiply_strides and arr_multiply_strides[aname]:
                stride = min(arr_multiply_strides[aname])
                if stride not in _TYPE_STRIDE.values():
                    stride = 4                       
                if stride == 1:   set_type(aname, 'char')
                elif stride == 2: set_type(aname, 'short')
                elif stride == 8: set_type(aname, 'double')
            elif len(nonzero) >= 2:
                g = _gcd_list(nonzero)
                stride = g if g in _TYPE_STRIDE.values() else 4
                if stride == 1:   set_type(aname, 'char')
                elif stride == 2: set_type(aname, 'short')
                elif stride == 8: set_type(aname, 'double')
            elif len(nonzero) == 1:
                candidate = nonzero[0]
                stride = candidate if candidate in _TYPE_STRIDE.values() else 4
                if stride == 1:   set_type(aname, 'char')
                elif stride == 2: set_type(aname, 'short')
                elif stride == 8: set_type(aname, 'double')
            else:
                stride = 4        
            self._array_stride[aname] = stride
            declared = self._array_declared_size.get(aname, 0)
            if declared > 0:
                n_elems = declared
            else:              
                max_off = self._arrays[aname]
                if max_off > 0:
                    n_elems = max_off // stride + 2
                else:
                    n_elems = 16
                n_elems += 1   
            self._array_nelems[aname] = n_elems
        for _, instr in self.tac:
            m = re.match(r'^(\w+)\[\d+\]\s*=\s*(\S+)$', instr)
            if m:
                aname, val = m.group(1), m.group(2)
                if aname in self._arrays and is_num_literal(val) and not is_int_literal(val):
                    set_type(aname, 'float')
        self._array_order = seen_order
    def emit_missing_target_stubs(self):
        try:
            fn_targets, fn_lines = next(self._fn_scope_iter)
        except StopIteration:
            return
        beginfunc_map = {}
        for lnum, instr in self.tac:
            m = re.match(r'^BeginFunc\s+(\w+)', instr)
            if m:
                beginfunc_map[lnum] = m.group(1)
        all_other_lines = set()
        for other_targets, other_lines in self._fn_scope_list:
            if other_lines is not fn_lines:  
                all_other_lines |= other_lines
        all_other_lines |= self._global_lines
        missing = fn_targets - fn_lines
        real_missing = missing - set(beginfunc_map.keys())
        cross_scope_missing = real_missing & all_other_lines
        real_missing = real_missing - all_other_lines
        fn_jumps_to_func = missing & set(beginfunc_map.keys())
        if fn_jumps_to_func:
            self.e()
            self.e(f"    # -- cross-function jump redirects --")
            for n in sorted(fn_jumps_to_func):
                self.lbl(self.tac_lbl(n))
                self.ins('j', beginfunc_map[n])
        if cross_scope_missing:
            self.e()
            self.e(f"    # -- out-of-range targets that land in another scope: redirect to epilogue --")
            for n in sorted(cross_scope_missing):
                self.lbl(self.tac_lbl(n))
                self.ins('j', self.epilogue_lbl)
                self._cross_scope_emitted.add(n)
        if real_missing:
            self.e()
            self.e(f"    # -- stub labels for out-of-range jump targets --")
            for n in sorted(real_missing):
                self.lbl(self.tac_lbl(n))
                self.ins("nop")
    def _prescan_function(self, fn_tac_lines):
        KEYWORDS = {'BeginFunc','EndFunc','PopParam','PushParam','Return',
                    'Call','goto','if','int','float','char','double',
                    'long','short',
                    'printint','printfloat','printchar','printstring',
                    'inputint','inputfloat','inputchar','inputstring',
                    'rtz','main'}
        for instr in fn_tac_lines:
            instr = re.sub(r'^//.*', '', instr).strip()
            if not instr:
                continue
            if re.match(r'^(BeginFunc|EndFunc)\b', instr):
                continue
            m = re.match(r'^(\w+)\s*=\s*Call\s+\w+$', instr)
            if m:
                self.ra_alloc.ensure(m.group(1)); continue
            if re.match(r'^Call\s+\w+$', instr):
                continue
            m = re.match(r'^PushParam\s+(.+)$', instr)
            if m:
                raw = m.group(1).strip()         
                cast_m = re.match(r'^\(\w+\)\s*(.+)$', raw)
                tok = cast_m.group(1).strip() if cast_m else raw
                if tok.startswith('&'):
                    ref_var = tok[1:].strip()
                    if re.match(r'^[A-Za-z_]\w*$', ref_var) and ref_var not in KEYWORDS:
                        self.ra_alloc.ensure(ref_var)
                elif not is_num_literal(tok) and re.match(r'^[A-Za-z_]\w*$', tok) and tok not in KEYWORDS:
                    self.ra_alloc.ensure(tok)
                continue
            m = re.match(r'^PopParam\s+(\w+)$', instr)
            if m:
                self.ra_alloc.ensure(m.group(1)); continue
            m = re.match(r'^Return\s+(\S+)$', instr)
            if m:
                tok = m.group(1)
                if not is_num_literal(tok) and re.match(r'^[A-Za-z_]\w*$', tok) and tok not in KEYWORDS:
                    self.ra_alloc.ensure(tok)
                continue
            m = re.match(r'^(\w+)\s*=\s*\(\w+\)\s*(\S+)$', instr)
            if m:
                self.ra_alloc.ensure(m.group(1))
                src = m.group(2)
                if not is_num_literal(src) and not src.startswith('"') and \
                        re.match(r'^[A-Za-z_]\w*$', src) and src not in KEYWORDS:
                    self.ra_alloc.ensure(src)
                continue
            for tok in re.findall(r'\b([A-Za-z_]\w*)\b', instr):
                is_global_not_shadowed = tok in _global_scalars and tok not in self.ra_alloc._shadow_locals
                if tok not in KEYWORDS and not re.match(r'^t\d+$', tok) and not is_global_not_shadowed:
                    self.ra_alloc.ensure(tok)
            for tok in re.findall(r'\bt\d+\b', instr):
                self.ra_alloc.ensure(tok)
    def _preseed_float_types(self, tac_lines, fname=None):
        FLOAT_OPS = {'+', '-', '*', '/'}
        scoped_types = getattr(self, '_fn_scoped_types', {})
        def _set_type_guarded(var, typ):
            if fname and f'{fname}::{var}' in scoped_types:
                return
            set_type(var, typ)
        # Pre-seed _var_types from the symbol table ONCE before the inference
        # loop.  This ensures that global/local pointer variables (e.g. p, q of
        # type ptr:double) have the correct type visible to get_type() from the
        # very first iteration, so the inference loop never needs to upgrade them
        # and cannot oscillate between ptr:float and ptr:double.
        # We guard with _set_type_guarded so function-scoped overrides are respected.
        for _sv, _st in _symtab_var_types.items():
            if get_type(_sv) != _st:
                _set_type_guarded(_sv, _st)
        changed = True
        while changed:
            changed = False
            for instr in tac_lines:
                instr = instr.strip()
                m_ref = re.match(r'^(\w+)\s*=\s*ref\s+(\w+)$', instr)
                if m_ref:
                    dst_r, src_r = m_ref.group(1), m_ref.group(2)
                    src_t = _symtab_var_types.get(src_r, get_type(src_r))
                    if src_t and not src_t.startswith('ptr:'):
                        ptr_t = f'ptr:{src_t}'
                    elif src_t:
                        ptr_t = src_t   
                    else:
                        ptr_t = 'ptr:int'
                    if get_type(dst_r) != ptr_t:
                        _set_type_guarded(dst_r, ptr_t)
                        changed = True
                    continue
                m_deref = re.match(r'^(\w+)\s*=\s*deref\s+(\w+)$', instr)
                if m_deref:
                    dst_d, src_d = m_deref.group(1), m_deref.group(2)
                    ptr_t = _symtab_var_types.get(src_d, get_type(src_d))
                    if ptr_t.startswith('ptr:'):
                        pointee_t = ptr_t[4:]   
                        if get_type(dst_d) != pointee_t:
                            _set_type_guarded(dst_d, pointee_t)
                            changed = True
                    continue
                m_pp = re.match(r'^PopParam\s+(\w+)$', instr)
                if m_pp:
                    pvar = m_pp.group(1)
                    fn_param_types_map = getattr(self, '_fn_param_types', {})
                    if fname and fname in fn_param_types_map:
                        fn_pp_types = fn_param_types_map[fname]
                        param_idx = sum(
                            1 for l in tac_lines[:tac_lines.index(instr)]
                            if re.match(r'^PopParam\s+', l.strip())
                        ) if instr in tac_lines else 0
                        if param_idx < len(fn_pp_types):
                            actual_t = fn_pp_types[param_idx]
                            if actual_t.startswith('ptr:') and get_type(pvar) != actual_t:
                                _set_type_guarded(pvar, actual_t)
                                changed = True
                                continue
                    st = _symtab_var_types.get(pvar, '')
                    if st.startswith('ptr:') and not get_type(pvar).startswith('ptr:'):
                        _set_type_guarded(pvar, st)
                        changed = True
                    continue
                # Propagate ptr:float / ptr:double from "deref ptr_var = float_val"
                # back onto ptr_var so that ALLOC temps get the right pointer type.
                m_dw = re.match(r'^deref\s+(\w+)\s*=\s*(\S+)$', instr)
                if m_dw:
                    ptr_v, src_v = m_dw.group(1), m_dw.group(2)
                    cur_ptr_t = get_type(ptr_v)
                    if is_num_literal(src_v) and not is_int_literal(src_v):
                        # A bare float literal (e.g. 99.99) tells us the pointee is
                        # some float-family type, but NOT which precision.  Only apply
                        # 'ptr:float' if the pointer has no float-family type yet.
                        # NEVER downgrade ptr:double → ptr:float: that causes an
                        # infinite loop because another rule (p = t0 where t0 is
                        # ptr:double) immediately upgrades it back.
                        if cur_ptr_t not in ('ptr:float', 'ptr:double'):
                            wanted = 'ptr:float'
                        else:
                            wanted = None
                    elif re.match(r'^[A-Za-z_]\w*$', src_v):
                        sv_t = get_type(src_v)
                        if sv_t in ('float', 'double'):
                            candidate = f'ptr:{sv_t}'
                            # Never downgrade ptr:double -> ptr:float: causes infinite
                            # oscillation with the deref-read rule that propagates the
                            # pointee type back onto t1, which then feeds t3=t1+t2 and
                            # makes t3 'float', which tries to downgrade n again.
                            if cur_ptr_t == 'ptr:double' and candidate == 'ptr:float':
                                wanted = None
                            else:
                                wanted = candidate
                        else:
                            wanted = None
                    else:
                        wanted = None
                    if wanted and cur_ptr_t != wanted:
                        _set_type_guarded(ptr_v, wanted)
                        changed = True
                    continue
                m = re.match(r'^(\w+)\s*=\s*(\S+)$', instr)
                if m:
                    dst, val = m.group(1), m.group(2)
                    if is_num_literal(val) and not is_int_literal(val):
                        if get_type(dst) not in ('float', 'double'):
                            _set_type_guarded(dst, 'float')
                            if get_type(dst) in ('float', 'double'):
                                changed = True
                    elif re.match(r'^[A-Za-z_]\w*$', val):
                        val_t = get_type(val)
                        dst_t = get_type(dst)
                        if val_t in ('float', 'double'):
                            if dst_t not in ('float', 'double'):
                                _set_type_guarded(dst, 'float')
                                if get_type(dst) in ('float', 'double'):
                                    changed = True
                        elif val_t.startswith('ptr:') and val_t != 'ptr:void':
                            # Forward: propagate ptr:float etc. from val to dst.
                            if dst_t != val_t:
                                _set_type_guarded(dst, val_t)
                                if get_type(dst) == val_t:
                                    changed = True
                        # Reverse inference: if dst is a well-typed ptr (e.g. fp is
                        # ptr:float from symtab) and val is an untyped TAC temp
                        # (e.g. t12 from ALLOC), infer val must share dst's type.
                        # This covers 'fp = t12' where fp->ptr:float, t12->unknown.
                        dst_t2 = get_type(dst)
                        if dst_t2.startswith('ptr:') and dst_t2 != 'ptr:void':
                            if re.match(r'^t\d+$', val) and get_type(val) in ('int', 'ptr:void', ''):
                                _set_type_guarded(val, dst_t2)
                                if get_type(val) == dst_t2:
                                    changed = True
                    continue
                m = re.match(r'^(\w+)\s*=\s*\((float|double)\)\s*(\S+)$', instr)
                if m:
                    dst, cast_type = m.group(1), m.group(2)
                    if get_type(dst) not in ('float', 'double'):
                        _set_type_guarded(dst, cast_type)
                        if get_type(dst) in ('float', 'double'):
                            changed = True
                    continue
                m = re.match(
                    r'^(\w+)\s*=\s*(.+?)\s*(<=|>=|==|!=|<<|>>|[+\-*/%&|^<>])\s*(.+)$',
                    instr)
                if m and m.group(2).strip():
                    _op1 = m.group(2).strip()
                    if not (re.match(r'^[A-Za-z_]\w*(\[\w+\])?$', _op1) or is_num_literal(_op1)):
                        m = None
                if m and m.group(2).strip():
                    dst  = m.group(1)
                    op1  = m.group(2).strip()
                    op   = m.group(3)
                    op2  = m.group(4).strip()
                    if op in FLOAT_OPS:
                        op1_float = (
                            (is_num_literal(op1) and not is_int_literal(op1)) or
                            (re.match(r'^[A-Za-z_]\w*$', op1) and get_type(op1) in ('float','double'))
                        )
                        op2_float = (
                            (is_num_literal(op2) and not is_int_literal(op2)) or
                            (re.match(r'^[A-Za-z_]\w*$', op2) and get_type(op2) in ('float','double'))
                        )
                        if op1_float or op2_float:
                            # Preserve double: if either operand is double, result is
                            # double not float (e.g. t3 = t1 + t2 where t1 is double)
                            op1_t = get_type(op1) if re.match(r'^[A-Za-z_]\w*$', op1) else 'float'
                            op2_t = get_type(op2) if re.match(r'^[A-Za-z_]\w*$', op2) else 'float'
                            result_t = 'double' if 'double' in (op1_t, op2_t) else 'float'
                            if get_type(dst) != result_t:
                                _set_type_guarded(dst, result_t)
                                if get_type(dst) in ('float', 'double'):
                                    changed = True
                    continue
                m = re.match(r'^print(float|double)\s+(\w+)$', instr)
                if m and get_type(m.group(2)) not in ('float', 'double'):
                    _set_type_guarded(m.group(2), m.group(1))
                    if get_type(m.group(2)) in ('float', 'double'):
                        changed = True
    def prologue(self, fname, nparams, fn_tac_lines=None):
        self.fname        = fname
        self.in_main      = (fname == "main")
        self._in_function = True
        self.ra_alloc     = RegAlloc()
        self.ra_alloc._array_names = set(self._arrays.keys())
        self._fn_shadow_locals = {
            v for v in _local_var_names if v in _global_scalars
        }
        self._locally_defined  = set()  
        self.ra_alloc._shadow_locals = self._fn_shadow_locals
        self.param_q      = []
        self.pop_idx = 0
        self.int_pop_idx = 0
        self.float_pop_idx = 0
        self.epilogue_lbl = f".Lepilogue_{fname}"
        self._fn_tac_lines = fn_tac_lines or []
        self._ref_params        = {}   
        self._ref_param_indices = set()  
        if fn_tac_lines:
            scoped_types = getattr(self, '_fn_scoped_types', {})
            fn_param_types_map = getattr(self, '_fn_param_types', {})
            fn_param_names = set()
            param_order_idx = 0
            for instr in fn_tac_lines:
                mp = re.match(r'^PopParam\s+(\w+)$', instr.strip())
                if mp:
                    pvar = mp.group(1)
                    fn_param_names.add(pvar)
                    scoped_key = f'{fname}::{pvar}'
                    if scoped_key in scoped_types:
                        set_type(pvar, scoped_types[scoped_key])
                    else:
                        ptypes = fn_param_types_map.get(fname, [])
                        if param_order_idx < len(ptypes):
                            set_type(pvar, ptypes[param_order_idx])
                        else:
                            set_type(pvar, 'int')
                    param_order_idx += 1
            self._preseed_float_types(fn_tac_lines, fname=fname)
            self.ra_alloc.set_safe_scratch_temps(fn_tac_lines)
            fn_pairs = list(enumerate(fn_tac_lines))
            self.ra_alloc.run_graph_coloring(fn_pairs)
            self._prescan_function(fn_tac_lines)
            tac_list = self.tac  
            for ci, (cl, cinstr) in enumerate(tac_list):
                if not re.match(rf'^(?:\w+\s*=\s*)?Call\s+{re.escape(fname)}\s*$',
                                cinstr.strip()):
                    continue
                push_args = []
                for _, pinstr in reversed(tac_list[:ci]):
                    pm = re.match(r'^PushParam\s+(.+)$', pinstr.strip())
                    if pm:
                        push_args.append(pm.group(1).strip())
                    elif re.match(r'^(BeginFunc|EndFunc)\b', pinstr.strip()):
                        break
                    elif re.match(r'^(?:\w+\s*=\s*)?Call\b', pinstr.strip()):
                        break
                push_args.reverse()   
                for idx, arg in enumerate(push_args):
                    if arg.startswith('&'):
                        self._ref_param_indices.add(idx)
        sregs = list(self.ra_alloc.used_sregs)
        fp_sregs = list(self.ra_alloc.used_fp_sregs)
        self._prologue_sregs = sregs
        self._prologue_fp_sregs = fp_sregs
        fn_instrs_strs = fn_tac_lines or []
        needs_ra = self._fn_has_calls(fn_instrs_strs)
        needs_fp = self._fn_needs_fp(self.ra_alloc)
        if self.ra_alloc.spill_slots > 0:
            needs_fp = True
        if not needs_fp and fn_tac_lines:
            for var in self.ra_alloc._spill:
                if re.match(r'^t\d+$', var) and get_type(var) not in ('float', 'double'):
                    needs_fp = True
                    break
        float_cast_spills = 0
        if fn_tac_lines:
            scoped_types = getattr(self, '_fn_scoped_types', {})
            for line in fn_tac_lines:
                line = line.strip()
                if re.match(r'^\w+\s*=\s*\((float|double)\)\s*\S+', line):
                    if not needs_fp:
                        needs_fp = True
                    float_cast_spills += 1
                pp_m = re.match(r'^PopParam\s+(\w+)$', line)
                if pp_m:
                    pvar = pp_m.group(1)
                    scoped_key = f'{fname}::{pvar}'
                    ptype = scoped_types.get(scoped_key, get_type(pvar))
                    if ptype in ('float', 'double'):
                        if not needs_fp:
                            needs_fp = True
                        float_cast_spills += 1
        float_reserve = 0
        if needs_fp and fn_tac_lines:
            fp_pool = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
            for line in fn_tac_lines:
                for tok in re.findall(r'\b[A-Za-z_]\w*\b', line):
                    if (get_type(tok) in ('float', 'double')
                            and tok not in self.ra_alloc._map
                            and tok not in self.ra_alloc._spill):
                        float_reserve += 1
            float_reserve = min(float_reserve, 8)
        frame = _compute_frame(len(sregs) + len(fp_sregs),
                               self.ra_alloc.spill_slots + float_reserve + float_cast_spills,
                               needs_ra, needs_fp)
        local_arr_bytes = 0
        fn_local_arrays = {}   
        for aname in self._array_order:
            if aname in _global_arrays:
                continue   
            n_elems = self._array_nelems.get(aname, 1)
            stride  = self._array_stride.get(aname, 4)
            byte_sz = n_elems * stride
            byte_sz = (byte_sz + 7) & ~7
            fn_local_arrays[aname] = byte_sz
            local_arr_bytes += byte_sz
        if local_arr_bytes % 16:
            local_arr_bytes += 16 - (local_arr_bytes % 16)
        frame += local_arr_bytes
        if frame % 16:
            frame += 16 - (frame % 16)
        arr_sp_off = 0
        self._local_arrays = {}
        for aname, byte_sz in fn_local_arrays.items():
            self._local_arrays[aname] = arr_sp_off
            arr_sp_off += byte_sz
        self._prologue_frame    = frame
        self._prologue_needs_ra = needs_ra
        self._prologue_needs_fp = needs_fp
        self.e()
        self.ins(".globl", fname)
        self.lbl(fname)
        self.e(f"    # -- prologue: {fname}  ({nparams} params) --")
        if frame > 0:
            self.ins("addi", "sp, sp", f"-{frame}")
        off = frame
        if needs_ra:
            off -= 8
            self.ins("sd", "ra", f"{off}(sp)")
        if needs_fp:
            off -= 8
            self.ins("sd", "s0", f"{off}(sp)")
        for reg in sregs:
            off -= 8
            self.ins("sd", reg, f"{off}(sp)")
        for reg in fp_sregs:
            off -= 8
            self.ins("fsd", reg, f"{off}(sp)")
        if needs_fp:
            self.ins("addi", "s0, sp", str(frame))
        if fname == 'main' and getattr(self, '_has_global_init', False) \
                and not getattr(self, '_has_post_main', False):
            self.ins("call", "__global_init")
        if self._arrays:
            self.e(f"    # -- array base pointers --")
            self.emit_array_la()
    def epilogue(self):
        self.emit_missing_target_stubs()
        sregs    = self._prologue_sregs
        fp_sregs = getattr(self, '_prologue_fp_sregs', [])
        frame    = self._prologue_frame
        needs_ra = self._prologue_needs_ra
        needs_fp = self._prologue_needs_fp
        self.e()
        self.lbl(self.epilogue_lbl)
        self.e(f"    # -- epilogue: {self.fname} --")
        t_pool = set(self.ra_alloc.CALLER_POOL)
        live_at_exit = set()
        if self._fn_tac_lines:
            KEYWORDS_LIVE = {'BeginFunc','EndFunc','PopParam','PushParam','Return',
                             'Call','goto','if','int','float','char','double',
                             'long','short',
                             'printint','printfloat','printchar','printstring',
                             'inputint','inputfloat','inputchar','inputstring',
                             'rtz','main','eq','ne','lt','le','gt','ge','true','false'}
            pairs = list(enumerate(self._fn_tac_lines))
            _, live_out = _liveness_analysis(pairs)
            if live_out:
                live_at_exit = live_out[-1]
        off = frame
        ra_off = None
        s0_off = None
        if needs_ra:
            off -= 8
            ra_off = off
        if needs_fp:
            off -= 8
            s0_off = off
        sreg_offs = []
        for _ in sregs:
            off -= 8
            sreg_offs.append(off)
        fp_sreg_offs = []
        for _ in fp_sregs:
            off -= 8
            fp_sreg_offs.append(off)
        if needs_ra and ra_off is not None:
            self.ins("ld", "ra", f"{ra_off}(sp)")
        for reg, roff in zip(sregs, sreg_offs):
            self.ins("ld", reg, f"{roff}(sp)")
        for reg, roff in zip(fp_sregs, fp_sreg_offs):
            self.ins("fld", reg, f"{roff}(sp)")
        if needs_fp and s0_off is not None:
            self.ins("ld", "s0", f"{s0_off}(sp)")
        if frame > 0:
            self.ins("addi", "sp, sp", str(frame))
        self.ins("ret")
    def emit_branch(self, lhs, op, rhs, label):
        def _is_float_operand(v):
            if is_num_literal(v) and not is_int_literal(v):
                return True
            if re.match(r'^[A-Za-z_]\w*$', v):
                if get_type(v) in ('float', 'double'):
                    return True
                if v in self.ra_alloc._float_vars:
                    return True
                if self._is_fp_reg(v):
                    return True
            return False
        lhs_is_float = _is_float_operand(lhs)
        rhs_is_float = _is_float_operand(rhs)
        if lhs_is_float or rhs_is_float:
            def _load_fp(v, fa_reg):
                if is_num_literal(v) and not is_int_literal(v):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, v))
                    self.ins("la",  "t4", lname)
                    self.ins("fld", fa_reg, "0(t4)")
                    return fa_reg
                if is_int_literal(v):
                    self.ins("li", "t4", to_int(v))
                    self.ins(int_to_double_ins(v), fa_reg, "t4")
                    return fa_reg
                fp_r = self._is_fp_reg(v)
                if fp_r:
                    if fp_r != fa_reg:
                        self.ins("fmv.d", fa_reg, fp_r)
                    return fa_reg
                if self.ra_alloc.is_spilled(v):
                    if get_type(v) in ('float', 'double') or (v in self.ra_alloc._float_vars):
                        self.ins("fld", fa_reg, f"{self.ra_alloc.spill_offset(v)}(s0)")
                    else:
                        ld  = "ld"  if get_type(v) == 'long' else "lw"
                        cvt = "fcvt.d.l" if get_type(v) == 'long' else "fcvt.d.w"
                        self.ins(ld,  "t4", f"{self.ra_alloc.spill_offset(v)}(s0)")
                        self.ins(cvt, fa_reg, "t4")
                    return fa_reg
                if self._is_global_scalar(v):
                    self._load_float_var_into(v, fa_reg)
                    return fa_reg
                r = self.ra_alloc.reg(v)
                if r and (r in RegAlloc.FP_CALLER_POOL or r in RegAlloc.FP_SAVED_POOL):
                    if r != fa_reg:
                        self.ins("fmv.d", fa_reg, r)
                    return fa_reg
                cvt = "fcvt.d.l" if get_type(v) == 'long' else "fcvt.d.w"
                self.ins(cvt, fa_reg, r if r else "zero")
                return fa_reg
            _load_fp(lhs, "fa0")
            _load_fp(rhs, "fa1")
            FP_CMP = {
                '<':  ("flt.d", "fa0", "fa1", False),
                '>':  ("flt.d", "fa1", "fa0", False),
                '<=': ("fle.d", "fa0", "fa1", False),
                '>=': ("fle.d", "fa1", "fa0", False),
                '==': ("feq.d", "fa0", "fa1", False),
                '!=': ("feq.d", "fa0", "fa1", True),
            }
            fop, fa_a, fa_b, invert = FP_CMP.get(op, ("feq.d", "fa0", "fa1", False))
            self.ins(fop, f"t4, {fa_a}", fa_b)
            if invert:
                self.ins("beqz", "t4", label)
            else:
                self.ins("bnez", "t4", label)
            return
        if re.match(r'^(\w+)\[(\w+)\]$', lhs):
            self._resolve_operand(lhs, "t4")
            lhs_reg = "t4"
        else:
            lhs_reg = self.var_reg_or_load(lhs, "t4")
        if re.match(r'^(\w+)\[(\w+)\]$', rhs):
            self._resolve_operand(rhs, "t5")
            rhs_reg = "t5"
        else:
            rhs_reg = self.var_reg_or_load(rhs, "t5")
            if lhs_reg == rhs_reg and lhs_reg not in ("t4", "t5"):
                self.load(rhs, "t5")
                rhs_reg = "t5"
        br, swap = self.BRANCH_MAP.get(op, ("bne", False))
        if swap:
            self.ins(br, f"{rhs_reg}, {lhs_reg}, {label}")
        else:
            self.ins(br, f"{lhs_reg}, {rhs_reg}, {label}")
    def emit_binary(self, dst_var, op1, op, op2):
        rr, ri = self.BINOP_MAP.get(op, (None, None))
        if not rr:
            self.e(f"    # [UNSUPPORTED OP '{op}']")
            return

        d = self.dst_reg(dst_var)
        if re.match(r'^(\w+)\[(\w+)\]$', op1):
            self._resolve_operand(op1, "t4")
            op1_reg = "t4"
        else:
            op1_reg = self.var_reg_or_load(op1, "t4")

        if is_num_literal(op2) and ri:
            self.ins(ri, f"{d}, {op1_reg}", to_int(op2))
        elif is_num_literal(op2) and op == '-':
            self.ins("addi", f"{d}, {op1_reg}", -to_int(op2))
        elif is_num_literal(op2):
            self.ins("li", "t5", to_int(op2))
            self.ins(rr, f"{d}, {op1_reg}", "t5")
        else:
            if re.match(r'^(\w+)\[(\w+)\]$', op2):
                self._resolve_operand(op2, "t5")
                op2_reg = "t5"
            else:
                op2_reg = self.var_reg_or_load(op2, "t5")
            if op1_reg == op2_reg and op1_reg in ("t4", "t5"):
                self.load(op2, "t5")
                op2_reg = "t5"
            self.ins(rr, f"{d}, {op1_reg}", op2_reg)

        self.flush_dst(dst_var, d)
    def _resolve_char_literal(self, val):
        escape_map = {
            "'\\0'": "0",  r"'\0'": "0",
            "'\\n'": "10", r"'\n'": "10",
            "'\\t'": "9",  r"'\t'": "9",
            "'\\r'": "13", r"'\r'": "13",
            "'\\\\'": "92",
        }
        if val in escape_map:
            return escape_map[val]
        m = re.match(r"^'(.)'$", val)
        if m:
            return str(ord(m.group(1)))
        m = re.match(r"^'(\d+)'$", val)
        if m:
            return m.group(1)
        return val
    def _resolve_operand(self, raw, scratch):
        m = re.match(r'^(\w+)\[(\w+)\]$', raw)
        if m:
            arr, off = m.group(1), m.group(2)
            self.arr_addr(arr, off, scratch)
            if get_type(arr) in ('float', 'double'):
                self.ins("flw", "fa0", f"0({scratch})")
                self.ins("fcvt.d.s", "fa0", "fa0")
                return scratch  
            ins = load_ins(arr)
            self.ins(ins, scratch, f"0({scratch})")
            return scratch
        return raw
    def emit_array_la(self):
        for aname in self._array_order:
            if aname not in _global_arrays and aname in self._local_arrays:
                sp_off = self._local_arrays[aname]
                reg = self.ra_alloc.reg(aname)
                if reg:
                    if sp_off == 0:
                        self.ins("mv", reg, "sp")
                    else:
                        self.ins("addi", f"{reg}, sp", sp_off)
                elif self.ra_alloc.is_spilled(aname):
                    if sp_off == 0:
                        self.ins("mv", "t4", "sp")
                    else:
                        self.ins("addi", "t4, sp", sp_off)
                    self.ins("sd", "t4", f"{self.ra_alloc.spill_offset(aname)}(s0)")
            else:
                reg = self.ra_alloc.reg(aname)
                if reg:
                    self.ins("la", reg, aname)
                elif self.ra_alloc.is_spilled(aname):
                    self.ins("la", "t4", aname)
                    self.ins("sd", "t4", f"{self.ra_alloc.spill_offset(aname)}(s0)")
    def arr_addr(self, arr, off, addr_reg="t4"):
        if is_int_literal(off):
            v = to_int(off)
            if self.ra_alloc.is_spilled(arr):
                self.ins("ld", addr_reg, f"{self.ra_alloc.spill_offset(arr)}(s0)")
                if v != 0:
                    self.ins("addi", addr_reg, addr_reg, v)
            else:
                base_r = self.ra_alloc.reg(arr)
                if base_r is None:
                    self.ins("la", addr_reg, arr)
                    if v != 0:
                        self.ins("addi", addr_reg, addr_reg, v)
                elif v == 0:
                    if base_r != addr_reg:
                        self.ins("mv", addr_reg, base_r)
                else:
                    self.ins("addi", addr_reg, base_r, v)
        else:
            off_r = self.var_reg_or_load(off, "t6")
            if off_r != "t6":
                self.ins("mv", "t6", off_r)
            if self.ra_alloc.is_spilled(arr):
                self.ins("ld", addr_reg, f"{self.ra_alloc.spill_offset(arr)}(s0)")
            else:
                base_r = self.ra_alloc.reg(arr)
                if base_r is None:
                    self.ins("la", addr_reg, arr)
                elif base_r != addr_reg:
                    self.ins("mv", addr_reg, base_r)
            self.ins("add", addr_reg, addr_reg, "t6")
        return addr_reg
    def emit_call(self, fname):
        param_types = getattr(self, '_fn_param_types', {}).get(fname, [])
        n = len(self.param_q)
        ordered = []
        for i in range(n):
            raw = self.param_q[n - 1 - i]
            val_str = str(raw)

            cast_m = re.match(r'^\((\w+)\)\s*(.+)$', val_str)
            if cast_m:
                explicit_type = cast_m.group(1)
                val = cast_m.group(2).strip()
                float_types = {'float', 'double'}
                int_types   = {'int', 'long', 'short', 'char'}
                if explicit_type in float_types:
                    ptype = 'float'
                elif explicit_type in int_types:
                    ptype = 'int'
                else:
                    ptype = explicit_type
            else:
                val = val_str
                if i < len(param_types):
                    ptype = param_types[i]
                    if ptype not in ('float', 'double'):
                        if re.match(r'^[A-Za-z_]\w*$', val) and get_type(val) in ('float', 'double'):
                            ptype = get_type(val)
                else:
                    ptype = 'int'
                    if is_num_literal(val) and not is_int_literal(val):
                        ptype = 'float'
                    elif re.match(r'^[A-Za-z_]\w*$', val) and get_type(val) in ('float', 'double'):
                        ptype = get_type(val)
            if val_str.startswith('&'):
                ptype = '__ref__'
                val   = val_str  
            ordered.append((val, ptype))
        int_arg_idx   = 0
        float_arg_idx = 0
        stack_args = []
        for val, param_type in ordered:
            if param_type == '__ref__':
                ref_var = val[1:].strip()   
                if self._is_global_scalar(ref_var):
                    if int_arg_idx < 8:
                        self.ins("la", f"a{int_arg_idx}", ref_var)
                        int_arg_idx += 1
                    else:
                        self.ins("la", "t4", ref_var)
                        self.ins("addi", "sp, sp", "-8")
                        self.ins("sd",   "t4", "0(sp)")
                        stack_args.append(('__skip__', False))
                else:
                    if not self.ra_alloc.is_spilled(ref_var):
                        off = self.ra_alloc.force_spill(ref_var)
                        r   = self.ra_alloc._map.get(ref_var)
                        if r:
                            self.ins(store_ins(ref_var), r, f"{off}(s0)")
                    else:
                        off = self.ra_alloc.spill_offset(ref_var)
                    if int_arg_idx < 8:
                        self.ins("addi", f"a{int_arg_idx}", "s0", str(off))
                        int_arg_idx += 1
                    else:
                        self.ins("addi", "t4", "s0", str(off))
                        self.ins("addi", "sp, sp", "-8")
                        self.ins("sd",   "t4", "0(sp)")
                        stack_args.append(('__skip__', False))
                continue
            val_is_float = param_type in ('float', 'double')
            if val_is_float:
                if float_arg_idx < 8:
                    fa_reg = f"fa{float_arg_idx}"
                    float_arg_idx += 1
                    if is_num_literal(val) and not is_int_literal(val):
                        lname = f".flt{len(self.flt_lits)}"
                        self.flt_lits.append((lname, val))
                        self.ins("la",  "t4", lname)
                        self.ins("fld", fa_reg, "0(t4)")
                    elif is_int_literal(val):
                        self.ins("li", "t4", to_int(val))
                        self.ins(int_to_double_ins(val), fa_reg, "t4")
                    elif self.ra_alloc.is_spilled(val):
                        if get_type(val) in ('float', 'double'):
                            self.ins("fld", fa_reg, f"{self.ra_alloc.spill_offset(val)}(s0)")
                        else:
                            ins = load_ins(val)
                            cvt = "fcvt.d.l" if get_type(val) == 'long' else "fcvt.d.w"
                            self.ins(ins, "t4", f"{self.ra_alloc.spill_offset(val)}(s0)")
                            self.ins(cvt, fa_reg, "t4")
                    else:
                        r = self.ra_alloc.reg(val)
                        fp_r = self._is_fp_reg(val)
                        if fp_r:
                            if fp_r != fa_reg:
                                self.ins("fmv.d", fa_reg, fp_r)
                        elif get_type(val) in ('float', 'double'):
                            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                            if r and r in _fp_regs:
                                if r != fa_reg:
                                    self.ins("fmv.d", fa_reg, r)
                            else:
                                self.ins("fmv.d.x", fa_reg, r if r else "zero")
                        else:
                            cvt = "fcvt.d.l" if get_type(val) == 'long' else "fcvt.d.w"

                            if self._is_global_scalar(val):
                                self.ins("la", "t6", val)
                                ld = "ld" if get_type(val) == 'long' else "lw"
                                self.ins(ld, "t4", "0(t6)")
                                self.ins(cvt, fa_reg, "t4")
                            else:
                                self.ins(cvt, fa_reg, r if r else "zero")
                else:
                    stack_args.append((val, True))
            else:
                if int_arg_idx < 8:
                    a_reg = f"a{int_arg_idx}"
                    int_arg_idx += 1
                    if is_num_literal(val) and not is_int_literal(val):
                        self.ins("li", a_reg, to_int(val))
                    elif re.match(r'^[A-Za-z_]\w*$', val) and get_type(val) in ('float', 'double'):
       
                        if self.ra_alloc.is_spilled(val):
                            self.ins("fld", "fa0", f"{self.ra_alloc.spill_offset(val)}(s0)")
                        else:
                            r = self.ra_alloc.reg(val)
                            fp_r = self._is_fp_reg(val)
                            if fp_r:
                                if fp_r != "fa0":
                                    self.ins("fmv.d", "fa0", fp_r)
                            else:
                                _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                                if r and r in _fp_regs:
                                    if r != "fa0":
                                        self.ins("fmv.d", "fa0", r)
                                else:
                                    self.ins("fmv.d.x", "fa0", r if r else "zero")
                        self.ins("fcvt.w.d", a_reg, "fa0", "rtz")
                    else:
                        self.load(val, a_reg)
                else:
                    stack_args.append((val, False))
        for val, is_flt in reversed(stack_args):
            if val == '__skip__':  
                continue
            if is_flt:
                if is_num_literal(val) and not is_int_literal(val):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, val))
                    self.ins("la",  "t4", lname)
                    self.ins("fld", "fa0", "0(t4)")
                else:
                    if is_int_literal(val):
                        self.ins("li", "t4", to_int(val))
                        self.ins(int_to_double_ins(val), "fa0", "t4")
                    else:
                        self._load_float_var_into(val, "fa0")
                self.ins("addi", "sp, sp", "-8")
                self.ins("fsd",  "fa0", "0(sp)")
            else:
                self.load(val, "t4")
                self.ins("addi", "sp, sp", "-8")
                self.ins("sd",   "t4", "0(sp)")
        self.ins("call", fname)
        if stack_args:
            self.ins("addi", "sp, sp", str(8 * len(stack_args)))
        self.param_q.clear()
    def _global_type_prescan(self):
        _IS_TEMP = re.compile(r'^t\d+$')
        for varname, declared_type in _symtab_var_types.items():
            if not _IS_TEMP.match(varname):
                set_type(varname, declared_type)
        _TYPE_WIDTH = {'char':1,'short':2,'int':4,'long':8,
                       'float':4,'double':8}
        for _, instr in self.tac:
            m = re.match(r'^print(int|long|short|float|double|char)\s+(\w+)$', instr)
            if m:
                kind, var = m.group(1), m.group(2)
                tmap = {'int':'int','long':'long','short':'short',
                        'float':'float','double':'double','char':'char'}
                hint = tmap[kind]
                if _TYPE_WIDTH.get(hint, 0) > _TYPE_WIDTH.get(get_type(var), 0):
                    set_type(var, hint)
                continue
            m = re.match(r'^input(int|long|short|float|double|char)\s+(\w+)$', instr)
            if m:
                kind, var = m.group(1), m.group(2)
                tmap = {'int':'int','long':'long','short':'short',
                        'float':'float','double':'double','char':'char'}
                hint = tmap[kind]
                if _TYPE_WIDTH.get(hint, 0) > _TYPE_WIDTH.get(get_type(var), 0):
                    set_type(var, hint)
                continue
            m = re.match(r'^(\w+)\s*=\s*\((float|double|long|short|char|int)\)\s*\S+$', instr)
            if m:
                var, typ = m.group(1), m.group(2)
                set_type(var, typ)
                continue
        cur_fn_params = []
        in_fn = False
        cur_fn = None
        fn_params = {}
        fn_param_types = {}
        for _, instr in self.tac:
            m_bf = re.match(r'^BeginFunc\s+(\w+)', instr)
            m_ef = re.match(r'^EndFunc\b', instr)
            m_pp = re.match(r'^PopParam\s+(\w+)$', instr)
            if m_bf:
                in_fn = True; cur_fn = m_bf.group(1); cur_fn_params = []
            elif m_pp and in_fn:
                cur_fn_params.append(m_pp.group(1))
            elif m_ef and in_fn:
                fn_params[cur_fn] = list(cur_fn_params)
                in_fn = False
        _scoped_type = {}   
        in_fn = False; cur_fn = None
        for _, instr in self.tac:
            m_bf = re.match(r'^BeginFunc\s+(\w+)', instr)
            m_ef = re.match(r'^EndFunc\b', instr)
            if m_bf:
                in_fn = True; cur_fn = m_bf.group(1); continue
            if m_ef:
                in_fn = False; cur_fn = None; continue
            if not in_fn:
                continue
            m = re.match(r'^print(int|long|short|float|double|char)\s+(\w+)$', instr)
            if m:
                kind, var = m.group(1), m.group(2)
                tmap = {'int':'int','long':'long','short':'short',
                        'float':'float','double':'double','char':'char'}
                _scoped_type[f'{cur_fn}::{var}'] = tmap[kind]
                continue
            m = re.match(r'^(\w+)\s*=\s*\((float|double|long|short|char|int)\)\s*\S+$', instr)
            if m:
                var, typ = m.group(1), m.group(2)
                key = f'{cur_fn}::{var}'
                if key not in _scoped_type:
                    _scoped_type[key] = typ
                continue
        _callsite_arg_types = {}   
        _ref_type = {}   
        for _, instr in self.tac:
            m_ref = re.match(r'^(\w+)\s*=\s*ref\s+(\w+)$', instr)
            if m_ref:
                dst_r, src_r = m_ref.group(1), m_ref.group(2)
                src_t = _symtab_var_types.get(src_r, get_type(src_r))
                if src_t and not src_t.startswith('ptr:'):
                    _ref_type[dst_r] = f'ptr:{src_t}'
                elif src_t:
                    _ref_type[dst_r] = src_t
        tac_instrs = [instr for _, instr in self.tac]
        for i, instr in enumerate(tac_instrs):
            cm = re.match(r'^(?:\w+\s*=\s*)?Call\s+(\w+)$', instr)
            if not cm:
                continue
            callee = cm.group(1)
            push_args = []
            for k in range(i - 1, -1, -1):
                pm = re.match(r'^PushParam\s+(.+)$', tac_instrs[k].strip())
                if pm:
                    push_args.insert(0, pm.group(1).strip())
                elif re.match(r'^(BeginFunc|EndFunc)\b', tac_instrs[k].strip()):
                    break
                elif re.match(r'^(?:\w+\s*=\s*)?Call\b', tac_instrs[k].strip()):
                    break
            actual_types = []
            for arg in push_args:
                if arg.startswith('&'):
                    ref_var = arg[1:].strip()
                    src_t = _symtab_var_types.get(ref_var, get_type(ref_var))
                    actual_types.append(f'ptr:{src_t}' if src_t and not src_t.startswith('ptr:') else (src_t or 'ptr:int'))
                elif arg in _ref_type:
                    actual_types.append(_ref_type[arg])
                elif re.match(r'^[A-Za-z_]\w*$', arg):
                    actual_types.append(_symtab_var_types.get(arg, get_type(arg)) or 'int')
                else:
                    actual_types.append('int')
            if callee not in _callsite_arg_types:
                _callsite_arg_types[callee] = actual_types
            else:
                existing = _callsite_arg_types[callee]
                for idx in range(min(len(existing), len(actual_types))):
                    if (actual_types[idx].startswith('ptr:') and
                            existing[idx].startswith('ptr:') and
                            actual_types[idx] != existing[idx]):
                        if existing[idx] == 'ptr:int':
                            existing[idx] = actual_types[idx]
        for fname, params in fn_params.items():
            ptypes = []
            callsite_types = _callsite_arg_types.get(fname, [])
            for idx, pvar in enumerate(params):
                scoped_key = f'{fname}::{pvar}'
                if scoped_key in _scoped_type:
                    ptype = _scoped_type[scoped_key]
                elif pvar in _symtab_var_types and not _IS_TEMP.match(pvar):
                    symtab_ptype = _symtab_var_types[pvar]
                    if (symtab_ptype.startswith('ptr:') and
                            idx < len(callsite_types) and
                            callsite_types[idx].startswith('ptr:') and
                            callsite_types[idx] != symtab_ptype):
                        ptype = callsite_types[idx]
                    else:
                        ptype = symtab_ptype
                else:
                    ptype = 'int'
                ptypes.append(ptype)
            fn_param_types[fname] = ptypes
        for fname, params in fn_params.items():
            ptypes = fn_param_types.get(fname, [])
            for idx, pvar in enumerate(params):
                scoped_key = f'{fname}::{pvar}'
                if idx < len(ptypes) and scoped_key not in _scoped_type:
                    _scoped_type[scoped_key] = ptypes[idx]
                    if ptypes[idx].startswith('ptr:') and not get_type(pvar).startswith('ptr:'):
                        set_type(pvar, ptypes[idx])
        self._fn_scoped_types = _scoped_type
        def _can_infer(varname):
            return _IS_TEMP.match(varname) or varname not in _symtab_var_types
        changed = True
        while changed:
            changed = False
            for _, instr in self.tac:
                m = re.match(r'^(\w+)\s*=\s*([A-Za-z_]\w*)$', instr)
                if m:
                    dst, src = m.group(1), m.group(2)
                    if (_can_infer(dst) and
                            get_type(src) in ('float','double') and
                            get_type(dst) not in ('float','double')):
                        set_type(dst, get_type(src)); changed = True
                    continue
                m = re.match(r'^(\w+)\s*=\s*(\S+)\s*[+\-*/]\s*(\S+)$', instr)
                if m:
                    dst, op1, op2 = m.group(1), m.group(2), m.group(3)
                    if not (re.match(r'^[A-Za-z_]\w*(\[\w+\])?$', op1) or is_num_literal(op1)):
                        m = None
                if m:
                    dst, op1, op2 = m.group(1), m.group(2), m.group(3)
                    op1_float = (is_num_literal(op1) and not is_int_literal(op1)) or \
                                get_type(op1) in ('float','double')
                    op2_float = (is_num_literal(op2) and not is_int_literal(op2)) or \
                                get_type(op2) in ('float','double')
                    if (_can_infer(dst) and
                            (op1_float or op2_float) and
                            get_type(dst) not in ('float','double')):
                        set_type(dst, 'float'); changed = True
        fn_return_types = {}
        cur_fn = None
        for _, instr in self.tac:
            m_bf = re.match(r'^BeginFunc\s+(\w+)', instr)
            m_ef = re.match(r'^EndFunc\b', instr)
            m_ret = re.match(r'^Return\s+(\S+)$', instr)
            if m_bf:
                cur_fn = m_bf.group(1)
            elif m_ef:
                cur_fn = None
            elif m_ret and cur_fn:
                val = m_ret.group(1)
                if (is_num_literal(val) and not is_int_literal(val)) or \
                        get_type(val) in ('float', 'double'):
                    fn_return_types[cur_fn] = 'float'
                elif cur_fn not in fn_return_types:
                    fn_return_types[cur_fn] = 'int'

        self._fn_param_types = fn_param_types
        self._fn_return_types = fn_return_types
    def convert(self, tac_text):
        for raw in tac_text.splitlines():
            if not raw.strip():
                continue
            lnum, instr = parse_line(raw)
            if lnum is not None:
                self.tac.append((lnum, instr))
        self.tac = _copy_propagate(self.tac)
        for raw in tac_text.splitlines():
            m = re.match(r'^\s*\d+\s+//\s*DEAD\s+CONST\s*:\s*(\w+)\s*=\s*(-?\d+)', raw)
            if m:
                self._dead_const_vals[m.group(1)] = m.group(2)
        self.collect_targets()
        self._global_type_prescan()
        self.e()
        self.e(".text")
        func_order = [instr.split()[1]
                      for _, instr in self.tac
                      if re.match(r'^BeginFunc\s+', instr)]
        fn_slices = {}
        cur_fn, cur_slice = None, []
        for _, instr in self.tac:
            m_bf = re.match(r'^BeginFunc\s+(\w+)', instr)
            is_ef = bool(re.match(r'^EndFunc\b', instr))
            if m_bf:
                cur_fn    = m_bf.group(1)
                cur_slice = [instr]
            elif is_ef and cur_fn:
                cur_slice.append(instr)
                fn_slices[cur_fn] = cur_slice
                cur_fn = None
            elif cur_fn:
                cur_slice.append(instr)
        is_bare_tac        = not func_order
        has_main_func      = 'main' in func_order
        global_tac = []
        _in_fn = False
        for lnum, instr in self.tac:
            if re.match(r'^BeginFunc\b', instr):
                _in_fn = True
            elif re.match(r'^EndFunc\b', instr):
                _in_fn = False
            elif not _in_fn:
                global_tac.append((lnum, instr))
        is_mixed_tac       = bool(func_order) and bool(global_tac) and not has_main_func
        is_funcs_only      = bool(func_order) and not has_main_func and not global_tac
        if is_bare_tac:
            all_instrs = [instr for _, instr in self.tac]
            self.ra_alloc._array_names = set(self._arrays.keys())
            self._preseed_float_types(all_instrs)
            self.ra_alloc.set_safe_scratch_temps(list(self.tac))
            self.ra_alloc.run_graph_coloring(list(self.tac))
            bare_has_calls = self._fn_has_calls(all_instrs)
            self._prescan_function(all_instrs)
            sregs    = list(self.ra_alloc.used_sregs)
            fp_sregs = list(self.ra_alloc.used_fp_sregs)
            bare_needs_ra = bare_has_calls
            bare_needs_fp = self._tac_needs_fp(all_instrs, self.ra_alloc)
            if not bare_needs_fp:
                all_tac_temps_bare = set()
                for line in all_instrs:
                    for tok in re.findall(r'\bt\d+\b', line):
                        if get_type(tok) not in ('float', 'double'):
                            all_tac_temps_bare.add(tok)
                if all_tac_temps_bare - self.ra_alloc._safe_scratch:
                    bare_needs_fp = True
            float_reserve = 0
            if bare_needs_fp:
                fp_pool = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                for line in all_instrs:
                    for tok in re.findall(r'\b[A-Za-z_]\w*\b', line):
                        if (get_type(tok) in ('float', 'double')
                                and tok not in self.ra_alloc._map
                                and tok not in self.ra_alloc._spill):
                            float_reserve += 1
                float_reserve = min(float_reserve, 8)
            base_slots = self.ra_alloc.spill_slots
            if base_slots + float_reserve > 0:
                bare_needs_fp = True
            bare_frame = _compute_frame(len(sregs) + len(fp_sregs),
                                        base_slots + float_reserve,
                                        bare_needs_ra, bare_needs_fp)
            self._bare_sregs    = sregs
            self._bare_fp_sregs = fp_sregs
            self._bare_frame    = bare_frame
            self._bare_needs_ra = bare_needs_ra
            self._bare_needs_fp = bare_needs_fp
            self.e()
            self.e("    .globl   main")
            self.lbl("main")
            self.e("")
            if bare_frame > 0:
                self.ins("addi", "sp, sp", f"-{bare_frame}")
            off = bare_frame
            if bare_needs_ra:
                off -= 8; self.ins("sd", "ra", f"{off}(sp)")
            if bare_needs_fp:
                off -= 8; self.ins("sd", "s0", f"{off}(sp)")
            for reg in sregs:
                off -= 8; self.ins("sd", reg, f"{off}(sp)")
            for reg in fp_sregs:
                off -= 8; self.ins("fsd", reg, f"{off}(sp)")
            if bare_needs_fp:
                self.ins("addi", "s0, sp", str(bare_frame))
            self.in_main = True
            self.emit_array_la()
        if is_mixed_tac:
            global_instrs = [instr for _, instr in global_tac]
            fn_slices['__global_main__'] = (
                ['BeginFunc main 0'] + global_instrs + ['EndFunc main']
            )
        has_global_init = has_main_func and bool(global_tac)
        self._has_global_init = has_global_init
        pre_main_tac  = []
        post_main_tac = []
        if has_global_init:
            global_lnums_set = {lnum for lnum, _ in global_tac}
            seen_beginfunc_main = False
            for lnum, instr in self.tac:
                if re.match(r'^BeginFunc\s+main\b', instr):
                    seen_beginfunc_main = True
                elif re.match(r'^EndFunc\b', instr) and seen_beginfunc_main:
                    pass  
                elif lnum in global_lnums_set:
                    if not seen_beginfunc_main:
                        pre_main_tac.append((lnum, instr))
                    else:
                        post_main_tac.append((lnum, instr))
        has_post_main = bool(post_main_tac)
        self._has_post_main = has_post_main
        if has_global_init:
            self.e()
            self.e("    # -- global variable initialisation (called from main) --")
            self.e("__global_init:")
            saved_ra      = self.ra_alloc
            saved_fname   = self.fname
            saved_in_fn   = self._in_function
            saved_epilogue = self.epilogue_lbl
            self.ra_alloc     = RegAlloc()
            self.fname        = "__global_init"
            self._in_function = True
            self.epilogue_lbl = ".Lepilogue___global_init"
            self.in_main      = False
            self._local_arrays = {}
            self._fn_shadow_locals = set()  
            self._locally_defined  = set()
            global_instrs_only = [instr for _, instr in pre_main_tac]
            self._preseed_float_types(global_instrs_only)
            self.ra_alloc._array_names = set(self._arrays.keys())
            self.ra_alloc.set_safe_scratch_temps(list(pre_main_tac))
            self.ra_alloc.run_graph_coloring(list(pre_main_tac))
            self._prescan_function(global_instrs_only)
            _ginit_needs_fp = self._tac_needs_fp(global_instrs_only, self.ra_alloc)
            _ginit_needs_ra = self._fn_has_calls(global_instrs_only)
            _ginit_frame    = _compute_frame(
                len(list(self.ra_alloc.used_sregs)) +
                len(list(self.ra_alloc.used_fp_sregs)),
                self.ra_alloc.spill_slots + (4 if _ginit_needs_fp else 0),
                _ginit_needs_ra, _ginit_needs_fp)
            _ginit_frame = max(_ginit_frame, 16)
            self.ins("addi", "sp, sp", f"-{_ginit_frame}")
            _goff = _ginit_frame
            if _ginit_needs_ra:
                _goff -= 8; self.ins("sd", "ra", f"{_goff}(sp)")
            else:
                _goff -= 8; self.ins("sd", "ra", f"{_goff}(sp)")
            if _ginit_needs_fp:
                _goff -= 8; self.ins("sd", "s0", f"{_goff}(sp)")
                self.ins("addi", "s0, sp", str(_ginit_frame))
            global_arrays_used = [a for a in self._array_order if a in _global_arrays]
            if global_arrays_used:
                self.e(f"    # -- global array base pointers --")
                for aname in global_arrays_used:
                    reg = self.ra_alloc.reg(aname)
                    if reg:
                        self.ins("la", reg, aname)
                    elif self.ra_alloc.is_spilled(aname):
                        self.ins("la", "t4", aname)
                        self.ins("sd", "t4", f"{self.ra_alloc.spill_offset(aname)}(s0)")
            for lnum, instr in pre_main_tac:
                self._dispatch(lnum, instr, fn_slices)
            self.e()
            self.lbl(".Lepilogue___global_init")
            if _ginit_needs_fp:
                self.ins("ld", "s0", f"{_ginit_frame - 16}(sp)")
            self.ins("ld",   "ra", f"{_ginit_frame - 8}(sp)")
            self.ins("addi", "sp, sp", str(_ginit_frame))
            self.ins("ret")
            self.ra_alloc     = saved_ra
            self.fname        = saved_fname
            self._in_function = saved_in_fn
            self.epilogue_lbl = saved_epilogue
        if has_post_main:
            self.e()
            self.e("    # -- global code after main (called from wrapper) --")
            self.e("__global_post:")
            saved_ra2      = self.ra_alloc
            saved_fname2   = self.fname
            saved_in_fn2   = self._in_function
            saved_epilogue2 = self.epilogue_lbl
            self.ra_alloc     = RegAlloc()
            self.fname        = "__global_post"
            self._in_function = True
            self.epilogue_lbl = ".Lepilogue___global_post"
            self.in_main      = False
            self._local_arrays = {}
            self._fn_shadow_locals = set()
            self._locally_defined  = set()
            post_instrs_only = [instr for _, instr in post_main_tac]
            self._preseed_float_types(post_instrs_only)
            self.ra_alloc._array_names = set(self._arrays.keys())
            self.ra_alloc.set_safe_scratch_temps(list(post_main_tac))
            self.ra_alloc.run_graph_coloring(list(post_main_tac))
            self._prescan_function(post_instrs_only)
            _gpost_needs_fp = self._tac_needs_fp(post_instrs_only, self.ra_alloc)
            _gpost_needs_ra = self._fn_has_calls(post_instrs_only)
            _gpost_frame    = _compute_frame(
                len(list(self.ra_alloc.used_sregs)) +
                len(list(self.ra_alloc.used_fp_sregs)),
                self.ra_alloc.spill_slots + (4 if _gpost_needs_fp else 0),
                _gpost_needs_ra, _gpost_needs_fp)
            _gpost_frame = max(_gpost_frame, 16)
            self.ins("addi", "sp, sp", f"-{_gpost_frame}")
            _poff = _gpost_frame
            _poff -= 8; self.ins("sd", "ra", f"{_poff}(sp)")
            if _gpost_needs_fp:
                _poff -= 8; self.ins("sd", "s0", f"{_poff}(sp)")
                self.ins("addi", "s0, sp", str(_gpost_frame))
            for lnum, instr in post_main_tac:
                self._dispatch(lnum, instr, fn_slices)
            self.e()
            self.lbl(".Lepilogue___global_post")
            if _gpost_needs_fp:
                self.ins("ld", "s0", f"{_gpost_frame - 16}(sp)")
            self.ins("ld",   "ra", f"{_gpost_frame - 8}(sp)")
            self.ins("addi", "sp, sp", str(_gpost_frame))
            self.ins("ret")
            self.ra_alloc     = saved_ra2
            self.fname        = saved_fname2
            self._in_function = saved_in_fn2
            self.epilogue_lbl = saved_epilogue2
        if is_mixed_tac:
            global_lnums = {lnum for lnum, _ in global_tac}
            for lnum, instr in self.tac:
                if lnum not in global_lnums:
                    self._dispatch(lnum, instr, fn_slices)

            self.prologue('main', 0, fn_slices['__global_main__'])
            self.in_main = True
            self.emit_array_la()
            for lnum, instr in global_tac:
                self._dispatch(lnum, instr, fn_slices)
            global_missing_mixed = self._global_targets - self._global_lines
            if global_missing_mixed:
                self.e()
                self.e("    # -- loop-exit / out-of-range jump targets --")
                for n in sorted(global_missing_mixed):
                    self.lbl(self.tac_lbl(n))
            self.e()
            self.ins("li",   "a0", 0)
            self.ins("j",    self.epilogue_lbl)
            self.epilogue()
        elif is_funcs_only:
            for lnum, instr in self.tac:
                self._dispatch(lnum, instr, fn_slices)
            self.e()
            self.e("    # -- synthetic main (functions-only TAC) --")
            self.ins(".globl", "main")
            self.lbl("main")
            self.ins("addi", "sp, sp", "-16")
            self.ins("sd",   "ra",  "8(sp)")
            self.ins("li",   "a0", 0)
            self.ins("ld",   "ra",  "8(sp)")
            self.ins("addi", "sp, sp", "16")
            self.ins("ret")
        else:
            all_global_lnums = {lnum for lnum, _ in global_tac} if has_global_init else set()
            if has_post_main and 'main' in fn_slices:
                fn_slices['__compiler_main'] = fn_slices.pop('main')
            for lnum, instr in self.tac:
                if lnum in all_global_lnums:
                    continue
                if has_post_main:
                    instr = re.sub(r'^(BeginFunc\s+)main\b', r'\1__compiler_main', instr)
                    instr = re.sub(r'^(EndFunc\s+)main\b',   r'\1__compiler_main', instr)
                self._dispatch(lnum, instr, fn_slices)
            if has_post_main:
                self.e()
                self.e("    # -- real entry point: sequences global_init, user main, global_post --")
                self.ins(".globl", "main")
                self.lbl("main")
                self.ins("addi", "sp, sp", "-16")
                self.ins("sd",   "ra", "8(sp)")
                self.ins("call", "__global_init")
                self.ins("call", "__compiler_main")
                self.ins("call", "__global_post")
                self.ins("li",   "a0", 0)
                self.ins("ld",   "ra", "8(sp)")
                self.ins("addi", "sp, sp", "16")
                self.ins("ret")
        def _emit_bare_exit():
            bf       = getattr(self, '_bare_frame',    16)
            bra      = getattr(self, '_bare_needs_ra', False)
            bfp      = getattr(self, '_bare_needs_fp', False)
            bsregs   = getattr(self, '_bare_sregs',   [])
            bfpsregs = getattr(self, '_bare_fp_sregs', [])
            off = bf
            ra_off = None
            s0_off = None
            if bra:
                off -= 8; ra_off = off
            if bfp:
                off -= 8; s0_off = off
            sreg_offs = []
            for _ in bsregs:
                off -= 8; sreg_offs.append(off)
            fp_sreg_offs = []
            for _ in bfpsregs:
                off -= 8; fp_sreg_offs.append(off)
            for reg, roff in zip(bsregs, sreg_offs):
                self.ins("ld", reg, f"{roff}(sp)")
            for reg, roff in zip(bfpsregs, fp_sreg_offs):
                self.ins("fld", reg, f"{roff}(sp)")
            if bfp and s0_off is not None:
                self.ins("ld", "s0", f"{s0_off}(sp)")
            if bra and ra_off is not None:
                self.ins("ld", "ra", f"{ra_off}(sp)")
            if bf > 0:
                self.ins("addi", "sp, sp", str(bf))
            self.ins("li",  "a0", 0)
            self.ins("ret")
        global_missing = self._global_targets - self._global_lines
        if global_missing and not is_mixed_tac:
            self.e()
            self.e("    # -- program exit / out-of-range jump targets --")
            for n in sorted(global_missing):
                self.lbl(self.tac_lbl(n))
                if is_bare_tac:
                    _emit_bare_exit()
                else:
                    self.ins("nop")
        elif is_bare_tac:
            self.e()
            _emit_bare_exit()
        self.e()
        self.e(".data")
        FMT_TABLE = {
            '.fmt_int':        '.fmt_int:        .asciz "%d\\n"',
            '.fmt_long':       '.fmt_long:       .asciz "%ld\\n"',
            '.fmt_char':       '.fmt_char:       .asciz "%c\\n"',
            '.fmt_float':      '.fmt_float:      .asciz "%f\\n"',
            '.fmt_str':        '.fmt_str:        .asciz "%s\\n"',
            '.fmt_scan_int':   '.fmt_scan_int:   .asciz "%d"',
            '.fmt_scan_long':  '.fmt_scan_long:  .asciz "%ld"',
            '.fmt_scan_float': '.fmt_scan_float: .asciz "%lf"',
        }
        for key in ['.fmt_int','.fmt_long','.fmt_char','.fmt_float','.fmt_str',
                    '.fmt_scan_int','.fmt_scan_long','.fmt_scan_float']:
            if key in self._used_fmts:
                self.out.append(FMT_TABLE[key])
        for gname, gtype in sorted(_global_scalars.items()):
            if gtype == 'long' or gtype.startswith('ptr:'):
                self.out.append(f"{gname}: .dword 0")
            elif gtype == 'double':
                self.out.append(f"{gname}: .dword 0")
            elif gtype == 'short':
                self.out.append(f"{gname}: .short 0")
            elif gtype == 'char':
                self.out.append(f"{gname}: .byte 0")
            else:
                self.out.append(f"{gname}: .word 0")
        for aname in self._array_order:
            if aname not in _global_arrays and aname in getattr(self, '_local_arrays', {}):
                continue   
            atype   = get_type(aname)
            n_elems = getattr(self, '_array_nelems', {}).get(aname, None)
            if n_elems is None:
                declared = getattr(self, '_array_declared_size', {}).get(aname, 0)
                max_off  = self._arrays[aname]
                stride   = getattr(self, '_array_stride', {}).get(aname, 4)
                if declared > 0:
                    n_elems = declared + 1   
                else:
                    n_elems = (max_off // stride) + 3 if stride > 0 else 3
            if atype == 'char':
                zeros = ", ".join(["0"] * n_elems)
                self.out.append(f"{aname}: .byte {zeros}")
            elif atype == 'short':
                zeros = ", ".join(["0"] * n_elems)
                self.out.append(f"{aname}: .short {zeros}")
            elif atype == 'float':
                zeros = ", ".join(["0"] * n_elems)
                self.out.append(f"{aname}: .word {zeros}")
            elif atype == 'double':
                zeros = ", ".join(["0"] * n_elems)
                self.out.append(f"{aname}: .dword {zeros}")
            else:
                if atype == 'long':
                    zeros = ", ".join(["0"] * n_elems)
                    self.out.append(f"{aname}: .dword {zeros}")
                else:
                    zeros = ", ".join(["0"] * n_elems)
                    self.out.append(f"{aname}: .word {zeros}")
        for lname, s in self.str_lits:
            self.out.append(f"    {lname}: .asciz {s}")
        for lname, v in self.flt_lits:
            self.out.append(f"    {lname}: .double {v}")
        if self._used_externs:
            text_idx = next((i for i, l in enumerate(self.out) if l.strip() == '.text'), None)
            if text_idx is not None:
                extern_lines = [f"    .extern  {sym}" for sym in sorted(self._used_externs)]
                self.out[text_idx:text_idx] = extern_lines
        return "\n".join(self.out) + "\n"
    def _dispatch(self, lnum, instr, fn_slices=None):
        if (lnum in self.jump_targets
                and not re.match(r'^BeginFunc\b', instr)
                and lnum not in self._cross_scope_emitted):
            self.e()
            self.lbl(self.tac_lbl(lnum))
        if instr.startswith("//"):
            #self.e(f"    # [ELIM] {instr}")
            return
        _new_locals = set()
        if self._fn_shadow_locals:
            defs, _ = _extract_defs_uses(instr)
            _new_locals = defs & self._fn_shadow_locals
        try:
            self._dispatch_body(lnum, instr, fn_slices)
        finally:
            self._locally_defined |= _new_locals
    def _dispatch_body(self, lnum, instr, fn_slices=None):
        m = re.match(r'^BeginFunc\s+(\w+)(?:\s+(\d+))?$', instr)
        if m:
            fname  = m.group(1)
            nparams = int(m.group(2) or 0)
            slice_ = (fn_slices or {}).get(fname, [])
            self.prologue(fname, nparams, slice_)
            return
        m = re.match(r'^EndFunc\b', instr)
        if m:
            self.epilogue()
            return
        m = re.match(r'^PopParam\s+(\w+)$', instr)
        if m:
            var = m.group(1)
            scoped_key = f'{self.fname}::{var}'
            scoped_types = getattr(self, '_fn_scoped_types', {})
            if scoped_key in scoped_types:
                vtype = scoped_types[scoped_key]
            else:
                vtype = get_type(var)
            if vtype.startswith('ptr:') and not get_type(var).startswith('ptr:'):
                set_type(var, vtype)
            param_pos = self.int_pop_idx + self.float_pop_idx
            if param_pos in self._ref_param_indices:
                if self.int_pop_idx < 8:
                    ptr_reg = f"a{self.int_pop_idx}"
                    self.int_pop_idx += 1
                else:
                    stack_idx  = self.int_pop_idx - 8
                    caller_off = stack_idx * 8
                    ptr_reg    = "t4"
                    self.ins("ld", ptr_reg, f"{caller_off}(s0)")
                    self.int_pop_idx += 1
                ptr_off = self.ra_alloc.force_spill(var)
                self.e(f"    # PopParam {var} (ref ptr) <- {ptr_reg} -> [{ptr_off}(s0)]")
                self.ins("sd", ptr_reg, f"{ptr_off}(s0)")
                self._ref_params[var] = ptr_off
                return
            if vtype in ('float', 'double'):
                if self.float_pop_idx < 8:
                    arg_reg = f"fa{self.float_pop_idx}"
                    self.float_pop_idx += 1
                    self.e(f"    # PopParam {var} (float) <- {arg_reg}")
                    off = self.ra_alloc.force_spill(var)
                    self.ra_alloc._float_vars.add(var)
                    self.ins("fsd", arg_reg, f"{off}(s0)")
                else:
                    stack_idx = self.float_pop_idx - 8
                    self.float_pop_idx += 1
                    caller_off = stack_idx * 8
                    self.e(f"    # PopParam {var} (float) <- stack[{stack_idx}] @ {caller_off}(s0)")
                    off = self.ra_alloc.force_spill(var)
                    self.ra_alloc._float_vars.add(var)
                    self.ins("fld", "ft4", f"{caller_off}(s0)")
                    self.ins("fsd", "ft4", f"{off}(s0)")
            elif vtype.startswith('ptr:'):
                if self.int_pop_idx < 8:
                    arg_reg = f"a{self.int_pop_idx}"
                    self.int_pop_idx += 1
                    self.e(f"    # PopParam {var} (ptr) <- {arg_reg}")
                    off = self.ra_alloc.force_spill(var)
                    self.ins("sd", arg_reg, f"{off}(s0)")
                else:
                    stack_idx  = self.int_pop_idx - 8
                    self.int_pop_idx += 1
                    caller_off = stack_idx * 8
                    self.e(f"    # PopParam {var} (ptr) <- stack[{stack_idx}] @ {caller_off}(s0)")
                    self.ins("ld", "t4", f"{caller_off}(s0)")
                    off = self.ra_alloc.force_spill(var)
                    self.ins("sd", "t4", f"{off}(s0)")
            else:
                if self.int_pop_idx < 8:
                    arg_reg = f"a{self.int_pop_idx}"
                    self.int_pop_idx += 1
                    self.e(f"    # PopParam {var} <- {arg_reg}")
                    self.store_var(var, arg_reg)
                else:
                    stack_idx = self.int_pop_idx - 8
                    self.int_pop_idx += 1
                    caller_off = stack_idx * 8
                    self.e(f"    # PopParam {var} <- stack[{stack_idx}] @ {caller_off}(s0)")
                    self.ins("ld", "t4", f"{caller_off}(s0)")
                    self.store_var(var, "t4")
            return
        m = re.match(r'^PushParam\s+(.+)$', instr)
        if m:
            self.param_q.append(m.group(1).strip())
            return
        m = re.match(r'^(\w+)\s*=\s*Call\s+(\w+)$', instr)
        if m:
            dst_var, fname = m.group(1), m.group(2)
            self.emit_call(fname)
            ret_is_float = get_type(dst_var) in ('float', 'double') or \
                           self._fn_return_types.get(fname) in ('float', 'double')
            if ret_is_float:
                off = self.ra_alloc.force_spill(dst_var)
                self.ins("fsd", "fa0", f"{off}(s0)")
                self.ra_alloc._float_vars.add(dst_var)
                set_type(dst_var, 'float')
                if self._is_global_scalar_write(dst_var):
                    self._store_float_result("fa0", dst_var)
            else:
                self.store_var(dst_var, "a0")
                if self._is_global_scalar_write(dst_var):
                    self._store_global(dst_var, "a0")
            return
        m = re.match(r'^Call\s+(\w+)$', instr)
        if m:
            self.emit_call(m.group(1))
            return
        m = re.match(r'^Return\s+(.+)$', instr)
        if m:
            val = m.group(1).strip()
            val_is_float = (
                (is_num_literal(val) and not is_int_literal(val)) or
                get_type(val) in ('float', 'double') or
                (val in self.ra_alloc._float_vars)
            )
            if val_is_float:
                if self.ra_alloc.is_spilled(val):
                    self.ins("fld", "fa0", f"{self.ra_alloc.spill_offset(val)}(s0)")
                elif is_num_literal(val) and not is_int_literal(val):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, val))
                    self.ins("la",  "t4", lname)
                    self.ins("fld", "fa0", "0(t4)")
                else:
                    r = self.ra_alloc.reg(val)
                    _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                    if r and r in _fp_regs:
                        if r != "fa0":
                            self.ins("fmv.d", "fa0", r)
                    else:
                        cvt = "fcvt.d.l" if get_type(val) == 'long' else "fcvt.d.w"
                        self.ins(cvt, "fa0", r if r else "zero")
            else:
                src_r = self.operand(val, "a0")
                if src_r != "a0":
                    self.ins("mv", "a0", src_r)
            self.ins("j", self.epilogue_lbl)
            return
        if instr.strip() == "Return":
            self.ins("li", "a0", 0)
            self.ins("j", self.epilogue_lbl)
            return
        m = re.match(r'^goto\s+(\d+)$', instr)
        if m:
            tgt = int(m.group(1))
            next_lnum = None
            for ll, _ in self.tac:
                if ll > lnum:
                    next_lnum = ll
                    break
            if tgt != next_lnum:
                self.ins("j", self.tac_lbl(tgt))
            return
        m = re.match(
            r'^if\s+(\S+)\s+(==|!=|<=|>=|<<|>>|<|>|lt|gt|le|ge|eq|ne)\s+(\S+)\s+goto\s+(\d+)$',
            instr)
        if m:
            lhs, op, rhs, tgt = m.group(1), m.group(2), m.group(3), int(m.group(4))
            self.emit_branch(lhs, op, rhs, self.tac_lbl(tgt))
            return
        m = re.match(r'^print(int|long|short|float|double|char|string)\s+(.+)$', instr)
        if m:
            kind, val = m.group(1), m.group(2).strip()
            if re.match(r'^[A-Za-z_]\w*$', val):
                if kind == 'long':   set_type(val, 'long')
                elif kind == 'short': set_type(val, 'short')
                elif kind == 'double': set_type(val, 'double')
                elif kind == 'float':  set_type(val, 'float')
                elif kind == 'char':   set_type(val, 'char')
            if kind in ("int", "short"):
                real_type = _global_scalars.get(val, get_type(val)) \
                    if re.match(r'^[A-Za-z_]\w*$', val) else 'int'
                if real_type == 'long':
                    self.use_extern("printf"); self.use_fmt(".fmt_long")
                    self.ins("la", "a0", ".fmt_long")
                    arr_m = re.match(r'^(\w+)\[(\w+)\]$', val)
                    if arr_m:
                        self._resolve_operand(val, "t4")
                        self.ins("mv", "a1", "t4")
                    else:
                        r = self.operand(val, "t4")
                        if r != "a1":
                            self.ins("mv", "a1", r)
                    self.ins("call", "printf")
                else:
                    self.use_extern("printf"); self.use_fmt(".fmt_int")
                    self.ins("la", "a0", ".fmt_int")
                    arr_m = re.match(r'^(\w+)\[(\w+)\]$', val)
                    if arr_m:
                        self._resolve_operand(val, "t4")
                        self.ins("mv", "a1", "t4")
                    else:
                        r = self.operand(val, "t4")
                        if r != "a1":
                            self.ins("mv", "a1", r)
                    self.ins("call", "printf")
            elif kind == "long":
                self.use_extern("printf"); self.use_fmt(".fmt_long")
                self.ins("la", "a0", ".fmt_long")
                arr_m = re.match(r'^(\w+)\[(\w+)\]$', val)
                if arr_m:
                    self._resolve_operand(val, "t4")
                    self.ins("mv", "a1", "t4")
                else:
                    r = self.operand(val, "t4")
                    if r != "a1":
                        self.ins("mv", "a1", r)
                self.ins("call", "printf")
            elif kind == "char":
                val = self._resolve_char_literal(val)
                is_str_var = val in self.ra_alloc._string_vars
                arr_m = re.match(r'^(\w+)\[(\w+)\]$', val)
                if is_str_var:
                    self.use_extern("printf"); self.use_fmt(".fmt_str")
                    self.ins("la", "a0", ".fmt_str")
                    r = self.operand(val, "t4")
                    if r != "a1":
                        self.ins("mv", "a1", r)
                    self.ins("call", "printf")
                elif arr_m:
                    self.use_extern("printf"); self.use_fmt(".fmt_char")
                    self.ins("la", "a0", ".fmt_char")
                    self._resolve_operand(val, "t4")
                    self.ins("mv", "a1", "t4")
                    self.ins("call", "printf")
                else:
                    self.use_extern("printf"); self.use_fmt(".fmt_char")
                    self.ins("la", "a0", ".fmt_char")
                    r = self.operand(val, "t4")
                    if r != "a1":
                        self.ins("mv", "a1", r)
                    self.ins("call", "printf")
            elif kind in ("float", "double"):
                self.use_extern("printf"); self.use_fmt(".fmt_float")
                self.ins("la", "a0", ".fmt_float")
                arr_m = re.match(r'^(\w+)\[(\w+)\]$', val)
                if arr_m and get_type(arr_m.group(1)) in ('float', 'double'):
                    self._resolve_operand(val, "t4")
                elif is_num_literal(val):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, val))
                    self.ins("la",  "t4",  lname)
                    self.ins("fld", "fa0", "0(t4)")
                else:
                    self._load_float_var_into(val, "fa0")
                self.ins("fmv.x.d", "a1", "fa0")
                self.ins("call",    "printf")
            elif kind == "string":
                self.use_extern("printf"); self.use_fmt(".fmt_str")
                self.ins("la", "a0", ".fmt_str")
                if val.startswith('"'):
                    slbl = f".str{len(self.str_lits)}"
                    self.str_lits.append((slbl, val))
                    self.ins("la", "a1", slbl)
                else:
                    r = self.operand(val, "t4")
                    if r != "a1":
                        self.ins("mv", "a1", r)
                self.ins("call", "printf")
            return
        m = re.match(r'^input(int|long|short|float|double|char)\s+(\w+)\[(\w+)\]$', instr)
        if m:
            kind, arr, off = m.group(1), m.group(2), m.group(3)
            arr_is_float = (kind in ('float', 'double') or
                            get_type(arr) in ('float', 'double'))
            if kind in ('int', 'short', 'long'):
                fmt = '.fmt_scan_long' if kind == 'long' else '.fmt_scan_int'
                ld  = 'ld'            if kind == 'long' else 'lw'
                si  = 'sd'            if kind == 'long' else 'sw'
                self.use_extern('scanf'); self.use_fmt(fmt)
                self.ins('addi', 'sp, sp', '-16')
                self.arr_addr(arr, off, 't4')
                self.ins('sd',   't4', '8(sp)')        
                self.ins('la',   'a0', fmt)
                self.ins('mv',   'a1', 'sp')          
                self.ins('call', 'scanf')
                self.ins(ld,     't3', '0(sp)')        
                self.ins('ld',   't4', '8(sp)')        
                self.ins('addi', 'sp, sp', '16')
                self.ins(si,     't3', '0(t4)')       
            elif arr_is_float:
                self.use_extern('scanf'); self.use_fmt('.fmt_scan_float')
                self.ins('addi', 'sp, sp', '-16')
                self.arr_addr(arr, off, 't4')
                self.ins('sd',   't4', '8(sp)')        
                self.ins('la',   'a0', '.fmt_scan_float')
                self.ins('mv',   'a1', 'sp')           
                self.ins('call', 'scanf')
                self.ins('fld',  'fa0', '0(sp)')      
                self.ins('fcvt.s.d', 'fa0', 'fa0')    
                self.ins('ld',   't4', '8(sp)')        
                self.ins('addi', 'sp, sp', '16')
                self.ins('fsw',  'fa0', '0(t4)')       
            elif kind == 'char':
                self.use_extern('getchar')
                self.arr_addr(arr, off, 't4')
                self.ins('call', 'getchar')
                self.ins('sb',   'a0', '0(t4)')
            return
        m = re.match(r'^input(int|long|short|float|double|char|string)\s+(\w+)$', instr)
        if m:
            kind, var = m.group(1), m.group(2)
            if kind == 'long':   set_type(var, 'long')
            elif kind == 'short': set_type(var, 'short')
            elif kind == 'double': set_type(var, 'double')
            elif kind == 'float':  set_type(var, 'float')
            elif kind == 'char':   set_type(var, 'char')
            if kind in ("int", "short"):
                self.use_extern("scanf"); self.use_fmt(".fmt_scan_int")
                self.ins("addi", "sp, sp", "-8")
                self.ins("la",   "a0", ".fmt_scan_int")
                self.ins("mv",   "a1", "sp")
                self.ins("call", "scanf")
                self.ins("lw",   "t4", "0(sp)")
                self.ins("addi", "sp, sp", "8")
                self.store_var(var, "t4")
            elif kind == "long":
                self.use_extern("scanf"); self.use_fmt(".fmt_scan_long")
                self.ins("addi", "sp, sp", "-8")
                self.ins("la",   "a0", ".fmt_scan_long")
                self.ins("mv",   "a1", "sp")
                self.ins("call", "scanf")
                self.ins("ld",   "t4", "0(sp)")
                self.ins("addi", "sp, sp", "8")
                self.store_var(var, "t4")
            elif kind == "char":
                self.use_extern("getchar")
                self.ins("call", "getchar")
                self.store_var(var, "a0")
            elif kind in ("float", "double"):
                self.use_extern("scanf"); self.use_fmt(".fmt_scan_float")
                self.ins("addi", "sp, sp", "-8")
                self.ins("la",   "a0", ".fmt_scan_float")
                self.ins("mv",   "a1", "sp")
                self.ins("call", "scanf")
                self.ins("fld",  "fa0", "0(sp)")
                self.ins("addi", "sp, sp", "8")
                off = self.ra_alloc.force_spill(var)
                self.ins("fsd",  "fa0", f"{off}(s0)")
                self.ra_alloc._float_vars.add(var)
                # Bug fix 2: if var is a global scalar float, also write the scanned
                # value back to the global .data label so that subsequent reads from
                # the global (e.g. show(f)) see the correct value.
                if var in _global_scalars and _global_scalars[var] in ('float', 'double'):
                    self._store_float_result("fa0", var)
            elif kind == "string":
                self.use_extern("fgets")
                self.load(var, "a0")
                self.ins("li",   "a1", "256")
                self.ins("la",   "a2", "stdin")
                self.ins("lw",   "a2", "0(a2)")
                self.ins("call", "fgets")
            return
        m = re.match(r'^(\w+)\[(\d+)\]\s*=\s*(.+)$', instr)
        if m:
            arr, byte_off, val = m.group(1), int(m.group(2)), m.group(3).strip()
            val = self._resolve_char_literal(val)
            self.arr_addr(arr, str(byte_off), "t4")
            arr_is_float = get_type(arr) in ('float', 'double')
            rhs_m = re.match(r'^(\w+)\[(\w+)\]$', val)
            if arr_is_float:
                if rhs_m:
                    self.arr_addr(rhs_m.group(1), rhs_m.group(2), "t5")
                    self.ins("flw", "fa1", "0(t5)")
                    self.ins("fsw", "fa1", "0(t4)")
                elif is_num_literal(val) and not is_int_literal(val):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, val))
                    self.ins("la",  "t5", lname)
                    self.ins("fld", "fa1", "0(t5)")
                    self.ins("fcvt.s.d", "fa1", "fa1")
                    self.ins("fsw", "fa1", "0(t4)")
                elif is_int_literal(val):
                    self.ins("li", "t5", to_int(val))
                    self.ins(int_to_float_ins(val), "fa1", "t5")
                    self.ins("fsw", "fa1", "0(t4)")
                else:
                    if self.ra_alloc.is_spilled(val):
                        src_is_fp = (get_type(val) in ('float', 'double') or
                                     val in self.ra_alloc._float_vars)
                        if src_is_fp:
                            self.ins("fld", "fa1", f"{self.ra_alloc.spill_offset(val)}(s0)")
                            self.ins("fcvt.s.d", "fa1", "fa1")
                        else:
                            self.ins("lw", "t5", f"{self.ra_alloc.spill_offset(val)}(s0)")
                            self.ins("fcvt.s.w", "fa1", "t5")
                    else:
                        r = self.ra_alloc.reg(val)
                        src_is_fp = (get_type(val) in ('float', 'double') or
                                     val in self.ra_alloc._float_vars)
                        if src_is_fp:
                            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                            if r and r in _fp_regs:
                                self.ins("fcvt.s.d", "fa1", r)
                            else:
                                self.ins("fmv.d.x", "fa1", r if r else "zero")
                                self.ins("fcvt.s.d", "fa1", "fa1")
                        else:
                            self.ins("fcvt.s.w", "fa1", r if r else "zero")
                    self.ins("fsw", "fa1", "0(t4)")
            else:
                if rhs_m:
                    self.arr_addr(rhs_m.group(1), rhs_m.group(2), "t5")
                    ins = load_ins(rhs_m.group(1))
                    self.ins(ins, "t3", "0(t5)")
                else:
                    self.load(val, "t3")
                s_ins = store_ins(arr)
                self.ins(s_ins, "t3", "0(t4)")
            return
        m = re.match(r'^(\w+)\[(\w+)\]\s*=\s*(.+)$', instr)
        if m:
            arr, off_var, val = m.group(1), m.group(2), m.group(3).strip()
            val = self._resolve_char_literal(val)
            arr_is_float = get_type(arr) in ('float', 'double')
            rhs_m = re.match(r'^(\w+)\[(\w+)\]$', val)
            if arr_is_float:
                if rhs_m:
                    self.arr_addr(rhs_m.group(1), rhs_m.group(2), "t5")
                    self.ins("flw", "fa1", "0(t5)")
                    self.arr_addr(arr, off_var, "t4")
                    self.ins("fsw", "fa1", "0(t4)")
                elif is_num_literal(val) and not is_int_literal(val):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, val))
                    self.ins("la",  "t5", lname)
                    self.ins("fld", "fa1", "0(t5)")
                    self.ins("fcvt.s.d", "fa1", "fa1")
                    self.arr_addr(arr, off_var, "t4")
                    self.ins("fsw", "fa1", "0(t4)")
                elif is_int_literal(val):
                    self.ins("li", "t5", to_int(val))
                    self.ins(int_to_float_ins(val), "fa1", "t5")
                    self.arr_addr(arr, off_var, "t4")
                    self.ins("fsw", "fa1", "0(t4)")
                else:
                    if self.ra_alloc.is_spilled(val):
                        src_is_fp = (get_type(val) in ('float', 'double') or
                                     val in self.ra_alloc._float_vars)
                        if src_is_fp:
                            self.ins("fld", "fa1", f"{self.ra_alloc.spill_offset(val)}(s0)")
                            self.ins("fcvt.s.d", "fa1", "fa1")
                        else:
                            self.ins("lw", "t5", f"{self.ra_alloc.spill_offset(val)}(s0)")
                            self.ins("fcvt.s.w", "fa1", "t5")
                    else:
                        r = self.ra_alloc.reg(val)
                        src_is_fp = (get_type(val) in ('float', 'double') or
                                     val in self.ra_alloc._float_vars)
                        if src_is_fp:
                            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                            if r and r in _fp_regs:
                                self.ins("fcvt.s.d", "fa1", r)
                            else:
                                self.ins("fmv.d.x", "fa1", r if r else "zero")
                                self.ins("fcvt.s.d", "fa1", "fa1")
                        else:
                            self.ins("fcvt.s.w", "fa1", r if r else "zero")
                    self.arr_addr(arr, off_var, "t4")
                    self.ins("fsw", "fa1", "0(t4)")
            else:
                off_r = self.var_reg_or_load(off_var, "t6")
                if off_r != "t6":
                    self.ins("mv", "t6", off_r)

                if rhs_m:
                    lhs_base_r = self.ra_alloc.reg(arr)
                    if self.ra_alloc.is_spilled(arr):
                        self.ins("ld", "t4", f"{self.ra_alloc.spill_offset(arr)}(s0)")
                    elif lhs_base_r and lhs_base_r != "t4":
                        self.ins("mv", "t4", lhs_base_r)
                    elif lhs_base_r is None:
                        self.ins("la", "t4", arr)
                    self.ins("add", "t4", "t4", "t6")
                    rhs_arr, rhs_off = rhs_m.group(1), rhs_m.group(2)
                    self.arr_addr(rhs_arr, rhs_off, "t5")
                    rhs_ins = load_ins(rhs_arr)
                    self.ins(rhs_ins, "t3", "0(t5)")
                    s_ins = store_ins(arr)
                    self.ins(s_ins, "t3", "0(t4)")
                else:
                    lhs_base_r = self.ra_alloc.reg(arr)
                    if self.ra_alloc.is_spilled(arr):
                        self.ins("ld", "t4", f"{self.ra_alloc.spill_offset(arr)}(s0)")
                    elif lhs_base_r and lhs_base_r != "t4":
                        self.ins("mv", "t4", lhs_base_r)
                    elif lhs_base_r is None:
                        self.ins("la", "t4", arr)
                    self.ins("add", "t4", "t4", "t6")
                    self.load(val, "t3")
                    s_ins = store_ins(arr)
                    self.ins(s_ins, "t3", "0(t4)")
            return
        m = re.match(r'^(\w+)\s*=\s*-\s+(\w+)\[(\w+)\]$', instr)
        if m:
            dst_var, arr, off = m.group(1), m.group(2), m.group(3)
            self.e(f"    # unary minus of array element {arr}[{off}]")
            self.arr_addr(arr, off, "t4")
            self.ins("lw", "t4", "0(t4)")
            d = self.dst_reg(dst_var)
            self.ins("neg", d, "t4")
            self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*-\s*(\w+)(\[.+\])$', instr)
        if m:
            dst_var, arr, subscript = m.group(1), m.group(2), m.group(3)
            self.e(f"    # unary minus of {arr}{subscript}")
            idx_m = re.match(r'\[(\w+)\]', subscript)
            if idx_m:
                self.arr_addr(arr, idx_m.group(1), "t4")
                self.ins("lw", "t4", "0(t4)")
            else:
                self.load(arr, "t4")
            d = self.dst_reg(dst_var)
            self.ins("neg", d, "t4")
            self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*(\w+)\[(\w+)\]$', instr)
        if m:
            dst_var, arr, off = m.group(1), m.group(2), m.group(3)
            self.e(f"    # array read {dst_var} = {arr}[{off}]")
            arr_type = get_type(arr)
            if arr_type in ('float', 'double'):
                if is_int_literal(off):
                    base_r = self.ra_alloc.reg(arr) if not self.ra_alloc.is_spilled(arr) else None
                    if self.ra_alloc.is_spilled(arr):
                        self.ins("ld", "t4", f"{self.ra_alloc.spill_offset(arr)}(s0)")
                        self.ins("flw", "fa0", f"{to_int(off)}(t4)")
                    else:
                        self.ins("flw", "fa0", f"{to_int(off)}({base_r})")
                else:
                    self.arr_addr(arr, off, "t4")
                    self.ins("flw", "fa0", "0(t4)")
                self.ins("fcvt.d.s", "fa0", "fa0")
                off_dst = self.ra_alloc.force_spill(dst_var)
                self.ins("fsd", "fa0", f"{off_dst}(s0)")
                self.ra_alloc._float_vars.add(dst_var)
                set_type(dst_var, 'float')
            else:
                d = self.dst_reg(dst_var)
                ld_ins = load_ins(arr)
                if is_int_literal(off):
                    base_r = self.ra_alloc.reg(arr) if not self.ra_alloc.is_spilled(arr) else None
                    if self.ra_alloc.is_spilled(arr):
                        self.ins("ld", "t4", f"{self.ra_alloc.spill_offset(arr)}(s0)")
                        self.ins(ld_ins, d, f"{to_int(off)}(t4)")
                    else:
                        self.ins(ld_ins, d, f"{to_int(off)}({base_r})")
                else:
                    self.arr_addr(arr, off, "t4")
                    self.ins(ld_ins, d, "0(t4)")
                self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*\((\w+)\)\s*(".*?"|\S+)$', instr)
        if m:
            dst_var, cast_type, src = m.group(1), m.group(2), m.group(3)
            self.e(f"    # cast ({cast_type})")
            _type_map = {
                'long': 'long', 'short': 'short', 'char': 'char',
                'float': 'float', 'double': 'double', 'int': 'int'
            }
            if cast_type in _type_map:
                set_type(dst_var, _type_map[cast_type])
            int_types   = {"int", "long", "short", "char"}
            float_types = {"float", "double"}
            src = self._resolve_char_literal(src)
            if cast_type in float_types:
                if is_num_literal(src) and not is_int_literal(src):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, src))
                    self.ins("la",  "t4",  lname)
                    self.ins("fld", "fa0", "0(t4)")
                elif is_int_literal(src):
                    self.ins("li",               "t4",  str(to_int(src)))
                    self.ins(int_to_double_ins(src), "fa0", "t4")
                elif self._is_global_scalar(src):
                    self._load_float_var_into(src, "fa0")
                elif self.ra_alloc.is_spilled(src):
                    src_already_float = (
                        get_type(src) in ('float', 'double') or
                        (src in self.ra_alloc._float_vars)
                    )
                    if src_already_float:
                        self.ins("fld", "fa0", f"{self.ra_alloc.spill_offset(src)}(s0)")
                    else:
                        _src_t = get_type(src)
                        if _src_t == 'long':
                            ld = "ld"; cvt = "fcvt.d.l"
                        elif _src_t == 'short':
                            ld = "lh"; cvt = "fcvt.d.w"
                        elif _src_t == 'char':
                            ld = "lb"; cvt = "fcvt.d.w"
                        else:
                            ld = "lw"; cvt = "fcvt.d.w"
                        self.ins(ld,  "t4",  f"{self.ra_alloc.spill_offset(src)}(s0)")
                        self.ins(cvt, "fa0", "t4")
                else:
                    r = self.ra_alloc.reg(src)
                    if r:
                        src_already_float = (
                            get_type(src) in ('float', 'double') or
                            (src in self.ra_alloc._float_vars)
                        )
                        if src_already_float:
                            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                            if r in _fp_regs:
                                if r != "fa0":
                                    self.ins("fmv.d", "fa0", r)
                            else:
                                self.ins("fmv.d.x", "fa0", r)
                        else:
                            cvt = "fcvt.d.l" if get_type(src) == 'long' else "fcvt.d.w"
                            self.ins(cvt, "fa0", r)
                    else:
                        self.ins("fcvt.d.w", "fa0", "zero")
                if self._is_global_scalar_write(dst_var):
                    self._store_float_result("fa0", dst_var)
                else:
                    off = self.ra_alloc.force_spill(dst_var)
                    self.ins("fsd", "fa0", f"{off}(s0)")
                self.ra_alloc._float_vars.add(dst_var)
            elif cast_type in int_types or cast_type.startswith("("):
                if src.startswith('"'):
                    slbl = f".str{len(self.str_lits)}"
                    self.str_lits.append((slbl, src))
                    d = self.dst_reg(dst_var)
                    self.ins("la", d, slbl)
                    self.flush_dst(dst_var, d)
                    self.ra_alloc._string_vars.add(dst_var)
                    return
                src = self._resolve_char_literal(src)
                d = self.dst_reg(dst_var)
                src_is_float_lit = is_num_literal(src) and not is_int_literal(src)
                src_is_float_var = (
                    get_type(src) in ('float', 'double') or
                    (src in self.ra_alloc._float_vars)
                )
                _cast_canon = {
                    'int':    'int',
                    'long':   'long',
                    'short':  'short',
                    'char':   'char',
                    'float':  'float',
                    'double': 'double',
                }
                canon_cast = _cast_canon.get(cast_type, cast_type)
                def _load_fp_src_into_fa0(s):
                    if is_num_literal(s) and not is_int_literal(s):
                        lname = f".flt{len(self.flt_lits)}"
                        self.flt_lits.append((lname, s))
                        self.ins("la",  "t4",  lname)
                        self.ins("fld", "fa0", "0(t4)")
                    elif self._is_global_scalar(s):
                        self._load_float_var_into(s, "fa0")
                    elif self.ra_alloc.is_spilled(s):
                        self.ins("fld", "fa0",
                                 f"{self.ra_alloc.spill_offset(s)}(s0)")
                    else:
                        r = self.ra_alloc.reg(s)
                        _fp_regs = (set(RegAlloc.FP_CALLER_POOL) |
                                    set(RegAlloc.FP_SAVED_POOL))
                        if r and r in _fp_regs:
                            if r != "fa0":
                                self.ins("fmv.d", "fa0", r)
                        else:
                            self.ins("fmv.d.x", "fa0", r if r else "zero")
                def _apply_int_cast(d_reg, src_type, tgt_type):                 
                    src_t = src_type or 'int'
                    tgt_t = tgt_type or 'int'
                    _width = {'char': 8, 'short': 16, 'int': 32, 'long': 64}
                    src_w = _width.get(src_t, 32)
                    tgt_w = _width.get(tgt_t, 32)
                    if tgt_t == 'char':
                        self.ins("slli", d_reg, d_reg, "56")
                        self.ins("srai", d_reg, d_reg, "56")
                        return
                    if tgt_t == 'short':
                        self.ins("slli", d_reg, d_reg, "48")
                        self.ins("srai", d_reg, d_reg, "48")
                        return
                    if tgt_t == 'int':
                        if src_t in ('long',):
                            self.ins("addiw", d_reg, d_reg, "0")
                        return
                    if tgt_t == 'long':
                        if src_t == 'int':
                            self.ins("addiw", d_reg, d_reg, "0")
                        return
                if src_is_float_lit or src_is_float_var:
                    _load_fp_src_into_fa0(src)
                    if canon_cast == 'long':
                        self.ins("fcvt.l.d", d, "fa0", "rtz")
                    else:
                        self.ins("fcvt.w.d", d, "fa0", "rtz")
                        if canon_cast == 'short':
                            self.ins("slli", d, d, "48")
                            self.ins("srai", d, d, "48")
                        elif canon_cast == 'char':
                            self.ins("slli", d, d, "56")
                            self.ins("srai", d, d, "56")
                else:
                    if is_int_literal(src):
                        src_val = int(src)
                        if   -128 <= src_val <= 127:          src_type = 'char'
                        elif -32768 <= src_val <= 32767:       src_type = 'short'
                        elif -2147483648 <= src_val <= 2147483647: src_type = 'int'
                        else:                                  src_type = 'long'
                    elif re.match(r'^[A-Za-z_]\w*$', src):
                        src_type = _cast_canon.get(get_type(src), get_type(src))
                    else:
                        src_type = 'int'
                    src_r = self.operand(src, "t4")
                    if src_r != d:
                        self.ins("mv", d, src_r)
                    _apply_int_cast(d, src_type, canon_cast)
                self.flush_dst(dst_var, d)
            else:
                d = self.dst_reg(dst_var)
                src_r = self.operand(src, "t4")
                if src_r != d:
                    self.ins("mv", d, src_r)
                self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*-\s+(\S+)$', instr)
        if m:
            dst_var, src = m.group(1), m.group(2)
            src = self._resolve_char_literal(src)
            d = self.dst_reg(dst_var)
            if is_int_literal(src):
                self.ins("li", d, str(-to_int(src)))
            else:
                src_r = self.operand(src, "t4")
                self.ins("neg", d, src_r)
            self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*-(\w+)$', instr)
        if m:
            dst_var, src = m.group(1), m.group(2)
            src = self._resolve_char_literal(src)
            d = self.dst_reg(dst_var)
            if is_int_literal(src):
                self.ins("li", d, str(-to_int(src)))
            else:
                src_r = self.operand(src, "t4")
                self.ins("neg", d, src_r)
            self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*~\s*(\w+)$', instr)
        if m:
            dst_var, src = m.group(1), m.group(2)
            d = self.dst_reg(dst_var)
            src_r = self.operand(src, "t4")
            self.ins("not", d, src_r)
            self.flush_dst(dst_var, d)
            return
        m = re.match(
            r'^(\w+)\s*=\s*(.+?)\s*(<=|>=|==|!=|<<|>>|[+\-*/%&|^<>])\s*(.+)$',
            instr)
        if m and m.group(2).strip():
            dst_var  = m.group(1)
            op1_raw  = m.group(2).strip()
            op       = m.group(3)
            op2_raw  = m.group(4).strip()
            _op1_valid = (
                re.match(r'^[A-Za-z_]\w*(\[\w+\])?$', op1_raw) or
                is_num_literal(op1_raw) or
                re.match(r'^[A-Za-z_]\w*\[.+\]$', op1_raw)
            )
            if not _op1_valid:
                m = None
        if m and m.group(2).strip():

            def _is_float_val(v):
                if is_num_literal(v) and not is_int_literal(v):
                    return True
                if re.match(r'^[A-Za-z_]\w*$', v) and get_type(v) in ('float', 'double'):
                    return True
                if v in self.ra_alloc._float_vars:
                    return True
                return False
            def _load_fp_operand(v, fa_reg):
                if is_num_literal(v) and not is_int_literal(v):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, v))
                    self.ins("la",  "t4", lname)
                    self.ins("fld", fa_reg, "0(t4)")
                    return fa_reg
                elif is_int_literal(v):
                    self.ins("li", "t4", to_int(v))
                    self.ins(int_to_double_ins(v), fa_reg, "t4")
                    return fa_reg
                else:
                    src_fp = self._is_fp_reg(v)
                    if src_fp:
                        return src_fp
                    elif self._is_global_scalar(v):
                        self._load_float_var_into(v, fa_reg)
                        return fa_reg
                    elif self.ra_alloc.is_spilled(v):
                        src_is_fp = (
                            get_type(v) in ('float', 'double') or
                            (v in self.ra_alloc._float_vars)
                        )
                        if src_is_fp:
                            self.ins("fld", fa_reg, f"{self.ra_alloc.spill_offset(v)}(s0)")
                        else:
                            _vt = get_type(v)
                            ld  = "ld"  if _vt == 'long' else "lw"
                            cvt = "fcvt.d.l" if _vt == 'long' else "fcvt.d.w"
                            self.ins(ld,  "t4", f"{self.ra_alloc.spill_offset(v)}(s0)")
                            self.ins(cvt, fa_reg, "t4")
                        return fa_reg
                    else:
                        r = self.ra_alloc.reg(v)
                        src_is_fp = (
                            get_type(v) in ('float', 'double') or
                            (v in self.ra_alloc._float_vars)
                        )
                        if src_is_fp:
                            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                            if r and r in _fp_regs:
                                if r != fa_reg:
                                    self.ins("fmv.d", fa_reg, r)
                            else:
                                self.ins("fmv.d.x", fa_reg, r if r else "zero")
                        else:
                            cvt = "fcvt.d.l" if get_type(v) == 'long' else "fcvt.d.w"
                            self.ins(cvt, fa_reg, r if r else "zero")
                        return fa_reg
            FLOAT_OPS = {'+': 'fadd.d', '-': 'fsub.d', '*': 'fmul.d', '/': 'fdiv.d'}
            op1_is_float = _is_float_val(op1_raw)
            op2_is_float = _is_float_val(op2_raw)

            if (op1_is_float or op2_is_float) and op in FLOAT_OPS:
                fop = FLOAT_OPS[op]
                op1_fp = self._is_fp_reg(op1_raw) if re.match(r'^[A-Za-z_]\w*$', op1_raw) else None
                op2_fp = self._is_fp_reg(op2_raw) if re.match(r'^[A-Za-z_]\w*$', op2_raw) else None
                self.ra_alloc._float_vars.add(dst_var)
                set_type(dst_var, 'float')
                dst_fp = self._is_fp_reg(dst_var)

                r1 = _load_fp_operand(op1_raw, "fa0")
                r2 = _load_fp_operand(op2_raw, "fa1")

                if r1 == r2:
                    self.ins("fmv.d", "fa1", r2)
                    r2 = "fa1"

                out_reg = dst_fp if dst_fp and dst_fp != r2 else "fa0"
                self.ins(fop, out_reg, r1, r2)

                if self._is_global_scalar_write(dst_var):
                    if out_reg != "fa0":
                        self.ins("fmv.d", "fa0", out_reg)
                    self._store_float_result("fa0", dst_var)
                elif not (dst_fp and out_reg == dst_fp):
                    self._store_float_result(out_reg, dst_var)
                return
            CMP_OPS = {'<', '>', '<=', '>=', '==', '!='}
            if op in CMP_OPS:
                if re.match(r'^(\w+)\[(\w+)\]$', op1_raw):
                    self._resolve_operand(op1_raw, "t4")
                    op1_reg = "t4"
                else:
                    op1_reg = self.var_reg_or_load(op1_raw, "t4")
                if re.match(r'^(\w+)\[(\w+)\]$', op2_raw):
                    self._resolve_operand(op2_raw, "t5")
                    op2_reg = "t5"
                elif is_num_literal(op2_raw):
                    self.ins("li", "t5", to_int(op2_raw))
                    op2_reg = "t5"
                else:
                    op2_reg = self.var_reg_or_load(op2_raw, "t5")
                if op1_reg == op2_reg and op1_reg in ("t4", "t5"):
                    self.load(op2_raw, "t5")
                    op2_reg = "t5"
                d = self.dst_reg(dst_var)
                if op == '<':
                    self.ins("slt",  f"{d}, {op1_reg}", op2_reg)
                elif op == '>':
                    self.ins("slt",  f"{d}, {op2_reg}", op1_reg)
                elif op == '<=':
                    self.ins("slt",  f"{d}, {op2_reg}", op1_reg)
                    self.ins("xori", f"{d}, {d}", 1)
                elif op == '>=':
                    self.ins("slt",  f"{d}, {op1_reg}", op2_reg)
                    self.ins("xori", f"{d}, {d}", 1)
                elif op == '==':
                    self.ins("sub",  f"{d}, {op1_reg}", op2_reg)
                    self.ins("seqz", f"{d}", d)
                elif op == '!=':
                    self.ins("sub",  f"{d}, {op1_reg}", op2_reg)
                    self.ins("snez", f"{d}", d)
                self.flush_dst(dst_var, d)
                return

            rr, ri   = self.BINOP_MAP.get(op, (None, None))
            if not rr:
                self.e(f"    # [UNSUPPORTED OP '{op}']")
                return

            if re.match(r'^(\w+)\[(\w+)\]$', op1_raw):
                self._resolve_operand(op1_raw, "t4")
                op1_reg = "t4"
            else:
                op1_reg = self.var_reg_or_load(op1_raw, "t4")

            d = self.dst_reg(dst_var)

            if is_num_literal(op2_raw) and ri:
                self.ins(ri, f"{d}, {op1_reg}", to_int(op2_raw))
            elif is_num_literal(op2_raw) and op == '-':
                self.ins("addi", f"{d}, {op1_reg}", -to_int(op2_raw))
            elif is_num_literal(op2_raw):
                self.ins("li", "t5", to_int(op2_raw))
                self.ins(rr, f"{d}, {op1_reg}", "t5")
            else:
                if re.match(r'^(\w+)\[(\w+)\]$', op2_raw):
                    self._resolve_operand(op2_raw, "t5")
                    op2_reg = "t5"
                else:
                    op2_reg = self.var_reg_or_load(op2_raw, "t5")
                if op1_reg == op2_reg and op1_reg in ("t4", "t5"):
                    self.load(op2_raw, "t5")
                    op2_reg = "t5"
                self.ins(rr, f"{d}, {op1_reg}", op2_reg)
            self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*(\S+)$', instr)
        if m:
            dst_var, val = m.group(1), m.group(2)
            val = self._resolve_char_literal(val)

            src_is_float = (
                (is_num_literal(val) and not is_int_literal(val)) or
                (re.match(r'^[A-Za-z_]\w*$', val) and get_type(val) in ('float', 'double')) or
                (val in self.ra_alloc._float_vars)
            )
            dst_is_float = (
                get_type(dst_var) in ('float', 'double') or
                (dst_var in self.ra_alloc._float_vars)
            )
            if src_is_float or dst_is_float:
                self.ra_alloc._float_vars.add(dst_var)

                src_resolved_type = get_type(val) if re.match(r'^[A-Za-z_]\w*$', val) else 'float'
                if src_resolved_type in ('float', 'double') or not dst_is_float:
                    set_type(dst_var, src_resolved_type if src_is_float else 'float')
                dst_fp = self._is_fp_reg(dst_var)
                tgt = dst_fp if dst_fp else "fa0"

                if is_num_literal(val) and not is_int_literal(val):
                    lname = f".flt{len(self.flt_lits)}"
                    self.flt_lits.append((lname, val))
                    self.ins("la",  "t4", lname)
                    self.ins("fld", tgt, "0(t4)")
                elif is_int_literal(val):
                    self.ins("li", "t4", to_int(val))
                    self.ins(int_to_double_ins(val), tgt, "t4")
                elif self._is_global_scalar(val):

                    self._load_float_var_into(val, tgt)
                elif self.ra_alloc.is_spilled(val):
                    val_is_fp = (
                        get_type(val) in ('float', 'double') or
                        (val in self.ra_alloc._float_vars)
                    )
                    if val_is_fp:
                        self.ins("fld", tgt, f"{self.ra_alloc.spill_offset(val)}(s0)")
                    else:
                        _vt = get_type(val)
                        if _vt == 'long':
                            _ld = "ld"; _cvt = "fcvt.d.l"
                        elif _vt == 'short':
                            _ld = "lh"; _cvt = "fcvt.d.w"
                        elif _vt == 'char':
                            _ld = "lb"; _cvt = "fcvt.d.w"
                        else:
                            _ld = "lw"; _cvt = "fcvt.d.w"
                        self.ins(_ld,  "t4", f"{self.ra_alloc.spill_offset(val)}(s0)")
                        self.ins(_cvt, tgt, "t4")
                else:
                    src_fp = self._is_fp_reg(val)
                    if src_fp:
                        if src_fp != tgt:
                            self.ins("fmv.d", tgt, src_fp)
                    else:
                        r = self.ra_alloc.reg(val)
                        val_is_fp = (
                            get_type(val) in ('float', 'double') or
                            (val in self.ra_alloc._float_vars)
                        )
                        if val_is_fp:
                            _fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                            if r and r in _fp_regs:
                                if r != tgt:
                                    self.ins("fmv.d", tgt, r)
                            else:
                                self.ins("fmv.d.x", tgt, r if r else "zero")
                        else:
                            cvt = "fcvt.d.l" if get_type(val) == 'long' else "fcvt.d.w"
                            self.ins(cvt, tgt, r if r else "zero")
                if self._is_global_scalar_write(dst_var):
                    if tgt != "fa0":
                        self.ins("fmv.d", "fa0", tgt)
                    self._store_float_result("fa0", dst_var)
                elif not dst_fp:
                    self._store_float_result("fa0", dst_var)
            else:
                d = self.dst_reg(dst_var)
                dst_type = _global_scalars.get(dst_var, get_type(dst_var))
                if is_int_literal(val):
                    self.ins("li", d, to_int(val))
                    if dst_type == 'int':
                        if not fits_in_32bit(val):
                            self.ins("addiw", d, d, "0")
                    elif dst_type == 'short':
                        self.ins("slli", d, d, "48")
                        self.ins("srai", d, d, "48")
                    elif dst_type == 'char':
                        self.ins("slli", d, d, "56")
                        self.ins("srai", d, d, "56")
                else:
                    src_type = get_type(val) if re.match(r'^[A-Za-z_]\w*$', val) else 'int'
                    src_r = self.operand(val, "t4")
                    if src_r != d:
                        self.ins("mv", d, src_r)
                    _iwidth = {'char': 8, 'short': 16, 'int': 32, 'long': 64}
                    sw = _iwidth.get(src_type, 32)
                    dw = _iwidth.get(dst_type, 32)
                    if sw != dw and src_type in _iwidth and dst_type in _iwidth:
                        if dst_type == 'long' and src_type == 'int':
                            self.ins("addiw", d, d, "0")
                        elif dst_type == 'int' and src_type == 'long':
                            self.ins("addiw", d, d, "0")
                        elif dst_type == 'short':
                            self.ins("slli", d, d, "48")
                            self.ins("srai", d, d, "48")
                        elif dst_type == 'char':
                            self.ins("slli", d, d, "56")
                            self.ins("srai", d, d, "56")
                self.flush_dst(dst_var, d)
            return
        m = re.match(r'^(\w+)\s*=\s*ref\s+(\w+)$', instr)
        if m:
            self.e(f"    # addr-of: {m.group(1)} = &{m.group(2)}")
            self._handle_addrof(m.group(1), m.group(2))
            return
        m = re.match(r'^(\w+)\s*=\s*deref\s+(\w+)$', instr)
        if m:
            self.e(f"    # ptr-load: {m.group(1)} = *{m.group(2)}")
            self._handle_ptr_read(m.group(1), m.group(2))
            return
        m = re.match(r'^deref\s+(\w+)\s*=\s*(\S+)$', instr)
        if m:
            self.e(f"    # ptr-store: *{m.group(1)} = {m.group(2)}")
            self._handle_ptr_write(m.group(1), m.group(2))
            return
        m = re.match(r'^(\w+)\s*=\s*ALLOC\s+(\w+)\s*\*\s*(\w+)$', instr)
        if m:
            dst_var, esize, count = m.group(1), m.group(2), m.group(3)
            self.e(f"    # heap alloc: {dst_var} = malloc({esize} * {count})")
            _alloc_t = _symtab_var_types.get(dst_var) or get_type(dst_var)
            if not _alloc_t or _alloc_t == 'int':
                _alloc_t = 'ptr:void'
            set_type(dst_var, _alloc_t)
            self.use_extern("malloc")
            if is_int_literal(esize) and is_int_literal(count):
                total = to_int(esize) * to_int(count)
                self.ins("li", "a0", total)
            elif is_int_literal(esize):
                cnt_r = self.var_reg_or_load(count, "t4")
                self.ins("li", "t5", to_int(esize))
                self.ins("mul", "a0", "t5", cnt_r)
            elif is_int_literal(count):
                es_r = self.var_reg_or_load(esize, "t4")
                self.ins("li", "t5", to_int(count))
                self.ins("mul", "a0", es_r, "t5")
            else:
                es_r  = self.var_reg_or_load(esize, "t4")
                cnt_r = self.var_reg_or_load(count, "t5")
                self.ins("mul", "a0", es_r, cnt_r)
            self.ins("call", "malloc")
            self.store_var(dst_var, "a0")
            if self._is_global_scalar_write(dst_var):
                self._store_global(dst_var, "a0")
            return
        m = re.match(r'^(\w+)\s*=\s*CALLOC\s+(\w+)\s*,\s*(\w+)$', instr)
        if m:
            dst_var, count, esize = m.group(1), m.group(2), m.group(3)
            self.e(f"    # heap calloc: {dst_var} = calloc({count}, {esize})")
            _calloc_t = _symtab_var_types.get(dst_var) or get_type(dst_var)
            if not _calloc_t or _calloc_t == 'int':
                _calloc_t = 'ptr:void'
            set_type(dst_var, _calloc_t)
            self.use_extern("calloc")
            if is_int_literal(count):
                self.ins("li", "a0", to_int(count))
            else:
                cnt_r = self.var_reg_or_load(count, "t4")
                if cnt_r != "a0":
                    self.ins("mv", "a0", cnt_r)
            if is_int_literal(esize):
                self.ins("li", "a1", to_int(esize))
            else:
                es_r = self.var_reg_or_load(esize, "t4")
                if es_r != "a1":
                    self.ins("mv", "a1", es_r)
            self.ins("call", "calloc")
            self.store_var(dst_var, "a0")
            if self._is_global_scalar_write(dst_var):
                self._store_global(dst_var, "a0")
            return
        m = re.match(r'^(\w+)\s*=\s*REALLOC\s+(\w+)\s*,\s*(\w+)\s*\*\s*(\w+)$', instr)
        if m:
            dst_var, ptr_var, esize, count = m.group(1), m.group(2), m.group(3), m.group(4)
            self.e(f"    # heap realloc: {dst_var} = realloc({ptr_var}, {esize} * {count})")
            _realloc_t = (_symtab_var_types.get(dst_var)
                          or get_type(dst_var)
                          or _symtab_var_types.get(ptr_var)
                          or get_type(ptr_var)
                          or 'ptr:void')
            if not _realloc_t or _realloc_t == 'int':
                _realloc_t = 'ptr:void'
            set_type(dst_var, _realloc_t)
            self.use_extern("realloc")
            ptr_r = self.var_reg_or_load(ptr_var, "t4")
            if ptr_r != "a0":
                self.ins("mv", "a0", ptr_r)
            if is_int_literal(esize) and is_int_literal(count):
                self.ins("li", "a1", to_int(esize) * to_int(count))
            elif is_int_literal(esize):
                cnt_r = self.var_reg_or_load(count, "t5")
                self.ins("li", "t4", to_int(esize))
                self.ins("mul", "a1", "t4", cnt_r)
            elif is_int_literal(count):
                es_r = self.var_reg_or_load(esize, "t5")
                self.ins("li", "t4", to_int(count))
                self.ins("mul", "a1", es_r, "t4")
            else:
                es_r  = self.var_reg_or_load(esize, "t4")
                cnt_r = self.var_reg_or_load(count, "t5")
                self.ins("mul", "a1", es_r, cnt_r)
            self.ins("call", "realloc")
            self.store_var(dst_var, "a0")
            if self._is_global_scalar_write(dst_var):
                self._store_global(dst_var, "a0")
            return
        m = re.match(r'^(\w+)\s*=\s*REALLOC\s+(\w+)\s*,\s*(\w+)$', instr)
        if m:
            dst_var, ptr_var, new_size = m.group(1), m.group(2), m.group(3)
            self.e(f"    # heap realloc: {dst_var} = realloc({ptr_var}, {new_size})")
            _realloc_t2 = (_symtab_var_types.get(dst_var)
                           or get_type(dst_var)
                           or _symtab_var_types.get(ptr_var)
                           or get_type(ptr_var)
                           or 'ptr:void')
            if not _realloc_t2 or _realloc_t2 == 'int':
                _realloc_t2 = 'ptr:void'
            set_type(dst_var, _realloc_t2)
            self.use_extern("realloc")
            ptr_r = self.var_reg_or_load(ptr_var, "t4")
            if ptr_r != "a0":
                self.ins("mv", "a0", ptr_r)
            if is_int_literal(new_size):
                self.ins("li", "a1", to_int(new_size))
            else:
                ns_r = self.var_reg_or_load(new_size, "t5")
                if ns_r != "a1":
                    self.ins("mv", "a1", ns_r)
            self.ins("call", "realloc")
            self.store_var(dst_var, "a0")
            if self._is_global_scalar_write(dst_var):
                self._store_global(dst_var, "a0")
            return
        m = re.match(r'^FREE\s+(\S+)$', instr)
        if m:
            target = m.group(1)
            self.e(f"    # heap free: free({target})")
            self.use_extern("free")
            if target == "0" or target.lower() == "null":
                self.ins("li", "a0", 0)
            else:
                ptr_r = self.var_reg_or_load(target, "t4")
                if ptr_r != "a0":
                    self.ins("mv", "a0", ptr_r)
            self.ins("call", "free")
            return
        m = re.match(r'^(\w+)\s*=\s*\(ptr:[^)]+\)\s*(\S+)$', instr)
        if m:
            dst_var, src_val = m.group(1), m.group(2)
            self.e(f"    # ptr-cast: {dst_var} = (ptr:...) {src_val}")
            # Stamp the destination with its pointer type from the symbol table
            st = _symtab_var_types.get(dst_var, 'ptr:void')
            set_type(dst_var, st)
            d = self.dst_reg(dst_var)
            if is_int_literal(src_val):
                self.ins("li", d, to_int(src_val))
            else:
                src_r = self.var_reg_or_load(src_val, "t4")
                if src_r != d:
                    self.ins("mv", d, src_r)
            self.flush_dst(dst_var, d)
            return
        self.e(f"    # [UNHANDLED] {instr}")
    def _handle_ptr_read(self, dst_var, ptr_var):
        ptr_r = self.var_reg_or_load(ptr_var, "t4")
        ptr_type = get_type(ptr_var)
        # Global pointer vars are excluded from _preseed_float_types type-inference
        # (all_vars -= _global_scalars.keys()), so _var_types for a global ptr like
        # 'q' stays 'int' even though _symtab_var_types has 'ptr:double'.
        # Fall back to _symtab_var_types so the correct pointee type is used.
        if not ptr_type.startswith("ptr:"):
            ptr_type = _symtab_var_types.get(ptr_var, ptr_type)
        if ptr_type.startswith("ptr:"):
            pointee_t = ptr_type[4:]
        else:
            pointee_t = get_type(dst_var)
        set_type(dst_var, pointee_t)
        ld = {"long":"ld","short":"lh","char":"lb","float":"flw","double":"fld"}.get(pointee_t, "lw")
        if ld in ("flw","fld"):
            # Float/double pointer load — must always use FP load instruction.
            # dst_reg() may return an FP register (e.g. ft0) when the register
            # allocator already classified this variable as float; using an integer
            # load (lw/ld) into an FP register is illegal on RISC-V, so we always
            # go through fa0 + spill regardless of what dst_reg() returns.
            self.ins(ld,  "fa0", f"0({ptr_r})")
            if ld == "flw":
                self.ins("fcvt.d.s", "fa0", "fa0")
            self.ins("fsd","fa0", f"{self.ra_alloc.force_spill(dst_var)}(s0)")
            self.ra_alloc._float_vars.add(dst_var)
        else:
            # Integer-family pointer load — dst_reg() must be an integer register.
            # Guard against the edge case where the allocator handed out an FP
            # register for this slot (shouldn't normally happen for int pointees,
            # but be safe and fall back to a temporary integer register).
            d = self.dst_reg(dst_var)
            fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
            if d in fp_regs:
                # Pointee is integer but dst landed in an FP reg — load into t4
                # and spill to the variable's stack slot instead.
                self.ins(ld, "t4", f"0({ptr_r})")
                off = self.ra_alloc.force_spill(dst_var)
                # Use a width-matched store so we don't corrupt adjacent slots.
                st = {"ld": "sd", "lh": "sh", "lb": "sb"}.get(ld, "sw")
                self.ins(st, "t4", f"{off}(s0)")
            else:
                self.ins(ld,  d,    f"0({ptr_r})")
                self.flush_dst(dst_var, d)
    def _handle_ptr_write(self, ptr_var, src_val):
        ptr_r = self.var_reg_or_load(ptr_var, "t4")
        self.ins("mv", "t5", ptr_r) 
        ptr_type = get_type(ptr_var)
        # Same global-ptr issue as _handle_ptr_read: _var_types for a global pointer
        # like 'p' is 'int' (excluded from inference), but _symtab_var_types has the
        # correct 'ptr:double'. Without this fix, 'deref p = 99.99' uses 'sw' instead
        # of 'fsd', silently truncating the double to a 32-bit integer store.
        if not ptr_type.startswith("ptr:"):
            ptr_type = _symtab_var_types.get(ptr_var, ptr_type)
        t = ptr_type[4:] if ptr_type.startswith("ptr:") else "int"
        si = {"long":"sd","short":"sh","char":"sb","float":"fsw","double":"fsd"}.get(t, "sw")
        if si not in ("fsw","fsd"):
            # Integer pointer write — resolve char literals first, then store
            resolved = self._resolve_char_literal(src_val)
            src_r = self.var_reg_or_load(resolved, "t4")
            self.ins(si, src_r, "0(t5)")
            return
        if is_num_literal(src_val) and not is_int_literal(src_val):
            lname = f".flt{len(self.flt_lits)}"
            self.flt_lits.append((lname, src_val))
            self.ins("la",  "t6", lname)
            self.ins("fld", "fa1", "0(t6)")
        elif is_int_literal(src_val):
            self.ins("li", "t6", to_int(src_val))
            self.ins("fcvt.d.w", "fa1", "t6")
        elif self._is_global_scalar(src_val) and _global_scalars.get(src_val) in ('float','double'):
            self._load_float_var_into(src_val, "fa1")
        elif (get_type(src_val) in ('float', 'double')
              or (re.match(r'^[A-Za-z_]\w*$', src_val)
                  and src_val in self.ra_alloc._float_vars)
              or t in ('float', 'double')):
            # t in ('float','double'): the pointee type demands a float value.
            # Trust the pointer's declared pointee type and load via fld even if
            # get_type(src_val) hasn't been resolved (e.g. missing TAC definition).
            if self.ra_alloc.is_spilled(src_val):
                self.ins("fld", "fa1", f"{self.ra_alloc.spill_offset(src_val)}(s0)")
            else:
                r = self.ra_alloc.reg(src_val)
                fp_regs = set(RegAlloc.FP_CALLER_POOL) | set(RegAlloc.FP_SAVED_POOL)
                if r and r in fp_regs:
                    if r != "fa1":
                        self.ins("fmv.d", "fa1", r)
                elif r:
                    off = self.ra_alloc.force_spill(src_val)
                    self.ins("fsd", r, f"{off}(s0)")
                    self.ins("fld", "fa1", f"{off}(s0)")
                else:
                    # No register and no spill slot — undefined value (missing TAC
                    # instruction in frontend). Emit safe zero rather than garbage.
                    self.ins("fmv.d.x", "fa1", "zero")
        else:
            src_r = self.var_reg_or_load(src_val, "t6")
            cvt = "fcvt.d.l" if get_type(src_val) == 'long' else "fcvt.d.w"
            self.ins(cvt, "fa1", src_r)
        if si == "fsw":
            self.ins("fcvt.s.d", "fa1", "fa1")
        self.ins(si, "fa1", "0(t5)")
    def _handle_addrof(self, dst_var, src_var):
        src_t = _symtab_var_types.get(src_var, get_type(src_var))
        if src_t and not src_t.startswith('ptr:'):
            set_type(dst_var, f'ptr:{src_t}')
        elif src_t:
            set_type(dst_var, src_t)
        d = self.dst_reg(dst_var)
        if self._is_global_scalar(src_var):
            self.ins("la", d, src_var)
        elif self.ra_alloc.is_spilled(src_var):
            self.ins("addi", d, "s0", str(self.ra_alloc.spill_offset(src_var)))
        else:
            off = self.ra_alloc.force_spill(src_var)
            r   = self.ra_alloc._map.get(src_var)
            if r:
                self.ins(store_ins(src_var), r, f"{off}(s0)")
            self.ins("addi", d, "s0", str(off))
        self.flush_dst(dst_var, d)
def main():
    import argparse
    import subprocess
    import shutil
    import tempfile
    import os
    ap = argparse.ArgumentParser(description="Convert TAC to RISC-V assembly")
    ap.add_argument("input",   nargs="?", default="optimized.tac")
    ap.add_argument("output",  nargs="?", default="output.s")
    ap.add_argument("--run",   action="store_true",
                    help="Compile the generated .s and run it immediately")
    ap.add_argument("--compiler", default=None,
                    help="Override GCC cross-compiler ( riscv64-linux-gnu-gcc)")
    ap.add_argument("--emulator", default=None,
                    help="Override QEMU emulator (qemu-riscv64)")
    args = ap.parse_args()
    if not os.path.exists(args.input):
        print(f"[ERROR] Input file not found: {args.input}", file=sys.stderr)
        sys.exit(1)
    with open(args.input) as f:
      tac = f.read()
    if tac.strip() == "# SEMANTIC_ERROR":
      # print("[SKIP] Semantic errors in source — assembly generation skipped.", file=sys.stderr)
      sys.exit(1)
    load_symtab_json(os.path.join(os.path.dirname(args.input), "symtab.json"))
    asm = TACtoRISCV().convert(tac)
    with open(args.output, "w") as f:
        f.write(asm)
    lines    = asm.splitlines()
    funcs    = [l for l in lines if re.match(r'^\w.*:$', l)]
    branches = [l for l in lines if re.search(r'\b(beq|bne|blt|bge|j )', l)]
    if not args.run:
        return
    COMPILER_CANDIDATES = [
        ("riscv64-linux-gnu-gcc",        "qemu-riscv64"),
        ("riscv64-unknown-linux-gnu-gcc", "qemu-riscv64"),
        ("riscv32-linux-gnu-gcc",        "qemu-riscv32"),
        ("riscv32-unknown-linux-gnu-gcc","qemu-riscv32"),
    ]
    compiler = args.compiler
    emulator = args.emulator
    if not compiler:
        for cc, qemu in COMPILER_CANDIDATES:
            if shutil.which(cc):
                compiler = cc
                if not emulator:
                    emulator = qemu
                break
    if not compiler:
        print("\n[ERROR] No RISC-V cross-compiler found on PATH.", file=sys.stderr)
        print("  Install one, e.g.:", file=sys.stderr)
        print("    sudo apt install gcc-riscv64-linux-gnu qemu-user", file=sys.stderr)
        print("  Or pass --compiler /path/to/riscv64-linux-gnu-gcc", file=sys.stderr)
        sys.exit(1)
    if not emulator:
        emulator = "qemu-riscv64"
    with tempfile.TemporaryDirectory() as tmpdir:
        bin_path = os.path.join(tmpdir, "a.out")
        #bin_path = os.path.join(os.getcwd(), "a.out")
        # riscv64-linux-gnu-gcc -static -o a.out output.s
        compile_cmd = [compiler, "-static", "-o", bin_path, args.output]
        result = subprocess.run(compile_cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print("[COMPILE FAILED]", file=sys.stderr)
            print(result.stderr, file=sys.stderr)
            sys.exit(result.returncode)
        run_cmd = None
        if shutil.which(emulator):
            run_cmd = [emulator, bin_path]
        else:
            run_cmd = [bin_path]
        run_result = subprocess.run(run_cmd, text=True)
if __name__ == "__main__":
    main()