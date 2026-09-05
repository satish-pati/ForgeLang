import re
import sys
from collections import defaultdict

PYTHON_KEYWORDS = {
    "False", "None", "True", "and", "as", "assert", "async", "await",
    "break", "class", "continue", "def", "del", "elif", "else", "except",
    "finally", "for", "from", "global", "if", "import", "in", "is",
    "lambda", "nonlocal", "not", "or", "pass", "raise", "return",
    "sum", "min", "max", "abs", "len", "range", "print", "input",
    "int", "float", "try", "while", "with", "yield",
}


def safe_name(name: str) -> str:
    if not name: return name
    name = name.strip()
    if name in PYTHON_KEYWORDS:
        return "_" + name
    return name


REL_MAP = {"<": "<", ">": ">", "<=": "<=", ">=": ">=", "==": "==", "!=": "!="}
ARITH_MAP = {
    "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
    "<<": "<<", ">>": ">>", "&": "&", "|": "|", "^": "^",
    "&&": "and", "||": "or",
}

def _wrap_char(v):
    """Signed 8-bit wrap: result in [-128, 127]"""
    v = int(v) & 0xFF
    return v if v < 128 else v - 256

def _wrap_short(v):
    """Signed 16-bit wrap: result in [-32768, 32767]"""
    v = int(v) & 0xFFFF
    return v if v < 32768 else v - 65536

def _wrap_int(v):
    """Signed 32-bit wrap: result in [-2147483648, 2147483647]"""
    v = int(v) & 0xFFFFFFFF
    return v if v < 2147483648 else v - 4294967296

def _wrap_long(v):
    """Signed 64-bit wrap: result in [-9223372036854775808, 9223372036854775807]"""
    v = int(v) & 0xFFFFFFFFFFFFFFFF
    return v if v < 9223372036854775808 else v - 18446744073709551616

def _trunc_div(a, b):
    """C-style truncating integer division (toward zero)."""
    if b == 0: raise ZeroDivisionError("division by zero")
    return int(a / b)

IGNORE_VARS = {
    "BeginFunc", "EndFunc", "PopParam", "PushParam", "Call", "Return", 
    "goto", "if", "deref", "ref", "ALLOC", "CALLOC", "REALLOC", "FREE", 
    "printint", "printfloat", "printchar", "printstring", 
    "inputint", "inputfloat", "inputchar", "inputstring",
    "int", "float", "char", "double", "short", "long", "void", "ptr"
}

#  line parser 

def parse_line(raw: str):
    line = raw.strip()
    if not line: return None
    m = re.match(r"^(\d+)\s+(.*)", line)
    if not m: return None
    lnum = int(m.group(1))
    rest = m.group(2).strip()

    if rest.startswith("//"): return None

    m2 = re.match(r"^BeginFunc\s+(\S+)\s+(\d+)$", rest)
    if m2: return {"op": "BeginFunc", "lnum": lnum, "name": m2.group(1), "nparams": int(m2.group(2))}

    m2 = re.match(r"^EndFunc\s+(\S+)$", rest)
    if m2: return {"op": "EndFunc", "lnum": lnum, "name": m2.group(1)}

    m2 = re.match(r"^PopParam(?:\s+(\S+))?$", rest)
    if m2: return {"op": "PopParam", "lnum": lnum, "var": (m2.group(1) or "")}

    m2 = re.match(r"^PushParam\s+(.+)$", rest)
    if m2: return {"op": "PushParam", "lnum": lnum, "val": m2.group(1).strip()}

    m2 = re.match(r"^Return\s*(.*)$", rest)
    if m2: return {"op": "Return", "lnum": lnum, "val": m2.group(1).strip()}

    m2 = re.match(r"^if\s+(\S+)\s+(<=|>=|==|!=|<|>)\s+(\S+)\s+goto\s+(\d+)$", rest)
    if m2: return {"op": "if", "lnum": lnum, "a": m2.group(1), "rel": m2.group(2), "b": m2.group(3), "target": int(m2.group(4))}

    m2 = re.match(r"^goto\s+(\d+)$", rest)
    if m2: return {"op": "goto", "lnum": lnum, "target": int(m2.group(1))}

    m2 = re.match(r"^(printint|printfloat|printchar|printstring)\s+(.+)$", rest)
    if m2: return {"op": "print", "lnum": lnum, "kind": m2.group(1), "val": m2.group(2).strip()}
    

    m2 = re.match(r"^(inputint|inputfloat|inputchar|inputstring)\s+(.+)$", rest)
    if m2: return {"op": "input", "lnum": lnum, "kind": m2.group(1), "var": m2.group(2).strip()}

    m2 = re.match(r"^FREE\s+(\S+)$", rest)
    if m2: return {"op": "free", "lnum": lnum, "ptr": m2.group(1)}

    m2 = re.match(r"^Call\s+(\S+)$", rest)
    if m2: return {"op": "call_void", "lnum": lnum, "fname": m2.group(1)}

    eq_idx = rest.find("=")
    if eq_idx < 0: return {"op": "unknown", "lnum": lnum, "raw": rest}

    if eq_idx > 0 and rest[eq_idx - 1] in (">", "<", "!", "="): return {"op": "unknown", "lnum": lnum, "raw": rest}

    lhs = rest[:eq_idx].strip()
    rhs = rest[eq_idx + 1:].strip()

    m2 = re.match(r"^deref\s+(\S+)$", lhs)
    if m2: return {"op": "deref_store", "lnum": lnum, "ptr": m2.group(1), "val": rhs}

    m2 = re.match(r"^(\w+)\[(\d+)\]$", lhs)
    if m2: return {"op": "arr_store", "lnum": lnum, "arr": m2.group(1), "offset": int(m2.group(2)), "val": rhs}

    m2 = re.match(r"^(\w+)\[(.+)\]$", lhs)
    if m2: return {"op": "arr_store_var", "lnum": lnum, "arr": m2.group(1), "offset_expr": m2.group(2).strip(), "val": rhs}

    m2 = re.match(r"^Call\s+(\S+)$", rhs)
    if m2: return {"op": "call_ret", "lnum": lnum, "result": lhs, "fname": m2.group(1)}

    m2 = re.match(r"^ALLOC\s+(\S+)\s*\*\s*(\S+)$", rhs)
    if m2: return {"op": "alloc", "lnum": lnum, "result": lhs, "elem_size": m2.group(1), "count": m2.group(2)}

    m2 = re.match(r"^CALLOC\s+(\S+),\s*(\S+)$", rhs)
    if m2: return {"op": "calloc", "lnum": lnum, "result": lhs, "count": m2.group(1), "elem_size": m2.group(2)}

    m2 = re.match(r"^REALLOC\s+(\S+),\s*(\S+)\s*\*\s*(\S+)$", rhs)
    if m2: return {"op": "realloc", "lnum": lnum, "result": lhs, "ptr": m2.group(1), "elem_size": m2.group(2), "count": m2.group(3)}

    m2 = re.match(r"^REALLOC\s+(\S+),\s*(\S+)$", rhs)
    if m2: return {"op": "realloc", "lnum": lnum, "result": lhs, "ptr": m2.group(1), "elem_size": "1", "count": m2.group(2)}

    m2 = re.match(r"^(\w+)\[(\d+)\]$", rhs)
    if m2: return {"op": "arr_load", "lnum": lnum, "result": lhs, "arr": m2.group(1), "offset": int(m2.group(2))}

    m2 = re.match(r"^(\w+)\[(.+)\]$", rhs)
    if m2: return {"op": "arr_load_var", "lnum": lnum, "result": lhs, "arr": m2.group(1), "offset_expr": m2.group(2).strip()}

    m2 = re.match(r"^ref\s+(\S+)$", rhs)
    if m2: return {"op": "ref", "lnum": lnum, "result": lhs, "src": m2.group(1)}

    m2 = re.match(r"^deref\s+(\S+)$", rhs)
    if m2: return {"op": "deref_load", "lnum": lnum, "result": lhs, "src": m2.group(1)}

    m2 = re.match(r"^\(([\w:]+)\)\s*(.+)$", rhs)
    if m2: return {"op": "cast", "lnum": lnum, "result": lhs, "cast_type": m2.group(1), "val": m2.group(2).strip()}

    m2 = re.match(r"^~\s+(\S+)$", rhs)
    if m2: return {"op": "unary", "lnum": lnum, "result": lhs, "uop": "~", "val": m2.group(1)}

    m2 = re.match(r"^-\s+(\S+)$", rhs)
    if m2: return {"op": "unary", "lnum": lnum, "result": lhs, "uop": "-", "val": m2.group(1)}

    for op in ["<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+", "-", "*", "/", "%", "&", "|", "^", "<", ">"]:
        pat = r"^(\S+)\s+" + re.escape(op) + r"\s+(\S+)$"
        m2 = re.match(pat, rhs)
        if m2: return {"op": "binop", "lnum": lnum, "result": lhs, "a": m2.group(1), "bop": op, "b": m2.group(2)}

    return {"op": "copy", "lnum": lnum, "result": lhs, "val": rhs}


#  transpiler 

class Transpiler:
    def __init__(self, instructions, lnum_to_idx):
        self.ins  = instructions
        self.l2i  = lnum_to_idx
        self.out  = []
        self.ind  = 0
        self._push_queue = []

        self.funcs = {}
        self._scan_functions()
        
        self.address_taken = set()
        self.ref_params = defaultdict(set)
        self._discover_pointers()

        self.global_vars = set()
        self.global_arrays = set()
        self.func_vars = defaultdict(set)
        self.func_arrays = defaultdict(set)
        
        self.global_blocks = []
        self.func_blocks = defaultdict(list)
        self._build_blocks()

    def _tidx(self, lnum: int):
        if lnum in self.l2i: return self.l2i[lnum]
        max_lnum = max(self.l2i.keys()) if self.l2i else -1
        if lnum > max_lnum: return len(self.ins)
        return len(self.ins)

    def _scan_functions(self):
        i = 0
        while i < len(self.ins):
            ins = self.ins[i]
            if ins and ins["op"] == "BeginFunc":
                fname = ins["name"]
                params = []
                j = i + 1
                while j < len(self.ins):
                    ni = self.ins[j]
                    if ni is None: j += 1; continue
                    if ni["op"] == "PopParam" and ni["var"]:
                        params.append(ni["var"]); j += 1
                    else: break
                end_i = None
                for k in range(i + 1, len(self.ins)):
                    ni = self.ins[k]
                    if ni and ni["op"] == "EndFunc" and ni["name"] == fname:
                        end_i = k; break
                self.funcs[fname] = {"params": params, "start": i, "end": end_i}
            i += 1

    def _discover_pointers(self):
        # 1. Any variable explicitly accessed via `ref` or `&` is marked as a memory address
        for ins in self.ins:
            if ins is None: continue
            if ins["op"] == "ref":
                src = ins["src"]
                if "[" not in src:
                    self.address_taken.add(src)
            for k, v in ins.items():
                if isinstance(v, str) and v.startswith("&"):
                    var = v[1:]
                    if "[" not in var:
                        self.address_taken.add(var)

        # 2. Track implicit reference parameters (e.g. `swap(&x, &y)`)
        pq = []
        for ins in self.ins:
            if ins is None: continue
            if ins["op"] == "PushParam":
                pq.append(ins["val"])
            elif ins["op"] in ("call_void", "call_ret"):
                fname = ins["fname"]
                if fname in self.funcs:
                    params = self.funcs[fname]["params"]
                    for idx, val in enumerate(pq):
                        if val.startswith("&"):
                            # Handle both potential eval orders conservatively
                            if idx < len(params):
                                self.ref_params[fname].add(params[idx])
                            rev_idx = len(pq) - 1 - idx
                            if rev_idx < len(params):
                                self.ref_params[fname].add(params[rev_idx])
                pq = []

    def _extract_vars(self, ins_dict):
        v_set = set()
        arr_set = set()
        func_names = set(self.funcs.keys())
        SKIP_KEYS = {"op", "lnum", "rel", "bop", "uop", "kind", "cast_type"}
        for k, v in ins_dict.items():
            if k in SKIP_KEYS:
                continue
            if isinstance(v, str):
                if v.startswith('"') or v.startswith("'"):
                    continue  # skip string literals — don't extract words from inside them
                for m in re.finditer(r"([A-Za-z_]\w*)\[", v):
                    if m.group(1) not in PYTHON_KEYWORDS and m.group(1) not in IGNORE_VARS:
                        arr_set.add(m.group(1))
                for word in re.findall(r"[A-Za-z_]\w*", v):
                    if word not in PYTHON_KEYWORDS and word not in IGNORE_VARS and word not in func_names:
                        v_set.add(word)
        if "arr" in ins_dict:
            arr_set.add(ins_dict["arr"])
            v_set.add(ins_dict["arr"])
        return v_set, arr_set

    def _build_blocks(self):
        leaders = set([0])
        for i, ins in enumerate(self.ins):
            if ins is None: continue
            op = ins["op"]
            if op in ("BeginFunc", "EndFunc", "Return"):
                leaders.add(i + 1)
            elif op in ("goto", "if"):
                tidx = self._tidx(ins["target"])
                if tidx is not None:
                    leaders.add(tidx)
                leaders.add(i + 1)

        leaders = sorted([l for l in leaders if l <= len(self.ins)])
        blocks = []
        for k in range(len(leaders)):
            start = leaders[k]
            if start >= len(self.ins): continue
            end = leaders[k+1] - 1 if k+1 < len(leaders) else len(self.ins) - 1
            if start <= end:
                blocks.append((start, end))

        for b_start, b_end in blocks:
            assigned = False
            for fname, meta in self.funcs.items():
                if meta["start"] <= b_start <= meta["end"]:
                    self.func_blocks[fname].append((b_start, b_end))
                    assigned = True
                    break
            if not assigned:
                self.global_blocks.append((b_start, b_end))

        for b_start, b_end in self.global_blocks:
            for i in range(b_start, b_end + 1):
                if self.ins[i] is not None:
                    v_set, a_set = self._extract_vars(self.ins[i])
                    self.global_vars.update(v_set)
                    self.global_arrays.update(a_set)

        for fname, f_blocks in self.func_blocks.items():
            for b_start, b_end in f_blocks:
                for i in range(b_start, b_end + 1):
                    if self.ins[i] is not None:
                        v_set, a_set = self._extract_vars(self.ins[i])
                        self.func_vars[fname].update(v_set)
                        self.func_arrays[fname].update(a_set)

    def W(self, text):
        self.out.append("    " * self.ind + text)

    def WL(self):
        self.out.append("")

    def R(self, tok: str) -> str:
        if not tok: return ""
        tok = tok.strip()
        if tok.startswith("'") and tok.endswith("'") and len(tok) >= 3:
            return f"ord({tok})"
        if tok.startswith('"'):
            return tok
        # Recognize numeric literals (int, float, scientific notation)
        try:
            float(tok)
            return tok
        except ValueError:
            pass
            
        m = re.match(r"^\(([\w:]+)\)(.*)$", tok)
        if m:
            ct, inner = m.group(1), m.group(2).strip()
            inner_expr = self.R(inner)
            if ct == "double": return f"float({inner_expr})"
            if ct == "float": return f"_to_float32({inner_expr})"
            if ct == "char": return f"_wrap_char({inner_expr})"
            if ct == "short": return f"_wrap_short({inner_expr})"
            if ct == "int": return f"_wrap_int({inner_expr})"
            if ct == "long": return f"_wrap_long({inner_expr})"
            if ct.startswith("ptr"): return f"int({inner_expr})"
            return f"int({inner_expr})"
            
        m = re.match(r"^(\w+)\[(.*)\]$", tok)
        if m:
            arr, off = m.group(1), m.group(2).strip()
            return f"_MEM.get({self.R(arr)} + {self.R(off)}, 0)"
            
        if tok.startswith("&"):
            return safe_name(tok[1:])
            
        sname = safe_name(tok)
        if tok in self.address_taken or tok in getattr(self, "current_ref_params", set()):
            return f"_MEM.get({sname}, 0)"
            
        return sname

    def _py_bop(self, bop: str) -> str:
        return ARITH_MAP.get(bop, bop)

    def _write(self, lhs: str, rhs_expr: str):
        if lhs.startswith("deref "):
            ptr = self.R(lhs[6:].strip())
            self.W(f"_MEM[{ptr}] = {rhs_expr}")
            return

        m = re.match(r"^(\w+)\[(.*)\]$", lhs)
        if m:
            arr, off = m.group(1), m.group(2).strip()
            self.W(f"_MEM[{self.R(arr)} + {self.R(off)}] = {rhs_expr}")
            return

        sname = safe_name(lhs)
        if lhs in self.address_taken or lhs in getattr(self, "current_ref_params", set()):
            self.W(f"_MEM[{sname}] = {rhs_expr}")
        else:
            self.W(f"{sname} = {rhs_expr}")

    #  main emit generation 

    def generate(self) -> str:
        self.out.append("")
        
        # Type wrapping helpers
        self.out.append("import math as _math, struct as _struct")
        self.out.append("def _float_to_int(v, bits):")
        self.out.append("    if _math.isnan(v): return 0")
        self.out.append("    hi=(1<<(bits-1))-1; lo=-(1<<(bits-1))")
        self.out.append("    if v>=hi+1: return hi")
        self.out.append("    if v<lo: return lo")
        self.out.append("    return int(v)")
        self.out.append("def _wrap_char(v):")
        self.out.append("    if isinstance(v,float): v=_float_to_int(v,32); v=v&0xFF; return v if v<128 else v-256")
        self.out.append("    v=int(v)&0xFF; return v if v<128 else v-256")
        self.out.append("def _wrap_short(v):")
        self.out.append("    if isinstance(v,float): v=_float_to_int(v,32); v=v&0xFFFF; return v if v<32768 else v-65536")
        self.out.append("    v=int(v)&0xFFFF; return v if v<32768 else v-65536")
        self.out.append("def _wrap_int(v):")
        self.out.append("    if isinstance(v,float): return _float_to_int(v,32)")
        self.out.append("    v=int(v)&0xFFFFFFFF; return v if v<2147483648 else v-4294967296")
        self.out.append("def _wrap_long(v):")
        self.out.append("    if isinstance(v,float): return _float_to_int(v,64)")
        self.out.append("    v=int(v)&0xFFFFFFFFFFFFFFFF; return v if v<9223372036854775808 else v-18446744073709551616")
        self.out.append("def _to_float32(v):")
        self.out.append("    try: return _struct.unpack('f',_struct.pack('f',float(v)))[0]")
        self.out.append("    except: return float('inf') if float(v)>0 else float('-inf')")
        self.out.append("def _trunc_div(a,b):")
        self.out.append("    if b==0: raise ZeroDivisionError")
        self.out.append("    return int(a/b)")
        self.out.append("")

                #  memory: dict of address->value, _MALLOC_PTR is next free address
        # start at 1000 so address 0 stays free to mean NULL

        self.out.append("_MEM = {}")
        self.out.append("_MALLOC_PTR = 1000")
        self.out.append("def _malloc(size):")
        self.out.append("    global _MALLOC_PTR")
        self.out.append("    p = _MALLOC_PTR")
        self.out.append("    try: sz = int(size)")
        self.out.append("    except: sz = 1000")
        self.out.append("    _MALLOC_PTR += sz")
        self.out.append("    return p")
        self.out.append("")

        # declare global arrays and variables at module level
        # arrays get a _malloc block, address-taken vars also get _malloc,
        # normal vars just start at 0


        for arr in sorted(self.global_arrays):
            self.out.append(f"{safe_name(arr)} = _malloc(1000)  # global array")
            
        for var in sorted(self.global_vars):
            if var in self.global_arrays: continue
            if var in self.address_taken:
                self.out.append(f"{safe_name(var)} = _malloc(4)  # address-taken global")
            else:
                self.out.append(f"{safe_name(var)} = 0  # global var")

        if self.global_arrays or self.global_vars:
            self.out.append("")

        # emit each function as a python def
        for fname, meta in self.funcs.items():
            self.current_ref_params = self.ref_params.get(fname, set())
            self.WL()
            params = meta["params"]
            self.W(f"def {fname}({', '.join(safe_name(p) for p in params)}):")
            self.ind += 1
            # need global so we can modify _MEM and _MALLOC_PTR from inside function
            self.W("global _MEM, _MALLOC_PTR")
            
            # if function uses any global vars, declare them global so assignment works
            f_vars = self.func_vars.get(fname, set())
            to_decl = f_vars.intersection(self.global_vars) - set(params)
            if to_decl:
                self.W(f"global {', '.join(safe_name(v) for v in sorted(to_decl))}")
            # local arrays need their own _malloc block
            f_arrays = self.func_arrays.get(fname, set())
            for arr in sorted(f_arrays):
                if arr not in self.global_arrays and arr not in params:
                    self.W(f"{safe_name(arr)} = _malloc(1000)  # local array")
                        
                        # local vars: address-taken ones get _malloc, rest just = 0   
            local_vars = f_vars - self.global_vars - set(params) - f_arrays
            for var in sorted(local_vars):
                if var in self.address_taken and var not in self.current_ref_params:
                    self.W(f"{safe_name(var)} = _malloc(4)  # address-taken local")
                else:
                    self.W(f"{safe_name(var)} = 0  # local var")


         # if a param itself is address-taken ( does &param inside func)
            # we need to move its value into _MEM so pointer ops work on it
       
            for p in params:
                if p in self.address_taken and p not in self.current_ref_params:
                    self.W(f"_{safe_name(p)}_val = {safe_name(p)}")
                    self.W(f"{safe_name(p)} = _malloc(4)  # wrap param")
                    self.W(f"_MEM[{safe_name(p)}] = _{safe_name(p)}_val")

            f_blocks = self.func_blocks.get(fname, [])
            if f_blocks:
                self._emit_state_machine(f_blocks)
            else:
                self.W("pass")
            self.ind -= 1

        self.current_ref_params = set()
        self.WL()
            # emit top-level (global scope) code the same way

        if self.global_blocks:
            self._emit_state_machine(self.global_blocks)

        if "main" in self.funcs:
            self.WL()
            self.W("if __name__ == '__main__':")
            self.ind += 1
            self.W("main()")
            self.ind -= 1

        return "\n".join(self.out) + "\n"
    

    # make a while True loop with _pc variable as program counter
    # each basic block becomes an if/elif branch, goto becomes _pc=N; continue
    def _emit_state_machine(self, blocks):
        if not blocks: return
        self.W(f"_pc = {blocks[0][0]}")
        self.W("while True:")
        self.ind += 1
        for idx, (b_start, b_end) in enumerate(blocks):
            if idx == 0:
                self.W(f"if _pc == {b_start}:")
            else:
                self.W(f"elif _pc == {b_start}:")
            
            # Next block start in THIS context (skip function bodies between global blocks)
            next_start = blocks[idx + 1][0] if idx + 1 < len(blocks) else len(self.ins)
            self.ind += 1
            self._emit_block(b_start, b_end, next_start)
            self.ind -= 1
        
        self.W("else:")
        self.ind += 1
        self.W("break")
        self.ind -= 1
        self.ind -= 1

    def _emit_block(self, start, end, next_start=None):
        if next_start is None: next_start = end + 1
        for i in range(start, end + 1):
            ins = self.ins[i]
            if ins is None: continue
            op = ins["op"]

            if op in ("BeginFunc", "PopParam"): continue
                
            if op == "EndFunc":
                self.W("return")
                continue
            
            if op == "PushParam":
                self._push_queue.append(self.R(ins["val"]))
                continue
                
            if op == "call_void":
                args = ", ".join(reversed(self._push_queue))
                self._push_queue = []
                self.W(f"{ins['fname']}({args})")
                continue
                
            if op == "call_ret":
                args = ", ".join(reversed(self._push_queue))
                self._push_queue = []
                self._write(ins['result'], f"{ins['fname']}({args})")
                continue

            if op == "if":
                a = self.R(ins["a"])
                b = self.R(ins["b"])
                py_rel = REL_MAP.get(ins["rel"], ins["rel"])
                tidx = self._tidx(ins["target"])
                self.W(f"if {a} {py_rel} {b}:")
                self.ind += 1
                self.W(f"_pc = {tidx}")
                self.W("continue")
                self.ind -= 1
                continue
                
            if op == "goto":
                tidx = self._tidx(ins["target"])
                self.W(f"_pc = {tidx}")
                self.W("continue")
                continue
                
            if op == "Return":
                v = ins.get("val")
                if v:
                    self.W(f"return {self.R(v)}")
                else:
                    self.W("return")
                continue

            self._emit_op(ins)

        last_ins = self.ins[end]
        if last_ins is None or last_ins["op"] not in ("goto", "Return", "EndFunc"):
            self.W(f"_pc = {next_start}")
            self.W("continue")

    # handles all the non-control-flow TAC instructions
    # print, input, array ops, pointer ops, memory alloc, casts, arithmetic etc.
    def _emit_op(self, ins):
        op = ins["op"]
        
        if op == "print":
            val_raw = ins["val"]
            kind = ins["kind"]
            if kind == "printstring":
             if val_raw.startswith('"') or val_raw.startswith("'"):
                    self.W(f"print({val_raw})")
             else:
                arr_py = self.R(val_raw)
                self.W(f"_p = {arr_py}")
                self.W(f"while _MEM.get(_p, 0) != 0:")
                self.ind += 1
                self.W(f"print(chr(int(_MEM[_p])), end='')")
                self.W(f"_p += 1")
                self.ind -= 1
                self.W(f"print()  # newline after string")
            elif kind == "printchar":
                val = self.R(val_raw)
                self.W(f"print(chr(_wrap_char(int({val})) & 0xFF))")
            else:
                val = self.R(val_raw)
                self.W(f"print({val})")

        elif op == "input":
            var_raw = ins["var"]
            kind = ins["kind"]
            if kind == "inputfloat": val = "float(input())"
            elif kind == "inputchar": val = "ord(input()[0])"
            elif kind == "inputstring": val = "input()"
            else: val = "int(float(input()))  # tolerates float input like 7.5"
            self._write(var_raw, val)

        elif op == "arr_store":
            self._write(f"{ins['arr']}[{ins['offset']}]", self.R(ins['val']))

        elif op == "arr_store_var":
            self._write(f"{ins['arr']}[{ins['offset_expr']}]", self.R(ins['val']))

        elif op == "arr_load":
            self._write(ins['result'], f"_MEM.get({self.R(ins['arr'])} + {ins['offset']}, 0)")

        elif op == "arr_load_var":
            self._write(ins['result'], f"_MEM.get({self.R(ins['arr'])} + {self.R(ins['offset_expr'])}, 0)")

        elif op == "ref":
            self._write(ins['result'], safe_name(ins['src']))

        elif op == "deref_load":
            self._write(ins['result'], f"_MEM.get({self.R(ins['src'])}, 0)")

        elif op == "deref_store":
            self.W(f"_MEM[{self.R(ins['ptr'])}] = {self.R(ins['val'])}")

        elif op in ("alloc", "calloc"):
            count = self.R(ins.get("count", "1"))
            esz = self.R(ins.get("elem_size", "1"))
            self._write(ins['result'], f"_malloc({count} * {esz})")

        elif op == "realloc":
            ptr = self.R(ins["ptr"])
            self._write(ins['result'], ptr) # Flat memory does not need to move data

        elif op == "free":
            ptr = self.R(ins["ptr"])
            self.W(f"_free_ptr = {ptr}")
            self.W(f"while _free_ptr in _MEM:")
            self.ind += 1
            self.W(f"del _MEM[_free_ptr]")
            self.W(f"_free_ptr += 1")
            self.ind -= 1

        elif op == "cast":
            val = self.R(ins["val"])
            ct = ins["cast_type"]
            if ct == "double": self._write(ins["result"], f"float({val})")
            elif ct == "float": self._write(ins["result"], f"_to_float32({val})")
            elif ct == "char": self._write(ins["result"], f"_wrap_char({val})")
            elif ct == "short": self._write(ins["result"], f"_wrap_short({val})")
            elif ct == "int": self._write(ins["result"], f"_wrap_int({val})")
            elif ct == "long": self._write(ins["result"], f"_wrap_long({val})")
            else: self._write(ins["result"], f"int({val})")

        elif op == "unary":
            self._write(ins["result"], f"{ins['uop']}{self.R(ins['val'])}")

        elif op == "binop":
            a_expr = self.R(ins["a"])
            b_expr = self.R(ins["b"])
            bop = ins["bop"]
            if bop == "/":
                self._write(ins["result"], f"_trunc_div({a_expr}, {b_expr})")
            else:
                self._write(ins["result"], f"{a_expr} {self._py_bop(bop)} {b_expr}")

        elif op == "copy":
            self._write(ins["result"], self.R(ins["val"]))

        elif op == "unknown":
            self.W(f"# unknown: {ins.get('raw')}")


#  entry point 
def main():
    import argparse
    import os  
    ap = argparse.ArgumentParser(
        description="Transpile  TAC) - Python 3")
    ap.add_argument("input",  nargs="?", default="unoptimized.tac",
                    help="TAC file to read (default: unoptimized.tac)")
    ap.add_argument("output", nargs="?", default="generated.py",
                    help="Python file to write (generated.py)")
    args = ap.parse_args()

    try:
        with open(args.input, "r", encoding="utf-8", errors="replace") as f:
            raw_lines = f.readlines()
    except FileNotFoundError:
        sys.exit(1)

    if raw_lines and raw_lines[0].strip() == "# SEMANTIC_ERROR":
        sys.exit(1)

    instructions = []
    lnum_to_idx: dict = {}
    for raw in raw_lines:
        ins = parse_line(raw)
        idx = len(instructions)
        if ins is not None:
            lnum_to_idx[ins["lnum"]] = idx
        instructions.append(ins)
    tr   = Transpiler(instructions, lnum_to_idx)
    code = tr.generate()
    if args.output == "-":
        sys.stdout.write(code)
    else:
        # Remove existing output file if it exists
        if os.path.exists(args.output):
            try:
                os.remove(args.output)
            except OSError:
                pass   
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(code)
if __name__ == "__main__":
    main()