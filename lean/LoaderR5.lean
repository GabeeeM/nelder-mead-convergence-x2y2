import NMRec5

/-! Data loader for recovery-tree certificates: builds `List LC3` and `KT` terms directly as kernel expressions
from a compact prefix token stream (numbers in hexadecimal), bypassing the elaborator.

Grammar: `LC3 := H x | T RT3`; `RT3 := L den rn rd YS c YS c | N RC3×9` (c = packed pair codes);
`RC3 := I YS c | S RT3 | V RT3 | K | U m RC3×m | G NS fs ld YS c m RC3×m | C NS m RC3×m`;
`YS := m B c` (packed multipliers); `NS := n x×n`. -/

namespace NMR3
/-- Bool form of `walkR3 t b cs = some []` (for `decide`) -/
def walkOK (t : NMC.KT) (b : NMC.Box) (cs : List LC3) : Bool :=
  match walkR3 t b cs with
  | some [] => true
  | _ => false
theorem walkOK_eq (t : NMC.KT) (b : NMC.Box) (cs : List LC3) (h : walkOK t b cs = true) : walkR3 t b cs = some [] := by
  unfold walkOK at h
  split at h
  · assumption
  · simp at h
end NMR3

namespace NMLoadR3
open Lean Elab Command Meta

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def parseHex (s : String) : Nat := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  let mut acc := 0
  let mut i := 0
  while i < n do
    let j := min n (i + 12)
    let mut chunk := 0
    for k in [i:j] do chunk := chunk * 16 + hexVal cs[k]!
    acc := acc * 16 ^ (j - i) + chunk
    i := j
  return acc

def toks (s : String) : Array String := ((s.splitOn " ").filter (· ≠ "")).toArray

def natE (s : String) : Expr := mkRawNatLit (parseHex s)
def natT : Expr := mkConst ``Nat
def pairT : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) natT natT
def listE (ty : Expr) (xs : Array Expr) : Expr := Id.run do
  let mut e := mkApp (mkConst ``List.nil [Level.zero]) ty
  for x in xs.reverse do e := mkApp3 (mkConst ``List.cons [Level.zero]) ty x e
  return e

def parseNS (ts : Array String) (i : Nat) : Expr × Nat := Id.run do
  let n := parseHex ts[i]!
  let mut xs : Array Expr := #[]
  for k in [0:n] do xs := xs.push (natE ts[i + 1 + k]!)
  return (listE natT xs, i + 1 + n)

def parseYS (ts : Array String) (i : Nat) : Expr × Nat := Id.run do
  let n := parseHex ts[i]!
  let mut xs : Array Expr := #[]
  for k in [0:n] do
    xs := xs.push (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) natT natT (natE ts[i + 1 + 2 * k]!)
      (natE ts[i + 2 + 2 * k]!))
  return (listE pairT xs, i + 1 + 2 * n)

def parsePY (ts : Array String) (i : Nat) : Expr × Nat :=
  (mkApp3 (mkConst ``NMR3.PY.mk) (natE ts[i]!) (natE ts[i+1]!) (natE ts[i+2]!), i + 3)

def boolE (s : String) : Expr := if s == "1" then mkConst ``Bool.true else mkConst ``Bool.false

mutual
partial def parseRT (ts : Array String) (i : Nat) : Except String (Expr × Nat) := do
  let t := ts[i]!
  if t == "XT" then return (mkConst ts[i+1]!.toName, i + 2)
  if t == "L" then
    let den := boolE ts[i+1]!
    let rn := natE ts[i+2]!; let rd := natE ts[i+3]!
    let (y1, i) := parsePY ts (i + 4)
    let p1 := natE ts[i]!
    let (y2, i) := parsePY ts (i + 1)
    let p2 := natE ts[i]!
    let i := i + 1
    return (mkAppN (mkConst ``NMR3.RT3.leaf) #[den, rn, rd, y1, p1, y2, p2], i)
  else if t == "N" then
    let mut cs : Array Expr := #[]
    let mut j := i + 1
    for _ in [0:9] do
      let (c, j') ← parseRC ts j
      cs := cs.push c; j := j'
    return (mkAppN (mkConst ``NMR3.RT3.node) cs, j)
  else throw s!"RT: bad token {t} at {i}"
partial def parseRC (ts : Array String) (i : Nat) : Except String (Expr × Nat) := do
  let t := ts[i]!
  if t == "XC" then return (mkConst ts[i+1]!.toName, i + 2)
  if t == "I" then
    let (ys, i) := parsePY ts (i + 1)
    return (mkApp2 (mkConst ``NMR3.RC3.inf) ys (natE ts[i]!), i + 1)
  else if t == "S" then
    let (r, i) ← parseRT ts (i + 1)
    return (mkApp (mkConst ``NMR3.RC3.sub) r, i)
  else if t == "K" then
    return (mkConst ``NMR3.RC3.skip, i + 1)
  else if t == "V" then
    let (r, i) ← parseRT ts (i + 1)
    return (mkApp (mkConst ``NMR3.RC3.subu) r, i)
  else if t == "U" then
    let (l, j) ← parseRL ts (i + 1)
    return (mkApp (mkConst ``NMR3.RC3.run) l, j)
  else if t == "G" then
    let (P, i) := parseNS ts (i + 1)
    let fs := natE ts[i]!
    let ld := natE ts[i+1]!
    let (ly, i) := parsePY ts (i + 2)
    let lp := natE ts[i]!
    let i := i + 1
    let (l, j) ← parseRL ts i
    return (mkAppN (mkConst ``NMR3.RC3.grun) #[P, fs, ld, ly, lp, l], j)
  else if t == "C" then
    let (P, i) := parseNS ts (i + 1)
    let (l, j) ← parseRL ts i
    return (mkApp2 (mkConst ``NMR3.RC3.gcyc) P l, j)
  else throw s!"RC: bad token {t} at {i}"
partial def parseRL (ts : Array String) (i : Nat) : Except String (Expr × Nat) := do
  let m := parseHex ts[i]!
  let mut cs : Array Expr := #[]
  let mut j := i + 1
  for _ in [0:m] do
    let (c, j') ← parseRC ts j
    cs := cs.push c; j := j'
  let mut l := mkConst ``NMR3.RL3.nil
  for c in cs.reverse do l := mkApp2 (mkConst ``NMR3.RL3.cons) c l
  return (l, j)
end

def parseLCs (ts : Array String) : Except String (Array Expr) := do
  let mut out : Array Expr := #[]
  let mut i := 0
  while i < ts.size do
    let t := ts[i]!
    if t == "H" then
      out := out.push (mkApp (mkConst ``NMR3.LC3.hole) (natE ts[i+1]!)); i := i + 2
    else if t == "T" then
      let (r, j) ← parseRT ts (i + 1)
      out := out.push (mkApp (mkConst ``NMR3.LC3.tree) r); i := j
    else throw s!"LC: bad token {t} at {i}"
  return out

/-- tree encoding (prefix order): `N d v mx <l> <r>`, `L n h` (h ∈ {0,1}) -/
partial def parseKT (ts : Array String) (i : Nat) : Except String (Expr × Nat) := do
  let t := ts[i]!
  if t == "N" then
    let d := ts[i+1]!.toNat!; let v := ts[i+2]!.toNat!; let mx := ts[i+3]!.toNat!
    let (l, i) ← parseKT ts (i + 4)
    let (r, i) ← parseKT ts i
    return (mkApp5 (mkConst ``NMC.KT.node) (mkRawNatLit d) (mkRawNatLit v) (mkRawNatLit mx) l r, i)
  else if t == "L" then
    let n := ts[i+1]!.toNat!
    let h := if ts[i+2]! == "1" then mkConst ``Bool.true else mkConst ``Bool.false
    return (mkApp2 (mkConst ``NMC.KT.leaf) (mkRawNatLit n) h, i + 3)
  else throw s!"KT: bad token {t} at {i}"

def addDef (n : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| addDecl (Declaration.defnDecl (mkDefinitionValEx n [] ty val (ReducibilityHints.regular 0)
    DefinitionSafety.safe []))

/-- `lc3s_def name "encoding"` : a `List LC3` -/
elab "lc3s_def " n:ident s:str : command => do
  match parseLCs (toks s.getString) with
  | .ok es => addDef n.getId (mkApp (mkConst ``List [Level.zero]) (mkConst ``NMR3.LC3)) (listE (mkConst ``NMR3.LC3) es)
  | .error msg => throwError msg

/-- `rt3_def name "encoding"` : an `RT3` (may reference earlier definitions with `XT name` / `XC name`) -/
elab "rt3_def " n:ident s:str : command => do
  match parseRT (toks s.getString) 0 with
  | .ok (e, _) => addDef n.getId (mkConst ``NMR3.RT3) e
  | .error msg => throwError msg

/-- `rc3_def name "encoding"` : an `RC3` -/
elab "rc3_def " n:ident s:str : command => do
  match parseRC (toks s.getString) 0 with
  | .ok (e, _) => addDef n.getId (mkConst ``NMR3.RC3) e
  | .error msg => throwError msg

/-- `ktr_def name "encoding"` : a `KT` -/
elab "ktr_def " n:ident s:str : command => do
  match parseKT (toks s.getString) 0 with
  | .ok (e, _) => addDef n.getId (mkConst ``NMC.KT) e
  | .error msg => throwError msg

end NMLoadR3
