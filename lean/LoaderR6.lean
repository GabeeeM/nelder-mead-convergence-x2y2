import LoaderR5

/-! Literal tracking states.  `sdefP n := e` / `sdefR n := e` evaluate the state expression `e` (which refers to
earlier literal states) with the compiled checker functions, define `n` as the resulting literal (an `RS` literal
shares the unchanged tail `RS.l prev` of the previous store), and add `n_eq : n = e` proved by `Eq.refl`, checked
by the kernel.  Nothing computed here is trusted: the kernel re-checks `n_eq`.  This stops the kernel from
re-evaluating the whole chain of states from the root in every check. -/

open NM NMC NMR NMR2 NMR3

namespace NMR3
/-- transport a node check along equalities of the tracked state -/
theorem rt_congr {b : Box} {t : RT3} {ps ps' : List W5} {rows rows' : RS} {σ : Nat} {mv : Bool} {post nE nC : Nat}
    (hp : ps' = ps) (hr : rows' = rows) (h : chkRT3 b t ps' rows' σ mv post nE nC = true) :
    chkRT3 b t ps rows σ mv post nE nC = true := hp ▸ hr ▸ h
/-- transport a node check along equalities of the whole tracked state -/
theorem rt_congr5 {b : Box} {t : RT3} {ps ps' : List W5} {rows rows' : RS} {σ σ' : Nat} {mv : Bool} {post nE nE' nC nC' : Nat}
    (hp : ps' = ps) (hr : rows' = rows) (hs : σ' = σ) (he : nE' = nE) (hc : nC' = nC)
    (h : chkRT3 b t ps' rows' σ' mv post nE' nC' = true) :
    chkRT3 b t ps rows σ mv post nE nC = true := hp ▸ hr ▸ hs ▸ he ▸ hc ▸ h
/-- child `k` (1..9) of a node; proofs then refer to the tree constant only (no copies of the children) -/
def RT3.child : RT3 → Nat → RC3
  | .node c1 c2 c3 c4 c5 c6 c7 c8 c9, k =>
    match k with
    | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6 | 7 => c7 | 8 => c8 | _ => c9
  | .leaf .., _ => .skip
def RT3.isNode : RT3 → Bool
  | .node .. => true
  | .leaf .. => false
theorem node_get (b : Box) (t : RT3) (ps : List W5) (rows : RS) (σ : Nat) (moved : Bool) (post nE nC : Nat)
    (h1 : chkRC3 b 1 post (t.child 1) ps rows σ nE nC = true) (h2 : chkRC3 b 2 post (t.child 2) ps rows σ nE nC = true)
    (h3 : chkRC3 b 3 post (t.child 3) ps rows σ nE nC = true) (h4 : chkRC3 b 4 post (t.child 4) ps rows σ nE nC = true)
    (h5 : chkRC3 b 5 post (t.child 5) ps rows σ nE nC = true) (h6 : chkRC3 b 6 post (t.child 6) ps rows σ nE nC = true)
    (h7 : chkRC3 b 7 post (t.child 7) ps rows σ nE nC = true) (h8 : chkRC3 b 8 post (t.child 8) ps rows σ nE nC = true)
    (h9 : chkRC3 b 9 post (t.child 9) ps rows σ nE nC = true) (hn : t.isNode = true) :
    chkRT3 b t ps rows σ moved post nE nC = true := by
  cases t with
  | leaf => simp [RT3.isNode] at hn
  | node c1 c2 c3 c4 c5 c6 c7 c8 c9 => exact node_of b c1 c2 c3 c4 c5 c6 c7 c8 c9 ps rows σ moved post nE nC h1 h2 h3 h4 h5 h6 h7 h8 h9
end NMR3

namespace NMLoadR6
open Lean Elab Command Meta Term NMLoadR3

def zEq (x y : Z) : Bool := x.p == y.p && x.n == y.n
def f5Eq (x y : F5) : Bool := zEq x.c1 y.c1 && zEq x.c2 y.c2 && zEq x.c3 y.c3 && zEq x.c4 y.c4 && zEq x.c5 y.c5
def rowEq : List F5 → List F5 → Bool
  | [], [] => true
  | a :: as, b :: bs => f5Eq a b && rowEq as bs
  | _, _ => false
def rowsEq : List (List F5) → List (List F5) → Bool
  | [], [] => true
  | a :: as, b :: bs => rowEq a b && rowsEq as bs
  | _, _ => false

def encZ (x : Z) : Expr := mkApp2 (mkConst ``NMC.Z.mk) (mkRawNatLit x.p) (mkRawNatLit x.n)
def encF5 (c : F5) : Expr := mkApp5 (mkConst ``NMC.F5.mk) (encZ c.c1) (encZ c.c2) (encZ c.c3) (encZ c.c4) (encZ c.c5)
def encW5 (w : W5) : Expr := mkApp5 (mkConst ``NMR.W5.mk) (encF5 w.w0) (encF5 w.w1) (encF5 w.w2) (encF5 w.w3) (encF5 w.w4)
def f5T : Expr := mkConst ``NMC.F5
def rowT : Expr := mkApp (mkConst ``List [Level.zero]) f5T
def encRow (r : List F5) : Expr := listE f5T (r.map encF5).toArray
def encRows (rs : List (List F5)) : Expr := listE rowT (rs.map encRow).toArray
def w5T : Expr := mkConst ``NMR.W5
def psT : Expr := mkApp (mkConst ``List [Level.zero]) w5T
def rsT : Expr := mkConst ``NMR3.RS

def decNat (e : Expr) : MetaM Nat := do
  match e with
  | .lit (.natVal n) => return n
  | _ => throwError "decNat: not a literal {e}"
def decZ (e : Expr) : MetaM Z := do
  let a := e.getAppArgs
  unless e.isAppOfArity ``NMC.Z.mk 2 do throwError "decZ"
  return ⟨← decNat a[0]!, ← decNat a[1]!⟩
def decF5 (e : Expr) : MetaM F5 := do
  let a := e.getAppArgs
  unless e.isAppOfArity ``NMC.F5.mk 5 do throwError "decF5"
  return ⟨← decZ a[0]!, ← decZ a[1]!, ← decZ a[2]!, ← decZ a[3]!, ← decZ a[4]!⟩
def decW5 (e : Expr) : MetaM W5 := do
  let a := e.getAppArgs
  unless e.isAppOfArity ``NMR.W5.mk 5 do throwError "decW5"
  return ⟨← decF5 a[0]!, ← decF5 a[1]!, ← decF5 a[2]!, ← decF5 a[3]!, ← decF5 a[4]!⟩
partial def decList {α} (d : Expr → MetaM α) (e : Expr) (acc : Array α := #[]) : MetaM (List α) := do
  if e.isAppOfArity ``List.nil 1 then return acc.toList
  else if e.isAppOfArity ``List.cons 3 then decList d e.appArg! (acc.push (← d e.appFn!.appArg!))
  else throwError "decList"
def defVal (n : Name) : MetaM Expr := do
  match (← getEnv).find? n with
  | some (.defnInfo v) => return v.value
  | _ => throwError "no literal definition {n}"

unsafe def evalPsFnImpl (e : Expr) : MetaM (List W5 → RS → List W5) := do
  evalExpr (List W5 → RS → List W5) (← mkArrow psT (← mkArrow rsT psT)) e
@[implemented_by evalPsFnImpl] opaque evalPsFn (e : Expr) : MetaM (List W5 → RS → List W5)
unsafe def evalRSFnImpl (e : Expr) : MetaM (List W5 → RS → RS) := do
  evalExpr (List W5 → RS → RS) (← mkArrow psT (← mkArrow rsT rsT)) e
@[implemented_by evalRSFnImpl] opaque evalRSFn (e : Expr) : MetaM (List W5 → RS → RS)

unsafe def evalNatEImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e
@[implemented_by evalNatEImpl] opaque evalNatE (e : Expr) : MetaM Nat

/-- the `NMS.*` constants of a state expression: (parts constant?, rows constant?) -/
def stateConsts (e : Expr) : MetaM (Option Name × Option Name) := do
  let mut p := none; let mut r := none
  for c in e.getUsedConstants do
    if (`NMS).isPrefixOf c then
      let ci ← getConstInfo c
      if ci.type == psT then
        if p.isSome && p != some c then throwError "two parts constants"
        p := some c
      else if ci.type == rsT then
        if r.isSome && r != some c then throwError "two row constants"
        r := some c
      else throwError "unexpected constant {c}"
  return (p, r)

def closeOver (e : Expr) (p r : Option Name) : Expr :=
  let e := e.replace fun x => match x with
    | .const c _ => if some c == p then some (mkBVar 1) else if some c == r then some (mkBVar 0) else none
    | _ => none
  mkLambda `ps .default psT (mkLambda `rows .default rsT e)

mutual
/-- value of a parts constant: a literal list, or an expression in earlier state constants (evaluated) -/
partial def decPs (n : Name) : MetaM (List W5) := do
  let v ← defVal n
  if v.isAppOfArity ``List.cons 3 || v.isAppOfArity ``List.nil 1 then
    try return ← decList decW5 v catch _ => pure ()
  let (p, r) ← stateConsts v
  let f ← evalPsFn (closeOver v p r)
  return f (← match p with | some c => decPs c | none => pure []) (← match r with | some c => decRS c | none => pure ⟨[], 0⟩)
/-- a row list term: nested `L ++ rest` with literal `L`, ending in a literal or `RS.l c` -/
partial def decRowsE (l : Expr) : MetaM (Option (List (List F5))) := do
  if l.isAppOfArity ``HAppend.hAppend 6 then
    let a := l.getAppArgs
    let some rest ← decRowsE a[5]! | return none
    try return some ((← decList (decList decF5) a[4]!) ++ rest) catch _ => return none
  else if l.isAppOfArity ``NMR3.RS.l 1 && l.appArg!.isConst then
    return some (← decRS l.appArg!.constName!).l
  else
    try return some (← decList (decList decF5) l) catch _ => return none
partial def decRS (n : Name) : MetaM RS := do
  let v ← defVal n
  if v.isAppOfArity ``NMR3.RS.mk 2 then
    if let .lit (.natVal m) := v.appArg! then
      if let some l ← decRowsE v.appFn!.appArg! then return ⟨l, m⟩
  let (p, r) ← stateConsts v
  let f ← evalRSFn (closeOver v p r)
  return f (← match p with | some c => decPs c | none => pure []) (← match r with | some c => decRS c | none => pure ⟨[], 0⟩)
end

def addLit (n : Name) (ty val e : Expr) : CoreM Unit := do
  addDecl (Declaration.defnDecl (mkDefinitionValEx n [] ty val (ReducibilityHints.regular 0) DefinitionSafety.safe []))
  let eqTy := mkApp3 (mkConst ``Eq [Level.one]) ty (mkConst n) e
  addDecl (Declaration.thmDecl { name := Name.str n "eq", levelParams := [], type := eqTy,
                                  value := mkApp2 (mkConst ``Eq.refl [Level.one]) ty (mkConst n) })

def elabState (stx : Syntax) (ty : Expr) : TermElabM Expr := do
  let e ← elabTermEnsuringType stx ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "state has metavariables"
  return e

/-- `sdefN n := e` : literal natural number (scale / step counts); `e` may refer to earlier `sdefN` literals -/
elab "sdefN " n:ident " := " t:term : command => liftTermElabM do
  let e ← elabState t natT
  let mut e' := e
  for c in e.getUsedConstants do
    if (`NMS).isPrefixOf c then
      let v ← defVal c
      unless v.isRawNatLit do throwError "sdefN: {c} is not a literal"
      e' := e'.replace fun x => if x.isConstOf c then some v else none
  let v ← evalNatE e'
  addLit n.getId natT (mkRawNatLit v) e

/-- `sdefP n := e` : literal parts list -/
elab "sdefP " n:ident " := " t:term : command => liftTermElabM do
  let e ← elabState t psT
  let (p, r) ← stateConsts e
  let f ← evalPsFn (closeOver e p r)
  let ps ← match p with | some c => decPs c | none => pure []
  let rs ← match r with | some c => decRS c | none => pure ⟨[], 0⟩
  let v := f ps rs
  addLit n.getId psT (listE w5T (v.map encW5).toArray) e

/-- number of `RS.l` constant links below a row-store constant before a flat literal (or an expression) -/
partial def chainLen (n : Name) : MetaM Nat := do
  let v ← defVal n
  if v.isAppOfArity ``NMR3.RS.mk 2 then
    let l := v.appFn!.appArg!
    if l.isAppOfArity ``HAppend.hAppend 6 then
      let b := l.appArg!
      if b.isAppOfArity ``NMR3.RS.l 1 && b.appArg!.isConst then return 1 + (← chainLen b.appArg!.constName!)
  return 0

def chainMax : Nat := 16

def appendE (front rest : Expr) : Expr :=
  mkApp6 (mkConst ``HAppend.hAppend [Level.zero, Level.zero, Level.zero])
    (mkApp (mkConst ``List [Level.zero]) rowT) (mkApp (mkConst ``List [Level.zero]) rowT)
    (mkApp (mkConst ``List [Level.zero]) rowT)
    (mkApp2 (mkConst ``instHAppendOfAppend [Level.zero]) (mkApp (mkConst ``List [Level.zero]) rowT)
      (mkApp (mkConst ``List.instAppend [Level.zero]) rowT))
    front rest

/-- `sdefR n := e` : literal row store.  When the previous store `r` is an unchanged tail, the literal is
`RS.mk (new ++ RS.l r) m` (small, and the kernel's equation check is one step); after `chainMax` such links the
store is written out flat (a checkpoint), so a row lookup unfolds at most `chainMax` constants. -/
elab "sdefR " n:ident " := " t:term : command => liftTermElabM do
  let e ← elabState t rsT
  let (p, r) ← stateConsts e
  let f ← evalRSFn (closeOver e p r)
  let ps ← match p with | some c => decPs c | none => pure []
  let rs ← match r with | some c => decRS c | none => pure ⟨[], 0⟩
  let v := f ps rs
  let k := v.l.length - rs.l.length
  let mut lit := encRows v.l
  if let some rc := r then
    if rs.l.length ≤ v.l.length && rowsEq (v.l.drop k) rs.l && (← chainLen rc) < chainMax then
      lit := appendE (encRows (v.l.take k)) (mkApp (mkConst ``NMR3.RS.l) (mkConst rc))
  addLit n.getId rsT (mkApp2 (mkConst ``NMR3.RS.mk) lit (mkRawNatLit v.n)) e

/-- `sdefRF n := e` : as `sdefR`, but always a flat literal (no shared tail): fast row lookups in deep trees -/
elab "sdefRF " n:ident " := " t:term : command => liftTermElabM do
  let e ← elabState t rsT
  let (p, r) ← stateConsts e
  let f ← evalRSFn (closeOver e p r)
  let ps ← match p with | some c => decPs c | none => pure []
  let rs ← match r with | some c => decRS c | none => pure ⟨[], 0⟩
  let v := f ps rs
  addLit n.getId rsT (mkApp2 (mkConst ``NMR3.RS.mk) (encRows v.l) (mkRawNatLit v.n)) e

end NMLoadR6
