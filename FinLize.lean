import Veil
set_option linter.dupNamespace false

def TSet.dmap
  [origin_set : TSet α κ] [target_set : TSet β l]
  (s1 : κ)
  (f : (x : α) → origin_set.contains x s1 = true → β) : l :=
  target_set.ofList <|
    (origin_set.toList s1).attach.map (fun x =>
      f x.1 <| by
        exact (origin_set.toList_contains_iff x.1 s1).2 x.2)

veil module DAG

-- enum address = {byz, rb0, rb1, rb2}
abbrev address := Fin 4
abbrev nodeSet := Std.ExtTreeSet address
abbrev block := Fin 52

abbrev round := Fin 13
abbrev wave := Fin 3
instantiate instw: LE wave
instantiate decLEw: DecidableRel instw.le
instantiate ordw: Ord wave

@[veil_decl]
structure vertex where
  time: round
  source: address
  payload: block

deriving instance Veil.Enumeration for vertex
deriving instance Veil.FinEncodableInjOnly for vertex

abbrev vtxs := Std.ExtTreeSet vertex
abbrev Set (a: Type) [Ord a] := Std.ExtTreeSet a

-- type msgs
@[veil_decl]
structure message where
  payload: vertex
  strong: vtxs
  weak: vtxs
deriving instance Veil.Enumeration for message
-- deriving instance Veil.FinEncodableInjOnly for message
-- instantiate mset: TSet message msgs

-- @[veil_decl]
structure edge where
  top: vertex
  bot: vertex
  gt: top.time > bot.time
deriving Repr

instance edge_deq
  [DecidableEq vertex]
  : DecidableEq edge
  | ⟨atop, abot, _⟩, ⟨btop, bbot, _⟩ =>
      match decEq atop btop, decEq abot bbot with
      | isTrue htop, isTrue hbot =>
          isTrue <| by
            cases htop
            cases hbot
            rfl
      | isFalse htop, _ =>
          isFalse <| by
            intro h
            apply htop
            cases h
            rfl
      | _, isFalse hbot =>
          isFalse <| by
            intro h
            apply hbot
            cases h
            rfl

instance [Inhabited address]: Nonempty edge :=
  ⟨ vertex.mk 1 default default
  , vertex.mk 0 default default
  , by simp
  ⟩

instance [VE: Veil.Enumeration vertex]
  : Veil.Enumeration edge where
  allValues := do
    let bot <- (Veil.Enumeration.allValues: List $ vertex)
    let top <- (Veil.Enumeration.allValues: List $ vertex)
    if h: top.time > bot.time then return ⟨top, bot, h⟩ else []
  complete := by
    intro a
    simp
    rcases a with ⟨top, bot, gt⟩
    use bot
    constructor
    exact VE.complete bot
    use top
    constructor
    exact VE.complete top
    use gt

instance: Lean.ToJson edge where
  toJson e := Lean.ToJson.toJson (e.top, e.bot)

instance [Hashable $ vertex]
  : Hashable edge where
  hash e := hash (e.top, e.bot)

instance edge_ord [Ord $ vertex]: Ord $ edge where
  compare a b := match compare a.top b.top with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare a.bot b.bot

instance [BEq $ vertex]: BEq $ edge where
  beq a b := BEq.beq (a.top, a.bot) (b.top, b.bot)

abbrev edgeT  := (vertex × vertex)

instance edgeT_ord [Ord $ vertex]
  : Ord $ edgeT where
  compare a b := match compare a.1 b.1 with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare a.2 b.2

instance edgeT_transOrd
  [VO: Ord $ vertex]
  [VT: Std.TransOrd $ vertex]
  : Std.TransOrd $ edgeT where
  eq_swap := by
    intros a b
    simp [edgeT_ord, VT.eq_swap (a := a.1) (b := b.1)]
    cases h: compare b.1 a.1 with
    | lt => simp
    | gt => simp
    | eq =>
      simp [VT.eq_swap (a := a.2) (b := b.2)]

  isLE_trans := by
    intros a b c hab hbc
    simp_all [edgeT_ord, Ordering.isLE]
    cases hab1: compare a.1 b.1 <;>
    cases hbc1: compare b.1 c.1 <;>
    simp_all
    . have hac1 := VT.lt_trans hab1 hbc1
      simp [hac1]
    . have hac1 := VT.lt_of_lt_of_eq hab1 hbc1
      simp [hac1]
    . have hac1 := VT.lt_of_eq_of_lt hab1 hbc1
      simp [hac1]
    have hac1 := VT.eq_trans hab1 hbc1
    simp [hac1]
    cases hab2: compare a.2 b.2 <;>
    cases hbc2: compare b.2 c.2 <;>
    simp_all
    . have hac2 := VT.lt_trans hab2 hbc2
      simp [hac2]
    . have hac2 := VT.lt_of_lt_of_eq hab2 hbc2
      simp [hac2]
    . have hac2 := VT.lt_of_eq_of_lt hab2 hbc2
      simp [hac2]
    have hac2 := VT.eq_trans hab2 hbc2
    simp [hac2]

-- set_option trace.Meta.synthInstance true in
instance
  [VO: Ord $ vertex]
  [VT: Std.TransOrd $ vertex]
  : Std.TransOrd edge where
  eq_swap := by
    intros a b
    simp [edge_ord]
    exact
      edgeT_transOrd.eq_swap
      (a := (a.top, a.bot))
      (b := (b.top, b.bot))

  isLE_trans := by
    intros a b c
    simp [edge_ord]
    exact
      edgeT_transOrd.isLE_trans
        (a := (a.top, a.bot))
        (b := (b.top, b.bot))
        (c := (c.top, c.bot))

instance
  [Ord $ vertex]
  [VE: Std.LawfulEqOrd vertex]
  : Std.LawfulEqOrd edge where
  eq_of_compare := by
    intros a b h
    simp [edge_ord] at h
    cases ht: compare a.top b.top <;>
    cases hb: compare a.bot b.bot <;>
    simp_all
    cases a
    cases b
    cases ht
    cases hb
    rfl

  compare_self := by
    intro a
    simp [edge_ord]

abbrev edges [Ord address] := Std.ExtTreeSet $ edge

set_option trace.Meta.synthInstance true in
@[veil_decl]
structure Graph where
  nodes: vtxs
  strong: edges
  weak: edges

function view: address → Graph
function current_round: address → round
function r_bcast: address → round → Option message
function r_deliver: address → round → address → Option message
relation chooseLeader: address → wave → Bool
function decidedWave: address → wave
function a_deliver: address → block → round → address → Option wave

relation voted: address → vertex → Bool
function recvLog: address → vertex → Option message

def blockOf: Nat → block := Fin.ofNat 52

#gen_state

-- def a_bcast (i: address_IndT) (r: round): block :=
--   match i with
--   | .byz => blockOf (4 * r + 3)
--   | .rb0 => blockOf (4 * r + 0)
--   | .rb1 => blockOf (4 * r + 1)
--   | .rb2 => blockOf (4 * r + 2)

def a_bcast (i: address) (r: round): block :=
  blockOf (4 * r + i)

def vertex.fromIR (i: address) (r: round): vertex :=
  vertex.mk r i (a_bcast i r)

-- def waveLeader (w: wave): address_IndT := match w with
--   | 0 => .rb0
--   | 1 => .byz
--   | 2 => .rb0

def waveLeader (w: wave): address := match w with
  | 0 => 0
  | 1 => 3
  | 2 => 1

def is_byz (i: address): Bool := i == 3

after_init {
  current_round I := (0: round)
  view I := Graph.mk default default default

  r_bcast I R := none
  r_deliver I R J := none
  chooseLeader I W := false
  decidedWave I := (0: wave)
  a_deliver I B R J := none

  recvLog I V := none
}

action ReliableBroadcast (i: address) (j: address) (r: round) {
  require r_bcast i r ≠ none
  require r_deliver i r j = none
  r_deliver i r j := r_bcast i r
}

action recv (i j: address) (r: round) {
  require r_deliver i r j ≠ none
  let m'o := r_deliver i r j
  let m := m'o.getD default
  let v := vertex.mk r i m.payload.payload
  if recvLog i v ≠ none then return ()
  recvLog i v := some m
}

procedure send (i: address) {
  let r := current_round i
  let b := a_bcast i r
  let v := vertex.mk r i b
  let g := view i
  require r_bcast i r = none
  require r ≠ 0
  if r == 1 then
    let m := message.mk v ∅ ∅
    r_bcast i r := some m
    voted i v := true
    recvLog i v := some m
    view i := Graph.mk (g.nodes.insert v) ∅ ∅
    return ()
  require
    ∃ s: Set address
    , s.size ≥ 3
    ∧ ∀ j ∈ s
      , vertex.fromIR j (r-1) ∈ g.nodes
  let hs := fun s =>
    ∀ j: address
    , j ∈ s
    ↔ vertex.fromIR j (r-1) ∈ g.nodes
  let s: Set address :| hs s
  let hw := fun w =>
    ∀ (j: address) (r': round)
    , let v := vertex.fromIR j r'
    ; (j, r') ∈ w
    ↔ (¬ voted j v)
    ∧ (v ∈ g.nodes)
    ∧ (r' < r)
  let w: Set (address × round) :| hw w
  -- let strongV: vtxs := TSet.map s (fun j => vertex.mk j (a_bcast j (r-1)) (r-1))
  -- let weakV: vtxs := TSet.map w (fun (j, r') => vertex.mk j (a_bcast j r') r')
  let strong: edges := if rn: 0 < r.val then -- if holds by requirement
    TSet.map s (fun j =>
    let v' := vertex.fromIR j (r-1)
    {top := v, bot := v', gt := by {
      have hvt: v.time = r := rfl
      have hv't: v'.time = r-1 := rfl
      simp [hvt, hv't]
      apply Fin.lt_def.mpr
      omega
    }}) else default
  let weak: edges :=
    if hw': hw w then -- if holds by pickSuchThat
    TSet.dmap w (fun (j, r') hv =>
    let v' := vertex.fromIR j r'
    {top := v, bot := v', gt := by {
      have hvt: v.time = r := rfl
      have hv't: v'.time = r' := rfl
      simp [hvt, hv't]
      have helem: (j, r') ∈ w := by exact hv
      have u := (hw' j r').mp helem
      rcases u with ⟨_, _, l⟩
      exact l
    }}) else default
  -- let weak: edges := TSet.map weakV (fun v' => {top := v, bot := v', gt := by decide})
  voted i v := true
  view i := Graph.mk (g.nodes.insert v) (g.strong ∪ strong) (g.weak ∪ weak)
}

procedure maintain (i: address) {
  let g := view i
  let recvIR: Set (address × round) :|
    ∀ (j: address) (r: round)
    , (j, r) ∈ recvIR
    ↔ recvLog j (vertex.fromIR j r) ≠ none
  let recv: vtxs := TSet.map recvIR (fun (j, r) => vertex.fromIR j r)
  view i := recv.foldl (fun ga v =>
  let msg := (recvLog i v).getD default
  if h: (
    let r := v.time
    let timecheck := r ≤ current_round i
    let deps := msg.strong ∪ msg.weak
    let depscheck :=
      ∀ v' ∈ deps
      , v ∈ g.nodes
    let weakness :=
      ∀ v' ∈ msg.weak
      , v'.time < r - 1
    let majority_escape := r = 1
    let majority := msg.strong.size ≥ 3
    let validity :=
      ∀ v' ∈ msg.strong
      , v'.time + 1 = r
      ∧ v'.time < 12
    let begins := r > 0
    ; timecheck
    ∧ (majority_escape ∨ majority)
    ∧ validity
    ∧ depscheck
    ∧ weakness
    ∧ begins
  ) then
    let strong: edges := TSet.dmap msg.strong fun v' hv' =>
    { top := v
    , bot := v'
    , gt := by {
      rcases h with ⟨_, _, validity, _⟩
      have hv: v' ∈ msg.strong := by exact hv'
      let u := validity v' hv
      rcases u with ⟨ul, ur⟩
      simp [← ul, ur]
    } }
    let weak: edges := TSet.dmap msg.weak fun v' hv' =>
    { top := v
    , bot := v'
    , gt := by {
      rcases h with ⟨_, _, _, _, weakness, begins⟩
      let u := weakness v' hv'
      have h?: v.time - 1 < v.time := by {
        apply Fin.lt_def.mpr
        apply Fin.lt_def.mp at begins
        omega
      }
      exact lt_trans u h?
      -- apply Fin.lt_def.mpr at u
    } }
    Graph.mk (g.nodes.insert v)
      (strong ∪ g.strong)
      (weak ∪ g.weak)
  else ga
  ) g
}

invariant [aggrement]
  ∀ (i j k k': address) (r r': round) (b: block)
  , ¬ is_byz i
  ∧ ¬ is_byz j
  → (do
      let wi <- a_deliver i b r k
      let wj <- a_deliver j b r' k'
      return r == r' && k == k' && wi == wj
    ).getD true

invariant [Tot]
  ∀ (i kb kc: address) (b c: block) (rb rc: round)
  , ¬ is_byz i
  ∧ b < c
  → (do
      let wb <- a_deliver i b rb kb
      let wc <- a_deliver i c rc kc
      return decide $ wb ≤ wc
    ).getD true

#gen_spec

-- #check_invariants

-- #model_check {}

end DAG

#check Std.ExtTreeSet
