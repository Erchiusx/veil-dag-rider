import Veil
set_option linter.dupNamespace false



veil module DAG

type address
type nodeSet
instantiate nset: ByzNodeSet address nodeSet

type block
instantiate inst: LE block
instantiate decLE: DecidableRel inst.le
instantiate ord: Ord block
abbrev round := Nat
abbrev wave := Fin 3
instantiate instw: LE wave
instantiate decLEw: DecidableRel instw.le
instantiate ordw: Ord wave

-- type vtxs

@[veil_decl]
structure vertex (address block: Type) where
  source: address
  payload: block
deriving instance Veil.Enumeration for vertex
deriving instance Veil.FinEncodableInjOnly for vertex
-- instantiate instv: LE $ vertex address block
-- instantiate decLEv: DecidableRel $ instv.le
-- instantiate ordv: Ord $ vertex address block
-- set_option trace.Meta.synthInstance true in
-- deriving instance DecidableEq for vertex

-- we need to quantify over vertices,
-- so the round parameter is separated from the vertex type
-- instantiate vset: TSet (vertex address block) vtxs

@[veil_decl]
structure message (address block : Type) where
  payload: vertex address block
  strong: List $ vertex address block
  weak: List $ vertex address block
-- deriving instance Veil.Enumeration for message
-- deriving instance Veil.FinEncodableInjOnly for message

@[veil_decl]
structure edge (address block: Type) where
  top: vertex address block
  bot: vertex address block
deriving instance Veil.Enumeration for edge

@[veil_decl]
structure Graph (address block edge: Type) where
  nodes: List $ vertex address block
  strong: List edge
  weak: List edge

function view
  : address
  → Graph address block (edge address block)
function current_round
  : address
  → round

immutable function a_bcast: address → round → block
-- function r_bcast
--   : address
--   → message address block
--   → Option round
function r_bcast: address → List (message address block × round)
-- function r_deliver
--   : address
--   → message address block
--   → address
--   → Option round
function r_deliver: address → List (message address block × address × round)
-- relation chooseLeader: address → wave → Bool
relation chooseLeader: address → wave → Bool
immutable -- by GlobalPerfectCoin, passed from outside
function waveLeader: wave → address
function decidedWave: address → wave
-- relation a_deliver_at: address → block → round → address → wave → Bool
function a_deliver_at: address → List (block × round × address)
function deliveredVertices: address → List (vertex address block)

-- function recvLog: address → (checked: vertex address block) → Option (round × (message address block vtxs))
function recvLog: address → List ((vertex address block × round × message address block))
-- when receiving, set the `recvLog` of the vertex from the r_deliver
function voted: address → List (vertex address block)
function waveVertexLeader: address → wave → Option (vertex address block)
immutable individual f: Nat
#gen_state

after_init {
  current_round I := 0
  view I := Graph.mk [] [] []

  r_bcast I := []
  r_deliver I := []

  chooseLeader I W := false
  decidedWave I := (0: wave)

  -- a_deliver_at I B R A W := false
  a_deliver_at I := []
  deliveredVertices I := []

  -- recvLog I V := none
  recvLog I := []
  voted I := []

  waveVertexLeader I W := none
}

procedure maintain_DAG (i: address) {
  let g := view i
  -- let v
  --  :| recvLog i v ≠ none
  --   ∧ ¬ vset.contains v g.nodes
  let recv := (recvLog i).mergeSort (fun (_, r, _) (_, r', _) => r < r')
  view i := recv.foldl (fun ga (v, r, msg) =>
  if (
    let timecheck := (r ≤ current_round i)
    let deps := msg.strong ++ msg.weak
    let depscheck := deps.all (fun v => v ∈ g.nodes)
    let majority_escape := r == 1
    let majority := msg.strong.length > 2 * f + 1
    let validity := (do
      let v' <- msg.strong
      let (c', r', _) <- recvLog i
      -- guard (v' == c')
      if v' ≠ c' then [] else
      pure $ r' + 1 == r
    ).all id
      ; timecheck
    && (majority_escape || majority)
    && validity
    && depscheck
  ) then
    let strong_edges := msg.strong.map (edge.mk v)
    let weak_edges := msg.weak.map (edge.mk v)
    Graph.mk
      (g.nodes.insert v)
      (strong_edges ++ g.strong)
      (weak_edges ++ g.weak)
    else ga ) g
}

action ReliableBroadcast (i: address) (j: address) {
  -- let m :| r_bcast i m ≠ none ∧ r_deliver j m i = none
  require r_bcast i ≠ []
  let mpack :| mpack ∈ r_bcast i
  let (m, r) := mpack
  if (m, i, r) ∈ r_deliver j then return ()
  -- r_deliver j m i := r_bcast i m
  r_deliver j := r_deliver j |> .insert (m, i, r)
}

-- action GlobalPerfectCoin (w: wave) {
--   if
--       waveLeader w = none
    -- ∧ ∃ s: nodeSet
    --   , nset.supermajority s
    --   ∧ ∀ i: address
    --     , nset.member i s
    --     → w ∈ chooseLeader i
--     then
--   -- let wl :| wl ∈ replicas
--       let wl <- pick address
--       waveLeader w := some wl
-- }

-- action ChooseLeader (i: address) (w: wave) {
--   require current_round i > 4 * (w-1)
--   -- chooseLeader i w := true
--   if ¬ w ∈ chooseLeader i
--     then chooseLeader i := chooseLeader i |> List.insert w
--   GlobalPerfectCoin w
-- }

action recv (i: address) {
  let output :| output ∈ r_deliver i
  let (m, j, r) := output
  -- -- require vset.count m.strong > (2 * f + 1)
  -- --   ∨ (r_deliver i m j <&> (·==1)) == some true
  if m.strong.length ≤ (2 * f + 1) ∧ r ≠ 1 then return ()
  let checked := vertex.mk j m.payload.payload
  if (checked, r, m) ∈ recvLog i then return ()
  -- recvLog i checked := (r_deliver i m j).map (·, m)
  recvLog i := recvLog i |> .insert (checked, r, m)
  -- maintain_DAG i
  -- move maintain_DAG to before advancing round
}

def subsets.{α} {t: Type α} (l: List t): List (List t) := match l with
| []      => [[]]
| x :: xs =>
  let rest := subsets xs
  rest ++ rest.map (fun ys => x :: ys)

procedure send (i: address) {
  let r := current_round i
  let b := a_bcast i r
  let v := vertex.mk i b
  let g := view i
  -- require
  --   ∀ m: message address block
  --   , r_bcast i m ≠ none
  --   → r_bcast i m ≠ some r
  require
    r_bcast i |> (·.all (fun (_, r') => r' ≠ r))
  require r ≠ 0
  if nset.is_byz i then
    let byz <- pick Bool
    if byz then
      let b <- pick block
      let j <- pick address
      let sliced := do
        let v <- g.nodes
        let (checked, rv, msg) <- recvLog i
        guard (v == checked)
        guard (rv == r)
        pure v
      let strong :| strong ∈ subsets sliced
      let weak :| weak ∈ subsets g.nodes
      let v := vertex.mk j b
      let m := message.mk v strong weak
      r_bcast i := r_bcast i |> .insert (m, r)
      voted i := g.nodes.insert v
      recvLog i := recvLog i |> .insert (v, r, m)
      let strong_edges := strong.map (fun v' => edge.mk v v')
      let weak_edges := weak.map (fun v' => edge.mk v v')
      view i := Graph.mk (voted i) (strong_edges ++ g.strong) (weak_edges ++ g.weak)
      return ()
  let slice := do
    let (_, rv, _) <- recvLog i
    guard (rv == r - 1)
    pure ()
  require r = 1 ∨ slice.length ≥ 2 * f + 1
  let strong := do
    let node <- g.nodes
    let (checked, r', _) <- recvLog i
    if r' == r-1 && node == checked then pure node else []
  let weak := do
    let node <- g.nodes
    let (checked, r', _) <- recvLog i
    if r' < r-1 && node == checked && (node ∉ voted i) then pure node else []
  let m := message.mk v strong weak
  r_bcast i := r_bcast i |> .insert (m, r)
  voted i := g.nodes.insert v
  recvLog i := recvLog i |> .insert (v, r, m)
  let strong_edges := strong.map (fun v' => edge.mk v v')
  let weak_edges := weak.map (fun v' => edge.mk v v')
  view i := Graph.mk (voted i) (strong_edges ++ g.strong) (weak_edges ++ g.weak)
}

procedure getWaveVertexLeader (i: address) (w: wave) {
  require w > 0
  require current_round i ≥ 4 * w
  if ¬ chooseLeader i w then chooseLeader i w := true
  let g := view i
  let mut ret := waveVertexLeader i w
  if ret ≠ none then return ret
  return g.nodes.foldl (fun ret v =>
        if (recvLog i).any (fun (checked, r, _)
          => r == 4 * (w-1) + 1
           ∧ checked == v
           ∧ some (v.source) == waveLeader w
        ) then some v else ret
      ) ret
}

-- set_option trace.Meta.synthInstance true
def findLog?
  (default: vertex address block)
  (logs: List $ (vertex address block × round × message address block))
  (v': vertex address block)
  [DecidableEq (vertex address block)] :=
  (logs.find?
    (fun (checked, _, _) => decide $ checked = v')).getD (default, 0, message.mk default [] [])
  -- this `getD` will not be triggered, `default` only passed for type

partial def strong_path
  (default: vertex address block)
  (g: Graph address block $ edge address block)
  (logs: List $ (vertex address block × round × message address block))
  (u v: vertex address block)
  [DecidableEq (vertex address block)]
  : Bool :=
  if u == v then true else
  let (_, ur, um) := findLog? default logs u
  let (v, vr, _) := findLog? default logs v
  if ur ≤ vr then false else
  um.strong.any (fun u' => strong_path default g logs u' v)

partial def path
  (default: vertex address block)
  (g: Graph address block $ edge address block)
  (logs: List $ (vertex address block × round × message address block))
  (u v: vertex address block)
  [DecidableEq (vertex address block)]
  : Bool :=
  if u == v then true else
  let (_, ur, um) := findLog? default logs u
  let (v, vr, _) := findLog? default logs v
  if ur ≤ vr then false else
  (um.strong ++ um.weak).any (fun u' => path default g logs u' v)

procedure orderVertices (i: address) (vertices: List $ vertex address block) {
  let g := view i
  let dd := deliveredVertices i
  let logs := recvLog i
  let v? :| v? ∈ g.nodes
  let verticesToDiliverRaw := do
    let wvl <- vertices
    let v <- g.nodes
    guard (path v? g logs wvl v)
    guard (v ∉ dd)
    pure v
  let verticesToDiliver :=
    verticesToDiliverRaw.eraseDups.mergeSort
      (fun u v => decide $ inst.le u.payload v.payload)
  deliveredVertices i := dd ++ verticesToDiliver
  a_deliver_at i := a_deliver_at i ++ do
    let v <- verticesToDiliver
    let (_, r, _) := findLog? v? logs v
    return (v.payload, r, v.source)
}

procedure waveReady (i: address) (w: wave) {
  if nset.is_byz i then return () -- we only care about how non-byz replicas work at waveReady
  require ¬ chooseLeader i w
  require w > 0
  require current_round i ≥ 4 * w
  let wd := decidedWave i
  require w > wd
  -- getWaveVertexLeader i w
  let wo <- getWaveVertexLeader i w
  -- let wo := waveVertexLeader i w
  if wo == none then return ()
  let g := view i
  let v? :| v? ∈ g.nodes
  let v := wo.getD v?
  -- let vl <- findLog i v v
  let logs := recvLog i
  let findLog! := findLog? v logs
  -- let vl := findLog! v
  -- this `getD` will never fail, v is only assisting the type;
  -- normally we should use the pattern `if let some vl := wo` ,
  -- but #gen_spec denies that??
  let sliceRound := (4: Nat) * w
  let readyVertices := (do
    let u <- g.nodes
    let (_, r, _) := findLog! u
    guard (r == sliceRound)
    guard (strong_path v g logs u v)
    pure v
  )
  let prepare := decide $ readyVertices.length ≥ 2 * f + 1
  if ¬ prepare then return ()
  chooseLeader i w := true
  let loopWaves := (do
    let index <- List.range (w-1 - wd)
    pure $ Fin.ofNat 3 (w-1 - index)
  )
  let chooseWaveLeaderWillReturn := fun w => decide $
    ∃ s: nodeSet
    , nset.supermajority s
    ∧ ∀ j: address
      , nset.member j s
      → chooseLeader j w
  let (leadersStack, _) := loopWaves.foldl
    -- since for-in loop in action does not work well,
    -- now use `foldl` and `bind` to simulate for-in
    -- GlobalPerfectCoin reconstruct: inline getWaveVertexLeader
    (fun (leadersStack, v) w' =>
      if chooseWaveLeaderWillReturn w'
      then (leadersStack, v)
      else
        let v'o := g.nodes.find? (fun ve =>
          let (checked, r', _) := findLog! ve
           ; checked.source == waveLeader w'
          && r' == 4 * (w-1) + 1
        );
        match v'o with
        | none => (leadersStack, v)
        | some v' => (leadersStack.insert v', v')
    )
    ([v], v)
  decidedWave i := w
  orderVertices i leadersStack
}

action advanceRound (i: address) {
  -- maintain_DAG i -- this stucks the elaborator, why???

  -- ## begin inlined maintain_DAG i

  let g := view i
  -- let v
  --  :| recvLog i v ≠ none
  --   ∧ ¬ vset.contains v g.nodes
  let recv := (recvLog i).mergeSort (fun (_, r, _) (_, r', _) => r < r')
  view i := recv.foldl (fun ga (v, r, msg) =>
  if (
    let timecheck := (r ≤ current_round i)
    let deps := msg.strong ++ msg.weak
    let depscheck := deps.all (fun v => v ∈ g.nodes)
    let majority_escape := r == 1
    let majority := msg.strong.length > 2 * f + 1
    let validity := (do
      let v' <- msg.strong
      let (c', r', _) <- recvLog i
      -- guard (v' == c')
      if v' ≠ c' then [] else
      pure $ r' + 1 == r
    ).all id
      ; timecheck
    && (majority_escape || majority)
    && validity
    && depscheck
  ) then
    let strong_edges := msg.strong.map (edge.mk v)
    let weak_edges := msg.weak.map (edge.mk v)
    Graph.mk
      (g.nodes.insert v)
      (strong_edges ++ g.strong)
      (weak_edges ++ g.weak)
    else ga ) g

  -- ## end inlined maintain_DAG i

  let r := current_round i
  require r ≤ 12
  if r == 0 then
    current_round i := 1
    send i
    return ()
  let slice := do
    let (_, rv, _) <- recvLog i
    guard (rv == r)
    pure ()
  if slice.length ≥ 2 * f + 1 then
    if r % 4 == 0 then
      waveReady i (Fin.ofNat 3 r/4)
    current_round i := r + 1
    send i
}

-- transition byz {
--   -- choosing leader
--   True
--   ∧ ( ∀ (i: address) (w: wave)
--       , (¬ nset.is_byz i ∧ chooseLeader' i w ↔ chooseLeader i w)
--       ∨ (nset.is_byz i ∧ chooseLeader i w → chooseLeader' i w)
--     )
--   ∧ ( ∀ (i: address)
--       , (¬ nset.is_byz i ∧ current_round' i = current_round i)
--       ∨ (nset.is_byz i ∧
--           ( current_round' i = current_round i
--           ∨ current_round' i = current_round i + 1
--           ∨ current_round' i = current_round i - 1
--           )
--         )
--     )
-- }

invariant [aggrement]
  ∀ (i j: address)
  , ¬ nset.is_byz i
  ∧ ¬ nset.is_byz j
  → (do
      let (b, r, a) <- a_deliver_at i
      let (b', r', a') <- a_deliver_at j
      guard (b == b')
      pure (r == r' && a == a')
    ).all id

invariant [Tot]
  ∀ (i j: address)
  , ¬ nset.is_byz i
  ∧ ¬ nset.is_byz j
  → let outputᵢ := a_deliver_at i
    let outputⱼ := a_deliver_at j
    let filterᵢ := do
      let (b, r, a) <- outputᵢ
      let (b', _, _) <- outputⱼ
      guard (b == b')
      pure (b, r, a)
    let filterⱼ := do
      let (b, r, a) <- outputⱼ
      let (b', _, _) <- outputᵢ
      guard (b == b')
      pure (b, r, a)
    filterᵢ = filterⱼ

-- set_option diagnostics true
#time #gen_spec

-- #check_invariants

#time #model_check {
  address := Fin (3*1+1)
  nodeSet := ByzNSet (3*1+1)
  block := Fin ((3*1+1) * (3 /- waves-/ * 4 /- 4 rounds each wave-/ + 1 /- vacuum for the last round -/))
} {
  f := 1
  a_bcast := fun i r => Fin.ofNat 52 (4 * r + i)
  waveLeader := fun w => match w with
  | 0 => 1
  | 1 => 2
  | 2 => 1
}

-- #check_invariants

end DAG

#check Veil.VeilM.pickSuchThat
