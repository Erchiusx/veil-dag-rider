import Veil
set_option linter.dupNamespace false

veil module DAG
-- types
type address
type nodeset
type block
type vertex
type vertexset
type path
abbrev round := Nat
abbrev wave := Nat
def round'of'wave (w: wave) (k: round): round := 4*(w-1) + k
def wave'of (r: round): wave := r / 4
variable (is_byz: address → Prop)
variable (a_bcast: address → round → block)

-- classes and instances
instantiate nset: NodeSet address is_byz nodeset
-- about DAG and vertex structure
class VertexSet
  (vertex vset: Type)
where
  member (a: vertex) (s: vset) : Prop
  empty: vset

  supermajority (s: vset): Prop

  empty_is_not_supermajority:
    ¬ supermajority empty
  empty_is_empty:
    ∀ (a: vertex)
    , ¬ member a empty
  insert:
    ∀ (v: vertex) (s: vset)
    , ∃ (s': vset)
      , ∀ (v': vertex)
        , member v' s' ↔ v' = v ∨ member v' s
instantiate vset: VertexSet vertex vertexset

class Vertex
  (vertex address nodeset block vertexset: Type)
  (is_byz: address → Prop)
  [nset: NodeSet address is_byz nodeset]
  [vset: VertexSet vertex vertexset]
where
  roundOf: vertex → round
  source: vertex → address
  block: vertex → block
  strong: vertex → vertexset
  weak: vertex → vertexset

  exists_source_set:
    ∀ (v: vertex)
    , ∃ (s: nodeset)
      , ∀ (i: address)
        , nset.member i s
        ↔ ∃ (v': vertex)
          , vset.member v' (strong v)
          ∧ source v' = i

  majority_inheritence:
    ∀ (v : vertex) (s: nodeset)
    , ( ∀ (u u': vertex)
        , vset.member u (strong v)
        ∧ vset.member u' (strong v)
        → source u ≠ source u'
      )
    ∧ ( ∀ (i: address)
        , nset.member i s
        ↔ ∃ (v': vertex)
          , vset.member v' (strong v)
          ∧ source v' = i
      )
    → nset.supermajority s

instantiate vtx: Vertex vertex address nodeset block vertexset is_byz

class Path
  (path vertex address block vertexset nodeset: Type)
  (is_byz: address → Prop)
  [nset: NodeSet address is_byz nodeset]
  [vset: VertexSet vertex vertexset]
  [vtx: Vertex vertex address nodeset block vertexset is_byz]
where
  member: vertex → path → Prop
  exclusion_round:
    ∀ (p: path)
      (v1 v2: vertex)
    , (member v1 p ∧ member v2 p)
    → vtx.roundOf v1 ≠ vtx.roundOf v2

  top: path → vertex
  bottom: path → vertex

  top_bottom_elem:
    ∀ (p: path)
    , member (top p) p
    ∧ member (bottom p) p

  connected:
    ∀ (p: path)
    , ∀ (v: vertex)
      , member v p
      → v = top p
      ∨ ∃ (v': vertex)
        , member v' p
        ∧ ( vset.member v' (vtx.strong v)
          ∨ vset.member v' (vtx.weak v)
          )

  round_bound:
    ∀ (p: path) (v: vertex)
    , member v p
    → vtx.roundOf v ≥ vtx.roundOf (bottom p)
    ∧ vtx.roundOf v ≤ vtx.roundOf (top p)
instantiate path_: Path path vertex address block vertexset nodeset is_byz

instantiate tot: TotalOrder address

-- relations
relation current_round (a: address) (r: round)

-- note: r_bcast and r_deliver is only applied to vertex
-- in this protocol
-- called r_bcastᵢ(m, r) or not
relation r_bcast
  (i: address)
  (m: vertex)
  (r: round)

-- called r_deliverᵢ(m, r, k) or not
relation r_deliver
  (i: address)
  (m: vertex)
  (r: round)
  (k: address)

relation r_will_deliver_at
  (i: address)
  (m: vertex)
  (r: round)
  (k: address)
  (t: round)

-- called choose_leaderᵢ(w) or not
relation choose_leader (i: address) (w: wave)

-- choose_leader returned or not
relation choose_leader_ret (w: wave) (a: address)

relation buffer (a: address) (v: vertex)
relation in'DAG (a: address) (v: vertex)
relation decidedWave (i: address) (w: wave)
relation deliveredVertex (i: address) (v: vertex)
relation getWaveVertexLeader (i: address) (w: wave) (v: vertex)

relation a_deliver_at (i: address) (m: block) (r: round) (k: address) (w: wave)

#gen_state

-- auxilary functions
syntax term:max "__sig": term
macro_rules
  | `($f __sig) =>
      `($f address nodeset block vertex vertexset path is_byz a_bcast)

def strong_connected_
  : path → Prop := fun p =>
  ∀ (v: vertex)
  , path_.member v p
  → v = path_.top p
  ∨ ∃ (v': vertex)
    , path_.member v' p
    ∧ vset.member v (vtx.strong v')

local notation "strong_connected" =>
  strong_connected_ address nodeset block vertex vertexset path is_byz

def exists_path_where_
  : (path -> vertex → Prop) → vertex → vertex →  Prop := fun f v u =>
  ∃ (p: path)
  , path_.top p = v
  ∧ path_.bottom p = u
  ∧ ( ∀ (vp: vertex)
      , path_.member vp p
      → f p v
    )
def exists_strong_path_where_
  : (path -> vertex → Prop) → vertex → vertex →  Prop := fun f v u=>
  ∃ (p: path)
  , path_.top p = v
  ∧ path_.bottom p = u
  ∧ strong_connected p
  ∧ ( ∀ (vp: vertex)
      , path_.member vp p
      → f p v
    )

local notation "exists_path_where" =>
  exists_path_where_ address nodeset block vertex vertexset path is_byz

local notation "exists_path" =>
  exists_path_where (fun _ _ => True)

local notation "exists_strong_path_where" =>
  exists_strong_path_where_ address nodeset block vertex vertexset path is_byz

local notation "exists_strong_path" =>
  exists_strong_path_where (fun _ _ => True)

def lete: Nat → Nat → Prop → Prop := fun u v p =>
  (u < v) ∨ (u = v ∧ p)

-- transitions

after_init {
  current_round A R           := False
  current_round A 0           := True
  r_bcast I M R               := False
  r_deliver I M R K           := False
  r_will_deliver_at I M R K T := False
  choose_leader A W           := False
  choose_leader_ret W A       := False
  buffer A V                  := False
  in'DAG A V                  := False
  a_deliver_at I B R K W      := False
  decidedWave I W             := False
  decidedWave I 0             := True
  deliveredVertex I V         := False
  getWaveVertexLeader I W V   := False
}

internal transition reliable_broadcast = fun st st' => True
  -- Agreement
  ∧ ( ∀ (i j k: address) (m: vertex) (r: round)
      , (¬ is_byz i)
      ∧ (¬ is_byz j)
      → ( st.r_deliver i m r k
        → ∀ (c: round), st.current_round i c
          → ∃ (t: round)
            , t ≥ c
            ∧ st'.r_will_deliver_at i m r k t
        )
    )
  -- Integrity
  ∧ ( ∀ (r: round) (i k: address)
      , (¬ is_byz i)
      ∧ ∀ (m1 m2: vertex)
        , st'.r_deliver i m1 r k
        ∧ st'.r_deliver i m2 r k
        → m1 = m2
    )
  -- Validity
  ∧ ( ∀ (k: address) (m: vertex) (r: round) (i: address)
      , st.r_bcast k m r
      → st'.r_bcast k m r
      ∧ ∃ (t: round)
        , t ≥ r
        ∧ ∀ (tb: round)
          , st.r_will_deliver_at i m r k tb
          → tb ≥ t
        ∧ st'.r_will_deliver_at i m r k t
    )
  -- time
  ∧ ( ∀ (k: address) (m: vertex) (r r': round) (i: address) (t: round)
      , st.r_will_deliver_at i m r k t
      → st'.r_will_deliver_at i m r k t
      ∧ ( st.current_round i r'
        ∧ r' ≥ t
        → st'.r_deliver i m r k
        )
    )
  -- none-deniable
  ∧ ( ∀ (i: address) (m: vertex) (r: round)
      , ((¬ is_byz i) ∧ st.r_bcast i m r ↔ st'.r_bcast i m r)
      ∨ ((is_byz i) ∧ st.r_bcast i m r → st'.r_bcast i m r)
    )
  ∧ ( ∀ (i k: address) (m: vertex) (r: round)
      , st.r_deliver i m r k → st'.r_deliver i m r k
    )
  ∧ ( ∀ (i k: address) (m: vertex) (r t: round)
      , st.r_will_deliver_at i m r k t
      → st'.r_will_deliver_at i m r k t
    )
  -- other states does not change
  ∧ st.current_round = st'.current_round
  ∧ st.choose_leader = st'.choose_leader
  ∧ st.choose_leader_ret = st'.choose_leader_ret
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader

def global'perfect'coin
  : State __sig
  → State __sig
  → Prop := fun st st' => True
  /-
    cannot deny called choose_leader,
    but can call at any time
  -/
  ∧ ( ∀ (i: address) (w: wave)
      , st.choose_leader i w → st'.choose_leader i w
    )
  /-
    glboal perfect coin will assign one leader once
    f + 1 nodes has chosen leader
  -/
  ∧ ( ∀ (w: wave)
      , ( ∃ (s: nodeset)
          , ( nset.greater_than_third s
            ∧ ∀ (a: address)
            , nset.member a s
            → st.choose_leader a w
            )
        )
      → ∃ (a: address)
        , st'.choose_leader_ret w a
    )
  /- and the result won't change -/
  ∧ ( ∀ (w: wave) (a: address)
      , st.choose_leader_ret w a
      → st'.choose_leader_ret w a
    )
  /- also the result is unique -/
  ∧ ( ∀ (w: wave) (a b: address)
      , st'.choose_leader_ret w a
      ∧ st'.choose_leader_ret w b
      → a == b
    )

internal transition GlobalPerfectCoin = fun st st' => True
  /-
    cannot deny called choose_leader,
    but can call at any time
  -/
  ∧ ( ∀ (i: address) (w: wave)
      , st.choose_leader i w → st'.choose_leader i w
    )
  /-
    glboal perfect coin will assign one leader once
    f + 1 nodes has chosen leader
  -/
  ∧ ( ∀ (w: wave)
      , ( ∃ (s: nodeset)
          , ( nset.greater_than_third s
            ∧ ∀ (a: address)
            , nset.member a s
            → st.choose_leader a w
            )
        )
      → ∃ (a: address)
        , st'.choose_leader_ret w a
    )
  /- and the result won't change -/
  ∧ ( ∀ (w: wave) (a: address)
      , st.choose_leader_ret w a
      → st'.choose_leader_ret w a
    )
  /- also the result is unique -/
  ∧ ( ∀ (w: wave) (a b: address)
      , st'.choose_leader_ret w a
      ∧ st'.choose_leader_ret w b
      → a == b
    )


-- def DAG_maintain
--   : State __sig
--   → State __sig
--   → Prop := fun st st' => True
internal transition DAG_maintain = fun st st' => True
  ∧ ( ∀ (a: address) (v: vertex)
      , (¬ is_byz a)
      -- if a vertex becomes valid, add it into DAG
      → ( (st'.in'DAG a v ∧ ¬ st'.buffer a v)
        ↔ (st.in'DAG a v ∧ ¬ st.buffer a v)
        ∨ ( st.buffer a v
          ∧ ( ∀ (v': vertex)
              , vset.member v' (vtx.strong v)
              ∨ vset.member v' (vtx.weak v)
              → st.in'DAG a v'
            )
          ∧ ( ∀ (v': vertex)
              , st.in'DAG a v'
              → vtx.roundOf v' ≠ vtx.roundOf v
              ∨ vtx.source v' ≠ vtx.source v
            )
          )
        )
      -- whether the vertex has passed the 'receive' checks maintains unchanged
      ∧ ( (st.in'DAG a v ∨ st.buffer a v)
        ↔ (st'.in'DAG a v ∨ st'.buffer a v)
        )
    )
  -- other state does not change
  ∧ st.current_round = st'.current_round
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.choose_leader = st'.choose_leader
  ∧ st.choose_leader_ret = st'.choose_leader_ret
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader

action send -- when a new round begins, in alg2 loop if
  (a: address)
  (v: vertex)
  (r: round) = {
    require current_round a r
    require vtx.source v = a
    require vtx.roundOf v = r
    require a_bcast a r = vtx.block v
    require
      ∀ (v: vertex)
      , ¬ r_bcast a v r
    if r = 0
      then -- first round
        require vtx.strong v = vset.empty
        require vtx.weak v = vset.empty
      else -- not first round
        let r' := r - 1
        require vset.supermajority (vtx.strong v)
        require
          ∀ (v': vertex)
          , vset.member v' (vtx.strong v)
          ↔ vtx.roundOf v' = r'
          ∧ in'DAG a v'
        require
          ∀ (v': vertex)
          , vset.member v' (vtx.weak v)
          ↔ ¬ ∃ (p: path)
              , (path_.top p = v)
              ∧ (path_.bottom p = v')
              ∧ ∀ (v'': vertex)
                , path_.member v'' p
                → v'' = v
                ∨ vset.member v'' (vtx.weak v)
                ∨ in'DAG a v''
    -- send it now with reliable broadcast
    r_bcast a v r := True
    in'DAG a v := True
  }

action receive -- upon r_deliverᵢ(v, r, pₖ) in the paper
  (i k: address)
  (v_receive v_record: vertex)
  (r: round) = {
    require r_deliver i v_receive r k
    -- set source and round of v
    require vtx.roundOf v_record = r
    require vtx.source v_record = k
    require vtx.block v_record = vtx.block v_receive
    require vtx.strong v_record = vtx.strong v_receive
    require vtx.weak v_record = vtx.weak v_receive
    -- check supermajority
    require vset.supermajority (vtx.strong v_receive)
    -- push v into buffer
    buffer i v_record := True
  }

def verticesToDeliver
  : State __sig
  → State __sig
  → address
  → vertex
  → wave
  → Prop := fun st st' i v w =>
  ∀ (wl: vertex) (leaders: vertexset)
  , st'.getWaveVertexLeader i w wl
  ∧ vset.member wl leaders
  ∧ ( ∀ (v': vertex)
      , vset.member v' leaders
      ↔ v' = wl
      ∨ ( ∃ (w': wave)
          , st'.getWaveVertexLeader i w' v'
          ∧ ∀ (wd: wave)
            , st.decidedWave i wd
            → w' > wd ∧ w' < w
        )
      ∧ ( ∀ (v'': vertex)
          , vset.member v'' leaders
          ∧ vtx.roundOf v'' > vtx.roundOf v'
          → exists_strong_path_where
              (fun _ v_ => st'.in'DAG i v_) v' v''
        )
    )
  → ∃ (l: vertex)
    , vset.member l leaders
    ∧ exists_path_where
        (fun _ v_ => st'.in'DAG i v_) l v

def wave_ready
  : State __sig
  → State __sig
  → wave
  → address
  → Prop := fun st st' w i
 => if ∃ (v: vertex) (s: vertexset)
      , st'.getWaveVertexLeader i w v
      ∧ vset.supermajority s
      ∧ ∀ (vs: vertex)
        , st'.in'DAG i vs
        → vtx.roundOf vs = round'of'wave w 4
        ∧ exists_path_where
            (fun _ vp => st'.in'DAG i vp)
            vs v
     then ( st'.decidedWave i = fun w' => w'=w )
        ∧ ( ∀ (v: vertex)
            , st'.deliveredVertex i v
            ↔ ( st.deliveredVertex i v
              ∨ (verticesToDeliver __sig) st st' i v w
              )
          )
     else st'.a_deliver_at i = st.a_deliver_at i
        ∧ st'.deliveredVertex i = st.deliveredVertex i
        ∧ st'.decidedWave i = st.decidedWave i

def advance_round_
  : State __sig
  → State __sig
  → Prop := fun st st' => True
  ∧ ( ∀ (i: address) (r: round)
      , (¬ is_byz i)
      ∧ st.current_round i r
      → if ( ∃ (s: vertexset)
              , vset.supermajority s
              ∧ ∀ (v: vertex)
                , vset.member v s
                → st.in'DAG i v
            )
         then ( ∀ (r': round), st'.current_round i r' = (r' = r+1))
            ∧ if  ∃ (w: wave)
                  , 4 * w = r
              then
                ∀ (w: wave)
                , 4 * w = r
                → (wave_ready __sig)
                  st st' w i
              else
                ∀ (b: block) (r: round) (k: address) (w: wave)
                , st.a_deliver_at i b r k w
                ↔ st'.a_deliver_at i b r k w
         else st'.current_round i = st.current_round i
            ∧ st'.a_deliver_at i = st.a_deliver_at i
    )
  ∧ (global'perfect'coin __sig) st st'
  ∧ ( ∀ (w: wave)
      , ((∃ (j: address)
          , st.choose_leader_ret w j)
          ∧ ∀ (i j: address)
            , st.choose_leader_ret w j
            → ( ∀ (v: vertex)
                , vtx.source v = j
                ∧ vtx.roundOf v = round'of'wave w 1
                ∧ w > 1
                ∧ st.in'DAG i v
                → st'.getWaveVertexLeader i w v
              )
        )
      ∨ ((¬ (∃ (j: address), st.choose_leader_ret w j))
        ∧ ( ∀ (j: address)
            , (st.getWaveVertexLeader j w = st'.getWaveVertexLeader j w)
          )
        )
    )
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG

axiom exists_leaders_set:
  ∀ (st st': State __sig) (i: address) (r: round)
  , st.current_round i r
  ∧ (advance_round_ __sig) st st'
  → ∃ (leaders: vertexset)
    , ( ∀ (v': vertex)
        , vset.member v' leaders
        ↔ ( ∃ (w': wave)
            , st'.getWaveVertexLeader i w' v'
            ∧ ∀ (wd: wave)
              , st.decidedWave i wd
              → w' > wd ∧ w' < 4 * r
          )
        ∧ ( ∀ (v'': vertex)
            , vset.member v'' leaders
            ∧ vtx.roundOf v'' > vtx.roundOf v'
            → exists_strong_path_where
                (fun _ v_ => st'.in'DAG i v_) v' v''
          )
      )

internal transition advance_round = fun st st' => True
  ∧ ( ∀ (i: address) (r: round)
      , (¬ is_byz i)
      ∧ st.current_round i r
      → if ( ∃ (s: vertexset)
              , vset.supermajority s
              ∧ ∀ (v: vertex)
                , vset.member v s
                → st.in'DAG i v
            )
         then ( ∀ (r': round), st'.current_round i r' = (r' = r+1))
            ∧ if  ∃ (w: wave)
                  , 4 * w = r
              then
                ∀ (w: wave)
                , 4 * w = r
                → if ∃ (v: vertex) (s: vertexset)
                    , st'.getWaveVertexLeader i w v
                    ∧ vset.supermajority s
                    ∧ ∀ (vs: vertex)
                      , st'.in'DAG i vs
                      → vtx.roundOf vs = round'of'wave w 4
                      ∧ ( ∃ (p: path)
                          , path_.top p = v
                          ∧ path_.bottom p = vs
                          ∧ ( ∀ (v: vertex)
                              , path_.member v p
                              → v = path_.top p
                              ∨ ∃ (v': vertex)
                                , path_.member v' p
                                ∧ vset.member v (vtx.strong v')
                            )
                          -- ∧ strong_connected p
                          ∧ ( ∀ (vp: vertex)
                              , path_.member vp p
                              → st'.in'DAG i vp
                            )
                        )
                      -- ∧ exists_path_where
                      --     (fun _ vp => st'.in'DAG i vp)
                      --     vs v
                   then ( st'.decidedWave i = fun w' => w'=w )
                      ∧ ( ∀ (v: vertex)
                          , st'.deliveredVertex i v
                          ↔ ( st.deliveredVertex i v
                            ∨ ( ∀ (wl: vertex) (leaders: vertexset)
                                , st'.getWaveVertexLeader i w wl
                                ∧ vset.member wl leaders
                                ∧ ( ∀ (v': vertex)
                                    , vset.member v' leaders
                                    ↔ v' = wl
                                    ∨ ( ∃ (w': wave)
                                        , st'.getWaveVertexLeader i w' v'
                                        ∧ ∀ (wd: wave)
                                          , st.decidedWave i wd
                                          → w' > wd ∧ w' < w
                                      )
                                    ∧ ( ∀ (v'': vertex)
                                        , vset.member v'' leaders
                                        ∧ vtx.roundOf v'' > vtx.roundOf v'
                                        → ∃ (p: path)
                                          , path_.top p = v'
                                          ∧ path_.bottom p = v''
                                          ∧ ( ∀ (v: vertex)
                                              , path_.member v p
                                              → v = path_.top p
                                              ∨ ∃ (v': vertex)
                                                , path_.member v' p
                                                ∧ vset.member v (vtx.strong v')
                                            )
                                          -- ∧ strong_connected p
                                          ∧ ( ∀ (vp: vertex)
                                              , path_.member vp p
                                              → st'.in'DAG i vp
                                            )
                                        -- → exists_strong_path_where
                                        --     (fun _ v_ => st'.in'DAG i v_) v' v''
                                      )
                                  )
                                → ∃ (l: vertex)
                                  , vset.member l leaders
                                  ∧ ( ∃ (p: path)
                                      , path_.top p = l
                                      ∧ path_.bottom p = v
                                      ∧ ( ∀ (vp: vertex)
                                          , path_.member vp p
                                          → st'.in'DAG i vp
                                        )
                                    )
                                  -- ∧ exists_path_where
                                  --     (fun _ v_ => st'.in'DAG i v_) l v
                              )
                            -- ∨ (verticesToDeliver __sig) st st' i v w
                            )
                        )
                   else st'.a_deliver_at i = st.a_deliver_at i
                      ∧ st'.deliveredVertex i = st.deliveredVertex i
                      ∧ st'.decidedWave i = st.decidedWave i
              else
                ∀ (b: block) (r: round) (k: address) (w: wave)
                , st.a_deliver_at i b r k w
                ↔ st'.a_deliver_at i b r k w
         else st'.current_round i = st.current_round i
            ∧ st'.a_deliver_at i = st.a_deliver_at i
    )
  /-
    cannot deny called choose_leader,
    but can call at any time
  -/
  ∧ ( ∀ (i: address) (w: wave)
      , st.choose_leader i w → st'.choose_leader i w
    )
  /-
    glboal perfect coin will assign one leader once
    f + 1 nodes has chosen leader
  -/
  ∧ ( ∀ (w: wave)
      , ( ∃ (s: nodeset)
          , ( nset.greater_than_third s
            ∧ ∀ (a: address)
            , nset.member a s
            → st.choose_leader a w
            )
        )
      → ∃ (a: address)
        , st'.choose_leader_ret w a
    )
  /- and the result won't change -/
  ∧ ( ∀ (w: wave) (a: address)
      , st.choose_leader_ret w a
      → st'.choose_leader_ret w a
    )
  /- also the result is unique -/
  ∧ ( ∀ (w: wave) (a b: address)
      , st'.choose_leader_ret w a
      ∧ st'.choose_leader_ret w b
      → a == b
    )
  ∧ ( ∀ (w: wave)
      , ((∃ (j: address)
          , st.choose_leader_ret w j)
          ∧ ∀ (i j: address)
            , st.choose_leader_ret w j
            → ( ∀ (v: vertex)
                , vtx.source v = j
                ∧ vtx.roundOf v = round'of'wave w 1
                ∧ w > 1
                ∧ st.in'DAG i v
                → st'.getWaveVertexLeader i w v
              )
        )
      ∨ ((¬ (∃ (j: address), st.choose_leader_ret w j))
        ∧ ( ∀ (j: address)
            , (st.getWaveVertexLeader j w = st'.getWaveVertexLeader j w)
          )
        )
    )
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG

safety [a_deliver_reasonable]
  ∀ (i k: address) (b: block) (r: round) (w: wave)
  , a_deliver_at i b r k w
  → a_bcast k r = b

invariant [a_deliver_tot]
  ∀ (i j k k': address) (m m': block) (r r': round) (wi wi' wj wj': wave)
  , a_deliver_at i m r k wi
  ∧ a_deliver_at i m' r' k' wi'
  ∧ a_deliver_at j m r k wj
  ∧ a_deliver_at j m' r' k' wj'
  → ( (lete wi wi' $ lete r r' $ tot.le k k')
    ↔ (lete wj wj' $ lete r r' $ tot.le k k')
    )

safety [round_exists_ne_uniq]
  ∀ (i: address)
  , (¬ is_byz i)
  → ( ∃ (r: round)
      , current_round i r
    )
  ∧ ( ∀ (r r': round)
      , current_round i r
      ∧ current_round i r'
      → r = r'
    )

safety [one_msg_each_round]
  ∀ (i j: address) (v v': vertex)
  , (¬ is_byz i)
  ∧ in'DAG i v
  ∧ in'DAG i v'
  ∧ (Vertex.roundOf nodeset block vertexset is_byz v = Vertex.roundOf nodeset block vertexset is_byz v')
  ∧ (Vertex.source nodeset block vertexset is_byz v = j)
  ∧ (Vertex.source nodeset block vertexset is_byz v' = j)
  → v = v'

safety [no_time_machine]
  ∀ (i k: address) (m: block) (r: round) (w: wave)
  , (¬ is_byz i)
  ∧ (a_deliver_at i m r k w)
  → r ≤ 4 * w

safety [deliver_block_from_somewhere]
  ∀ (i k: address) (b: block) (r: round) (w: wave)
  , (¬ is_byz i)
  ∧ (a_deliver_at i b r k w)
  → ∃ (v: vertex)
    , in'DAG i v
    ∧ (vtx.block v = b)

#gen_spec

set_option veil.printCounterexamples true in
#check_invariants

end DAG
