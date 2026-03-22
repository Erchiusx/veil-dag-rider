import Veil

veil module DAG

type address
type nodeset
type block
type vertex
type vertexset
variable (is_byz: address → Prop)

instantiate nset: NodeSet address is_byz nodeset
abbrev round := Nat
relation current_round (a: address) (r: round)
-- reliable broadcast related
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

-- global perfect coin related

abbrev wave := Nat
def round'of'wave (w: wave) (k: round): round := 4*(w-1) + k
def wave'of (r: round): wave := r / 4
-- called choose_leaderᵢ(w) or not
relation choose_leader (i: address) (w: wave)

-- choose_leader returned or not
relation choose_leader_ret (w: wave) (a: address)

-- byzantine atomic broadcast related

-- called a_bcastᵢ(m, r) or not
relation a_bcast (i: address) (m: block) (r: round)


-- about DAG and vertex structure
class Vertex
  (vertex address block vertexset: Type)
where
  roundOf: vertex → round
  source: vertex → address
  block: vertex → block
  strong: vertex → vertexset
  weak: vertex → vertexset
instantiate vtx: Vertex vertex address block vertexset

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
instantiate vset: VertexSet vertex vertexset

type path
class Path
  (path vertex address block vertexset: Type)
  [vtx: Vertex vertex address block vertexset]
  [vset: VertexSet vertex vertexset]
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
instantiate path_: Path path vertex address block vertexset

relation buffer (a: address) (v: vertex)
relation in'DAG (a: address) (v: vertex)

namespace vset
def alignment (s: vertexset): Prop :=
  ∀ (a b: vertex)
  , vset.member a s
  ∧ vset.member b s
  → vtx.roundOf a = vtx.roundOf b
end vset

-- data structure for algorithm 3
relation decidedWave (i: address) (w: wave)
relation deliveredVertex (i: address) (v: vertex)
relation getWaveVertexLeader (i: address) (w: wave) (v: vertex)

relation a_deliver_at (i: address) (m: block) (r: round) (w: wave)

instantiate tot: TotalOrder address
set_option linter.dupNamespace false
#gen_state

syntax term:max "__sig": term
macro_rules
  | `($f __sig) =>
      `($f address nodeset block vertex vertexset is_byz path)

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
  a_bcast I B R               := False
  a_deliver_at I B R W        := False
  decidedWave I W             := False
  decidedWave I 0             := True
  deliveredVertex I V         := False
  getWaveVertexLeader I W V   := False
}

/-
  reliable broadcast related relations:
  - r_bcast
  - r_deliver
  - r_will_deliver_at
-/
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
  ∧ st.a_bcast = st'.a_bcast
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader

/-
  coin related relations:
  - choose_leader
  - choose_leader_ret
-/
internal transition global'perfect'coin = fun st st'
  /-
    cannot deny called choose_leader,
    but can call at any time
  -/
  => True
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
  /-
    TODO: find a way to represent unpredictability and fairness
  -/
  -- other states does not change
  ∧ st.current_round = st'.current_round
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.a_bcast = st'.a_bcast
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader

/-
  DAG maintainess related relations:
  - buffer
  - in'DAG
-/
internal transition DAG_maintain = fun st st'
  /-
    maintain the DAG structure
    it seems like that we need loop structures
    for the maintainess,
    so I'm trying to use internal transition to simulate that;

    Note: byz processes may maintain a not valid DAG structure
  -/
  => True
  ∧ ( ∀ (a: address) (v: vertex)
      , (¬ is_byz a)
      -- if a vertex becomes valid, add it into DAG
      → ( (st'.in'DAG a v ∧ ¬ st'.buffer a v)
        ↔ (st.in'DAG a v ∧ ¬ st.buffer a v)
        ∨ ( ∀ (r: round)
            , st.current_round a r
            ∧ st.buffer a v
            → ( ∀ (v': vertex)
                , vset.member v' (vtx.strong v)
                ∨ vset.member v' (vtx.weak v)
                → st.in'DAG a v'
              )
          )
        )
      -- whether the vertex has passed the 'receive' checks
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
  ∧ st.a_bcast = st'.a_bcast
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader

def strong_connected_
  : path → Prop := fun p =>
  ∀ (v: vertex)
  , path_.member v p
  → v = path_.top p
  ∨ ∃ (v': vertex)
    , path_.member v' p
    ∧ vset.member v (vtx.strong v')

local notation "strong_connected" =>
  strong_connected_ address block vertex vertexset path

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
  exists_path_where_ address block vertex vertexset path

local notation "exists_path" =>
  exists_path_where (fun _ _ => True)

local notation "exists_strong_path_where" =>
  exists_strong_path_where_ address block vertex vertexset path

local notation "exists_strong_path" =>
  exists_strong_path_where (fun _ _ => True)

internal transition get_wave_vertex_leader = fun st st' => True
  ∧ ( ∀ (w: wave) (j: address)
      , (st.choose_leader_ret w j
        ∧ ∀ (i: address)
          , ( ∃ (v: vertex)
              , vtx.source v = j
              ∧ vtx.roundOf v = round'of'wave w 1
              ∧ w > 1
              ∧ st.in'DAG i v
              ↔ st'.getWaveVertexLeader i w v
            )
        )
      ∨ ( (¬ st.choose_leader_ret w j)
        ∧ (st.getWaveVertexLeader = st'.getWaveVertexLeader)
        )
    )
  ∧ st.current_round = st'.current_round
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.choose_leader = st'.choose_leader
  ∧ st.a_bcast = st'.a_bcast
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex

internal transition a_bcast_ = fun st st'
  -- the a_bcast function is not called by this protocol,
  -- it is rather an external event stream
  -- this transition is to simulate this.
  => True
  ∧ ( ∀ (i: address) (b: block) (r: round)
      , st.a_bcast i b r → st'.a_bcast i b r
    )
  ∧ ( ∀ (i: address) (b c: block) (r: round)
      , st'.a_bcast i b r ∧ st'.a_bcast i c r
      → b = c
    )
  ∧ ( ∀ (i j: address) (b: block) (r1 r2: round)
      , st'.a_bcast i b r1
      ∧ st'.a_bcast j b r2
      → i = j
      ∧ r1 = r2
    )
  -- only affect a_bcast
  ∧ st.current_round = st'.current_round
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.choose_leader = st'.choose_leader
  ∧ st.choose_leader_ret = st'.choose_leader_ret
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
  ∧ st.decidedWave = st'.decidedWave
  ∧ st.deliveredVertex = st'.deliveredVertex
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader

def identity
  : State __sig
  → State __sig
  → Prop := fun st st' => True
  ∧ st.current_round = st'.current_round
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.choose_leader = st'.choose_leader
  ∧ st.choose_leader_ret = st'.choose_leader_ret
  ∧ st.a_bcast = st'.a_bcast
  ∧ st.a_deliver_at = st'.a_deliver_at
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
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
    require a_bcast a (vtx.block v) r
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

def wave_ready
  : State __sig
  → State __sig
  → wave
  → address
  → Prop := fun st st' w i => True
  ∧ ( ∀ (v: vertex)
      , st.getWaveVertexLeader i w v
        → if ∃ (s: vertexset)
          , vset.supermajority s
          ∧ ∀ (vs: vertex)
            , st.in'DAG i vs
            → vtx.roundOf vs = round'of'wave w 4
            ∧ exists_path_where
                (fun _ vp => st.in'DAG i vp)
                vs v
      then ( ∀ (leaders: vertexset)
          , ( vset.member v leaders
            ∧ ( ∀ (v': vertex)
                , vset.member v' leaders
                ↔ v' = v
                ∨ ( ∃ (w': wave)
                    , ( ∀ (wd: wave)
                        , st.decidedWave i w'
                        → w' > wd ∧ w' < w
                      )
                    ∧ st.getWaveVertexLeader i w' v
                  )
                ∧ ∀ (v'': vertex)
                  , vset.member v'' leaders
                  ∧ vtx.roundOf v'' > vtx.roundOf v
                  → exists_strong_path_where
                      (fun _ v_ => st.in'DAG i v_) v' v''
              )
            → ( ∀ (v l: vertex)
                , (¬ st.deliveredVertex i v)
                ∧ (st.in'DAG i v)
                ∧ (vset.member l leaders)
                ∧ exists_path l v
                → st'.a_deliver_at i (vtx.block v) (vtx.roundOf v) w
                ∧ st'.deliveredVertex i v
              )
          )
        )
        else  st'.a_deliver_at i = st.a_deliver_at i
            ∧ st'.deliveredVertex i = st.deliveredVertex i
    )

internal transition advance_round_ = fun st st' => True
  ∧ ( ∀ (i: address) (r: round)
      , st.current_round i r
      ∧ (¬ is_byz i)
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
                → st'.choose_leader i w = True
                -- → (wave_ready address nodeset block vertex vertexset is_byz path)
                --   st st' w i
                -- ∧ st'.decidedWave i w
                -- ∧ ∀ (w': wave)
                --   , w' ≠ w
                --   → ¬ st'.decidedWave i w'
              else
                ∀ (b: block) (r: round) (w: wave)
                , st.a_deliver_at i b r w
                ↔ st'.a_deliver_at i b r w
         else st'.current_round i = st.current_round i
            ∧ st'.a_deliver_at i = st.a_deliver_at i
    )
  ∧ st.r_bcast = st'.r_bcast
  ∧ st.r_deliver = st'.r_deliver
  ∧ st.r_will_deliver_at = st'.r_will_deliver_at
  ∧ st.choose_leader_ret = st'.choose_leader_ret
  ∧ st.a_bcast = st'.a_bcast
  ∧ st.buffer = st'.buffer
  ∧ st.in'DAG = st'.in'DAG
  ∧ st.getWaveVertexLeader = st'.getWaveVertexLeader



-- internal transition protocol = fun st st' => True
  -- ∧ (reliable'broadcast address nodeset block vertex vertexset is_byz path order) st st'
  -- ∧ (global'perfect'coin address nodeset block vertex vertexset is_byz path order) st st'
  -- ∧ (DAG_maintain address nodeset block vertex vertexset is_byz path order) st st'
  -- ∧ (get_wave_vertex_leader address nodeset block vertex vertexset is_byz path order) st st'
  -- ∧ (a_bcast_ address nodeset block vertex vertexset is_byz path order) st st'
  -- ∧ (advance_round_ address nodeset block vertex vertexset is_byz path order) st st'

-- safety [block_from_nowhere]
--   ∀ (v: vertex) (i: address)
--   , (in'DAG i v) ∧ (¬ is_byz i)
--   → a_bcast (vtx.source v) (vtx.block v) (vtx.roundOf v)

invariant [round_nonempty]
  ∀ (i: address)
  , (¬ is_byz i)
  → ∃ (r: round)
    , current_round i r

-- invariant [round_unique]
--   ∀ (i: address) (r1 r2: round)
--   , (¬ is_byz i) ∧ (current_round i r1) ∧ (current_round i r2)
--   → r1 = r2

-- invariant [will_choose_wave_leader]
--   ∀ (i: address) (r: round) (w: wave)
--   , (¬ is_byz i)
--   ∧ current_round i r
--   ∧ 4 * r > w
--   → choose_leader i w

def lete: Nat → Nat → Prop → Prop := fun u v p =>
  (u < v) ∨ (u = v ∧ p)

invariant [a_bcast_tot]
  ∀ (i j: address)
    (m m': block) (r r': round)
    (wi wi' wj wj': wave)
  , ( (¬ is_byz i) ∧ (¬ is_byz j)
  ∧ (a_deliver_at i m r wi)
  ∧ (a_deliver_at i m' r' wi')
  ∧ (a_deliver_at j m r wj)
  ∧ (a_deliver_at j m' r' wj') )
  ∧ ( ∃ (k k': address)
      , a_bcast k m r
      ∧ a_bcast k' m' r'
    )
  → ( ∀ (k k': address)
      , a_bcast k m r
      ∧ a_bcast k' m' r'
      → ( (lete wi wi' $ lete r r' $ tot.le k k')
        ↔ (lete wj wj' $ lete r r' $ tot.le k k')
        )
    )

-- invariant [block_consistency]
--   ∀ (v: vertex) (u: vertex) (i: address) (j: address)
--   , ( (¬ is_byz i) ∧ (¬ is_byz j)
--     ∧ (in'DAG i v) ∧ (in'DAG j u)
--     ∧ (vtx.source u = vtx.source v)
--     ∧ (vtx.roundOf u = vtx.roundOf v)
--     ∧ (¬ is_byz (vtx.source u))
--     )
--   → vtx.block u = vtx.block v



#gen_spec

-- theorem advance_round_a_bcast_total_order :
--   ∀ (st : @State address nodeset block vertex vertexset is_byz path order),
--       (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--               block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--               nset vtx vset path path_dec path_ne path_ order order_dec order_ne toto
--               tota).assumptions
--           st →
--         (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--                 block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--                 nset vtx vset path path_dec path_ne path_ order order_dec order_ne toto tota).inv
--             st →
--           (@DAG.advance_round_.ext address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ order order_dec
--               order_ne toto tota)
--               st fun _ st' =>


-- set_option veil.printCounterexamples true

-- @[invProof]
-- theorem advance_round__block_from_nowhere :
--     ∀ (st : @State address nodeset block vertex vertexset is_byz path order),
--       (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--               block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--               nset vtx vset path path_dec path_ne path_ order order_dec order_ne toto
--               tota).assumptions
--           st →
--         (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--                 block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--                 nset vtx vset path path_dec path_ne path_ order order_dec order_ne toto tota).inv
--             st →
--           (@DAG.advance_round_.ext address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ order order_dec
--               order_ne toto tota)
--             st fun _ (st' : @State address nodeset block vertex vertexset is_byz path order) =>
--             @DAG.block_from_nowhere address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ order order_dec
--               order_ne toto tota st' :=
--   by {
--     intros st has invs st' tr
--     simp
--     intros _ _ _ _ a_bcast_inv _ _ h_inv _ v i
--     rcases invs with ⟨_, ⟨_, ⟨_, st_inv⟩⟩ ⟩
--     have tran := st_inv v i
--     have h_inv' := h_inv i v
--     have a_bcast_inv' := a_bcast_inv (vtx.source v) (vtx.block v) (vtx.roundOf v)
--     simp [← h_inv']
--     intro h1 h2
--     have tran' := tran (And.intro h1 h2)
--     simp [a_bcast_inv'] at tran'
--     exact tran'
--   }



-- @[invProof]
-- theorem advance_round__round_nonempty :
--     ∀ (st : @State address nodeset block vertex vertexset is_byz path order),
--       (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--               block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--               nset vtx vset path path_dec path_ne path_ order order_dec order_ne toto
--               tota).assumptions
--           st →
--         (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--                 block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--                 nset vtx vset path path_dec path_ne path_ order order_dec order_ne toto tota).inv
--             st →
--           (@DAG.advance_round_.ext address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ order order_dec
--               order_ne toto tota)
--             st fun _ (st' : @State address nodeset block vertex vertexset is_byz path order) =>
--             @DAG.round_nonempty address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ order order_dec
--               order_ne toto tota st' :=
--   by {
--     intros _ _ invs _ tr
--     simp
--     intros _ _ _ _ _ _ _ _ _ i h
--     rcases invs with ⟨_, ⟨_, ⟨st_round_nonempty, _⟩ ⟩ ⟩
--     have prev := st_round_nonempty i h
--     cases prev with
--     | intro r hi =>
--       have focus := tr i r hi h
--       split at focus
--       . rcases focus with ⟨focus, _⟩
--         have focus := focus (r+1)
--         use (r+1)
--         simp at focus
--         exact focus
--       . use r
--         have focus := focus r
--         simp [focus]
--         exact hi
--   }

#check_invariants

-- @[invProof]
-- theorem advance_round__round_nonempty :
--     ∀ (st : @State address nodeset block vertex vertexset is_byz path),
--       (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--               block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--               nset vtx vset path path_dec path_ne path_ tot).assumptions
--           st →
--         (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--                 block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--                 nset vtx vset path path_dec path_ne path_ tot).inv
--             st →
--           (@DAG.advance_round_.ext address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_)
--             st fun _ (st' : @State address nodeset block vertex vertexset is_byz path) =>
--             @DAG.round_nonempty address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ tot st' :=
--   by {
--     intros _ _ invs _ tr
--     simp
--     intros _ _ _ _ _ _ _ _ i h
--     rcases invs with ⟨_, st_round_nonempty⟩
--     have prev := st_round_nonempty i h
--     cases prev with
--     | intro r hi =>
--       have focus := tr i r hi h
--       split at focus
--       . rcases focus with ⟨focus, _⟩
--         have focus := focus (r+1)
--         use (r+1)
--         simp at focus
--         exact focus
--       . use r
--         rcases focus with ⟨lfocus, _⟩
--         have focus := lfocus r
--         simp [focus]
--         exact hi
--   }

-- @[invProof]
--   theorem advance_round__a_bcast_tot :
--     ∀ (st : @State address nodeset block vertex vertexset is_byz path),
--       (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--               block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--               nset vtx vset path path_dec path_ne path_ tot).assumptions
--           st →
--         (@System address address_dec address_ne nodeset nodeset_dec nodeset_ne block block_dec
--                 block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec vertexset_ne is_byz
--                 nset vtx vset path path_dec path_ne path_ tot).inv
--             st →
--           (@DAG.advance_round_.ext address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_)
--             st fun _ (st' : @State address nodeset block vertex vertexset is_byz path) =>
--             @DAG.a_bcast_tot address address_dec address_ne nodeset nodeset_dec nodeset_ne
--               block block_dec block_ne vertex vertex_dec vertex_ne vertexset vertexset_dec
--               vertexset_ne is_byz nset vtx vset path path_dec path_ne path_ tot st' :=
--     by {
--       intros
--         st has inv st' tr
--         _ _ _ _ _ _ _ _
--         i j m m' r r' oi oi' oj oj'
--         asum
--       rcases asum with ⟨⟨ib, jb, di, di', dj, dj'⟩, ex⟩
--       rcases inv with ⟨tot_st, ner_st⟩
--       have ⟨icr, ner_ci⟩ := ner_st i ib
--       have ⟨jcr, ner_cj⟩ := ner_st j jb
--       have atri := tr i icr ner_ci ib
--       have atrj := tr j jcr ner_cj jb
--       split at atri
--       . split at atrj
--         rcases atri with ⟨icr', tran'i⟩
--         rcases atrj with ⟨jcr', tran'j⟩
--         split at tran'i
--         . sorry
--         . split at tran'j
--           . case isTrue hjw =>
--               rcases hjw with ⟨wj, jw⟩
--               have tran'j' := tran'j wj jw
--               rcases tran'j' with ⟨α, _, _⟩
--               rcases α with ⟨_, mutj⟩
--               have he : ∃ (v: vertex), st.getWaveVertexLeader j wj v := by {
--                 clear mutj
--               }
--           -- . have h' := tot_st i j m m' r r' oi oi' oj oj'
--           --   apply h'
--           --   repeat' constructor
--           --   . exact ib
--           --   . exact jb
--           --   . simp [tran'i m r oi]
--           --     exact di
--           --   . simp [tran'i m' r' oi']
--           --     exact di'
--           --   . simp [tran'j m r oj]
--           --     exact dj
--           --   . simp [tran'j m' r' oj']
--           --     exact dj'
--     }



end DAG
