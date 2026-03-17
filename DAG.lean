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

-- called choose_leaderᵢ(w) or not
relation choose_leader (i: address) (w: wave)

-- choose_leader returned or not
relation choose_leader_ret (w: wave) (a: address)

-- byzantine atomic broadcast related

-- called a_bcastᵢ(m, r) or not
relation a_bcast (i: address) (m: block) (r: round)

-- called a_deliverᵢ(m, r, k) or not
relation a_deliver (i: address) (m: block) (r: round)

-- about DAG and vertex structure
type vertex
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
instantiate vset : VertexSet vertex vertexset

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

variable (client'msg: round → address → block)

-- data structure for algorithm 3
relation decidedWave (i: address) (w: wave)
relation deliveredVertex (i: address) (v: vertex)


#gen_state

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
  a_deliver I B R             := False
  decidedWave I W             := False
  decidedWave I 0             := True
}

/-
  reliable broadcast related relations:
  - r_bcast
  - r_deliver
  - r_will_deliver_at
-/
internal transition reliable'broadcast = fun st st'
  => True
  -- Agreement
  ∧ ( ∀ (i j k: address) (m: vertex) (r: round)
      , (¬ is_byz i)
      ∧ (¬ is_byz j)
      ∧ ( st.r_deliver i m r k
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
  -- others don't change
  ∧ ( ∀ (a: address) (r: round)
      , st.current_round a r ↔ st'.current_round a r
    )
  ∧ ( ∀ (a: address) (w: wave)
      , (st.choose_leader a w ↔ st'.choose_leader a w)
      ∧ (st.choose_leader_ret w a ↔ st'.choose_leader_ret w a)
    )
  ∧ ( ∀ (a: address) (v: vertex)
      , (st.buffer a v ↔ st'.buffer a v)
      ∧ (st.in'DAG a v ↔ st'.in'DAG a v)
    )
  ∧ ( ∀ (i: address) (b: block) (r: round)
      , (st.a_bcast i b r ↔ st'.a_bcast i b r)
      ∧ (st.a_deliver i b r ↔ st'.a_deliver i b r)
    )

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
      , ( (¬ is_byz i)
        ∧ (st.choose_leader i w ↔ st'.choose_leader i w)
        )
      ∨ ( (is_byz i)
        ∧ (st.choose_leader i w → st'.choose_leader i w)
        )
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
  -- others don't change
  ∧ ( ∀ (a: address) (r: round)
      , st.current_round a r ↔ st'.current_round a r
    )
  ∧ ( ∀ (i k: address) (m: vertex) (r t: round)
      , (st.r_bcast i m r ↔ st'.r_bcast i m r)
      ∧ (st.r_deliver i m r k ↔ st'.r_deliver i m r k)
      ∧ ( st.r_will_deliver_at i m r k t
        ↔ st'.r_will_deliver_at i m r k t
        )
    )
  ∧ ( ∀ (a: address) (v: vertex)
      , (st.buffer a v ↔ st'.buffer a v)
      ∧ (st.in'DAG a v ↔ st'.in'DAG a v)
    )
  ∧ ( ∀ (i: address) (b: block) (r: round)
      , (st.a_bcast i b r ↔ st'.a_bcast i b r)
      ∧ (st.a_deliver i b r ↔ st'.a_deliver i b r)
    )

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
  -- others don't change
  ∧ ( ∀ (a: address) (r: round)
    , st.current_round a r ↔ st'.current_round a r
  )
  ∧ ( ∀ (i k: address) (m: vertex) (r t: round)
      , (st.r_bcast i m r ↔ st'.r_bcast i m r)
      ∧ (st.r_deliver i m r k ↔ st'.r_deliver i m r k)
      ∧ ( st.r_will_deliver_at i m r k t
        ↔ st'.r_will_deliver_at i m r k t
        )
    )
  ∧ ( ∀ (a: address) (w: wave)
      , (st.choose_leader a w ↔ st'.choose_leader a w)
      ∧ (st.choose_leader_ret w a ↔ st'.choose_leader_ret w a)
    )
  ∧ ( ∀ (i: address) (b: block) (r: round)
      , (st.a_bcast i b r ↔ st'.a_bcast i b r)
      ∧ (st.a_deliver i b r ↔ st'.a_deliver i b r)
    )

action send
  (a: address)
  (v: vertex)
  (r: round) = {
    require current_round a r
    require vtx.source v = a
    require vtx.roundOf v = r
    require vtx.block v = client'msg r a
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

action receive
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

#check_invariants

end DAG
