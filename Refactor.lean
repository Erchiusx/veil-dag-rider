import Veil
-- set_option trace.Meta.synthInstance true


veil module DAG_TSet

type node
type block
@[veil_decl]
structure vertex (node block: Type) where
  source: node
  payload: block

type vtxs
type edges
instantiate vset: TSet (vertex node block) vtxs
instantiate eset: TSet (vertex node block × vertex node block) edges

@[veil_decl]
structure Graph (vtxs edges: Type) where
  nodes: vtxs
  strong: edges
  weak: edges
function view: node → Graph vtxs edges
#gen_state

after_init {
  view N := Graph.mk vset.empty eset.empty eset.empty
}

action empty {
  return ()
}

safety [DAG_structure]
  ∀ (n: node) (e: vertex node block × vertex node block)
  , let g := view n
  ( vset.contains e.1 g.nodes
  ∧ ( eset.contains e g.strong
    ∨ eset.contains e g.weak
    )
  → vset.contains e.2 g.nodes
  )

#gen_spec

-- #model_check {
--   node := Fin (3 * 1 + 1)
--   nodeset := ByzNSet (3 * 1 + 1)
-- } {}
#check_invariants

end DAG_TSet

veil module DAG_List
type node
type block
@[veil_decl]
structure vertex (node block: Type) where
  source: node
  payload: block

@[veil_decl]
structure Graph (node block: Type) where
  nodes: List $ vertex node block
  strong: List $ vertex node block × vertex node block
  weak: List $ vertex node block × vertex node block
function view: node → Graph node block

#gen_state

after_init {
  view N := Graph.mk [] [] []
}
action empty {
  return ()
}

safety [DAG_structure]
  ∀ (n: node) (e: vertex node block × vertex node block)
  , let g := view n
  ( g.nodes.contains e.1
  ∧ ( g.strong.contains e
    ∨ g.weak.contains e
    )
  → g.nodes.contains e.2
  )

#gen_spec

#check_invariants

end DAG_List

veil module DAG_structure_simulated_pair
type node
type block
@[veil_decl]
structure vertex (node block: Type) where
  source: node
  payload: block

@[veil_decl]
structure edge (node block: Type) where
  origin: vertex node block
  target: vertex node block

@[veil_decl]
structure Graph (node block: Type) where
  nodes: List $ vertex node block
  strong: List $ edge node block
  weak: List $ edge node block
function view: node → Graph node block

#gen_state

after_init {
  view N := Graph.mk [] [] []
}

action empty {
  return ()
}

safety [DAG_structure]
  ∀ (n: node) (e: edge node block)
  , let g := view n
  ( g.nodes.contains e.origin
  ∧ ( g.strong.contains e
    ∨ g.weak.contains e
    )
  → g.nodes.contains e.target
  )

#gen_spec

#check_invariants

end DAG_structure_simulated_pair
