import Veil
import Examples.Other.ReliableBroadcast

#print ReliableBroadcast.State

veil module DagRider'ReliableBroadcast

type nodeset
type address
type round
type block
type vertex

variable (is_byz : address → Prop)

instantiate nset : NodeSet address is_byz nodeset
open NodeSet

relation vertex_msg
  (creator : address)
  (dst : address)
  (r : round)
  (v : vertex)
  (b : block)

relation strong_edge
  (v : vertex)
  (u : vertex)

relation weak_edge
  (v : vertex)
  (u : vertex)

relation v_creator
  (v : vertex)
  (creator : address)

relation v_round
  (v : vertex)
  (r : round)

relation v_block
  (v : vertex)
  (b : block)

relation broadcasted
  (n : address)
  (r : round)
  (v : vertex)

relation delivered
  (n : address)
  (v : vertex)

relation inserted
  (n : address)
  (v : vertex)

relation ready_for_round
  (n : address)
  (r : round)

relation current_round
  (n : address)
  (r : round)

#gen_state

after_init {
  vertex_msg C D R V B := False;
  strong_edge V U := False;
  weak_edge V U := False;
  v_creator V C := False;
  v_round V R := False;
  v_block V B := False;
  broadcasted N R V := False;
  delivered N V := False;
  inserted N V := False;
  ready_for_round N R := False;
  current_round N R := False
}

internal transition byz = fun st st' =>
  (∀ (creator dst : address) (r : round) (v : vertex) (b : block),
      (¬ is_byz creator ∧ (st.vertex_msg creator dst r v b ↔ st'.vertex_msg creator dst r v b))
      ∨
      (is_byz creator ∧ (st.vertex_msg creator dst r v b → st'.vertex_msg creator dst r v b)))
  ∧
  (∀ (v u : vertex),
      (st.strong_edge v u → st'.strong_edge v u))
  ∧
  (∀ (v u : vertex),
      (st.weak_edge v u → st'.weak_edge v u))
  ∧
  (∀ (v : vertex) (creator : address),
      (st.v_creator v creator → st'.v_creator v creator))
  ∧
  (∀ (v : vertex) (r : round),
      (st.v_round v r → st'.v_round v r))
  ∧
  (∀ (v : vertex) (b : block),
      (st.v_block v b → st'.v_block v b))
  ∧
  (st.broadcasted = st'.broadcasted)
  ∧
  (st.delivered = st'.delivered)
  ∧
  (st.inserted = st'.inserted)
  ∧
  (st.ready_for_round = st'.ready_for_round)
  ∧
  (st.current_round = st'.current_round)

action init_round0 (n : address) (r : round) = {
  require ¬ is_byz n;
  require ¬ current_round n r;
  current_round n r := True
}

action broadcast_vertex
  (n : address)
  (r : round)
  (v : vertex)
  (b : block) = {
  require ¬ is_byz n;
  require current_round n r;
  require ¬ broadcasted n r v;
  require ∀ V, ¬ broadcasted n r V;
  v_creator v n := True;
  v_round v r := True;
  v_block v b := True;
  vertex_msg n DST r v b := True;
  broadcasted n r v := True
}

action add_strong_edge
  (n : address)
  (v u : vertex) = {
  require ¬ is_byz n;
  require inserted n u;
  require delivered n v;
  require strong_edge v u = False;
  strong_edge v u := True
}

action add_weak_edge
  (n : address)
  (v u : vertex) = {
  require ¬ is_byz n;
  require inserted n u;
  require delivered n v;
  require weak_edge v u = False;
  require ¬ strong_edge v u;
  weak_edge v u := True
}

action deliver_vertex
  (n creator : address)
  (r : round)
  (v : vertex)
  (b : block) = {
  require vertex_msg creator n r v b;
  delivered n v := True
}

action insert_vertex
  (n : address)
  (v : vertex) = {
  require delivered n v;
  require ∀ u, strong_edge v u → inserted n u;
  require ∀ u, weak_edge v u → inserted n u;
  inserted n v := True
}

action mark_ready
  (n : address)
  (r_next r_prev : round) = {
  require current_round n r_prev;
  require ∃ (q : nodeset), nset.supermajority q ∧
    ∀ (u_creator : address),
      nset.member u_creator q →
      ∃ (u : vertex), inserted n u ∧ v_creator u u_creator ∧ v_round u r_prev;
  ready_for_round n r_next := True
}

action advance_round
  (n : address)
  (r_prev r_next : round) = {
  require current_round n r_prev;
  require ready_for_round n r_next;
  require ¬ current_round n r_next;
  current_round n r_prev := False;
  current_round n r_next := True
}

end DagRider'ReliableBroadcast
