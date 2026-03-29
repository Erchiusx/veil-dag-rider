import Veil
set_option linter.dupNamespace false

veil module DAG

type address
instantiate _address: LE address
instantiate decLE : DecidableRel _address.le

type block
abbrev round := Nat

@[veil_decl] structure vertex (address block: Type) where
  block: block
  source: address
  round: round
  strong: List (vertex address block)


#gen_state

#gen_spec
set_option veil.printCounterexamples true in
#check_invariants

end DAG
