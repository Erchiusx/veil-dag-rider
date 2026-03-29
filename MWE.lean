import Veil

veil module test

type address
relation current_round: address → Nat → Bool

#gen_state

transition test_dependent_if {
  if (∃ (n: Nat), n > 0)
  then (∀ (i: address) (n: Nat), n > 0 → current_round' i = (· = n))
  else current_round' = current_round
}

transition test_cononical {
  ((∃ (n: Nat), n > 0) ∧ (∀ (i: address) (n: Nat), n > 0 → current_round' i = (· = n)))
  ∨ ((∃ (n: Nat), n > 0) ∧ (current_round' = current_round))
}

transition test_ite {
  ite
    (∃ (n: Nat), n > 0)
    (∀ (i: address) (n: Nat), n > 0 → current_round' i = (· = n))
    ((∃ (n: Nat), n > 0) ∧ (current_round' = current_round))
}

end test
