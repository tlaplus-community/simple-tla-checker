---- MODULE Test ----
VARIABLES x, y
Init ==
  ∧ x = "foobar"
  ∧ y = FALSE
Next ==
  ∨ x' = ~x
=====================
