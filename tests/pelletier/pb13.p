% #expect: unsat

fof(goal, conjecture, (p | (q & r)) <=>
  ((p | q) & (p | r))).