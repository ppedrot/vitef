open Fork

TACTIC EXTEND fork
  | ["fork" tactic(init) ">>" tactic(tac) ] -> [ fork_tac init tac ]
END;;
