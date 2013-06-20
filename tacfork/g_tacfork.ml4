open Fork

TACTIC EXTEND fork
  | ["fork" tactic(tac) ] -> [ fork_tac tac ]
END;;
