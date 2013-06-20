open Fork

TACTIC EXTEND fork
  | ["fork" tactic(init) ">>" tactic(tac) ] -> [ fork_tac init (One tac) ]
  | ["fork" tactic(init) ">>" "[" tactic_list_sep(tacs, "|") "]" ] -> [ fork_tac init (Many tacs) ]
END;;
