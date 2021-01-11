term  : Type
form  : Type

App (s : symb) : "cod (fin (symb_arity s))" (term) -> term

Atm (a : atom) : "cod (fin (atom_arity a))" (term) -> form
Arr : form -> form -> form
Top : form
Bot : form
Cnj : form -> form -> form
Dsj : form -> form -> form
All : (term -> form) -> form
Exs : (term -> form) -> form
