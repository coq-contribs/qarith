Require Export QArith_base.

Infix LEFTA 3 "*" Qmult : Q_scope.

Open Scope Q_scope.

Infix NONA 5 "<=" Qle : Q_scope.
Infix LEFTA 4 "==" Qeq : Q_scope.

Notation "x <= y <= z" := (Qle x y)/\(Qle y z)
  (at level 5, y at level 4):Q_scope. 

Infix LEFTA 4 "<" Qlt : Q_scope.

Infix LEFTA 4 "+" Qplus : Q_scope.

Infix LEFTA 4 "-" Qminus : Q_scope.

Distfix 3 " - _" Qopp :Q_scope.
