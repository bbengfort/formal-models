------------------------------- MODULE Reduce -------------------------------

EXTENDS Integers

Add(x,y) == x+y

(* You don't need to know how this works (janky) *)
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] == \* here's where the magic is
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 16:54:13 EDT 2018 by benjamin
\* Created Tue Aug 14 16:34:54 EDT 2018 by benjamin
