.. highlight:: tla

Expressions
###########

.. _operator:

\=\=
====

::

  Op(x, y, ...) == expr

Defines ``Op`` as an operator, roughly equivalent to a programming function.

.. _HOO:

Higher-Order Operators
----------------------

::

  Op(param(_, _, ...), x) == expr

Declares that the ``param`` parameter is itself an operator with *n* parameters.

.. _LAMBDA:

LAMBDA
------

::

  LAMBDA x: ...

Defines an anonymous operator.

.. _IF:

IF
==

::

  IF condition THEN expr1 ELSE expr2

If statement. Unlike programming languages (and the `pluscal if <if_pluscal>`), ``else`` must always be defined.


.. _CASE:

CASE
====

::

  CASE cond1 -> expr1
    [] cond2 -> expr2
    \* ...
    [] OTHER -> expr_default

Selects an expression from an `arbitrary` true condition. If none match, then ``OTHER`` is used as the default. If none match and there is no ``OTHER``, raises an error.

.. _LET:

LET
===

::

  LET op1 == expr1
      op2 == expr2
  IN expr

Defines ``op1``, ``op2``, etc as scoped operators in ``expr``.

.. _EXTENDS:

EXTENDS
=======

::

  EXTENDS TLC, Integers, FiniteSets

Includes operators defined in these modules as part of your spec.

.. _INSTANCE:
.. _LOCAL:

INSTANCE
========

::
  
  INSTANCE Module

Includes all operators defined in ``Module`` *except* any operators declared ``LOCAL``.

You can use ``LOCAL INSTANCE`` to make all of the imported operators local, too.

.. _!:

Namedspaced Instances
=====================

::

  M == INSTANCE Module

Includes all operators under the ``M`` namespace. If ``op`` is an operator in ``Module``, ``op`` is imported as ``M!op``.

.. _CONSTANT:

CONSTANT
========

::

  CONSTANT C1, C2, Op(_, _)

Defines ``C1``, etc as values that will be defined by the `model`, not the spec. Constants can either be assigned to ordinary values, `model values <model_value>`, or sets of model values. Constant operators may only be assigned to ordinary operators (not model values).

.. _ASSUME:

ASSUME
------

::

  CONSTANT C1
  ASSUME expr(C1)

Forces an expression involving constants to be true. If false, prevents the model from running. Can be used to constraint the valid parameters for a model.

Logical Operations
##################

.. _=>:

=>
==

::

  P => Q

True if ``P`` is true ONLY if ``Q`` is true. Still true if ``P`` is false and ``Q`` is true. Equivalent to ``~P \/ Q``.

.. _<=>:

<=>
===

::

  P <=> Q

True if ``P`` and ``Q`` are both true or both false. Equivalent to ``(P /\ Q) \/ (~P /\ ~Q)``.

.. _\\A:

\\A
===
::

  \A x \in Set:
    F(x)

True if ``F`` is true for *every single element* in ``Set``.

.. _\\E:

\\E
===

::

  \E x \in Set:
    F(x)

True if ``F`` is true for *at least one element* in ``Set``.

.. _CHOOSE:

CHOOSE
======

::

  CHOOSE x \in Set:
    F(x)

Returns an `arbitrary` element in ``Set`` which satisfies ``F``. If no such element exists, raises an error.

.. _temporal_logic:


Temporal Logic
##############

.. _[]:

[]
==

Always. ``[]P`` is true if ``P`` is true for every state. Equivalent to declaring P an `invariant`.


.. _<>:

<>
==

Eventually. ``<>P`` is true if ``P`` is true for at least one state in every `behavior`.

.. _~>:

~>
==

Leads-to. ``P ~> Q`` is true if, for every state where ``P`` is true, there is a present or future state where ``Q`` is true.
