.. highlight:: tla

Types
#####

.. _=:
.. _/=:
.. _#:
.. _comparison:

All types use ``=`` for equality and ``/=`` (or ``#``) for inequality. Two values are equal if they have the same value, otherwise they are unequal. If the two values are different types, such as integers and strings, comparison raises an error.

The one exception to this are `model values <model_value>`. A model value is comparable to anything and is unequal to everything but itself.

Simple Types
============

.. _boolean:

Boolean
-------

``TRUE`` or ``FALSE``. ``BOOLEAN`` is the set ``{TRUE, FALSE}``. The following operations are defined over booleans:


+--------+---------------------+
| ``/\`` | and ("conjunction") |
+--------+---------------------+
| ``\/`` | or ("disjunction")  |
+--------+---------------------+
| ``~``  | not                 |
+--------+---------------------+

.. _integer:

Integer
-------

0, 1, -123, etc. If we `EXTENDS` ``Integers``, we get the following operations:


+---------------+----------------------+
| ``+ - *``     | plus/minus/times     |
+---------------+----------------------+
| ``%``         | remainder            |
+---------------+----------------------+
| ``\div``      | integer division     |
+---------------+----------------------+
| ``< > <= >=`` | comparison ops       |
+---------------+----------------------+
| ``a..b``      | ``{a, a+1, ..., b}`` |
+---------------+----------------------+


Extending integers also gives us the sets ``Int``, which is the set of all integers, and ``Nat``, which is the set ``{0, 1, 2, ...}``. Both of these are infinite sets and so are ``unquantifiable``.

.. _string:

String
------

"a", "b", "hello", etc. Strings **must** use double quotes, not single quotes. ``STRING`` is the set of all strings. It is an infinite set and so ``unquantifiable``.

There are no operators over strings.

.. _model_value:


Model Value
-----------

A value that's only equal to itself. Can only be made via an assignment to a `CONSTANT`.

Complex Types
=============

.. _set:

Set
===

A collection of unique, unordered elements. Written ``{a, b, ...}``. All values must be `comparable <comparison>`.

Sets support for following operators:


+--------------------+-------------------+
| ``x \in S``        | is an element     |
+--------------------+-------------------+
| ``x \notin S``     | not an element    |
+--------------------+-------------------+
| ``S \subseteq T``  | subset            |
+--------------------+-------------------+
| ``S \union T``     | set merge         |
+--------------------+-------------------+
| ``S \intersect T`` | set intersection  |
+--------------------+-------------------+
| ``S \ T``          | set difference    |
+--------------------+-------------------+
| ``SUBSET S``       | set of subsets    |
+--------------------+-------------------+
| ``UNION S``        | merge set of sets |
+--------------------+-------------------+

.. _map:
.. _filter:

There are two set transformations:


+---------------------+------------+
| ``{x \in S: P(x)}`` | set filter |
+---------------------+------------+
| ``{P(x): x \in S}`` | set map    |
+---------------------+------------+

.. _module_finitesets:

If we `extend <EXTENDS>` ``FiniteSets``, we get the following operators:

+--------------------+-------------------------+
| ``IsFiniteSet(S)`` | what is says            |
+--------------------+-------------------------+
| ``Cardinality(S)`` | number of elements in S |
+--------------------+-------------------------+

.. _sequence:
.. _tuple:

Sequence
========

Also called a **Tuple**. An ordered collection of elements. Written ``<<a, b, ... >>``. The first element is ``seq[1]``, the second at ``seq[2]``, etc. Sequences are 1-indexed.  Sequences are 1-indexed. Sequences are 1-indexed.

``DOMAIN Sequence`` is the set ``1..Len(Sequence)``.

.. _\X:

``Set1 \X Set2 \X ...`` is the set of all tuples where the first element is in ``Set1``, the second element is in ``Set2``, etc. ``Set1 \X (Set2 \X Set3)`` is a 2-tuple where the first element is in ``Set1`` and the second element is a *tuple* in ``Set2 \X Set3``.

.. _module_sequences:

If we extend ``Sequences``, we get the following operators:


+----------------------+------------------------------------------+
| ``Len(S)``           | Length of sequence                       |
+----------------------+------------------------------------------+
| ``Seq(Set)``         | Set of all sequences of elements in set. |
|                      | `Unquantifiable`.                        |
+----------------------+------------------------------------------+
| ``Head(S)``          | First element of sequence.               |
+----------------------+------------------------------------------+
| ``Tail(s)``          | All elements of sequence but first.      |
+----------------------+------------------------------------------+
| ``Append(S, e)``     | The sequence ``S \o <<e>>``.             |
+----------------------+------------------------------------------+
| ``S1 \o S2``         | Concatenate two sequences                |
+----------------------+------------------------------------------+

.. _struct:

Structure
=========

A mapping from strings to values. Written ``[key1 |-> val1, key2 |-> val2]``. Elements are accessed either by ``struct["key"]`` or ``struct.key``.

``DOMAIN struct`` is the set of string keys.

``[key1: set1, key2: set2]`` is the set of all structures where the value of the first key is in ``set1``, etc.

.. _function:

Function
========

A mapping from elements of a set to values. Written ``[e1 \in Set1, e2 \in Set2, ... |-> F(e1, e2, ...)]``. Values are accessed with ``f[a, b, c...]``. The sets may be unquantifiable.

.. _DOMAIN:

``DOMAIN func`` is the set ``func`` is defined over. If ``func`` is a multivalued function, then the domain will be a set of ``tuples <tuple>``: ``Set1 \X Set2 \X ...``.

``[Set1 -> Set2]`` is the set of all functions where the domain is ``Set1`` that map to values in ``Set2``.
