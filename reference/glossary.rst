.. highlight:: tla


Glossary
########

.. _action:

Action
======

A relation between the values of a variable at the current state and the values of a variable in the next state. One `label <labels>` corresponds to one action. If TLC can execute a label, the corresponding action is said to be *enabled*.


.. _arbitrary:

Arbitrary
=========

A place where TLC can choose one of several possibilities, but needs to be **deterministic**. TLC will **not** create multiple behaviors. Currently the two situatons where TLC may make an arbitrary choice is with `CASE` and `CHOOSE`.

.. _behavior:

Behavior
========

A sequence of states making up one possible timeline of the system.

.. _concurrency:

Concurrency
===========

Where multiple parts of the system can execute without a fixed order. Some parts can start executing before others finish. Very, very dangerous.

.. _deadlock:

Deadlock
========

A situation where the spec isn't able to do anything: it can only take `stutter`-steps. For most specs, this is considered an error, and TLC will consider it an error by default.


.. _fairness:

Fairness
========

An `action` is weakly fair when, if it always can happen, it is guaranteed to happen. This means the spec cannot stutter.

An action is strongly fair when, if never permanently disabled, it is guaranteed to happen. This means the spec cannot livelock.

.. _invariant:

Invariant
=========

Some `operator <operator>` that must hold true at every state of every behavior.

.. _liveness:

Liveness
========

The requirement that a system is guaranteed to always reach a desired state, such as consensus or termination. Encoded as a `temporal property <temporal_property>`.

.. _model:

Model
=====

A configuration of what properties we're checking a spec for, what we are assigned for constants, and what other restrictions or runtime optimizations we are making. The model checker for TLA+ is `TLC`.

.. _nondeterminism:

Nondeterminism
==============

There are several possible things that could validly happen. In PlusCal, the points of nondeterminism are `processes <process>`, `with`, and `either`. Multiple possible starting states also count here. When `TLC` has to make a nondeterministic choice, it creates a separate `behavior` for each choice and evaluates them all. Eg given the code

::

  with x \in {1, 2, 3} do
    y := x;
  end with;

TLC will examine three different behaviors: one where it assigns 1 to y, one where it assigns 2, and one where it assigns 3.

Nondeterminism can lead to `state-space Explosion <state_space_explosion>`.

.. _term_pluscal:

PlusCal
=======

A pseudocode-like "algorithm language" that compiles to TLA+. Handles things like assignments, loops, control flow, processes. If it's an all-lowercase term inside of an ``algorithm`` block, it's PlusCal, otherwise it's TLA+.

::

  \* incrementing the second element of a sequence
  \* TLA+

  seq' = [seq EXCEPT ![2] = @ + 1]

  \* PlusCal

  seq[2] := seq[2] + 1;


.. _safety:

Safety
======

The property that a system does not reach valid states. Can be encoded as either an `invariant` or a `temporal_property`.

.. _specification:

Specification
=============

A formal description of how a system should behave, along with the `invariants <invariant>` it should satisfy. Checked with a `model checker <model>`.

.. _state_space_explosion:

State-Space Explosion
=====================

A situation where a spec has many `nondeterministic <nondeterminism>` choices that TLC must check. As the `model` gets broader the number of states exponentially increases. This is a necessary evil and a common challenge of specifying.

.. _stutter:

Stutter
=======

A step which leaves all variables unchanged. Equivalent to "nothing happening". Stuttering is always implicitly valid.

If the only possible actions are stutter-steps, _and_ the spec does not say otherwise, the spec `deadlocks <deadlock>`.

.. _temporal_property:

Temporal Property
=================

An `operator <operator>` to hold over a sequence of states, or an entire `behavior`. Uses expressions in `Temporal Logic <temporal_logic>`.

.. _TLC:

TLC
===

The *model checker* for TLA+. When given a spec and an `invariant`, TLC will stake every possible starting state and examine every possible `behavior` of each state.

.. _unquantifiable:

Unquantifiable
==============

Infinite sets are considered _unquantifiable_. You may test membership with ``\in`` or ``\subseteq``, but you may not use `\\E`, `\\A`, or `CHOOSE` operators.
