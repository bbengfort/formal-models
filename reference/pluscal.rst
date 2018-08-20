.. highlight:: tla

PlusCal
#######

.. _pluscal_variables:

variables
=========

::
  
  variables
    var1 = val;
    var2 \in set;

Creates global variables. ``var1`` will be assigned to ``val``. ``var2`` will be a `nondeterministic <nondeterminism>` element of ``set``. This may lead to multiple possible initial states.

.. _||:
.. _:=:

assignment
==========

::

  var := val;

Assigns ``val`` to ``var``. ``var`` may be assigned to once per ``label <labels>``.

::

  var1 := val1 || var2 := val2;

Simultaneously performs several assignments. This can be used to assign to multiple fields in the same structure.

::

  struct.field1 := val1 ||
  struct.field2 := val2 ||
  \* ...


assert
======

.. _assert_pluscal:

::

  assert bexp;

If ``bexp`` is true, does nothing. If ``bexp`` is false, then is treated as a spec failure. Can be used to test invariants that are only required to be true at specific points of execution.

Requires `EXTENDS` ``TLC``.

.. _await:

await
=====

::

  Label1:
    await bexp;
    \* body

Blocks execution of ``Label1`` until ``bexp`` is true. If all `processes <process>` are blocked by awaits (or `with`), the spec `deadlocks <deadlock>`. Also aliased to ``when``; there is no difference between the two.

If placed at the end of a label, ``await`` blocks execution until ``bexp`` is true *after execution of the label*. eg the following can never be executed:

::

  Label:
    x := 1;
    await x /= 1;

As execution of the label would make the ``await`` expression false.


.. _define:

define
======

::

  define
    op1 == expr1
    op2 == expr2
  end define;

Defines new TLA+ `operators <operator>`. Unlike operators defined before the PlusCal block, these operators may refer to global variables.

A ``define`` block must go above any macros, procedures, and processes.

.. _if_pluscal:

if
==

::

    if bexp1 then
      body1
    elsif bexp2 then
      body2
    elseif bexp3 then
      \* ...
    else
      body_else
    end if;

Behaves exactly like an if in any other language. The body may contain :ref:`labels <labels>`. If so, ``end if`` must be followed by a label. 

.. _skip:

skip
====

::

  skip;

A noop. Can be used to fill out parts of an incomplete spec.

.. _while:

while
=====

::

 while bexp do
  body;
 end while;

behaves like a while in any other language. A ``while`` statement must be immediately preceded by a `label <labels>`.

.. _either:

either
======

::

  either
    body1
  or
    body2
  or
    \* ...
  end either;

`Nondeterministically <nondeterminism>` executes one body. The body may contain :ref:`labels <labels>`. If so, ``end either`` must be followed by a label. 

.. _with:

with
====

You can use ``with`` deterministically or :ref:`nondeterministically <nondeterminism>`. In both cases, the body must follow `macro rules <macro_body>`.

Deterministic
~~~~~~~~~~~~~

::

  with var1 = val1, 
       var2 = val2,
       \* ...
  do
     body
  end with;

Creates new temporary variables ``var1``, ``var2`` etc that exist inside of the ``with`` block. Each var may include preceding variables as part of the definition, eg

::

  with a = 1, b = a + 1 do
    \* ...
  end with;

Nondeterministic
~~~~~~~~~~~~~~~~

::

  with var1 \in set1, 
       var2 \in set2,
       \* ...
  do
     body
  end with;

`Nondeterministically <nondeterminism>` selects an element of each set to assign to the corresponding temporary variable. If any of these sets are empty, execution `blocks <await>` until all sets are nonempty. This can cause a `deadlock`.

.. _process:

process
=======

::

  [fair[+]] process name = val
  variables
    var1 = val;
    var2 \in set;
  begin
    Label:
      \* body
  end process;

Creates a single process with value ``val``. When there are multiple processes in a spec, TLC will `nondeterministically <nondeterminism>` choose a process and evaluate one label before making another nondeterministic selection.

``var1`` and ``var2`` are local to the process. For the initial state TLC will nondetermistically select an initial value for ``var2``.

If your spec has multiple processes, every ``val`` must be comparable. If for one process ``val`` is a string, then the rest must also be strings (or `model values <model_value>`.)

Preceding ``process`` with ``fair`` makes it a `weakly fair <fairness>` process. Preceding it with ``fair+`` will make it a `strongly fair <fairness>` process.

.. _process_set:
.. _self:

Process Sets
~~~~~~~~~~~~

::

  [fair[+]] process name \in set
    \* ...
  end process;

Creates a separate process for each element in ``set``. If the process set has a local variable ``var`` defined with ``\in``, the processes are not required to all initialize to the same value for ``var``.

If a process is defined as part of a process set, ``self`` will be the value it is assigned to.

.. _labels:
   
Labels
======

::

  Label1:
    body1
  Label2:
    body2

Represents a single unit of atomicity. `TLC` will evaluate everything in a label at one instant before checking any invariants or temporal properties. TLC cannot evaluate a label partway and switch to another process.

Each label corresponds to a single `action`. If suffixed with a ``+`` (as in ``Label:+``), the action is one step more `fair <fairness>` than the enclosing process. If suffixed with a ``+``, the action is one step less fair.

The names of labels must be globally unique. All processes have an implicit ``Done`` label at the very end.

.. _label_rules:

Label Placement Rules
~~~~~~~~~~~~~~~~~~~~~

There are some minimum requirements where you need to place labels:


* You must have a label at the beginning of each `process` and before every `while` loop.
* You may not place a label inside a `macro` or a `with` block.
* You must place a label after every `goto` and `return` statement.
* If any branch of an `either` or an `if` block has a label in it, then you must place a label the ``end statement;``;
* You may not assign to the same variable twice in a label. (use `|| <||>` instead)

.. _goto:

goto
====

::

  goto Label;

Goes to the corresponding label in the same process.

.. _macro:

macro
=====

::

  macro name(var1, var2) begin
    body
  end macro;

Called with ``name(var1, var2)``. Macros are direct code replacements and can refer to values outside of the macro. For example, given

::

  macro assign_to_x(y) begin
    x := y 
  end macro

  \* ...

Then ``assign_to_x(self)`` will expand to ``x := self``, using the local `process <process>` definition of ``self``.

.. _macro_body:

Macro Body
~~~~~~~~~~

There are some limitations to what can go in a macro body:

* At least one assignment
* No multiple assignments to a single variable (use `|| <||>` instead)
* No `while` loops
* No labels
* No procedure calls

.. _procedure:
.. _call:
.. _return:
   
procedure
=========

::

  procedure name(param1=default1, param2=default2) 
  variables localvar1 = val1, localvar2 = val2; 
  begin
    Label1:
      body1
    Label2:
      body2
      return;
  end procedure;

If a param is not assigned a default, TLC will automatically initialize the constant ``defaultInitValue``. Unlike macros, procedures may contain `labels`. 

Called with ``call name(val1, val2)``. The procedure labels inherit the same ``fairness`` properties as the calling process. The ``call`` expression must be immediately followed by either a ``return``, a `goto`, or another label.

When TLC evaluates ``return``, it ends the procedure and hands control back to the calling process. **This does not return any value to the calling process**. If TLC reaches the end of the procedure without evaluating a ``return``, it raises this as an error.
