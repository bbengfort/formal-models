# TLA+ and PlusCal

- every TLA+ spec must start with `----` and the word `MODUL`E and end with `====` 

`EXTENDS` loads/imports other modules


`\*` is line comment 

```
(* 
Is a multiline comment. 
*)
```

PlusCal has to be specified in comments:

```
(*-- algorithm wire_alg

end algorithm; *)
```

declare variables with `variables` keyword (and initializes them with equals sign) 

`:=` is the assignment operator. 
`==` is definition

Logic:

`/\` is and 
`\/` is or 
`~` is not 

"TLA is as terrible as you can make a tool before it stops being useful" 

We have:
    - specifications: describe what system is supposed to do 
    - models: execute and check our system

Labels: describe atomicity inside the algorithm; every state transition chooses one process and one label to execute. 
In PlusCal there is a global sequential ordering (but maybe not in TLA+) 

`process` allows you to model concurrency be defining the proceedure for a single process (adds non-determinism) 

Translate a spec into TLA+ with CMD+T -- writes the spec with keyword `Spec` by default.

<> "diamond" is eventually true 
[] "box" is always true 
<>[] means "true at termination"
[]<> means "always eventually true" 


`<Stuttering>` - basically, everything crashes 

`fair process` - means the process will never crash. 

Is there a gitignore for the TLA+ Toolbox? Searching


TLC adds print statements, assertions, random timestamping for temporal logic (creator isn't sure what the acryonym stands for). 

for every type we have a way of generating the set of that type. For numbers it's `a..b` - the set of numbers between `a` and `b`. 

only one loop in PlusCal - `do while` 

`either` causes the program to branch, enumerates the possibilities at this step with `or`

`with` allows us to create temporary variables to assign to parts

macros and with bodies:
    - no while loop 
    - no labels 
    - cannot assign to same variable twice 

`assert` allows you to embed invariants directly into PlusCalc with by extending `TLC` 

Types in TLA+:
    - numbers 
    - booleans 
    - strings (`"abc"`)
    - model value 

Complex:
    - Sets 
    - Sequences 
    - Structures 
    - Functions 


You can run on AWS and Azure 

- parallelizable until temporal checking, then just get a big CPU


\E there exists an element matches condition 
\A all elements match condition 
on empty set, \E is false and \A is true. 

CHOOSE gives you an arbitrary element, it's always the same element 

Sequences are 1-indexed! 

Sequences are functions, as are structures, the way they are represented visually is all that differs. 
`@@` concatenates functions together. 

[Integer -> Integer] would return the set of all functions that maps an integer to another integer. 

## Concurrency and Temporal Logic 

Two processes are operating with several steps, and those steps can occur in any order. 

If you have two processes a with steps 1,2,3 and be with steps 1,2 - there are 60 possible orderings (6!/3!2!); if you have 10 possible starting states, this means 600 possible executions, any of which could cause an error. TLA+ models all behaviors to check for bugs. 

Labels are units of atomicity; TLC will run a label in one process, evaluate all invariants, then run the next label in the next process. 

Rules for labels:
    - must go before a while loop (a while loop requires a label, though in single process it does it for you). 
    - a label must go before every process 
    - you can't put a label in a with or in a macro 
    - if a label is in a either or an if statement, then there must be a label that follows it 
    - you cannot assign a variable multiple times in a single label 

 In a struct, you can use || to glob an assignment together to modify multiple parts of a struct/function at once

 You can use goto to jump to a label in the same process (e.g. to create a while loop, etc). 

 await prevents label from executing until condition is true. (when is a synonym) 
 It is essentially a killer of states - e.g. if there is an ordering of labels:

 Read Write Read Write 

 once a label encounters a write it is not longer able to add that label to the ordering of events, e.g. a Read must come next. 

 Note that in either/or if an await is in the either/or it could prune the possible states because await is a killer of states. However, if you add a label inside of the either/or then deadlock could occur. 

 "adding labels tends to surface bugs, it doesn't eliminate bugs" as do awaits. 

 The problem is that every branching point increases the combinatorial explosion. E.g. if we don't think there is a deadlock and we don't add the predicates, then we'll have less labels to evaluate. There is an intuition and an art to this. 

 Use procedures very carefully; they require labels which means they dramatically increase the number of states. Using macros instead limits the number of states that are generated and is much better. 

## Temporal Logic 

<> diamond - must be true at least once. 

fair - if something can happen, it will happen (weakly fair vs. strong fair). 
    weak fair: if an action is permenantly enabled it will eventually happen 
    strong fair: if an action keeps cycling between enabled and disabled it will eventually happen 

you almost always want to use weak fairness (guarantees that threads/procs can't crash) strong gives you additional firepower. 

`~>` leads to; P ~> Q means that every time P is true it leads to Q being true. 

`<>[]` at some point it will become true and will stay true forever
`[]<>` is equivalent to ~P ~> P
