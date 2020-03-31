Some notes on Lean usage.

Shortcuts
=========
In vscode, ctrl-shift-p followed by typing "lean doc" brings up the lean
documentation in a new tab on the right Lean panel.

Language
========

infix
-----
Define custom infix notation:
    
    infix `is_a_max_of`:55 := is_max

This creates a 'is_a_max_of' infix predicate with precidence 55 and that
associates to the left (use infixr to associate to the right).

French quotes are entered with \f< and \f>.

brief
-----
Short explanations:

* section [optional section name]
  scope command. The scope of variable and universe declarations are contained
  within the `section` and matching `end` commands.  Like a braces '{' and '}'
  in C++.
* namespace <name>, end <name>
  Similar concept to that of other languages. All declarations within the 
  namespace have a prefix of <name> when referenced outside the namespace.
* protected
  Specifies that a declaration, when brought into another namespace with 
  open, does not get its name shortened. 
* private
  Specifies that a declaration cannot be accessed from another namespace.
* open <name of namespace>
  Open can be used to remove the requirement to type the prefix of a namespace.
  There are options for being specific in how objects are renamed.
* export
  I don't understand...
* universe
  I don't understand....
* variable      
  Introduces a single variable
* variables (multiple)
* parameter 
  I don't understand....
* parameters (multiple)
* options:
    typing `set_option` <option> <true|false> changes Lean behaviour. 
    Some options are:
       pp.implicit : display implicit arguments
        pp.universes : display hidden universe parameters
        pp.coercions : show coercions
        pp.notation : display output using defined notations
        pp.beta : beta reduce terms before displaying them
        pp.numeral: ?



Conventions
===========

ext
---
Many lemmas have 'ext' in the name. For example, set.ext. I think it refers to
'set extension', the act of definiting a set by enumerating its members. This is
in contrast to an intensional definition: defining a set by mentioning a
defining property.

The "Logic and Proof" tutorial mentions the 'ext' convention:

    Here, ext is short for “extensionality.” In symbolic terms, it is the 
    following fact:

        ∀x(x∈A↔x∈B)→A=B.
        
        This reduces proving A=B
        to proving ∀x(x∈A↔x∈B), which we can do using ∀ and ↔ introduction.

Wikipedia has a nice article on extensionality defined in the realm of 
Logic. https://en.wikipedia.org/wiki/Extensionality
tr;dr: judging objects to be equal based on their external properties rather
       than their definition. 

Documentation references
========================
Sets
----
Tutorial
https://leanprover.github.io/logic_and_proof/sets_in_lean.html

Core library
https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

Mathlib
https://leanprover-community.github.io/mathlib_docs/data/set/basic.html#set.ext

Kevin Buzzard links:
https://github.com/ImperialCollegeLondon/M40001_lean
https://github.com/ImperialCollegeLondon/group-theory-game
`
