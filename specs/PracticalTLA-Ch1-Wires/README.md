Chapter 1, _Practical TLA_
===

In which we use several variations of a bank account wiring algorithm to model a simple TLA model and learn to use the tools.

Concepts covered:
* How to boot up the toolkit
* How to translate 

Notes
* CMD+T is to translate PlusCal to TLA+
* F11 runs a model
* `process` lets you introduce concurrency
* `<STEP>:` defines an atomic operation that happens at once point in time.
* "Temporal Properties" test "eventual consistency"
  * `<>[]` is the "eventually-always" operator
* "Stuttering" - when a process fails to proceed. This is like when a server dies in real life.
