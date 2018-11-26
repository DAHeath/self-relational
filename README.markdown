TODO
* Implementation
  Here's the basic idea:
    - Replace all instances of command sequences by command products, using the
      sequence proof rule.
    - Partition the input command into loop commands/non-loop commands, using
      associativity and commutativity.
    - Model all the non-loop commands using the product proof rule along with
      command-specific rules.
    - Perform simultaneous induction over the loops using the loop rule.
    - Iterate until all commands been dispatched to a CHC system.

  I'm not yet sure how best to incorporate loop unrolling (using the command
  isomorphism rule) in this system, but there should be a way.

* Complete proof of the loop rule. Thus far I've completed a rule for the
  product of two loops, but the more general rule is tricky.
* Paper
  - Overview examples
  - Related work
  - Evaluation
