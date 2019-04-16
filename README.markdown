Here's the basic idea:
  - Replace all instances of command sequences by command products, using the
    sequence proof rule.
  - Partition the input command into loop commands/non-loop commands, using
    command isomorphisms
  - Model all the non-loop commands using the product proof rule along with
    command-specific rules.
  - Perform simultaneous induction over the loops using the loop rule.
  - Iterate until all commands been dispatched to a CHC system.
