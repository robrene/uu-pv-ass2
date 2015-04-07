# Program Verification Assignment 2a Report: Leader Election

## Base implementation

The implementation of the base algorithm can be found in the file `leader.pml`. The `init` function creates *N* processes with randomly generated unique identifiers. It also initializes these processes with message channels organized as a ring. These channels support either a normal message or a message broadcasting the new leader ID. In addition to executing the algorithm, each process decrements the `activeProcesses` counter immediately before terminating, as well as noting their elected leader in the corresponding position of the `leaders` array. After having fired off all the processes, the `init` function blocks while waiting for all processes to finish. When all proceses have terminated, it performs a check to see if all processes elected the same leader.

### Details

The first part of the specification is to check that the algorithm always terminates. To do this, I used an LTL instruction:

    []<>(activeProcesses == 0)

This ensures that at every possible execution point, in particular each execution point after the processes have been started, all individual processes always have to terminate.

The second part of the specification is to check that when the algorithm terminates, all processes agree on the same leader. We can use the `activeProcesses` counter as a sound indication that all processes have terminated. The `init` function blocks while waiting for the condition to become true, after which it uses `assert` to ensure all elements in the `leader` array are equal.

### Execution

First, we compile the verifier:

    $ spin -a leader.pml
    $ gcc -DCOLLAPSE -DVECTORSZ=100000 -O2 pan.c -o pan

The `COLLAPSE` option performs a sound compression of state vectors to improve memory usage. The `VECTORSZ` option allows for bigger state vectors, which are required for the verifier to work. Now we can run the verifier as such:

    $ ./pan -a

The `-a` flag is required because we use an LTL "never claim" in combination with accept labels.

### Results

The tests were ran for values of *N* between 2 and 10. For all runs, 0 errors were found. The claim that the processes always terminate was always fulfilled. The asserts that all processes elected the same leader always passed. None of the code was marked as unreached.

I believe it is safe to say that the algorithm as described in the assignment and as implemented in `leader.pml` fulfills the specifications after model checking.

## Non-deterministic extension

The implementation of the extended algorithm can be found in the file `leader_nondet.pml`. To make the algorithm non-deterministic, a two round approach was taken. The message channels were extended to allow "round-one" messages, "round-two" messages and "leader-broadcast" messages. The first round is very similar to the base DLER algorithm. Instead of always discarding the received *x'* when it is smaller that the process ID, there is a non-deterministic chance that the *x'* gets passed through anyway, as a wild-card of sorts.

When a process receives its own ID as *x'*, it counts itself as "candidate". The process now enters the second round, and sends its own ID as a round-two message. When a process receives a round-two message, it also enters the second round.

In the second round, only nominated leader IDs are being passed around. Every process records the lowest nominated ID it has encountered so far. The algorithm stops when a nominated leader receives its own ID. This causes it to send a leader-broadcast message just as in the base algorithm.

This extension gives each process a non-deterministic non-zero chance to become a nominated leader, after which the nominee with the lowest ID will become the leader.

### Algorithm

1. Every process *i* sends its own ID to its successor in the ring as a "round-one" message.

2. **Round 1:** When a process *i* with ID *x<sub>i</sub>* receives an ID *x'* as a "round-one" message from its predecessor, it does the following:

  (a) If *x'* < *x<sub>i</sub>*, it non-deterministically chooses to either discard *x'*, or to forward it to its successor.

  (b) If *x'* > *x<sub>i</sub>*, it forwards *x'* to its successor.

  (c) If *x'* = *x<sub>i</sub>*, the process becomes a nominee for leadership, and sends its own ID to its successor in the ring as a "round-two" message and subsequently goes to round two. It also stores its ID as a possible leader *x<sub>s</sub>*.

3. When a process *i* receives an ID *x'* as a "round-two" message from its predecessor, it forwards it to its successor as a "round-two" message and subsequently goes to round two. It also stores *x'* as a possible leader *x<sub>s</sub>*.

4. **Round 2:** When a process *i* with a stored possible leader ID *x<sub>s</sub>* receives an ID *x'* as a "round-two" message from its predecessor, it does the following:

  (a) If *x'* < *x<sub>s</sub>*, it forwards *x'* to its successor. It also stores *x'* as the new possible leader.

  (b) If *x'* > *x<sub>s</sub>*, it discards *x'*.

  (c) If *x'* = *x<sub>s</sub>*, the process wins and declares itself as the leader.

### Results

The same methods were used to validate the specification. The same results were observed as with the base algorithm. No errors, no unreached code, all assertions evaluated to true and the LTL expression indicates termination.

## Scalability

The following numbers were obtained on a Macbook Pro (Late 2013 model) running on a 2.4 GHz Intel Core i5 with 8 GB 1600 MHz DDR3 memory, operating system Mac OS X Yosemite 10.10.2, spin version 6.4.2.

### Base algorithm

| N  | `time ./pan -a` | Total actual memory usage |
|----|-----------------|---------------------------|
|  2 | 0.08s | 147.073 MB |
|  3 | 0.08s | 147.073 MB |
|  4 | 0.09s | 147.073 MB |
|  5 | 0.09s | 147.073 MB |
|  6 | 0.10s | 147.073 MB |
|  7 | 0.15s | 147.073 MB |
|  8 | 0.28s | 147.073 MB |
|  9 | 0.75s | 147.073 MB |
| 10 | 2.50s | 156.610 MB |
| 11 | 8.57s | 175.684 MB |
| 12 | 29.68s | 242.441 MB |

### Extended algorithm

| N  | `time ./pan -a` | Total actual memory usage |
|----|-----------------|---------------------------|
|  2 | 0.09s | 147.073 MB |
|  3 | 0.09s | 147.073 MB |
|  4 | 0.09s | 147.073 MB |
|  5 | 0.12s | 147.073 MB |
|  6 | 0.19s | 147.073 MB |
|  7 | 0.50s | 147.073 MB |
|  8 | 1.84s | 156.610 MB |
|  9 | 6.83s | 194.757 MB |
| 10 | 26.93s | 318.735 MB |
| 11 | 104.94s | 728.815 MB |
| 12 | 415.61s | 2528.275 MB |

### Conclusion

Calculating the execution tree of all states becomes exponentially harder for increasing *N*. Even for this relatively simple model, verifying the small specification for this algorithm quickly becomes too expensive for large values of *N*.

Memory requirements seem stagnant at first, with a lower bound of 147.073 MB for most values of *N*. However, after a certain point, memory requirement growth explodes exponentially. Using the simple optimization flags proved to be enough to run the verification on a commodity consumer laptop, with room to spare. However, these requiremens will need to be kept in mind when evaluating more complicated models.
