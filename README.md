# Privacy-preserving policy evaluation using homomorphic encryption

## Structure

- policy.cpp contains the implementation of policy evaluation itself.
- parser.cpp implements parsing of policies of a certain format.
- djn.cpp/Paillier.cpp/opowmod.cpp/SEQ.cpp implements homomorphic encryption
- data/\* contains all of the policies
- data/results/\* is where the results of the policy evaluation are stored.

## Running the experiment

The experiment can be run by executing

```
./experiment.sh EXPID
```

where EXPID is the experiment experiment id:
- Experiment 1 performs policy evaluation on single atomic targets with varying query size.
- Experiment 2 performs policy evaluation on all of the combination rules.
- Experiment 3 performs policy evaluation on complex policies.

## Output format
For the sake of traceability and easy data aggregation, we defined a specific output format:
```
[1, 0, 1, 1]===[0,0,1]===[0.585648]===[55333]
```
This format contains several columns:
- The first column has information about the policy and query: the number of targets, the number of operations, the query size and the repetition number.
- The second columns contains the result of the evaluation 
- The third column has the evaluation time in seconds.
- The fourth columns contains the bandwidth in bytes.
