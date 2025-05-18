<!-- # TLA<sup>+</sup> Web Explorer -->
# Spectacle 

<!-- <img src="assets/glassestall3.png" height=31 alt="Spectacle logo" style="vertical-align: middle"> -->

<!-- <img src="assets/glasses-svgrepo-com.svg" width="50" height="20" alt="Spectacle logo" style="vertical-align: middle"> -->


Spectacle is an interactive, web-based tool for exploring, visualizing, and sharing formal specifications written in the [TLA<sup>+</sup> specification language](https://lamport.azurewebsites.net/tla/tla.html).  The motivation is to have a better way to quickly interact with a formal specification and easily share results. For example, it provides a way to share protocol behaviors and counterexample traces in a convenient, portable, and repeatable manner. 

 A live version of the tool is currently hosted [here](https://will62794.github.io/spectacle/#!/home), and below are some example specifications to try out:

- [Lock server](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2Flockserver.tla&constants%5BServer%5D=%7B%22s1%22%2C%20%22s2%22%7D&constants%5BClient%5D=%7B%22c1%22%2C%20%22c2%22%7D)
- [Microwave](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2Fwith_state_graphs%2FMicrowave.tla&constants%5BImplementStartSafety%5D=FALSE&constants%5BImplementOpenDoorSafety%5D=FALSE)
- [Cabbage Goat Wolf Puzzle](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FCabbageGoatWolf.tla) (animated)
- [Distributed termination detection (EWD998)](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FEWD998.tla&constants%5BN%5D=3) (animated)
- [Two phase commit](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FTwoPhase_anim.tla&constants%5BRM%5D=%7Brm1%2Crm2%7D) (animated)
- [Paxos](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FPaxos.tla&constants%5BServer%5D=%7B%22s1%22%2C%22s2%22%2C%20%22s3%22%7D&constants%5BSecondary%5D=%22Secondary%22&constants%5BPrimary%5D=%22Primary%22&constants%5BNil%5D=%22Nil%22&constants%5BInitTerm%5D=0&constants%5BAcceptor%5D=%7Ba1%2Ca2%2Ca3%7D&constants%5BQuorum%5D=%7B%7Ba1%2Ca2%7D%2C%7Ba2%2Ca3%7D%2C%7Ba1%2Ca3%7D%2C%7Ba1%2Ca2%2Ca3%7D%7D&constants%5BProposer%5D=%7Bp1%2Cp2%7D&constants%5BValue%5D=%7Bv1%2Cv2%7D&constants%5BBallot%5D=%7B0%2C1%2C2%2C3%7D&constants%5BNone%5D=None)
- [FlexiblePaxos](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FFlexiblePaxos.tla&constants%5BValue%5D=%7Bv1%2Cv2%7D&constants%5BAcceptor%5D=%7Ba1%2Ca2%7D&constants%5BQuorum1%5D=%7B%7Ba1%7D%2C%20%7Ba2%7D%7D&constants%5BQuorum2%5D=%7B%7Ba1%2Ca2%7D%7D&constants%5BBallot%5D=%7B0%2C1%2C2%2C3%7D)
- [Raft](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FAbstractRaft_anim.tla&constants%5BServer%5D=%7Bs1%2Cs2%2C%20s3%7D&constants%5BSecondary%5D="Secondary"&constants%5BPrimary%5D="Primary"&constants%5BNil%5D="Nil"&constants%5BInitTerm%5D=0) (animated)
- [Snapshot Isolation](https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fwill62794%2Fsnapshot-isolation-spec%2Frefs%2Fheads%2Fmaster%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=%22Empty%22) 

You can also explore some interesting (and infamous) traces of different protocols:

- [Solution to the cabbage goat wolf puzzle](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FCabbageGoatWolf.tla&trace=f3cb45ca%2C4357915f_7da698e2%2C126ae834_bf3b326e%2C76c2f092_652fccef%2C7229f089_f598e730%2C29e91cea_2ac3323e%2C50fe2821_bf3b326e%2C1d26e01c_9abe74ba%2C5f98d202_f598e730%2C3a9fa186_34b35f78%2Ca49994fc_bf3b326e%2Ceec0674a_652fccef%2C2afe63ed_f598e730%2C2883b61a_7da698e2%2C73ea1058_bf3b326e) (Cabbage Goat Wolf Puzzle)
- [Raft log entry is written and later rolled back](https://will62794.github.io/spectacle/#!/home?specpath=.%2Fspecs%2FAbstractRaft_anim.tla&constants%5BServer%5D=%7Bs1%2Cs2%2Cs3%7D&constants%5BSecondary%5D=%22Secondary%22&constants%5BPrimary%5D=%22Primary%22&constants%5BNil%5D=%22Nil%22&constants%5BInitTerm%5D=0&trace=318c702a%2C0785f33f%2Cbbf1576c%2C79ad3285%2C708acdc2%2C2cd8de84%2Cfbeeee44%2Cac5d32a8%2Cc1e2949e%2Cd8547bce%2C7735c8df) (Raft)
- [Write skew anomaly under snapshot isolation](https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fwill62794%2Fsnapshot-isolation-spec%2Frefs%2Fheads%2Fmaster%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=%22Empty%22&trace=4d9d875e%2Cb0868cc6%2C2f4fe314%2C351c185a%2C9af072f2%2C0ad7710e%2C39e3312d%2Cc5dbe6f2%2C0005740a) (Snapshot Isolation) 
- [Read-only anomaly under snapshot isolation](https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fwill62794%2Fsnapshot-isolation-spec%2Frefs%2Fheads%2Fmaster%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=%22Empty%22&trace=4d9d875e%2C27dfd06a%2C639eed1f%2C4cb5a71b%2C4708fef8%2C429a81d3%2Ce9311886%2C7478057a%2C2ea8cbe7%2C6a3128ec%2Cd2bef298%2C071ae0d9) (Snapshot Isolation)



The tool implements a [full TLA+ interpreter in Javascript](https://github.com/will62794/spectacle/blob/master/js/eval.js), building on top of the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) for parsing specifications. This allows for interactive exploration of specs natively in the browser, without reliance on an external language server. 

<!-- The Javascript interpreter is likely slower than TLC, but highly efficient model checking isn't currently a goal of the tool.  -->

<!-- Note also that you can basically use the existing web interface as a simple TLA+ expression evaluator, since making changes to definitions in the spec should automatically update the set of generated initial states. -->

<!-- This project Utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) to provide a web based TLA+ interface for exploring and sharing specifications.  -->
<!-- There are still some TLA+ language features that [may not be implemented](https://github.com/will62794/spectacle/issues), but a reasonable number of specs should be handled correctly. For example, see this [Paxos spec](https://will62794.github.io/spectacle/#!/home?specpath=./specs/Paxos.tla). Additional testing is needed to verify the correctness of this interpreter on more complex specs. -->

<!-- A basic, preliminary test suite can be found [here](https://will62794.github.io/spectacle/test.html). -->

## Usage Notes

The current tool expects that a specification has defined its initial state predicate and next state relation as `Init` and `Next` definitions, respectively. If your specification has these defined under different names, they will not be recognized and no initial state or next state evaluation will occur. In this case, you can still use the tool in REPL mode, though. 

Eventually this will be made configurable, but the current tool looks for these hard-coded definitions. Also, there is incomplete support for user module imports, so specs are largely expected to be written in a single module. The interpreter does, however, support most operators from the [TLA+ standard modules](https://github.com/tlaplus/tlaplus/tree/c25a01393ef7d9b0315f3d3b1581988e7a4a57b2/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules) by default.

You can also see a live demo of the tool and its features in [this presentation](https://www.youtube.com/watch?v=kSSWmxQLvmw), which also gives a very high level overview of the tool architecture and implementation details. 

### Running Locally

If you would like to run Spectacle locally and offline, you can do so by cloning the repo and running `make serve` from the root directory. This will start up a local Python server serving the app at [`127.0.0.1:8000`](http://127.0.0.1:8000).

<!-- Note that in addition to copying and pasting in the text of a TLA+ spec or writing it in the browser interface, you can also load a spec file from a given URL by using the following URL path format: -->
<!-- ``` -->
<!-- https://will62794.github.io/spectacle/#!/home?specpath=<tla_spec_url> -->
<!-- ``` -->
<!-- where `tla_spec_url` is a URL pointing to raw TLA+ module file. For example, you can see that [this link](https://will62794.github.io/tla-web/#!/home?specpath=https://gist.githubusercontent.com/will62794/4250c4b6a8e68b0d9e038186739af8cc/raw/3470b5999f896abb478733e8fc07e7ed9e3039da/HourClock.tla) loads a simple spec from a [personal Github gist](https://gist.githubusercontent.com/will62794/4250c4b6a8e68b0d9e038186739af8cc/raw/3470b5999f896abb478733e8fc07e7ed9e3039da/HourClock.tla). -->


<!-- ### REPL Mode -->

<!-- You can also open a specification in REPL mode, which gives you access to a live REPL for dynamically evaluating TLA+ expressions in the context of a specification. See [here](https://will62794.github.io/tla-web/#!/home?specpath=./specs/repl.tla&repl=true) for an example REPL scratchpad. -->

## Testing

Currently, nearly all testing of the tool is done via conformance testing against TLC. That is, for a given specification, we [generate its reachable state graph using TLC](https://github.com/will62794/spectacle/blob/0060a9bedfbf78c9c6ef1eacf701b13f85048f5e/specs/with_state_graphs/gen_state_graphs.sh) and compare this for equivalence against the reachable state graph generated by the Javascript interpreter. You can see the result of all current tests that are run on [this page](https://will62794.github.io/spectacle/test.html), and the underlying test specs [here](https://github.com/will62794/spectacle/tree/0060a9bedfbf78c9c6ef1eacf701b13f85048f5e/specs/with_state_graphs).
