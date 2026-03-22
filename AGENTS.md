
## Overview

The core implementation of the Javascript TLA+ interpreter lives in `eval.js`, where the `evalExpr` is the main evaluation function, and recursively calls other evaluation functions depending on the type of expression being evaluated.

Main UI code, which uses the MithrilJS framework, lives in `app.js`, and this makes use of the interpreter logic for trace exploration.

## Testing

Testing of the core Javascript interpreter in `eval.js` is done by conformance checking output against the TLC model checker state graph. So, a test is created as a dedicated TLA+ spec in `specs/with_state_graphs`, and upon creation, we need to run

```
./gen_state_graphs.sh <test_spec_name>
```
from within `specs/with_state_graphs` which will generate a JSON state graph from TLC for that spec, which is then used to compare against the output of the Javascript TLA+ interpreter. 

After creating such a test spec file, it also needs to be added as an entry in the `testGroups` object in `test.js`. Which group the file goes into can be judged based on its general category of functinoality being tested, but its not too important, and can go into "General" by default.

DO NOT use Playwright or worry about those tests for the core intepreter type tests as described above.

DO NOT touch `benchmark.js` either, only edit `test.js`.