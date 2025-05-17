// TODO: Just a skeleton here.

console.log("Worker is running...")

self.importScripts('tree-sitter.js');
self.importScripts('eval.js');
self.importScripts('lib/lodash.min.js');
self.importScripts('hash-sum/hash-sum.js');

let parser;
let languageName = "tlaplus";
let enableEvalTracing = false;

onmessage = async (e) => {


    let action = e.data.action;
    let newText = e.data.newText;
    let specPath = e.data.specPath;
    let constValInputs = e.data.constValInputs;
    let invariantExpr = e.data.invariantExpr;

    await TreeSitter.init();
    parser = new TreeSitter();

    let tree = null;
    var ASSIGN_PRIMED = false;


    // Load the tree-sitter TLA+ parser.
    let language;
    LANGUAGE_BASE_URL = "js";
    const url = `tree-sitter-${languageName}.wasm`;
    try {
        console.log("Loading language from", url);
        language = await TreeSitter.Language.load(url);
    } catch (e) {
        console.error(e);
        return;
    }

    tree = null;
    parser.setLanguage(language);

    console.log("Message received from main script");
    const workerResult = `Result: ${e.data}`;
    console.log(e.data);
    console.log("Posting message back to main script");

    let spec = new TLASpec(newText, specPath);
    return spec.parse().then(function(){
        console.log("SPEC WAS PARSED IN WEBWORKER.", spec);

        let constVals = {};
        let constTlaVals = {};
        let model = {};

        model.spec = spec;
        model.specText = newText;
        model.specTreeObjs = spec.spec_obj;
        model.errorObj = null;
        model.actions = spec.spec_obj.actions;

        // Evaluate each CONSTANT value expression.
        for (var constDecl in constValInputs) {
            let constValText = constValInputs[constDecl];
            if (constValText === undefined) {
                throw "no constant value given for " + constDecl;
            }
            // console.log("constDecl:", constDecl, constValText);
            constVals[constDecl] = constValText;

            model.specDefs = spec.spec_obj["op_defs"]
    
            let ctx = new Context(null, new TLAState({}), model.specDefs, {}, constTlaVals);
            // Flag so that we treat unknown identifiers as model values during evaluation.
            ctx.evalModelVals = true;
            let cVal = evalExprStrInContext(ctx, constValText);
            // console.log("cval:", cVal);
            constTlaVals[constDecl] = cVal;
        }
    
        // console.log("constTlaVals:", constTlaVals);

        //
        // TODO: Fully implement this.
        //
        if(action === "loadTrace"){
            let hashTrace = e.data.stateHashList;

            // Generate initial states.
            let interp = new TlaInterpreter();

            let initStates = interp.computeInitStates(spec.spec_obj, constTlaVals, true, spec);
            console.log("initStates:", initStates);
            currNextStates = initStates;

            for (const stateHash of hashTrace) {
                console.log("stateHash:", stateHash);
                // Check each state for possible quant bounds hash,
                // if it has one.
                let stateAndQuantBounds = stateHash.split("_");
                let rethrow = true;
                if (stateAndQuantBounds.length > 1) {
                    let justStateHash = stateAndQuantBounds[0];
                    let quantBoundHash = stateAndQuantBounds[1];
                    chooseNextState(justStateHash, quantBoundHash, rethrow);
                } else {
                    chooseNextState(model, stateHash, undefined, rethrow);
                }
            }
        }


        // Generate initial states.
        let interp = new TlaInterpreter();

        let start = performance.now();
        let reachableStates = interp.computeReachableStates(spec.spec_obj, constTlaVals, invariantExpr, spec, logMetricsInterval=200);
        const duration = (performance.now() - start).toFixed(1);
        console.log("Reachable states from WebWorker.", reachableStates, `duration: ${duration}ms`);
        console.log(`Computed ${reachableStates.states.length} reachable states in ${duration}ms.`);

        if(!reachableStates.invHolds){
            postMessage(reachableStates);
            return;
        }

        // Seems it is fine to serialize TLAState objects back through the web worker.
        postMessage(reachableStates);
        return;


    }).catch(function(e){
        console.log("Error parsing and loading spec.", e);
        // model.errorObj = {parseError: true, obj: e, message: "Error parsing spec."};
    });

};