//
// Test script runs on 'test.html' page.
//

let tree;
let parser;

let totalLOC = 0;

// Parse URL params;
const urlSearchParams = new URLSearchParams(window.location.search);
const urlParams = Object.fromEntries(urlSearchParams.entries());
let enableEvalTracing = parseInt(urlParams["debug"]);


function displayEvalGraph(nodeGraph, divname) {

    console.log("#displayEvalGraph");
    let stategraphDiv = document.getElementById(divname);
    if (stategraphDiv === null) {
        // TODO: Work out synchronization of this eval graph computation with other UI
        // element interactions properly.
        return;
    }
    stategraphDiv.innerHTML = "";
    // stategraphDiv.hidden = false;

    // cytoscape.use("dagre");

    var cy = cytoscape({
        container: stategraphDiv, // container to render in
        style: [
            {
                selector: 'node',
                // shape: "barrel",
                size: "auto",
                style: {
                    'label': function (el) {
                        return el.data()["expr_text"].replaceAll("\n", "");
                    },
                    // "width": function(el){
                    //     console.log(el);
                    //     return el.data().expr_text.length * 10 + 20;
                    // },
                    // "height": 15,
                    "background-color": "white",
                    "text-valign": "center",
                    // "text-halign": "center",
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "black",
                    "padding-left": "10px",
                    "font-family": "monospace",
                    "font-size": "7px",
                    "shape": "rectangle"
                }
            },
        ]
    });

    console.log("nodeGraph:", nodeGraph);
    console.log("nodeGraph:", nodeGraph.map(d => d[0]));
    let nodes = _.uniq(_.flatten(nodeGraph.map(d => d[0])))
    for (const node of nodes) {
        cy.add({
            group: 'nodes',
            data: {
                id: hashSum(node),
                expr_text: node
            },
            position: { x: 200, y: 200 }
        });
    }

    let eind = 0;
    for (const edgeData of nodeGraph) {
        let edge = edgeData[0];
        let retVal = edgeData[1];
        let edgeOrder = edgeData[2];
        let evalDur = edgeData[3];
        cy.add({
            group: 'edges', data: {
                id: 'e' + eind,
                source: hashSum(edge[0]),
                target: hashSum(edge[1]),
                // label: retVal[0]["val"].toString() //+ " " + edgeOrder + "(" + retVal.length + ") [" + evalDur + "ms]"
                label: retVal[0]["val"].toString() + " (n=" + retVal.length + ")" // + ") [" + evalDur + "ms]"
            }
        });
        eind++;
    }
    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle",
        "font-family": "monospace",
        "font-size": "8px",
        "color": "blue",
        "width": 2,
        "label": function (el) {
            return el.data().label;
        }
    })
    // let layout = cy.layout({name:"cose"});
    // let layout = cy.layout({ name: "breadthfirst" });
    let layout = cy.layout({ name: "dagre", nodeDimensionsIncludeLabels: true });
    // let layout = cy.layout({ name: "elk" });
    cy.resize();
    layout.run();
}

function toggleTestDetails(testId) {

    // alert("details"+testId);
    let resultsDivId = "test_result_details_" + testId;
    let testResultsDiv = document.getElementById(resultsDivId);
    let isHidden = testResultsDiv.getAttribute("hidden");
    // Hide.
    if (isHidden === null) {
        testResultsDiv.setAttribute("hidden", true);
    } else {
        // Unhide.
        testResultsDiv.removeAttribute("hidden");
    }
    console.log(isHidden);

}

// Do two arrays (treated as sets) contain the same elements.
function arrEq(a1, a2) {
    console.log("arrEq a1:", a1);
    console.log("arrEq a1:", a2);
    let a1Uniq = _.uniqWith(a1, _.isEqual)
    let a2Uniq = _.uniqWith(a2, _.isEqual)

    console.log("arrEq a1 uniqwith:", a1);
    console.log("arrEq a2 uniqwith:", a2);

    let sameSize = a1Uniq.length === a2Uniq.length;
    if (!sameSize) {
        return false;
    }
    let sameEls = _.every(a1Uniq, (s) => _.find(a2Uniq, t => _.isEqual(s, t)));
    return sameEls;
}


function tlcReachableEdgesSpec(testId, specVariables, node) {
    let spec = `----MODULE ${testId}_TLC_reachable----\n`;
    for (var kvar in specVariables) {
        spec += "VARIABLE " + kvar + "\n";
    }
    spec += `Init == \n`;

    let stateStr = node["label"];
    console.log("STATE STR:", stateStr);
    stateStr = stateStr
        .replaceAll("\\n", " ")
        .replaceAll("\\\\", "\\");
    let stateDisjunct = "  \\/ (" + stateStr + ")"
    spec += stateDisjunct + "\n";

    spec += "Next == UNCHANGED <<" + Object.keys(specVariables).join(",") + ">>\n"
    spec += "====";
    return spec;
}

function tlcInitStatesSpec(testId, specVariables, stateGraph){

    // First check matching initial states.
    let initStatesTLC = stateGraph["objects"].filter(obj => obj.hasOwnProperty("label") && obj["style"] === "filled");
    let specOfInitTLCReachableStates = `----MODULE ${testId}_TLC_reachable----\n`;
    for (var kvar in specVariables) {
        specOfInitTLCReachableStates += "VARIABLE " + kvar + "\n";
    }
    specOfInitTLCReachableStates += `Init == \n`;
    for (const obj of initStatesTLC) {
        // Retrieve the TLA state string and deal with some string escaping.
        let stateStr = obj["label"];
        stateStr = stateStr
            .replaceAll("\\n", " ")
            .replaceAll("\\\\", "\\");
        let stateDisjunct = "  \\/ (" + stateStr + ")"
        specOfInitTLCReachableStates += stateDisjunct + "\n";
    }

    specOfInitTLCReachableStates += "Next == UNCHANGED <<" + Object.keys(specVariables).join(",") + ">>\n"
    specOfInitTLCReachableStates += "===="
    return specOfInitTLCReachableStates;
}

async function testSemanticError(test, parsedSpec, specPath, constvals, spec) {
    console.log("### TEST: Checking for semantic error.")
    const start = performance.now();
    let interp = new TlaInterpreter();

    try{
        interp.computeReachableStates(parsedSpec, constvals, undefined, spec);
    } catch(e) {
        console.log("Semantic error test passed.");
        console.log(currEvalNode.startPosition)
        let origLoc = spec.rewriter.getOrigLocation(currEvalNode.startPosition.row + 1, currEvalNode.startPosition.column + 1)
        console.log("ORIG LOC:", origLoc)
        let errLineMatches = test["errLine"] === origLoc[0];
        return {
            "pass": errLineMatches,
            "duration_ms": performance.now() - start,
            "errLineActual": currEvalNode.startPosition.row + 1,
        }
    }
    console.log("Semantic error test failed.");
    return {
        "pass": false,
        "duration_ms": performance.now() - start
    }
}

// Check equivalence of given state graph and state graph
// generated by given spec.
async function testStateGraphEquiv(testId, stateGraph, parsedSpec, specPath, constvals, spec, isSemanticErrorTest) {

    const start = performance.now();

    //
    // Test matching initial states and edges. 
    //

    let interp = new TlaInterpreter();

    console.log("### TEST: Computing reachable states with JS interpreter.")
    let reachableObj = interp.computeReachableStates(parsedSpec, constvals, undefined, spec);

    let initial = reachableObj["initStates"];
    let reachable = reachableObj["states"];
    let reachableEdges = reachableObj["edges"];

    console.log("### TEST: Processing reachable states computed by TLC.")

    let specVariables = parsedSpec["var_decls"];
    let objects = stateGraph["objects"];
    let edges = stateGraph.hasOwnProperty("edges") ? stateGraph["edges"] : [];
    console.log("edges:", edges);

    let specOfInitTLCReachableStates = tlcInitStatesSpec(testId, specVariables, stateGraph)

    // Parse this generated spec and record its initial states.
    enableEvalTracing = false; // turn off tracing here to avoid pollution of main eval logs.
    tlcspec = new TLASpec(specOfInitTLCReachableStates, specPath);
    tlcspec.parseSync();
    parsedTLCSpec = tlcspec.spec_obj;
    let initialTLC = interp.computeReachableStates(parsedTLCSpec, constvals, undefined, tlcspec)["states"];

    console.log("spec init JS  :", initial);
    console.log("spec init TLC :", initialTLC);
    console.log("----------------------");

    let jsInitFingerprints = initial.map(s => s.fingerprint());
    let tlcInitFingerprints = initialTLC.map(s => s.fingerprint());

    let initDiffInJS = _.differenceBy(initial, initialTLC, s => s.fingerprint());
    let initDiffInTLC = _.differenceBy(initialTLC, initial, s => s.fingerprint());

    let initAreEquiv = arrEq(jsInitFingerprints, tlcInitFingerprints);

    // Now check matching edges.
    let reachableEdgesTLC = [];
    for (const edge of edges) {
        let to = edge["head"];
        let from = edge["tail"];

        let fromNode = objects.filter(obj => obj.hasOwnProperty("label") && obj["_gvid"] == from)[0];
        let toNode = objects.filter(obj => obj.hasOwnProperty("label") && obj["_gvid"] == to)[0];

        let edgeNodes = [fromNode, toNode];

        // Compute JS version of this edge node.
        let edgeNodeJSVals = edgeNodes.map(node => {
            // Spec that records the reachable edges from TLC generated state graph.
            let specOfTLCReachableEdges = tlcReachableEdgesSpec(testId, specVariables, node)

            // Parse this generated spec and record its initial states.
            enableEvalTracing = false; // turn off tracing here to avoid pollution of main eval logs.
            spec = new TLASpec(specOfTLCReachableEdges, specPath);
            spec.parseSync();

            parsedTLCSpec = spec.spec_obj;
            let nodeVal = interp.computeReachableStates(parsedTLCSpec, constvals, undefined, spec)["states"];
            assert(nodeVal.length === 1);
            return nodeVal[0];
        });

        console.log("edge node JS", edgeNodeJSVals);
        reachableEdgesTLC.push(edgeNodeJSVals);
    }

    console.log("edges reachable JS  :", reachableEdges);
    console.log("edges reachable TLC :", reachableEdgesTLC);
    console.log("----------------------");
    // console.log("eq:", arrEq(reachable, reachableTLC));

    // Compute fingerprints for each edge by concatenating fingerprints of the edge nodes.
    let jsEdgeFingerprints = reachableEdges.map(e => e[0].fingerprint() + "-" + e[1].fingerprint());
    let tlcEdgeFingerprints = reachableEdgesTLC.map(e => e[0].fingerprint() + "-" + e[1].fingerprint());

    let edgesAreEquiv = arrEq(jsEdgeFingerprints, tlcEdgeFingerprints);

    let edgesDiffInJS = _.differenceBy(reachableEdges, reachableEdgesTLC, e => e[0].fingerprint() + "-" + e[1].fingerprint());
    let edgesDiffInTLC = _.differenceBy(reachableEdgesTLC, reachableEdges, e => e[0].fingerprint() + "-" + e[1].fingerprint());
    // console.log("edgesDiff:", edgesDiff);

    const duration = (performance.now() - start).toFixed(1);

    let statusObj = {
        "initial_states_equiv": initAreEquiv,
        "pass": initAreEquiv && edgesAreEquiv,
        "initialJS": initial,
        "initialTLC": initialTLC,
        "reachableJS": [], // reachable,
        "reachableTLC": [], //reachableTLC,
        "reachableEdgesJS": reachableEdges,
        "reachableEdgesTLC": reachableEdgesTLC,
        "initStatesDiffInJS": initDiffInJS,
        "initStatesDiffInTLC": initDiffInTLC,
        "edgesDiffInJS": edgesDiffInJS,
        "edgesDiffInTLC": edgesDiffInTLC,
        "duration_ms": duration
    }
    return statusObj;

}

(async () => {

    // Set up parser.
    await TreeSitter.init();
    parser = new TreeSitter();

    const newLanguageName = "tlaplus";
    const url = `${LANGUAGE_BASE_URL}/tree-sitter-${newLanguageName}.wasm`
    let lang = await TreeSitter.Language.load(url);
    parser.setLanguage(lang);

    let tree = null;

    // let testsDiv = document.getElementById("tests");
    let initExpected;
    let nextExpected;

    // Set of specs whose reachable states we test for JS <-> TLC conformance.
    testGroups = {
        "General": [
            { "spec": "simple1_multiline_block_comment", "constvals": undefined },
            { "spec": "simple2", "constvals": undefined },
            { "spec": "simple3", "constvals": undefined },
            { "spec": "simple5", "constvals": undefined },
            { "spec": "S1", "constvals": undefined },
            { "spec": "simple_arith", "constvals": undefined },
            { "spec": "simple_boolean", "constvals": undefined },
            { "spec": "simple_negation", "constvals": undefined },
            { "spec": "simple_domain", "constvals": undefined },
            { "spec": "simple_implies", "constvals": undefined },
            { "spec": "simple_inline_comment", "constvals": undefined },
            { "spec": "simple_inline_comment_conj", "constvals": undefined },
            { "spec": "simple_inline_comment_constant", "constvals": {"C": new IntValue(44), "D": new IntValue(55)} },
            { "spec": "simple_definition", "constvals": undefined },
            { "spec": "simple_definition2", "constvals": undefined },
            { "spec": "simple6", "constvals": undefined },
            { "spec": "simple7", "constvals": undefined },
            { "spec": "simple8", "constvals": undefined },
            { "spec": "simple_constant_operator", "constvals": {"Op": "NewOp"} },
            { "spec": "simple_constant_operator_infix", "constvals": {"|": "NewOp"} },
            { "spec": "simple_infix_def", "constvals": undefined },
            { "spec": "simple_enabled", "constvals": undefined },
            { "spec": "simple_fcn_literal", "constvals": undefined },
            { "spec": "simple_fcn_def", "constvals": undefined },
            { "spec": "simple_lazy", "constvals": undefined },
            { "spec": "simple_subset", "constvals": undefined },
            { "spec": "simple_quant", "constvals": undefined },
            { "spec": "simple_quant2", "constvals": undefined },
            { "spec": "simple_setfiltermap", "constvals": undefined },
            { "spec": "simple_set_of_fns", "constvals": undefined },
            { "spec": "simple_disjunction_constant", "constvals": undefined },
            { "spec": "simple_conjunction_constant", "constvals": undefined },
            { "spec": "simple_disjunction_init", "constvals": undefined },
            { "spec": "simple_quant_multi", "constvals": undefined },
            { "spec": "simple_defined_var_assignment", "constvals": undefined },
            { "spec": "simple_defined_var_assignment_transitive", "constvals": undefined },
            { "spec": "simple_quant_tuple", "constvals": undefined },
            { "spec": "simple_multiline", "constvals": undefined },
            { "spec": "simple_letin", "constvals": undefined },
            { "spec": "simple_letin_fn_def", "constvals": undefined },
            { "spec": "simple_operator", "constvals": undefined },
            { "spec": "simple_lambda", "constvals": undefined },
            { "spec": "simple_lambda_letin", "constvals": undefined },
            { "spec": "simple_nested_lambda", "constvals": undefined },
            { "spec": "simple_folds", "constvals": undefined },
            { "spec": "simple_seq", "constvals": undefined },
            { "spec": "simple_strings", "constvals": undefined },
            { "spec": "simple_if_then", "constvals": undefined },
            { "spec": "simple_record", "constvals": undefined },
            { "spec": "simple_recursive", "constvals": undefined },
            { "spec": "simple_seq_update", "constvals": undefined },
            { "spec": "simple_seq_update2", "constvals": undefined },
            { "spec": "simple_sets", "constvals": undefined },
            { "spec": "simple_fcn_polymorphism", "constvals": undefined },
            { "spec": "simple_seq_update3", "constvals": undefined},
            { "spec": "simple_primed", "constvals": undefined },
            { "spec": "simple_primed_defs", "constvals": undefined },
            { "spec": "simple_var_tuple", "constvals": undefined },
            { "spec": "simple_choose", "constvals": undefined },
            { "spec": "simple_tlc_fn", "constvals": undefined },
            { "spec": "simple_tlc_fn_compose", "constvals": undefined },
            { "spec": "simple_tlc_ops", "constvals": undefined },
            { "spec": "set_dot_notation", "constvals": undefined },
            { "spec": "record_literal_eval", "constvals": undefined },
            { "spec": "seq_append", "constvals": undefined },
            { "spec": "empty_domain_and_seq", "constvals": undefined },
            { "spec": "primed_tuple", "constvals": undefined },
            { "spec": "mldr_init_only", "constvals": undefined },
            { "spec": "tla_expr_eval", "constvals": undefined },
            { "spec": "tla_case_with_state_assignment", "constvals": undefined },
            { "spec": "simple_mod3_counter", "constvals": undefined },
            { "spec": "pre_module_comments", "constvals": undefined },
            { "spec": "lockserver_nodefs", "constvals": undefined },
            { "spec": "lockserver_nodefs1", "constvals": undefined },
            { "spec": "conj_parsing", "constvals": undefined },
            { "spec": "operator_param_clash_before_var_def", "constvals": undefined },
            { "spec": "operator_param_clash_before_const_def", "constvals": {"c": new IntValue(12)} },
            // TODO: Re-enable this test once we figure out to deal with interaction b/w declarations and module imports.
            // { "spec": "operator_param_clash_before_var_def_inter", "constvals": undefined },
            { "spec": "def_before_var_decl", "constvals": undefined },
            {
                "spec": "lockserver_constant_comment",
                "constvals": {
                    "Server": new SetValue([new StringValue("s1"), new StringValue("s2")]),
                    "Client": new SetValue([new StringValue("c1"), new StringValue("c2")])
                }
            },

        ],
    "UNCHANGED": [
        { "spec": "simple_unchanged_no_tuple", "constvals": undefined },
        { "spec": "simple_unchanged_nested_def", "constvals": undefined },
        { "spec": "simple_unchanged_nested_tuple_def", "constvals": undefined },
        { "spec": "simple_unchanged_nested_tuple", "constvals": undefined },
        { "spec": "simple_unchanged", "constvals": undefined },
        { "spec": "simple_unchanged_with_quant", "constvals": undefined },
        { "spec": "lockserver_nodefs_unchanged", "constvals": undefined },
    ],
    "Module instantiation": [
        { "spec": "simple_extends", "constvals": undefined },
        { "spec": "simple_extends_local_def", "constvals": undefined },
        { "spec": "simple_extends_instance", "constvals": undefined },
        { "spec": "simple_extends_instance_transitive", "constvals": undefined },
        { "spec": "simple_extends_instance_def", "constvals": undefined },
        { "spec": "simple_extends_instance_def_user_infix_op", "constvals": undefined },
        { "spec": "simple_extends_instance_def_transitive", "constvals": undefined },
        { "spec": "simple_extends_instance_def_transitive_import", "constvals": undefined },
        { "spec": "simple_extends_instance_duplicate_def_names", "constvals": undefined },
        { "spec": "simple_extends_with_var", "constvals": undefined },
        { "spec": "simple_extends_with_var_and_const", "constvals": {"d": new IntValue(22)} }
    ],
    "Module instantiation with substitution": [
        { "spec": "simple_extends_instance_with_const_subst", "constvals": undefined },
        { "spec": "simple_extends_instance_with_var_subst", "constvals": undefined },
        { "spec": "simple_extends_instance_def_with_subst", "constvals": undefined },
        { "spec": "simple_extends_instance_def_with_var_subst_one_implicit", "constvals": undefined },
        { "spec": "simple_extends_instance_def_with_var_subst_same_name", "constvals": undefined },
        { "spec": "simple_extends_instance_with_var_subst_identity", "constvals": undefined },
        { "spec": "simple_extends_instance_def_with_var_subst_default_name", "constvals": undefined },
        { "spec": "simple_extends_instance_with_var_and_const_subst", "constvals": undefined },
        { "spec": "simple_extends_instance_with_var_and_const_subst_transitive", "constvals": undefined },
        { "spec": "simple_extends_instance_def_with_var_subst", "constvals": undefined },
        { "spec": "simple_extends_instance_def_with_var_subst_and_primed_action", "constvals": undefined },
        { "spec": "simple_extends_instance_def_parameterized_var_subst_no_clash", "constvals": undefined },
        { "spec": "simple_extends_instance_def_parameterized_var_subst_with_clash", "constvals": undefined },
        { "spec": "simple_extends_instance_def_parameterized", "constvals": undefined },
    ],
    "Large Specs": [
        { "spec": "EWD998_regression1", "constvals": undefined },
        { "spec": "EWD998_bounded1", "constvals": undefined },
        { "spec": "EWD998_depth_bounded1", "constvals": undefined },
        { "spec": "AsyncTerminationDetection_init", "constvals": undefined },
        { "spec": "AsyncTerminationDetection", "constvals": undefined },
        { "spec": "Paxos_1a", "constvals": undefined },
        { "spec": "Paxos_1b_case1", "constvals": undefined },
        { "spec": "NQueens_N3", "constvals": { "N": new IntValue(3) } },
        { "spec": "TwoPhase", "constvals": undefined },
        { "spec": "TwoPhase_RMPrepare", "constvals": undefined },
        { "spec": "LogExample_bounded", "constvals": undefined },
        { "spec": "Elevator", "constvals": undefined },
        {
            "spec": "Prisoners",
            "constvals": {
                "Prisoner": new SetValue([new StringValue("p1"), new StringValue("p2"), new StringValue("p3")]),
                "Counter": new StringValue("p1")
            }
        },
        {
            "spec": "ShardTxn",
            "constvals": {
                "Keys": new SetValue([new StringValue("k1")]),
                "Values": new SetValue([new StringValue("t1")]),
                "RC": new StringValue("linearizable"),
                "WC": new StringValue("majority"),
                "NoValue": new StringValue("NoValue"),
                "STMTS": new IntValue(1),
            }
        },
        {
            "spec": "TxnsMoveRange",
            "constvals": {
                "MIGRATIONS": new IntValue(1),
                "TXN_STMTS": new IntValue(1),
                "Txns": new SetValue([new StringValue("t1")]),
                "NameSpaces": new SetValue([new StringValue("ns1")]),
                "Shards": new SetValue([new StringValue("s1"), new StringValue("s2")]),
                "Keys": new SetValue([new StringValue("k1"), new StringValue("k2")]),
            }
        },
        {
            "spec": "RaftMongo",
            "constvals": {
                "Server": new SetValue([new StringValue("n1")]),
                "Follower": new StringValue("Follower"),
                "Leader": new StringValue("Leader"),
                "Candidate": new StringValue("Candidate"),
                "Nil": new StringValue("Nil"),
            }
        },
        {
            "spec": "AbstractRaft_BecomeLeader",
            "constvals": {
                "Server": new SetValue([new StringValue("n1"), new StringValue("n2"), new StringValue("n3")]),
                "Secondary": new StringValue("Secondary"),
                "Primary": new StringValue("Primary"),
                "Nil": new StringValue("Nil"),
                "InitTerm": new IntValue(0),
            }
        },
        {
            "spec": "RaftWithReconfigBroken_Bounded", 
            "constvals": {
                "Server": new SetValue([new StringValue("s1"), new StringValue("s2"), new StringValue("s3")]), 
                // TODO: Set this to correct function value.
                "MaxTerm": new IntValue(2),
                "MaxLogLen": new IntValue(2),
            }        
        },
        {
            "spec": "show521677",
            "constvals": {
                "StrongConsistency" : new StringValue("StrongConsistency"),
                "BoundedStaleness" : new StringValue("BoundedStaleness"),
                "SessionConsistency" : new StringValue("SessionConsistency"),
                "ConsistentPrefix" : new StringValue("ConsistentPrefix"),
                "EventualConsistency" : new StringValue("EventualConsistency"),
                "StalenessBound": new IntValue(1),
                "VersionBound": new IntValue(3)
            }
        },
        // { "spec": "TestLinQueue", "constvals": undefined },
        {"spec": "DieHard", "constvals": undefined},
        {
            "spec": "DieHarder", 
            "constvals": {
                "Jug": new SetValue([new StringValue("j1"), new StringValue("j2")]), 
                // TODO: Set this to correct function value.
                "Capacity": new FcnRcdValue(
                    [new StringValue("j1"), new StringValue("j2")],
                    [new IntValue(3), new IntValue(5)],
                )
            }        
        },
        { "spec": "Microwave", "constvals": {
            "ImplementStartSafety": new BoolValue(false),
            "ImplementOpenDoorSafety": new BoolValue(false),
        } },
        // { "spec": "Consistency", "constvals": undefined },
    ],
    "Semantic Errors": [
        {  
            "spec": "semantic_error1", 
            "constvals": undefined, 
            "isSemanticErrorTest": true,
            "errLine": 10
        },
    ],
}

    const urlSearchParams = new URLSearchParams(window.location.search);
    const params = Object.fromEntries(urlSearchParams.entries());
    const arg = params["test"];

    let allTestsList = [];
    for(const [key, value] of Object.entries(testGroups)) {
        allTestsList.push(...value);
    }

    // Allow URL arg to choose which test to run.
    let testsToRun;
    if (arg === "all" || arg === undefined) {
        testsToRun = testGroups;
        // testsToRun = allTestsList;
    } else {
        testsToRun = allTestsList.filter(t => t["spec"] === arg);
    }

    function createTestStatusElems(tests) {
        // For when running a single test.
        if (tests instanceof Array) {
            tests = { "": tests }
        }

        let testsDiv = document.getElementById("tests");
        // let isSingleTest = urlParams.hasOwnProperty("test");
        let testTable = document.createElement("table");
        testTable.id = "test_table";
        testsDiv.appendChild(testTable);
        let testHeader = document.createElement("tr");
        let testHeaderName = document.createElement("th");
        let testHeaderStatus = document.createElement("th");
        testHeaderName.innerHTML = "Test";
        testHeaderStatus.innerHTML = "Status";
        testHeader.appendChild(testHeaderName);
        testHeader.appendChild(testHeaderStatus);
        testTable.appendChild(testHeader);

        for (var group in tests) {

            let testHeader = document.createElement("div");
            testHeader.innerHTML = `<h3 style="margin-top: 10px;">${group}</h3>`;
            testTable.appendChild(testHeader);

            for (var test of tests[group]) {
                let testId = test["spec"];
                console.log("testid:", testId);
                // Show the spec text and test name first.
                let testHeader = document.createElement("div");
                testHeader.innerHTML = `<b>Test: <a href='?test=${testId}&debug=0'> ${testId} </a></b>`;
                if (!urlParams.hasOwnProperty("test")) {
                    testHeader.href = "?test=" + testId;
                } else {
                    testHeader.setAttribute("onclick", `toggleTestDetails(\"${testId}\")`);
                }
                // testHeader.style = "cursor:pointer";
                // testHeader.setAttribute("onclick", `toggleTestDetails(\"${testId}\")`);
                // testsDiv.appendChild(testHeader);

                let statusText = "STATUS: -"; //(areEquiv ? "PASS &#10003" : "FAIL &#10007");
                let statusColor = "gray"; // areEquiv ? "green" : "red";
                div = document.createElement("div");
                div.id = "test_status-" + testId;
                div.innerHTML = statusText;
                div.style = "margin-bottom:5px; font-weight: bold; color:" + statusColor;

                let testRow = document.createElement("tr");
                let testColName = document.createElement("td");


                testColName.innerHTML = `<b><a href='?test=${testId}&debug=1'> ${testId} </a></b>`;
                if (!urlParams.hasOwnProperty("test")) {
                    testHeader.href = "?test=" + testId;
                } else {
                    testHeader.setAttribute("onclick", `toggleTestDetails(\"${testId}\")`);
                }


                let testColStatus = document.createElement("td");
                // testColName.innerHTML = testId;
                testColStatus.innerHTML = statusText;
                testColStatus.id = "test_status-" + testId;

                testRow.appendChild(testColName);
                testRow.appendChild(testColStatus);
                testTable.appendChild(testRow);
                // testsDiv.appendChild(div);
            }
        }

        // infoDiv.appendChild(computedDiv);
        // infoDiv.appendChild(oracleDiv);
        // testsDiv.appendChild(infoDiv);
    }

    createTestStatusElems(testsToRun);

    function handleTestResult(test, statusObj) {
        let testsDiv = document.getElementById("tests");
        let statusDiv = document.getElementById("test_status-" + test["spec"]);
        if (statusObj["pass"]) {
            statusDiv.style = "margin-bottom:5px; font-weight: bold; color:" + "green";
            statusDiv.innerHTML = "STATUS: PASS &#10003 (" + (statusObj["duration_ms"] + "ms)");
        } else {
            statusDiv.style = "margin-bottom:5px; font-weight: bold; color:" + "red";
            statusDiv.innerHTML = "STATUS: FAIL &#10007 (" + statusObj["duration_ms"] + "ms)";
        }

        // Show generated spec with reachable states for debugging single tests.
        let isSingleTest = urlParams.hasOwnProperty("test");
        // if (isSingleTest) {
        // let genSpecBlock = document.createElement("div");
        // genSpecBlock.style = "margin-top:10px;";
        // genSpecBlock.style = "margin-top:10px;border:solid;width:40%;";
        // genSpecBlock.innerHTML = "<div> TLC reachable states: </div>";
        // genSpecBlock.innerHTML += "<pre>" + specOfTLCReachableStates + "</pre>";
        // testsDiv.appendChild(genSpecBlock);
        // }

        if (!statusObj["pass"] && isSingleTest && !test["isSemanticErrorTest"]) {
            let reachableEdges = statusObj["reachableEdgesJS"];
            let reachableEdgesTLC = statusObj["reachableEdgesTLC"];

            infoDiv = document.createElement("div");
            infoDiv.style = "width:100%";

            statesDiffDiv = document.createElement("div");
            statesDiffDiv.style = "float:left;border:solid;padding:4px;margin:3px; min-width:20%;width:60%;";

            // Init states diff.
            if(statusObj["initStatesDiffInJS"].length + statusObj["initStatesDiffInTLC"].length > 0){
                statesDiffDiv.innerHTML = "<h4>States diff</h4>";
                statesDiffDiv.innerHTML += `${statusObj["initStatesDiffInJS"].length} initial states computed by JS, but not by TLC.<br>`;

                for (const s of statusObj["initStatesDiffInJS"]) {
                    statesDiffDiv.innerHTML += `<pre>(${s.fingerprint()})</pre>`;
                    statesDiffDiv.innerHTML += `<pre>${s.toString()}</pre>`;
                }

                statesDiffDiv.innerHTML += `${statusObj["initStatesDiffInTLC"].length} initial states computed by TLC, but not by JS.<br>`;
                for (const s of statusObj["initStatesDiffInTLC"]) {
                    statesDiffDiv.innerHTML += `<pre>(${s.fingerprint()})</pre>`;
                    statesDiffDiv.innerHTML += `<pre>${s.toString()}</pre>`;
                }

                infoDiv.appendChild(statesDiffDiv);
            }

            edgesDiffDiv = document.createElement("div");
            edgesDiffDiv.style = "float:left;border:solid;padding:4px;margin:3px; min-width:20%;width:60%;";

            // if(statusObj["edgesDiffInTLC"].length > 0){
            //     edgesDiffDiv.innerHTML += `${statusObj["edgesDiffInTLC"].length} edges that were generated by TLC, but not generated by JS interpreter.`;

            //     for (const e of statusObj["edgesDiffInTLC"]) {
            //         edgesDiffDiv.innerHTML += `<pre>(${e[0].fingerprint()})</pre>`;
            //         edgesDiffDiv.innerHTML += `<pre>${e[0].toString()}</pre>`;
            //     }
            // }

            // Edges diff.
            edgesDiffDiv.innerHTML = "<h4>Edges diff</h4>";
            if(statusObj["edgesDiffInJS"].length > 0){
                edgesDiffDiv.innerHTML += `${statusObj["edgesDiffInJS"].length} edges that were generated by JS interpreter, but not generated by TLC.`;

                for (const e of statusObj["edgesDiffInJS"]) {
                    edgesDiffDiv.innerHTML += `<pre>FROM (${e[0].fingerprint()}):</pre>`;
                    edgesDiffDiv.innerHTML += `<pre>${e[0].toString()}</pre>`;
                    edgesDiffDiv.innerHTML += `<pre>TO (${e[1].fingerprint()}):</pre>`;
                    edgesDiffDiv.innerHTML += `<pre>${e[1].toString()}</pre>`;
                    edgesDiffDiv.innerHTML += "<pre>-----------</pre>";
                }
            }
            if(statusObj["edgesDiffInTLC"].length > 0){
                edgesDiffDiv.innerHTML += `${statusObj["edgesDiffInTLC"].length} edges that were generated by TLC, but not generated by JS interpreter.`;

                for (const e of statusObj["edgesDiffInTLC"]) {
                    edgesDiffDiv.innerHTML += `<pre>FROM (${e[0].fingerprint()}):</pre>`;
                    edgesDiffDiv.innerHTML += `<pre>${e[0].toString()}</pre>`;
                    edgesDiffDiv.innerHTML += `<pre>TO (${e[1].fingerprint()}):</pre>`;
                    edgesDiffDiv.innerHTML += `<pre>${e[1].toString()}</pre>`;
                    edgesDiffDiv.innerHTML += "<pre>-----------</pre>";
                }
            }

            infoDiv.appendChild(edgesDiffDiv);


            // JS computed states.
            jsComputedDiv = document.createElement("div");
            jsComputedDiv.style = "float:left;border:solid;padding:4px;margin:3px; min-width:20%;width:60%;";
            jsComputedDiv.innerHTML = "<h4>State graph computed by JS</h4>";
            jsComputedDiv.innerHTML += `${statusObj["initialJS"].length} initial states, ${reachableEdges.length} reachable edges`;

            // Print JS initial states.
            jsComputedDiv.innerHTML += "<br><b>Initial</b><br>";
            let initialJSSorted = _.sortBy(statusObj["initialJS"], v => v.fingerprint());
            for (const s of initialJSSorted) {
                jsComputedDiv.innerHTML += `<pre>(${s.fingerprint()})</pre>`;
                jsComputedDiv.innerHTML += `<pre>${s.toString()}</pre>`;
            }

            // Print JS edges.
            jsComputedDiv.innerHTML += "<br><b>Edges</b><br>";
            let reachableEdgesSorted = _.sortBy(reachableEdges, v => v[0].fingerprint() + "-" + v[1].fingerprint());
            for (const s of reachableEdgesSorted) {
                jsComputedDiv.innerHTML += `<pre>FROM (${s[0].fingerprint()}):</pre>`;
                jsComputedDiv.innerHTML += `<pre>${s[0].toString()}</pre>`;
                jsComputedDiv.innerHTML += `<pre>TO (${s[1].fingerprint()}):</pre>`;
                jsComputedDiv.innerHTML += `<pre>${s[1].toString()}</pre>`;
                jsComputedDiv.innerHTML += "<pre>-----------</pre>";
            }

            // TLC computed states.
            tlcOracleDiv = document.createElement("div");
            tlcOracleDiv.style = "float:left;border:solid;padding:4px;margin:3px; min-width:20%;width:60%;";
            tlcOracleDiv.innerHTML = "<h4>State graph computed by TLC</h4>";
            tlcOracleDiv.innerHTML += `${statusObj["initialTLC"].length} initial states, ${reachableEdgesTLC.length} reachable edges`;

            // Print TLC initial states.
            tlcOracleDiv.innerHTML += "<br><b>Initial</b><br>";
            let initialTLCSorted = _.sortBy(statusObj["initialTLC"], v => v.fingerprint());
            for (const s of initialTLCSorted) {
                tlcOracleDiv.innerHTML += `<pre>(${s.fingerprint()})</pre>`;
                tlcOracleDiv.innerHTML += `<pre>${s.toString()}</pre>`;
            }

            // Print TLC edges.
            tlcOracleDiv.innerHTML += "<br><b>Edges</b><br>";
            let reachableEdgesTLCSorted = _.sortBy(reachableEdgesTLC, v => v[0].fingerprint() + "-" + v[1].fingerprint());
            for (const s of reachableEdgesTLCSorted) {
                tlcOracleDiv.innerHTML += `<pre>FROM (${s[0].fingerprint()}):</pre>`;
                tlcOracleDiv.innerHTML += `<pre>${s[0].toString()}</pre>`;
                tlcOracleDiv.innerHTML += `<pre>TO (${s[1].fingerprint()}):</pre>`;
                tlcOracleDiv.innerHTML += `<pre>${s[1].toString()}</pre>`;
                tlcOracleDiv.innerHTML += "<pre>-----------</pre>";
            }
            infoDiv.appendChild(jsComputedDiv);
            infoDiv.appendChild(tlcOracleDiv);
            testsDiv.appendChild(infoDiv);
        }
    }

    function fetchTestSpec(test, onCompleteFn) {
        let specStatesPath = `./specs/with_state_graphs/${test["spec"]}.tla.dot.json`;
        let specPath = `./specs/with_state_graphs/${test["spec"]}.tla`;

        let fetchGraph, fetchSpec;
        // For error tests we don't need to fetch the TLC generated state graph.
        if(test["isSemanticErrorTest"]) {
            fetchGraph = Promise.resolve(null);
            fetchSpec = fetch(specPath).then(response => response.text());
        } else{
            fetchGraph = fetch(specStatesPath).then(response => response.json());
            fetchSpec = fetch(specPath).then(response => response.text());
        }
      
        return Promise.all([fetchGraph,fetchSpec]).then(function([specStateGraph, specText]){
            // console.log("graph:", specStateGraph);
            // console.log("text:", specText);

            // Test spec by comparing its state graph to the one generated by TLC.
            let spec = new TLASpec(specText, specPath);
            totalLOC += specText.split("\n").length
            spec.parse().then(function () {
                return spec.spec_obj;
            }).then(function (parsedSpec) {
                console.log("The parsed spec:", parsedSpec);
                if(test["isSemanticErrorTest"]) {
                    return testSemanticError(test, parsedSpec, specPath, test["constvals"], spec);
                }
                return testStateGraphEquiv(test["spec"], specStateGraph, parsedSpec, specPath, test["constvals"], spec, test["isSemanticErrorTest"])
            }).then(function (statusObj) {
                handleTestResult(test, statusObj);
                onCompleteFn();
            }).catch(function (err) {
                // Continue on error to run other tests.
                console.error(err);
                handleTestResult(test, { "pass": false, "duration_ms": 0, "error": true });
                onCompleteFn();
            });
        })
    }

    function testAllSpecs(tests, onTestCompletion) {
        if (tests.length === 0) {
            onTestCompletion();
            return;
        }
        // Run this test, and then recurse on the remaining tests.
        fetchTestSpec(tests[0], function () {
            testAllSpecs(tests.slice(1), onTestCompletion);
        });
    }

    function onTestCompletion() {
        console.log("All tests finished running.");
        console.log("total spec test LOC: ", totalLOC);
    }

    // Run all tests sequentially.
    if(testsToRun instanceof Array){
        testAllSpecs(testsToRun, onTestCompletion);
    } else{
        testAllSpecs(allTestsList, onTestCompletion);
    }



    // Fetch all specs and state graphs first, then execute the tests.
    // N.B. Disabled since it overloads browser window.
    // let allReqs = testsToRun.map(fetchTestSpec);

    // $.when(...allReqs).done(function () {
    //     // console.log("ARGUMENTS:", arguments);
    //     const start = performance.now();

    //     // Run the specified tests.
    //     for (var i = 0; i < testsToRun.length; i++) {
    //     // for (var i = 0; i < 1; i++) {
    //             test = testsToRun[i];
    //         specText = arguments[i][0]
    //         specStateGraph = arguments[i][1]
    //         console.log(`Running test '${test["spec"]}'`);
    //         try {
    //             testStateGraphEquiv(test["spec"], specStateGraph, specText, test["constvals"]);
    //         } catch (e) {
    //             // TODO: Handle exceptions more appropriately inside this block.
    //             console.error(e);
    //             return;
    //         }
    //     }

    //     // Measure test duration.
    //     const duration = (performance.now() - start).toFixed(1);
    //     console.log(`All tests ran in ${duration}ms`);
    //     let durationDiv = document.getElementById("test-duration");
    //     durationDiv.style = "margin-top:25px;";
    //     durationDiv.innerText = `All ${testsToRun.length} tests ran in ${duration}ms`;
    // });

})();