//
// TLA+ web explorer UI logic.
//

let tree;
let parser;
let languageName = "tlaplus";

let vizInstance = null;

let Pane = {
    Constants: 1,
    Trace: 2
}

let Tab = {
    StateSelection: 1,
    Constants: 2,
    SpecEditor: 3,
    Load: 4,
    EvalGraph: 5
}

let TraceTab = {
    Trace: 1,
    REPL: 2,
    Animation: 3,
    Check: 4 // Added Check tab
}

let model = {
    specText: null,
    allInitStates: [],
    nextStatePred: null,
    currState: null,
    currNextStates: [],
    currNextStatesAlias: [],
    currTrace: [],
    currTraceActions: [],
    currTraceAliasVals: [],
    forwardHistory: [], // Stack to store states we've stepped back from
    forwardHistoryActions: [], // Stack to store actions we've stepped back from
    spec: null,
    specTreeObjs: null,
    specDefs: null,
    specConsts: null,
    specConstInputVals: {},
    specConstVals: {},
    parser: null,
    traceExprInputText: "",
    traceExprs: [],
    hiddenStateVars: [],
    // State hash that trace lasso goes back to.
    lassoTo: null,
    errorObj: null,
    currPane: Pane.Trace,
    tracePaneHidden: false,
    nextStatePreview: null,
    replMode: false,
    replResult: null,
    replError : false,
    constantsPaneHidden: false,
    selectedTab: Tab.SpecEditor,
    selectedTraceTab: TraceTab.Trace,
    rootModName: "",
    debug: false,
    showLoadFileBox: false,
    loadSpecFailed: false,
    specUrlInputText: "",
    specEditorChanges: [],
    enableAnimationView: false,
    explodedConstantExpr: null,
    generatingInitStates: false,
    // Special definition that will enable animation feature.
    animViewDefName: "AnimView",
    lockedTrace: null,
    lockedTraceActions: null,
    showStateDiffsInSelection: false,
    copyLinkPressCooldown: false,
    invariantExprToCheck: "",
    invariantViolated: false,
    invariantCheckerRunning: false,
    invariantCheckingDuration: 0,
    // Trace loading state
    traceLoadingWorker: null,
    traceLoadingInProgress: false,
    traceLoadingProgress: { currentState: 0, totalStates: 0 }, // 0-100
    traceLoadingError: null,
    traceLoadingStart: null
}

const exampleSpecs = {
    "TwoPhase": {
        specpath: "./specs/TwoPhase.tla",
    },
    "TwoPhase (animated)": {
        specpath: "./specs/TwoPhase_anim.tla",
        constant_vals: {
            "RM": "{rm1,rm2}",
        }
    },
    "TeachingConcurrency": {
        specpath: "./specs/Simple.tla",
        constant_vals: {
            "N": "3",
        }
    },
    "lockserver": {
        specpath: "./specs/lockserver.tla",
        constant_vals: {
            "Server": "{s1,s2}",
            "Client": "{c1,c2}"
        }
    },
    "Paxos": {
        specpath: "./specs/Paxos.tla",
        constant_vals: {
            "Acceptor": "{a1,a2,a3}",
            "Quorum": "{{a1,a2},{a2,a3},{a1,a3},{a1,a2,a3}}",
            "Proposer": "{p1,p2}",
            "Value": "{v1,v2}",
            "Ballot": "{0,1,2,3}",
            "None": "None"
        }
    },
    "Raft": {
        specpath: "./specs/AbstractRaft.tla",
        constant_vals: {
            "Server": "{s1,s2,s3}",
            "Primary": "\"Primary\"",
            "Secondary": "\"Secondary\"",
            "Nil": "\"Nil\"",
            "InitTerm": 0
        }
    },
    "Raft (animated)": {
        specpath: "./specs/AbstractRaft_anim.tla",
        constant_vals: {
            "Server": "{s1,s2,s3}",
            "Primary": "\"Primary\"",
            "Secondary": "\"Secondary\"",
            "Nil": "\"Nil\"",
            "InitTerm": 0
        }
    },
    "EWD998 (animated)": {
        specpath: "./specs/EWD998.tla",
        constant_vals: {
            "N": "3"
        }
    },
    "BlockingQueue (animated)": {
        specpath: "./specs/BlockingQueue.tla",
        constant_vals: {
            "Producers": "{p1,p2}",
            "Consumers": "{c}",
            "BufCapacity": 1
        }
    },
    "Battery Relay (animated)": {
        specpath: "./specs/BatteryRelay.tla",
        constant_vals: {
            "Cost": "[ Truck |-> 10, Car |-> 5, Bike |-> 2, Scooter |-> 1 ]",
            "MaxLevel": 17
        }
    },
    "Dining Philosophers (animated)": {
        specpath: "./specs/DiningPhilosophers.tla",
        constant_vals: {
            "N": 5
        }
    }

};

// The main app component.
let App;

// Parse URL params;
const urlSearchParams = new URLSearchParams(window.location.search);
const urlParams = Object.fromEntries(urlSearchParams.entries());
let enableEvalTracing = false;
let evalNodeGraphsPerAction = {};

let invCheckerWebWorker = null;

function displayStateGraph() {
    // TODO: Will need to flesh out this functionality further.

    let stategraphDiv = document.getElementById('stategraph');
    stategraphDiv.hidden = false;

    var cy = cytoscape({
        container: document.getElementById('stategraph'), // container to render in
        style: [
            {
                selector: 'node',
                style: {
                    'label': function (el) {
                        return JSON.stringify(el.data()["state"]);
                    },
                    "background-color": "lightgray",
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "black"
                }
            },
        ]
    });

    let reachable = computeReachableStates(specTreeObjs, specConstVals);
    let edges = reachable["edges"];
    console.log(reachable["edges"]);
    console.log(reachable);

    for (const state of reachable["states"]) {
        dataVal = { id: state.fingerprint(), state: state };
        console.log(dataVal);
        cy.add({
            group: 'nodes',
            data: dataVal,
            position: { x: 200, y: 200 }
        });
    }

    let eind = 0;
    for (const edge of edges) {
        cy.add({
            group: 'edges', data: {
                id: 'e' + eind,
                source: hashSum(edge[0]),
                target: hashSum(edge[1])
            }
        });
        eind++;
    }
    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle"
    })
    // let layout = cy.layout({name:"cose"});
    let layout = cy.layout({ name: "breadthfirst" });
    layout.run();
}


function displayEvalGraph(nodeGraph) {
    if(nodeGraph === undefined){
        nodeGraph = evalNodeGraph;
    }
    // return;
    console.log("#displayEvalGraph");
    let stategraphDiv = document.getElementById('eval-graph-pane');
    if(stategraphDiv === null){
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
                style: {
                    'label': function (el) {
                        // Only show expression type in the main label
                        return el.data().expr_type;
                    },
                    // Make nodes wider to accommodate text
                    "width": function(el) {
                        // Calculate width based on text length, with minimum size
                        let textLength = el.data().expr_type.length;
                        return Math.max(15, textLength * 8);
                    },
                    "height": 20,
                    "background-color": function(el){
                        if(el.data().expr_type === "conj_list"){
                            return "#FFD699"; // Light orange
                        }
                        if(el.data().expr_text.includes("' = ")) {
                            return "#FFB3B3"; // Light red
                        }
                        return "#B3D9FF"; // Light blue
                    },
                    "text-valign": "center",
                    "text-halign": "center",
                    "text-wrap": "wrap",
                    "text-max-width": function(el) {
                        // Allow text to wrap within node width
                        return el.width() - 4;
                    },
                    "border-style": "solid",
                    "border-width": "1",
                    "border-color": "gray",
                    "font-family": "monospace",
                    "font-size": "8px",
                    "shape": "rectangle",
                    "padding": "2px"
                }
            },
        ]
    });

    let nodes = _.uniqBy(_.flatten(nodeGraph.map(d => d[0])), "textId")
    for (const node of nodes) {
        cy.add({
            group: 'nodes',
            data: { 
                id: hashSum(node.textId), 
                expr_text: node.textId,
                expr_type: node.type
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
                source: hashSum(edge[0].textId),
                target: hashSum(edge[1].textId),
                label: edgeOrder + "(" + retVal.length + ") [" + evalDur + "ms]"
            }
        });
        eind++;
    }
    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle",
        "font-family": "monospace",
        "font-size": "10px",
        "color": "blue",
        "width": 2,
        "label": function (el) {
            return el.data().label;
        }
    })

    // Add tooltips for nodes
    cy.on('mouseover', 'node', function(evt) {
        let node = evt.target;
        let tooltip = document.createElement('div');
        tooltip.className = 'cytoscape-tooltip';
        tooltip.style.position = 'absolute';
        tooltip.style.backgroundColor = 'white';
        tooltip.style.border = '1px solid #ccc';
        tooltip.style.padding = '5px';
        tooltip.style.borderRadius = '3px';
        tooltip.style.fontFamily = 'monospace';
        tooltip.style.fontSize = '12px';
        tooltip.style.zIndex = '1000';
        tooltip.style.maxWidth = '300px';
        tooltip.style.wordWrap = 'break-word';
        tooltip.innerHTML = node.data('expr_text');
        
        document.body.appendChild(tooltip);
        
        function updateTooltipPosition() {
            let pos = node.renderedPosition();
            let containerPos = stategraphDiv.getBoundingClientRect();
            tooltip.style.left = (containerPos.left + pos.x + 10) + 'px';
            tooltip.style.top = (containerPos.top + pos.y - 10) + 'px';
        }
        
        updateTooltipPosition();
        node.on('position', updateTooltipPosition);
    });

    cy.on('mouseout', 'node', function(evt) {
        let tooltip = document.querySelector('.cytoscape-tooltip');
        if (tooltip) {
            tooltip.remove();
        }
        evt.target.removeListener('position');
    });

    let layout = cy.layout({ name: "dagre", nodeDimensionsIncludeLabels: true });
    cy.resize();
    layout.run();
}

// TODO: Implement this properly.
function toggleSpec() {
    let pane = document.getElementById("code-input-pane");
    pane.style.width = "0%";
}

// Set a CONSTANT value to a string value equal to the name of the CONSTANT declaration.
function setConstantAsString(constDecl){
    model.specConstInputVals[constDecl] = '"' + constDecl + '"';
}

function setConstantAsModelValue(constDecl){
    model.specConstInputVals[constDecl] = constDecl;
}

function toggleHiddenConstants(){
    model.constantsPaneHidden = !model.constantsPaneHidden;
}

function componentChooseConstants(hidden) {
    // If there are CONSTANT declarations in the spec, we must
    // instantiate them with some concrete values.
    if (_.isEmpty(model.specConsts)) {
        return m("span", {}, "");
    }
    // console.log("Instantiating spec constants.");

    let chooseConstsElems = [];
    for (const constDecl in model.specConsts) {
        let newRow = m("tr", {}, [
            m("td", { style: { "vertical-align": "middle" } }, constDecl),
            m("td", { style: { "vertical-align": "middle" } }, "←"),
            m("td", {}, [
                m("div", { class: "input-group" }, [
                    m("input", {
                        class: "form-control form-control-sm",
                        id: `const-val-input-${constDecl}`,
                        "data-testid": `const-val-input-${constDecl}`,
                        style: {
                            "width": "220px"
                        },
                        oninput: (e) => model.specConstInputVals[constDecl] = e.target.value,
                        value: model.specConstInputVals[constDecl],
                        placeholder: "Enter TLA+ value."
                    }),
                    m("div", { class: "input-group-append" }, [ 
                    m("button", {
                        class: "btn btn-outline-secondary btn-sm",
                        style: {
                            "font-size": "14px"
                        },
                            onclick: () => setConstantAsModelValue(constDecl)
                        }, "Model Value")
                    ])
                ])
            ])
        ])
        chooseConstsElems.push(newRow);
    }

    chooseConstsTable = m("table", {id:"choose-constants-table"}, chooseConstsElems);


    function hideButtonDiv(){
        let text = model.constantsPaneHidden ? "Show CONSTANTs" : "Hide CONSTANTs";
        let hideButtonDiv = m("div", { id: "hide-constants-button", class: "btn btn-primary btn-sm", onclick: toggleHiddenConstants }, text)
        return hideButtonDiv;
    }

    function constantButtons(){
        let setButtonDiv = m("button", { 
            id: "set-constants-button", 
            "data-testid": "set-constant-config-button",
            class: "btn btn-sm btn-primary", 
            onclick: () => {
                setConstantValues();
                model.selectedTab = Tab.StateSelection;
            } 
        }, "Set CONSTANTs");
        if(model.constantsPaneHidden){
            // return [hideButtonDiv()];
        }
        return [setButtonDiv];
    }

    return m("div", {id: "constants-box", hidden: hidden}, [
        // m("div", { id: "constants-header" },
        //     [
                // Allow hiding of choose constants pane.
                // m("div", { id: "constants-title", class: "pane-title", onclick: function(x){
                //     model.constantsPaneHidden = !model.constantsPaneHidden;
                // }}, "CONSTANT Instantiation"),
        // m("div", { id: "set-constants-button" }, setButtonDiv),
        m("div", { id: "constant-buttons-div" }, constantButtons()),
            // ]),
        m("div", { id: "choose-constants-elems", hidden: model.constantsPaneHidden }, chooseConstsTable),
    ]);
}


function componentNextStateChoiceElementForAction(ind, actionLabel, nextStatesForAction) {
    let actionDisabled = (nextStatesForAction.length === 0);

    // stateObj = nextStatesForAction[0];
    // let state = stateObj["state"];
    // let stateQuantBounds = stateObj["quant_bound"];
    // let hash = state.fingerprint();

    // let varNames = _.keys(state.getStateObj());
    // let actionLabelText = getActionLabelText(actionLabel, stateQuantBounds);

    // let stateVarElems = varNames.map((varname, idx) => {
    //     let cols = [
    //         m("td", { class: "state-varname" }, varname),
    //         m("td", { class: "state-choice-varval" }, [tlaValView(state.getVarVal(varname))]),
    //         // m("td", { class: "state-choice-varval"}, [state.getVarVal(varname).toString()]),
    //         m("td", { style: "width:5px" }, ""), // placeholder row.
    //     ]

    //     return [
    //         m("tr", { style: "" }, cols)
    //     ];
    // });


    let actionLabelObj = getActionLabelText(actionLabel);
    let actionName = actionLabelObj.name;

    let actionParamChoices = nextStatesForAction.map(st => {
        // let state = s["state"];
        let quantBounds = st["quant_bound"];
        let hash = st["state"].fingerprint();

        // let varNames = _.keys(state.getStateObj());
        let actionLabelText = getActionLabelText(actionLabel, quantBounds);
        let classList = ["action-choice-param", "flex-col"];
        if(actionDisabled){
            classList.push("action-choice-disabled");
        }

        // console.log("actionlabel:", actionLabelText, st, hash);

        // TODO: Disambiguate action labels when they have different quant bounds
        // but lead to the same state.
        return m("div", 
        { 
            class: classList.join(" "), 
            "data-testid": "action-choice-param",
            // colspan: 2,
            onclick: () => chooseNextState(hash, hashQuantBounds(quantBounds)),
            // onmouseover: () => {
            //     // Enable if UI performance lag isn't too noticeable.
            //     console.log("onmouseover:", st["state"]);
            //     model.nextStatePreview = st["state"];
            // },
            // onmouseout: () => {
            //     model.nextStatePreview = null;
            // }
        }, 
        actionLabelText.params);
    });

    if (actionLabelObj.params.length == 0) {
        actionParamChoices = [];
    }

    let classList = ["action-choice-name", "flex-col"];
    if(actionDisabled){
        classList.push("action-choice-disabled");
    }
    if(actionLabelObj.params.length === 0 && !actionDisabled){
        classList.push("blue-hover");
    }
    let actionNameDiv = [m("div", {
        class: classList.join(" "),
        onclick: function () {
            if (!actionDisabled && actionLabelObj.params.length == 0) {
                let hash = nextStatesForAction[0]["state"].fingerprint();
                console.log("choose next hash:", hash);
                chooseNextState(hash);
            }
        }
    }, actionName)];

    let actionNameElem = [m("tr", {}, 
        [m("td", {}, [m("div", {class: ""}, 
            actionNameDiv
        )]),
        m("td", {}, [m("div", {class: "flex-grid"}, 
            actionParamChoices
        )])]
    )];

    let allElems = [];

    if (model.currTrace.length > 0 && actionLabel) {
        // Don't need this for initial state.
        allElems = allElems.concat(actionNameElem);
    }

    let opac = model.lassoTo === null ? "100" : "50";
    let nextStateElem = m("div", {
        class: "init-state",
        style: `opacity: ${opac}%`,
        onclick: function () {
            if (actionLabelObj.params.length == 0) {
                // let hash = nextStatesForAction[0]["state"].fingerprint();
                // console.log("choose nhhhhhhhhhext hash:", hash);
                // chooseNextState(hash);
            }
        }        // onmouseover: () => {
        //     model.nextStatePreview = state;
        // },
        // onmouseout: () => {
        //     model.nextStatePreview = null;
        // }
    }, m("table", { class: "trace-select-table" }, allElems));
    return nextStateElem;
}

function componentNextStateChoiceElement(stateObj, ind, actionLabel, diffOnly) {
    let state = stateObj["state"];
    let stateQuantBounds = stateObj["quant_bound"];
    let hash = state.fingerprint();

    let varNames = _.keys(state.getStateObj());
    let actionLabelObj = getActionLabelText(actionLabel, stateQuantBounds);
    let actionLabelText = actionLabelObj.name + actionLabelObj.params;

    // If we are showing diffs only, then only show vars that have changed from the current state to this one.
    if (model.currTrace.length > 0 && diffOnly) {
        let currState = model.currTrace[model.currTrace.length - 1]["state"];
        varNamesChanged = state.varDiff(currState);
        console.log("varNamesChanged:", varNamesChanged);
        varNames = varNames.filter(v => varNamesChanged.includes(v));
    }

    let stateVarElems = varNames.map((varname, idx) => {
        let cols = [
            m("td", { class: "state-varname" }, varname),
            m("td", { class: "state-choice-varval" }, [tlaValView(state.getVarVal(varname))]),
            // m("td", { class: "state-choice-varval"}, [state.getVarVal(varname).toString()]),
            m("td", { style: "width:5px" }, ""), // placeholder row.
        ]

        return [
            m("tr", { style: "" }, cols)
        ];
    });

    let actionNameElem = [m("tr", { style: "width:100%" }, [
        m("td", { class: "action-name", colspan: 2 }, actionLabelText)
    ])];

    let allElems = [];

    if (model.currTrace.length > 0 && actionLabel) {
        // Don't need this for initial state.
        allElems = allElems.concat(actionNameElem);
    }
    // Show full states for initial state choices.
    // TODO: Possibly have option to toggle this behavior.
    // When showing diffs only, we always show the full (diff'd) state, possible also with action label.
    if(model.currTrace.length === 0 || actionLabelText.length === 0 || diffOnly){
        allElems = allElems.concat(stateVarElems);
    }

    let opac = model.lassoTo === null ? "100" : "50";
    let nextStateElem = m("div", {
        class: "init-state next-state-choice-full",
        style: `opacity: ${opac}%`,
        "data-testid": "next-state-choice",
        onclick: () => chooseNextState(hash),
        // onmouseover: () => {
        //     model.nextStatePreview = state;
        // },
        // onmouseout: () => {
        //     model.nextStatePreview = null;
        // }
    }, m("table", { class: "trace-select-table" }, allElems));
    return nextStateElem;
}

function errorMsgStr(errorObj) {
    errorPosStr = "";
    if (errorObj !== null && errorObj.errorPos === null) {
        errorPosStr = errorObj.errorPos === null ? "" : "(" + errorObj.errorPos + ")";
    }
    return errorObj === null ? "" : "ERROR: " + errorObj.message + " " + errorPosStr;
}

function componentErrorInfo() {
    let errorInfo = m("div", {
        class: "error-info alert alert-danger",
        role: "alert",
        hidden: model.errorObj === null
    }, errorMsgStr(model.errorObj));
    return errorInfo;
}

function componentNextStateChoices(nextStates) {
    nextStates = model.currNextStates;

    let nextStateElems = [];

    if (model.lassoTo !== null) {
        // If we're stuck in a lasso, don't permit any further next state choices.
        return [];
    }

    // Handle case where next states are not broken down per action.
    if (nextStates instanceof Array) {
        for (var i = 0; i < nextStates.length; i++) {
            var state = nextStates[i];
            let nextStateElem = componentNextStateChoiceElement(state, i);
            nextStateElems.push(nextStateElem);
        }
    }
    else if (model.showStateDiffsInSelection && model.currTrace.length > 0) {
        let diffOnly = true;
        for (const [actionId, nextStatesForAction] of Object.entries(nextStates)) {
            let i = 0;
            let action = model.actions[actionId];
            for (const state of nextStatesForAction) {
                // let nextStateElem = componentNextStateChoiceElement(state, i, action.name);
                let nextStateElem = componentNextStateChoiceElement(state, i, action.name, diffOnly);
                nextStateElems.push(nextStateElem);
                i += 1;
            }
        }
    }
    else {
        // Action specific case.
        for (const [actionId, nextStatesForAction] of Object.entries(nextStates)) {
            let i = 0;
            let action = model.actions[actionId];

            let nextStateElem = componentNextStateChoiceElementForAction(i, action.name, nextStatesForAction);
            nextStateElems.push(nextStateElem);

            // for (const state of nextStatesForAction.slice(0, 1)) {
            //     let nextStateElem = componentNextStateChoiceElement(state, i, action.name);
            //     nextStateElems.push(nextStateElem);
            //     i += 1;
            // }


        }
    }

    // Fill up rows of table/grid with max number of elements.
    let outRows = [m("tr", componentErrorInfo())]
    let statesPerRow = 1;
    let currRow = [];
    let count = 0;
    for (const elem of nextStateElems) {
        currRow.push(m("th", elem));
        count += 1;
        if (currRow.length == statesPerRow || count === nextStateElems.length) {
            outRows.push(m("tr", { width: "100%", "margin": "5px" }, currRow));
            currRow = [];
        }
    }
    return m("table", { width: "98%" }, outRows);
}


function recomputeInitStates(){
    let interp = new TlaInterpreter();
    let includeFullCtx = true;
    initStates = interp.computeInitStates(model.specTreeObjs, model.specConstVals, includeFullCtx, model.spec);
    initStates = initStates.map(c => ({"state": c["state"], "quant_bound": c["quant_bound"]}))
    model.allInitStates = _.cloneDeep(initStates);
    console.log("Set initial states: ", model.allInitStates);
    return initStates;
}

function recomputeNextStates(fromState) {
    let interp = new TlaInterpreter();
    let nextStates;

    evalNodeGraphsPerAction = {};

    // Compute next states broken down by action.
    // TODO: Consider if this functionality more appropriately lives inside the interpreter logic.
    if (model.actions.length > 1) {
        let nextStatesByAction = {}
        for (const action of model.actions) {
            assert(action instanceof TLAAction);
            // console.log("FROM:", fromState)
            const start = performance.now();
            cloneTime = 0;
            numClones = 0;


            let nextStatesForAction = interp.computeNextStates(model.specTreeObjs, model.specConstVals, [fromState], action.node, model.spec)
            // console.log("nextStatesForAction", nextStatesForAction); 
            nextStatesForAction = nextStatesForAction.map(c => {
                let deprimed = c["state"].deprimeVars();
                return { "state": deprimed, "quant_bound": c["quant_bound"] };
            });
            // nextStatesForActionQuantBound = nextStatesForActionQuantBound.map(c => c["quant_bound"]);
            nextStatesByAction[action.id] = nextStatesForAction;

            evalNodeGraphsPerAction[action.id] = evalNodeGraph;

            const duration = (performance.now() - start).toFixed(1);

            console.log(`Generating next states for action '${action.name}' took ${duration}ms, (${nextStatesForAction.length} distinct states generated, clone time: ${cloneTime.toFixed(2)}ms, ${numClones} clones)`)
            cloneTime = 0;
            numClones = 0;
        }
        nextStates = nextStatesByAction;
    } else {
        nextStates = interp.computeNextStates(model.specTreeObjs, model.specConstVals, [fromState], undefined, model.spec)
            .map(c => {
                let deprimed = c["state"].deprimeVars();
                return { "state": deprimed, "quant_bound": c["quant_bound"] };
            });
    }

    return nextStates;
}

// Step back one state in the current trace.
function traceStepBack() {
    // Clear out a lasso condition in this case.
    if (model.lassoTo !== null) {
        model.lassoTo = null;
        return;
    }
    
    // Save current state to forward history before stepping back
    if (model.currTrace.length > 0) {
        model.forwardHistory.push(model.currTrace[model.currTrace.length - 1]);
        model.forwardHistoryActions.push(model.currTraceActions[model.currTraceActions.length - 1]);
    }
    
    model.currTrace = model.currTrace.slice(0, model.currTrace.length - 1);
    model.currTraceActions = model.currTraceActions.slice(0, model.currTraceActions.length - 1);
    updateTraceRouteParams();

    // Back to initial states.
    if (model.currTrace.length === 0) {
        console.log("Back to initial states.")
        console.log("stepping back");
        let nextStates = recomputeInitStates();
        model.currNextStates = _.cloneDeep(nextStates);
        return;
    } else {
        console.log("stepping back");
        let lastState = model.currTrace[model.currTrace.length - 1];
        let nextStates = recomputeNextStates(lastState["state"]);
        model.currNextStates = _.cloneDeep(nextStates);
    }
}

function traceStepForward() {
    // If no forward history, we can't step forward
    if (model.forwardHistory.length === 0) {
        return;
    }

    // Pop the last state from forward history and add it to current trace
    let nextState = model.forwardHistory.pop();
    let nextAction = model.forwardHistoryActions.pop();
    
    model.currTrace.push(nextState);
    model.currTraceActions.push(nextAction);
    updateTraceRouteParams();

    // Update next states
    let nextStates = recomputeNextStates(nextState["state"]);
    model.currNextStates = _.cloneDeep(nextStates);
}

// Adds the given new params to the current route params and updates the route.
function updateRouteParams(newParams){
    let oldParams = m.route.param();
    let updatedParams = Object.assign(oldParams, newParams);
    m.route.set("/home", updatedParams);
}

function clearRouteParams(){
    m.route.set("/home", {});
}

// Compute a hash of a quantifier bounds objects, which should be simply a
// mapping from identifier strings to TLA values.
function hashQuantBounds(quantBounds){
    let keysSorted = _.keys(quantBounds).sort();
    let kvPairs = keysSorted.map(k => [k, quantBounds[k].fingerprint()]);
    return hashSum(kvPairs);
}

// Updates the current URL route to store the current trace.
function updateTraceRouteParams() {
    let traceHashed = model.currTrace.map((s, ind) => {
        let action = model.currTraceActions[ind];
        quantBounds = "";
        // Append the quant bounds used for the action to execute this step in the trace, if
        // one is available.
        if(action !== undefined && action.length > 1 && action[1] !== undefined){
            let quantBounds = action[1];
            return s["state"].fingerprint() + "_" + quantBounds;
        } else{
            return s["state"].fingerprint();
        }

    });
    let oldParams = m.route.param();
    if (traceHashed.length === 0) {
        delete oldParams.trace;
    }
    let traceParamObj = traceHashed.length > 0 ? { trace: traceHashed.join(",") } : {}
    let newParams = Object.assign(oldParams, traceParamObj);

    // Save set of hidden vars in the route as well.
    if(model.hiddenStateVars.length > 0){
        let hiddenVarsStr = model.hiddenStateVars.join(",");
        newParams["hiddenVars"] = hiddenVarsStr;
    } else {
        delete newParams.hiddenVars;
    }

    if(model.explodedConstantExpr !== null){ 
        newParams["explodedConstantExpr"] = model.explodedConstantExpr;
    } else {
        delete newParams.explodedConstantExpr;
    }

    // Update CONSTANT params.
    if (Object.keys(model.specConstInputVals).length !== 0) {
        Object.assign(newParams, { constants: model.specConstInputVals });
    } else {
        delete newParams["constants"];
    }

    m.route.set("/home", newParams);
}

// Determine the action id that corresponds to the given next state, if it exists.
function actionIdForNextState(nextStateHash) {
    // Find the action id that corresponds to the selected next state.
    let actionId = _.findKey(model.currNextStates, (states) => _.find(states, (s) => s["state"].fingerprint() === nextStateHash));
    return actionId;
}

function chooseNextState(statehash_short, quantBoundsHash, rethrow = false) {
    // Clear forward history since we're taking a new path
    model.forwardHistory = [];
    model.forwardHistoryActions = [];
    
    // console.log("currNextStates:", JSON.stringify(currNextStates));
    // console.log("chooseNextState: ", statehash_short);

    let currNextStatesSet = _.flatten(_.values(model.currNextStates));
    let nextStateChoices = currNextStatesSet.filter(s => {
        if (quantBoundsHash === undefined || _.isEmpty(quantBoundsHash)) {
            return s["state"].fingerprint() === statehash_short;
        } else {
            // If quant bounds are given, then choose next state that both
            // matches state hash and also matches the quant bounds hash. This
            // can matter when, for example, two distinct actions (e.g. those
            // with different parameters) lead to the same state.
            let sameQuantParams = _.isEqual(hashQuantBounds(s["quant_bound"]), quantBoundsHash);
            return s["state"].fingerprint() === statehash_short && sameQuantParams;
        }
    });

    let nextStateActionId = null;
    if (model.actions.length > 1 && model.currTrace.length >= 1) {
        nextStateActionId = actionIdForNextState(statehash_short)
        // console.log("actionid:", nextStateActionId);
    }

    if (nextStateChoices.length === 0) {
        throw Error("Given state hash " + statehash_short + " does not exist among possible next states.")
    }
    let nextState = nextStateChoices[0];

    // If the next state already exists in the current trace, then treat it as a
    // "lasso" transition, and freeze the trace from continuing.
    // * DISABLE LASSO TRANSITIONS FOR NOW. *
    // if (model.currTrace.map(s => s.fingerprint()).includes(statehash_short)) {
    //     console.log("Reached LASSO!");
    //     model.lassoTo = statehash_short;
    //     return;
    // }

    // console.log("nextState:", JSON.stringify(nextState));
    // console.log("nextStatePred:", model.nextStatePred);

    // Append next state to the trace and update current route.
    model.currTrace.push(nextState);
    // Recrod the quant bounds used in the action as well in case we need to tell between two different actions
    // with the same type but different params that lead to the same state.
    model.currTraceActions.push([nextStateActionId, quantBoundsHash]);
    updateTraceRouteParams();

    const start = performance.now();

    try {
        let nextStates = recomputeNextStates(nextState["state"]);
        const duration = (performance.now() - start).toFixed(1);

        const start2 = performance.now();
        model.currNextStates = _.cloneDeep(nextStates);
        const duration2 = (performance.now() - start2).toFixed(1);

        console.log(`Generating next states took ${duration}ms (cloning took ${duration2}ms )`)
    } catch (e) {
        console.error("Error computing next states.", e);
        if (currEvalNode !== null) {
            // Display line where evaluation error occurred.
            showEvalError(currEvalNode, e);
        }
        if(rethrow){
            throw e;
        }
        return;
    }
}

function setConstantValues(reload = true) {
    console.log("Setting constant values");
    let constVals = {};
    let nullTree;
    let constTlaVals = {};

    // Evaluate each CONSTANT value expression.
    for (var constDecl in model.specConsts) {
        let constValText = model.specConstInputVals[constDecl];
        if (constValText === undefined) {
            throw "no value given for '" + constDecl + "' CONSTANT";
        }
        // console.log("constDecl:", constDecl, constValText);
        constVals[constDecl] = constValText;

        let ctx = new Context(null, new TLAState({}), model.specDefs, {}, model.specConstVals);

        // 
        // If this refers to a definition in the spec, then we treat it as a
        // definition substitution. and leave it as a plain string. 
        // Otherwise, we try to evaluate it as an expression.
        // 
        // TODO: Eventually should more of this be handled directly in the interpreter?
        //
        let cVal = null;
        // console.log("model.specDefs:", model.specDefs);
        if (_.find(model.specDefs, d => d.name === constValText) !== undefined) {
            cVal = constValText;
        } else {
            // Flag so that we treat unknown identifiers as model values during evaluation.
            ctx.evalModelVals = true;
            cVal = evalExprStrInContext(ctx, constValText, exprTagName = "CONSTANT");
        }
        console.log(`Setting constant value: '${constDecl}' to '${cVal}'`);
        constTlaVals[constDecl] = cVal;
    }

    console.log("constTlaVals:", constTlaVals);
    model.specConstVals = constTlaVals;

    let currParams = m.route.param();
    m.route.set("/home", Object.assign(currParams, { constants: model.specConstInputVals }));

    if(reload){
        console.log("Reloading spec from setConstantValues.");
        reloadSpec();
    }
}

// TODO: Simple reachability benchmark that can eventually be incorporated into 
// benchmarks page.
function reachableBench() {
    let start = performance.now();
    let reachable = computeReachableStates(specTreeObjs, specConstVals)["states"];
    const duration = (performance.now() - start).toFixed(1);
    console.log(`Computed ${reachable.length} reachable states in ${duration}ms.`);
}

function showEvalError(currEvalNode, e) {
    // Display line where evaluation error occurred.
    const $codeEditor = document.querySelector('.CodeMirror');
    // console.log(currEvalNode["startPosition"]);
    // console.log(currEvalNode["endPosition"]);
    let errorLine = currEvalNode["startPosition"]["row"];
    let errorCol = currEvalNode["startPosition"]["column"];

    let ret = model.specTreeObjs["rewriter"].getOrigLocation(errorLine, errorCol);
    console.log("ERROR pos:", ret);

    model.errorObj = Object.assign(e, { errorPos: [errorLine, errorCol] });

    // $codeEditor.CodeMirror.addLineClass(errorLine, 'background', 'line-error');
    $codeEditor.CodeMirror.addLineClass(ret[0], 'background', 'line-error');
    console.log("error evaluating node: ", currEvalNode);
    console.log(e);
}

/**
 * Clear the current trace, re-parse the spec and generate initial states.
 */
function reloadSpec() {
    console.log("Clearing current trace.");
    model.currTrace = []
    model.currTraceActions = []
    model.currTraceAliasVals = []
    model.lassoTo = null;
    model.errorObj = null;
    model.traceExprs = [];
    model.hiddenStateVars = [];

    // if(model.showRewritten){
    //     const $codeEditor = document.querySelector('.CodeMirror');
    //     $codeEditor.CodeMirror.setValue(model.specTreeObjs.spec_rewritten);
    //     return;
    // }

    let hasInit = model.spec.hasDefinitionByName("Init");
    let hasNext = model.spec.hasDefinitionByName("Next");

    // let hasInit = model.specTreeObjs["op_defs"].hasOwnProperty("Init");
    // let hasNext = model.specTreeObjs["op_defs"].hasOwnProperty("Next");

    // Init or Next is missing, we allow the spec to be loaded but just stop here before trying
    // to generate any initial states.
    if (!hasInit || !hasNext) {
        console.log("Warning: 'Init' or 'Next' predicate not found. Still loading spec without generating states.");

        // Switch to spec pane and REPL pane.
        model.selectedTab = Tab.SpecEditor;
        model.selectedTraceTab = TraceTab.REPL;
        return;
    }

    console.log("Generating initial states.");
    let interp = new TlaInterpreter();
    const start = performance.now();

    // TODO: Can work on this more to consider web workers for off-thread state generation.
    // console.log("Starting web worker for state generation.");
    // model.generatingInitStates = true;
    // startWebWorker();   
    // return;

    // let allInitStates;
    let initStates;
    try {
        initStates = recomputeInitStates();
    } catch (e) {
        console.error(e);
        console.error("Error computing initial states.");
        if (currEvalNode !== null) {
            // Display line where evaluation error occurred.
            showEvalError(currEvalNode, e);
        }
        return;
    }

    const duration = (performance.now() - start).toFixed(1);
    console.log(`Generating ${model.allInitStates.length} initial states took ${duration}ms.`);

    // Display states in HTML.
    // let initStatesDiv = document.getElementById("initial-states");
    // initStatesDiv.innerHTML = "";
    // renderNextStateChoices(initStates);
    // console.log("Rendered initial states");

    model.currNextStates = _.cloneDeep(initStates);

    // displayEvalGraph();

    // Check for trace to load from given link.
    // displayStateGraph();
    // m.redraw();
}

// Function for rendering a TLA+ value that appears in a state/trace, etc.
// Optionally takes a previous value to check for diffs when rendering.
function tlaValView(tlaVal, prevTlaVal = null) {
    if (tlaVal instanceof FcnRcdValue) {
        let valPairs = _.zip(tlaVal.getDomain(), tlaVal.getValues());

        // If the previous value was not a function/record, then just diff the whole thing.
        let wholeDiff = false;
        if(prevTlaVal !== null && !(prevTlaVal instanceof FcnRcdValue)){
            wholeDiff = true;
        }

        // If domains of old and new val are the same, then show the diff of their sub-values.
        let domainsMatch = false;
        if (prevTlaVal !== null && (prevTlaVal instanceof FcnRcdValue) && prevTlaVal.getDomain().length === tlaVal.getDomain().length && 
                        _.isEqual(prevTlaVal.getDomain().map(v => v.fingerprint()), tlaVal.getDomain().map(v => v.fingerprint()))) {
            // valPairs = _.zip(prevTlaVal.getValues(), tlaVal.getValues());
            domainsMatch = true;
        }

        let borderStyle = { style: "border:solid 0.5px gray;vertical-align:middle" };
        return m("table", {style: {"background-color": wholeDiff ? "lightyellow" : "none"}}, valPairs.map(p => {
            let key = p[0];
            let val = p[1];
            // If checking for diff, do it now.
            let diff = false;
            let prevKeyVal = null;
            if (prevTlaVal !== null && (prevTlaVal instanceof FcnRcdValue) && prevTlaVal.argInDomain(key) && prevTlaVal.applyArg(key).fingerprint() !== val.fingerprint()) {
                diff = true;
                prevKeyVal = prevTlaVal.applyArg(key);
                // console.log("prevKeyVal:", prevKeyVal);
            }
            let addedKey = false;
            if(prevTlaVal !== null && (prevTlaVal instanceof FcnRcdValue)&& !prevTlaVal.argInDomain(key)){
                addedKey = true;
            }

            let bgColor = diff && !domainsMatch ? "lightyellow" : "none";

            // TODO: Improve handling of highlighting for newly added keys.
            if(addedKey){
                bgColor = "#eaffde";
            }

            // If key value is not a function/record itself, then let's highlight the cell.
            let keyVal = val;
            if(!(keyVal instanceof FcnRcdValue) && diff){
                // keyVal = val;
                bgColor = "lightyellow";
            }

            return m("tr", borderStyle, [
                m("td", borderStyle, key.toString()),
                // TOOD: Uniform diff styling.
                m("td", {style: {
                    "background-color": bgColor, 
                    "vertical-align": "middle"
                }}, tlaValView(val, prevKeyVal)), // TODO: do we want to recursively apply?
            ]);
        }));
    }

    // Display sets as lists of their items.
    if (tlaVal instanceof SetValue) {
        if (tlaVal.getElems().length === 0) {
            return m("span", "{}"); // empty set.
        }
        let borderStyle = { style: "border:solid 0.5px gray" };

        // If all elements are short, just display the set as a string.
        let elemLengths = tlaVal.getElems().map((v, idx) => v.toString().length)
        let maxLength = _.max(elemLengths);
        let diff = prevTlaVal !== null && prevTlaVal.fingerprint() !== tlaVal.fingerprint();

        let SHORT_SET_ELEM_DISPLAY_LEN = 4;
        if (maxLength <= SHORT_SET_ELEM_DISPLAY_LEN) {
            let style = {"background-color": diff ? "lightyellow" : "none"};
            return m("span", {style: style}, tlaVal.toString());
        }

        let setElems = tlaVal.getElems().map((v, idx) => {
            pre = idx === 0 ? "{ " : "";
            suff = idx === (tlaVal.getElems().length - 1) ? " }" : ",";

            // TODO: Consider how to show set diffs.
            let diff = false;
            if (prevTlaVal !== null && !prevTlaVal.contains(v)) {
                diff = true;
            }

            let style = {}
            // style = {"background-color": diff? "lightyellow" : "none"}};

            return m("tr", [
                // TODO: Recursively apply value view function?
                // m("td", m.trust(pre + v.toString() + suff)),
                m("td", {style: style}, pre + v.toString() + suff),
            ]);
        });

        let style = {"background-color": diff ? "lightyellow" : "none"};
        return m("table", {style: style}, setElems);
    }

    // Display tuples as lists of their items.
    if (tlaVal instanceof TupleValue) {
        const SHORT_TUPLE_ELEM_DISPLAY_LEN = 30;

        let diff = false;
        if(prevTlaVal !== null && (prevTlaVal instanceof TupleValue) && prevTlaVal.fingerprint() !== tlaVal.fingerprint()){
            diff = true;
        }

        let style = {style: {"background-color": diff ? "lightyellow" : "none"}};

        if (tlaVal.getElems().length === 0) {
            return m("span", style, "<<>>"); // empty set.
        }
        let borderStyle = { style: "border:solid 0.5px gray" };

        let tupleElems = tlaVal.getElems().map((v, idx) => {
            pre = idx === 0 ? "<< " : "&nbsp;&nbsp;&nbsp;";
            suff = idx === (tlaVal.getElems().length - 1) ? " >>" : ",";
            return m("tr", [
                // TODO: Recursively apply value view function?
                m("td", m.trust(pre + v.toString() + suff)),
            ]);
        });

        // If tuple is short enough, we will just display it as a string.
        if(tlaVal.toString().length > SHORT_TUPLE_ELEM_DISPLAY_LEN){
            return m("table", style, tupleElems);
        }

        return m("table", style, [m("tr", m("td", tlaVal.toString()))]);
    }

    let style = {};
    if (prevTlaVal !== null && prevTlaVal.fingerprint() !== tlaVal.fingerprint()) {
        style = {
            "background-color": "lightyellow"
        };
    }

    return m("span", {style: style}, tlaVal.toString());
}


//
// Animation view logic.
//
function makeSvgAnimObj(tlaAnimElem) {
    let name = tlaAnimElem.applyArg(new StringValue("name")).getVal();
    let attrs = tlaAnimElem.applyArg(new StringValue("attrs"));
    let innerText = tlaAnimElem.applyArg(new StringValue("innerText"));
    let children = tlaAnimElem.applyArg(new StringValue("children"));


    // Experimental Graphviz visualization elemen support.
    if (name === "digraph") {
        // console.log("tlaAnimElem:", tlaAnimElem);

        let nodes = attrs.applyArg(new StringValue("V"));
        let edges = attrs.applyArg(new StringValue("E"));
        let nodeAttrsFn = attrs.applyArg(new StringValue("nodeAttrsFn"));

        // console.log("nodes:", nodes);
        // console.log("edges:", edges);
        // console.log("labelFn:", labelFn);

        let graphvizStr = `digraph {\n`;
        for (let i = 0; i < nodes.getElems().length; i++) {
            let node = nodes.getElems()[i];
            let nodeStr = node.toString();

            console.log(nodeAttrsFn.getDomain())

            let nodeAttrsObj = {};
            nodeAttrsFn.applyArg(node).getDomain().forEach(v => {
                let val = nodeAttrsFn.applyArg(node).applyArg(v);
                nodeAttrsObj[v.getVal()] = val.getVal();
            });

            let nodeAttrsStr = Object.entries(nodeAttrsObj).map(([key, value]) => `${key}="${value}"`).join(",");
            graphvizStr += `  ${nodeStr} [${nodeAttrsStr}];\n`;
        }
        for (let i = 0; i < edges.getElems().length; i++) {
            let edge = edges.getElems()[i];
            let from = edge.getValues()[0].getVal();
            let to = edge.getValues()[1].getVal();
            let edgeStr = `  ${from} -> ${to};`;
            graphvizStr += `${edgeStr}\n`;
        }
        graphvizStr += `}`;

        // console.log("graphvizStr:", graphvizStr);

        let ret = vizInstance.renderSVGElement(graphvizStr);
        return m("g", [m.trust(ret.children[0].outerHTML)]);
    }

    // console.log("name:", name);
    // console.log("attrs:", attrs);
    // console.log("children:", children);
    if (children instanceof FcnRcdValue) {
        children = children.toTuple();
    }
    let childrenElems = children.getElems();

    let attrKeys = attrs.getDomain()
    let attrVals = attrs.getValues()

    let rawKeys = attrKeys.map(v => v.getVal());
    let rawVals = attrVals.map(v => v.getVal());
    let attrObj = _.fromPairs(_.zip(rawKeys, rawVals));

    if (innerText.getVal().length > 0) {
        return m(name, attrObj, innerText.getVal());
    }
    return m(name, attrObj, childrenElems.map(c => makeSvgAnimObj(c)));
}

// Compute action label text with quantifier bound values filled in.
function getActionLabelText(actionLabel, quantBounds) {
    let actionLabelText = actionLabel ? actionLabel : "";

    // For now just assume actions have the form "Action(x,y,z)",
    // so we only do replacements after the the first parenthesis.
    let parenSplit = actionLabelText.indexOf("(");
    if (parenSplit < 0) {
        // No parameters to replace.
        return { name: actionLabelText, params: "" };
    }
    // console.log("actionlabel pre:", actionLabelText);
    let pre = actionLabelText.slice(0, parenSplit);
    let post = actionLabelText.slice(parenSplit).replace("(", "").replace(")", "");
    let post_param_args = post.split(",").map(v => v.trim());
    // console.log("actionlabel post split:", post_param_args);
    let post_param_arg_vals = post_param_args;

    // Parse out bound quantifer values for display in parameterized action label.
    if (quantBounds) {
        for (const [quant, bound] of Object.entries(quantBounds)) {
            // console.log(" actionlabel quant:", quant, "bound:", bound);
            for (let i = 0; i < post_param_arg_vals.length; i++) {
                if (post_param_arg_vals[i] === quant) {
                    post_param_arg_vals[i] = bound.toString();
                }
            }
        }
    }
    // console.log("actionlabel post param arg vals:", post_param_arg_vals);
    actionLabelText = { name: pre, params: "(" + post_param_arg_vals.join(",") + ")" };
    return actionLabelText
}

function animationViewForTraceState(state){
    let viewNode = model.spec.getDefinitionByName(model.animViewDefName).node;
    let initCtx = new Context(null, state, model.specDefs, {}, model.specConstVals);
    initCtx.setGlobalDefTable(model.spec.globalDefTable);
    initCtx.setSpecObj(model.spec);
    initCtx["defns_curr_context"] = model.spec.getDefinitionByName(model.animViewDefName)["curr_defs_context"];
    let start = performance.now();
    // evalNodeGraph = [];
    try{
        ret = evalExpr(viewNode, initCtx);
    }
    catch(e){
        console.error(e);
        console.error("Error evaluating animation view.");
        return null;
    }
    // console.log("evalNodeGraph:", evalNodeGraph.length);
    const duration = (performance.now() - start).toFixed(1);
    console.log(`Animation view computed in ${duration}ms.`);
    // displayEvalGraph(evalNodeGraph);
    viewVal = ret[0]["val"];
    let viewSvgObj = makeSvgAnimObj(viewVal);
    return viewSvgObj;
}

function componentTraceViewerState(stateCtx, ind, isLastState, actionId) {

    //
    // Optionally enable experimental animation feature.
    //

    let state = stateCtx["state"];
    let stateQuantBounds = stateCtx["quant_bound"];
    let allVarNames = _.keys(state.getStateObj());
    let varNames = _.keys(state.getStateObj());

    // console.log("statectx:", stateCtx);

    let action = model.actions[actionId];
    let actionLabel = action ? action.name : null;
    let actionLabelObj = getActionLabelText(actionLabel, stateQuantBounds);
    let actionLabelText = actionLabelObj.name + actionLabelObj.params;

    model.animationExists = model.spec.hasDefinitionByName(model.animViewDefName);
    let vizSvg = m("svg", { width: 0, height: 0 }, []);

    if (model.animationExists && model.enableAnimationView) {
        // let viewSvgObj = animationViewForTraceState(state);
        // vizSvg = m("div", { id: "anim-div" }, m("svg", { width: "100%", height: "100%" }, [viewSvgObj]));
        vizSvg = m("div", { id: "anim-div" }, m("svg", { width: "100%", height: "100%" }, []));
    }

    function makeVarRows(varNames, param) { 
        return varNames.map((varname, idx) => {
            let varnameCol = "none";
            let varDiff = null;
            if (Object.keys(model.currNextStates).length > 0 && model.nextStatePreview !== null) {
                let selectedNextState = model.nextStatePreview;
                // console.log(selectedNextState);
                let currState = model.currTrace[model.currTrace.length - 1]["state"];
                varDiff = selectedNextState.varDiff(currState);
                // console.log("var diff:", varDiff);
            }

            // TODO: Enable to show modified variables.
            // if(ind === model.currTrace.length - 1 && ind > 0){
            if(ind > 0){
                varDiff = model.currTrace[ind]["state"].varDiff(model.currTrace[ind - 1]["state"]);

                // For case of state being exploded on a parameter.
                // console.log("param:", param)
                // console.log("varname:", varname)
                // console.log("state:", state)
                if(param !== undefined){
                    function projectStateToParam(state, param){
                        return new TLAState(_.mapValues(state.stateVars, v => {
                            // console.log("v:", v)
                            if(v instanceof FcnRcdValue && v.argInDomain(param)){
                                return v.applyArg(param);
                            }
                            return v;
                        }));
                    }

                    // Project each state var to the param, and then diff.
                    let stateVarParamProjected = projectStateToParam(model.currTrace[ind]["state"], param);
                    let stateVarParamProjectedPrev = projectStateToParam(model.currTrace[ind - 1]["state"], param);

                    // console.log("stateVarParamProjected:", stateVarParamProjected);
                    // console.log("stateVarParamProjectedPrev:", stateVarParamProjectedPrev);

                    varDiff = stateVarParamProjected.varDiff(stateVarParamProjectedPrev);

                }
            }

            // Show modified variables in blue.
            // if (varDiff !== null && varDiff.includes(varname) && ind === model.currTrace.length - 1) {
            if (varDiff !== null && varDiff.includes(varname) && ind > 0) {
                // varnameCol = "none"; // Optionally disable highlighting.
                varnameCol = "lightyellow";
            } else{
                varnameCol = "none";
            }
            let varVal = state.getVarVal(varname);
            if(param !== undefined){
                varVal = varVal.applyArg(param);
            }
            let prevVarVal = null;
            if(ind > 0){
                prevVarVal = model.currTrace[ind - 1]["state"].getVarVal(varname);
                if(param !== undefined){
                    prevVarVal = prevVarVal.applyArg(param);
                }
            }
            
            let cols = [
                m("td", {
                    class: "th-state-varname trace-state-table-td",
                    // style: {"background-color": varnameCol},
                    onclick: (e) => {
                        // model.hiddenStateVars.push(varname);
                        // We also store hidden vars in route url params.
                        // updateTraceRouteParams();
                    }
                }, [
                    m("span", {class: "state-varname-text",style: {"background-color": varnameCol, "padding":"0px 0px 0px 0px"}}, varname),
                    // m("span", {class: "state-varname-text",style: {"background-color": varnameCol, "padding":"0px"}}, "  x")
                ]),
                m("td", {style: {
                }, class: "trace-state-table-td"}, [tlaValView(varVal, prevVarVal)]),
                m("td", { 
                    style: {
                        "border-right": "1px solid gray",
                        "width": "20px",
                    },
                    hidden: false, class: "" 
                }, 
                    m("img", {
                        style: {"width": "11px", "height": "11px"},
                        class: "hide-var-icon",
                        src: "assets/hide-icon.svg",
                        onclick: (e) => {
                            model.hiddenStateVars.push(varname);
                            // We also store hidden vars in route url params.
                            updateTraceRouteParams();
                        }
                    })), // placeholder row.
            ]

            return m("tr", {class: "trace-state-table-row"}, cols);
        });
    }



    // Trace expression values, if any are present.
    let traceExprRows = model.traceExprs.map((expr, ind) => {
        let ctx = new Context(null, state, model.specDefs, {}, model.specConstVals);
        // All definitions in the root module should be accessible.
        ctx["defns_curr_context"] = _.keys(model.spec.spec_obj["op_defs"]);
        ctx.setGlobalDefTable(model.spec.globalDefTable);
        ctx.setSpecObj(model.spec);
        let exprVal = evalExprStrInContext(ctx, expr);
        let cols = [
            m("td", { class: "th-state-traceexpr" }, m("span", expr)),
            m("td", { class: "td-state-traceexpr" }, [tlaValView(exprVal)]),
            // Button to delete trace expression.
            m("td", {
                class: "trace-expr-delete",
                style: {
                    "text-align": "center",
                    "vertical-align": "middle"
                },
                onclick: (e) => { 
                    _.remove(model.traceExprs, v => (v === expr));
                    updateRouteParams({traceExprs: model.traceExprs});
                }
            }, trashIcon()), // placeholder row.
        ]

        // Demarcate trace expressions.
        if (ind === 0) {
            return m("tr", { class: "tr-state-traceexpr" }, cols);
        }
        return m("tr", { class: "tr-state-traceexpr"}, cols);
    });

    // Evaluate the current input trace expression to dynamically display its value.
    // Use more careful error handling to ignore bogus inputs as they are input on the fly.
    if (model.traceExprInputText.length) {
        let exprVal;
        try {
            let ctx = new Context(null, state, model.specDefs, {}, model.specConstVals);

            // All definitions in the root module should be accessible.
            ctx["defns_curr_context"] = _.keys(model.spec.spec_obj["op_defs"]);
            ctx.setGlobalDefTable(model.spec.globalDefTable);
            ctx.setSpecObj(model.spec);
            exprVal = evalExprStrInContext(ctx, model.traceExprInputText);
            // console.log("exprVal:", exprVal);
        }
        catch (e) {
            // Ignore and suppress errors here since we assume bogus inputs may appear transiently.
            exprVal = null;
        }

        let displayVal = exprVal === null ? "" : tlaValView(exprVal)
        let addClass = exprVal === null ? " tr-state-traceexpr-currinput-error" : "";
        let cols = [
            m("td", { class: "th-state-traceexpr-currinput", style: "border-right:solid 1px black;" }, m("span", model.traceExprInputText)),
            m("td", { class: "td-state-traceexpr-currinput" }, [displayVal]),
            m("td", ""), // placeholder row.
        ]

        let currTraceExprRow = m("tr", { class: "tr-state-traceexpr-currinput" + addClass }, cols);
        traceExprRows = traceExprRows.concat([currTraceExprRow]);
    }

    let stateColorBg = "transparent";
    let lassoToInd = (model.lassoTo !== null) ? _.findIndex(model.currTrace, s => s.fingerprint() === model.lassoTo) + 1 : ""
    let lassoNote = ((model.lassoTo !== null) && isLastState) ? " (Back to State " + lassoToInd + ")" : "";
    // let lastStateNote = isLastState ? "  (Current) " : "";
    let lastStateNote = isLastState ? "" : "";
    let stateIndLabel = "State " + (ind + 1) + " " + lastStateNote;
    let stateHeaderText = lassoNote;
    if (actionId !== null) {
        stateHeaderText += "   " + actionLabelText;
    }


    let explodedConstantVal = null;
    if(model.explodedConstantExpr !== null){
        explodedConstantVal = model.specConstVals[model.explodedConstantExpr];
    }
    let headerColSpanCount = 2;
    if(model.explodedConstantExpr !== null){
        headerColSpanCount += explodedConstantVal.getElems().length;
    }

    let headerRow = [m("tr", { style: `background-color: ${stateColorBg};border-bottom:solid 1px gray;`, class: "trace-state-header" }, [
        m("th", { colspan: headerColSpanCount, style: "padding-top: 4px; padding-bottom: 8px;" }, [
            m("span", { style: "color:black;padding-right:16px;border-right:solid 0px gray;font-size:14px;font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;font-weight: 600;" }, stateIndLabel),
            // m("span", { style: "color:black;padding-right:8px;border-right:solid 0px gray;font-size:14px;" }, stateIndLabel),
            m("span", { style: "color:black;padding-bottom:2px;font-family:monospace;font-size:12px;" }, stateHeaderText)
        ]),
        m("th", { colspan: 2 }, "") // filler.
    ])];

    // Filter out hidden variables.
    varNamesToShow = _.difference(varNames, model.hiddenStateVars);
    let varRows = makeVarRows(varNamesToShow);

    let explodedVars = [];

    if (explodedConstantVal !== null) {
        // 
        // Explode all state vars whose DOMAIN is equal to the exploded state var value.
        // e.g. Exploded var might be set of servers/nodes {s1,s2,s3}.
        // 
        explodedVars = varNamesToShow.filter(vname => {
            let varVal = state.getVarVal(vname);
            // console.log(varVal);
            return (varVal instanceof FcnRcdValue) && new SetValue(varVal.getDomain()).fingerprint() === explodedConstantVal.fingerprint();
        });

        // console.log("Explode vars:", explodedVars);
        varRows = m("tr", {class: "trace-state-table-row"}, [
            // Unexploded vars.
            makeVarRows(varNamesToShow.filter(n => !explodedVars.includes(n))),
            // Exploded vars.
            explodedConstantVal.getElems().map((param) => {
                return m("td", m("table", { style: "border:solid 1px" }, [
                    m("td", {
                        "style": "border-bottom:solid black 1px;color:gray;padding-bottom:3px;padding-top:3px;", 
                        colspan:2
                    }, param.toString()),
                    makeVarRows(explodedVars, param)
                ]))
            }),
        ])
    }

    let rows = headerRow.concat(varRows).concat(traceExprRows);

    let rowElemsTable = m("table", { class: "trace-state-table" }, rows);
    // let rowElems = m("div", { class: "trace-state-table-div" }, rowElemsTable);

    // stateVarElems = m("div", {id:"trace-state-holder"}, [rowElems,vizSvg]);
    stateVarElems = m("div", { id: "trace-state-holder" }, [rowElemsTable]);

    let traceStateElemChildren = [stateVarElems];
    if (model.animationExists && model.enableAnimationView) {
        // traceStateElemChildren.push(vizSvg);
    }
    let traceStateElem = m("div", { "class": "trace-state tlc-state", "data-testid": "trace-state-elem" }, traceStateElemChildren);
    return traceStateElem;
}

// TODO: Flesh out trace state visualization more thoroughly.
function traceStateView(state) {
    let sobj = state.getStateObj();
    let serverProcs = sobj["semaphore"].getDomain();
    let clientProcs = sobj["clientlocks"].getDomain();
    let serverProcElems = serverProcs.map((p, i) => {
        let col = sobj["semaphore"].applyArg(p).getVal() ? "red" : "gray";
        return m("circle", { fill: col, cx: 10 + 20 * i, cy: 10, r: 5 });
    })
    let clientProcElems = clientProcs.map((p, i) => {
        return m("circle", { fill: "gray", cx: 10 + 20 * i, cy: 25, r: 5 });
    })

    return m("svg", { width: 100, height: 50 }, serverProcElems.concat(clientProcElems));
}

function componentTraceViewer(hidden) {
    // Show loading state if trace is being loaded
    if (model.traceLoadingInProgress) {
        return m("div", { hidden: hidden }, [
            m("div", { class: "pane-heading", id: "", style: "margin-top: 10px;" }, [
                m("div", { class: "alert alert-info" }, [
                    m("div", { class: "d-flex align-items-center" }, [
                        m("div", { class: "spinner-border spinner-border-sm me-2" }),
                        m("div", [
                            "Loading trace... ",
                            m("span", { class: "badge bg-secondary" }, 
                                `State ${model.traceLoadingProgress.currentState} of ${model.traceLoadingProgress.totalStates}`
                            )
                        ])
                    ])
                ])
            ])
        ]);
    }

    // Show error state if trace loading failed
    if (model.traceLoadingError) {
        return m("div", { hidden: hidden }, [
            m("div", { class: "pane-heading", id: "", style: "margin-top: 10px;"  }, [
                m("div", { class: "alert alert-danger" }, [
                    m("strong", "Error loading trace: "),
                    model.traceLoadingError
                ])
            ])
        ]);
    }

    // let stateInd = 0;
    let traceElems = [];
    for (var ind = 0; ind < model.currTrace.length; ind++) {
        let state = model.currTrace[ind];
        let actionId = model.currTraceActions[ind][0];
        let isLastState = ind === model.currTrace.length - 1;
        let traceStateElem = componentTraceViewerState(state, ind, isLastState, actionId);
        traceElems.push(traceStateElem);
    }

    let children = [
        model.tracePaneHidden ? "" : componentButtonsContainer(),
    ];

    if (!model.tracePaneHidden && model.hiddenStateVars.length > 0) {
        children.push(componentHiddenStateVars(model.tracePaneHidden));
    }

    if (model.animationExists) {
        let animSwitch = m("div", { class: "form-check form-switch" }, [
            m("input", {
                class: "form-check-input",
                type: "checkbox",
                role: "switch",
                id: "animateSwitchCheck",
                onclick: function (event) {
                    model.enableAnimationView = this.checked;
                }
            }),
            m("label", {
                class: "form-check-label",
                for: "animateSwitchCheck",
                role: "switch"
            }, "Show animation")
        ]);
    }

    return m("div", { hidden: hidden }, [
        m("div", { class: "pane-heading", id: "trace-state-heading" }, children),
        m("div", { id: "trace", hidden: model.tracePaneHidden }, traceElems)
    ])
}

// Re-execute a trace based on a given list of state hashes.
function loadTraceWebWorker(stateHashList){
    // Clear any existing worker
    if (model.traceLoadingWorker) {
        model.traceLoadingWorker.terminate();
    }

    // Initialize trace loading state
    model.traceLoadingWorker = new Worker("js/worker.js");
    model.traceLoadingInProgress = true;
    model.traceLoadingProgress = { currentState: 0, totalStates: stateHashList.length };
    model.traceLoadingError = null;
    model.traceLoadingStart = performance.now();

    // Set up message handler
    model.traceLoadingWorker.onmessage = function(e) {
        let response = e.data;
        console.log("Message received from trace loading worker:", response);

        if (response.type === "progress") {
            model.traceLoadingProgress = {
                currentState: response.currentState,
                totalStates: response.totalStates
            };
            m.redraw();
        }
        else if (response.type === "error") {
            model.traceLoadingError = response.error;
            model.traceLoadingInProgress = false;
            m.redraw();
        }
        else if (response.type === "complete") {

            // Reset trace and load in the computed trace states.
            resetTrace();

            // Add each computed state into the current trace here.
            for (let stateInfo of response.trace) {
                console.log("stateInfo:", stateInfo);
                let stateObj = stateInfo[0];

                let stateDeserialized = TLAState.fromJSON(stateObj);
                let quantBoundsDeserialized = _.mapValues(stateInfo[3], (v, k) => {
                    return TLAValue.fromJSON(v);
                });
                console.log("quantBoundsDeserialized:", quantBoundsDeserialized);

                model.currTrace.push({"state": stateDeserialized, "quant_bound": quantBoundsDeserialized});
                model.currTraceActions.push([stateInfo[1], stateInfo[2], quantBoundsDeserialized]);
            }

            // console.log("model.currTrace:", model.currTrace);
            // console.log("model.CURR TRACE ACTIONS:", model.currTraceActions);

            // Re-compute the current set of next states.
            let nextStates = recomputeNextStates(model.currTrace[model.currTrace.length - 1]["state"]);
            model.currNextStates = _.cloneDeep(nextStates);
    
            updateTraceRouteParams();
            
            model.traceLoadingInProgress = false;
            const duration = performance.now() - model.traceLoadingStart;
            console.log(`Trace loading completed in ${duration.toFixed(1)}ms`);
            m.redraw();
        }
    };

    // Send initial message to worker
    model.traceLoadingWorker.postMessage({
        action: "loadTrace",
        stateHashList: stateHashList,
        newText: model.specText,
        specPath: model.specPath,
        constValInputs: model.specConstInputVals
    });
}

// TODO: Think about more fully fledged worker execution framework.
function startCheckInvariantWebWorker(invariantExpr){
    invCheckerWebWorker = new Worker("js/worker.js");
    model.invariantCheckerStart = performance.now()
    model.invariantCheckerRunning = true;
    invCheckerWebWorker.postMessage({
        action: "checkInvariant",
        newText: model.specText,
        specPath: model.specPath,
        constValInputs: model.specConstInputVals,
        invariantExpr: invariantExpr
    });
    console.log("Posted message to invariant checking worker.");

    invCheckerWebWorker.onmessage = function(e) {
        console.log("Message received from worker");
        let response = e.data;
        console.log("Response from worker:", response);
        model.generatingInitStates = false;
        m.redraw();

        model.invariantCheckerRunning = false;

        if(response.invHolds !== undefined && !response.invHolds){
            // TODO: Display invariant violation.
            console.log("Invariant violation detected.");
            // Reconstruct trace from hash trace
            let traceStates = [];
            resetTrace()
            for (let stateHash of response.hashTrace) {
                chooseNextState(stateHash)
            }
            model.invariantViolated = true;
            model.invariantCheckingDuration = performance.now() - model.invariantCheckerStart;
            model.invariantCheckingResponse = response;
            // Switch to trace tab after finding invariant violation
            // model.currPane = Pane.Trace;
        }

        if(response.invHolds !== undefined && response.invHolds){
            model.invariantCheckingDuration = performance.now() - model.invariantCheckerStart;
            model.invariantCheckingResponse = response;
        }
        m.redraw();
    };
}

// Called when an updated spec is finished being re-parsed.
function onSpecParse(newText, parsedSpecTree, spec){

    model.spec = spec;
    model.specText = newText;
    model.specTreeObjs = parsedSpecTree;
    model.errorObj = null;
    model.actions = parsedSpecTree.actions;

    model.currTrace = [];
    model.currNextStates = [];
    model.replInput = "";

    let hasInit = model.spec.hasDefinitionByName("Init");
    let hasNext = model.spec.hasDefinitionByName("Next");

    // 
    // Now we allow specs without an Init or Next explicitly defined 
    // e.g. if people want to play around as a calculator/scratchpad.
    // 
    // if (!hasInit || !hasNext) {
        // console.log("Warning: 'Init' or 'Next' predicate not found.");
        // let errMsg = "";
        // if (!hasInit) {
        //     errMsg = "Initial state predicate missing. Please define one as 'Init'."
        // } else if (!hasNext) {
        //     errMsg = "Next state predicate missing. Please define one as 'Next'."
        // }
        // model.errorObj = { message: "ERROR: " + errMsg, errorPos: null };
        // return;
    // }

    model.rootModName = model.specTreeObjs["root_mod_name"];
    model.specConsts = model.specTreeObjs["const_decls"];
    model.specDefs = model.specTreeObjs["op_defs"];
    model.specAlias = model.specTreeObjs["op_defs"]["Alias"];

    model.animationExists = model.spec.hasDefinitionByName(model.animViewDefName);

    if(hasNext){
        model.nextStatePred = model.spec.getDefinitionByName("Next")["node"];
    }

     // Load constants if given.
     let constantParams = m.route.param("constants");
     if (constantParams) {
         console.log("CONSTANT params:", constantParams);
         model.specConstInputVals = constantParams;
         let reload = false;
         try {
             setConstantValues(reload);
         } catch (e) {
             console.error("Error setting constant values:", e);
             model.errorObj = {parseError: true, obj: e, message: e};
             return;
         }
     }

    // console.log("constinputvals:", model.specConstInputVals);
    if (!_.isEmpty(model.specConsts) && _.isEmpty(model.specConstInputVals)) {
        console.log("specConsts:", model.specConsts);
        console.log("Switching to constants pane");
        // model.currPane = Pane.Constants; // TODO: Work out pane UI.
        model.selectedTab = Tab.Constants
        m.redraw();
        return;
    }

    // const duration = (performance.now() - startTime).toFixed(1);

    reloadSpec();
}

async function handleCodeChange(editor, changes) {
    console.log("handle code change");

    model.specEditorChanges = model.specEditorChanges.concat(changes).filter(c => c !== undefined);

    // Iterate over changes.
    // if(changes){
    //     for (const change of changes) {
    //         console.log("CHANGE:", change);
    //         console.log("CHANGE:", change.from);
    //     }
    // }

    // TODO: Enable once working out concurrency issues.
    // updateRouteParams({changes: model.specEditorChanges.slice(1)});


    // Enable resizable panes (experimental).
    // $( "#initial-states" ).resizable({handles:"s"});

    // $("#code-input-pane").resizable({
    //     handles: "e",
    //     // alsoResize: "#explorer-pane",
    //     // handles: {"e": ".splitter"},
    //     // handleSelector: ".splitter",
    //     resizeHeight: false,
    // });

    // $( "#explorer-pane" ).resizable({
    // handles:"w"
    // });

    // Remove any existing line error highlights.
    var nlines = codeEditor.lineCount();
    for (var i = 0; i < nlines; i++) {
        codeEditor.removeLineClass(i, "background");
    }

    const newText = codeEditor.getValue() + '\n';
    const edits = tree && changes && changes.map(treeEditForEditorChange);

    const start = performance.now();
    if (edits) {
        for (const edit of edits) {
            tree.edit(edit);
        }
    }

    let parsedSpecTree;
    // parsedSpecTree = parseSpec(newText, model.specPath);

    let spec = new TLASpec(newText, model.specPath);
    return spec.parse().then(function(){
        console.log("SPEC WAS PARSED.", spec);
        onSpecParse(newText, spec.spec_obj, spec);
        m.redraw(); //explicitly re-draw on promise resolution.
    }).catch(function(e){
        console.log("Error parsing and loading spec.", e);
        model.errorObj = {parseError: true, obj: e, message: "Error parsing spec."};
    });
}

function resetTrace() {
    // Clear forward history when resetting
    model.forwardHistory = [];
    model.forwardHistoryActions = [];
    model.invariantViolated = false;
    model.invariantCheckingDuration = 0;

    // Clear the current trace but don't reset all parameters or reload the entire spec.
    model.currTrace = []
    model.currTraceActions = []
    model.currTraceAliasVals = []
    model.lassoTo = null;
    model.errorObj = null;

    let nextStates = recomputeInitStates();
    model.currNextStates = _.cloneDeep(nextStates);

    updateTraceRouteParams();
}

function copyTraceLinkToClipboard() {
    let link = window.location.href;
    navigator.clipboard.writeText(link);
}

function lockTrace(){
    model.lockedTrace = model.currTrace;
    model.lockedTraceActions = model.currTraceActions;
}

function unlockTrace(){
    model.lockedTrace = null;
    model.lockedTraceActions = null;
}

function linkIcon(){
    return m("svg", {
        xmlns: "http://www.w3.org/2000/svg",
        // width: "16",
        // height: "16", 
        style: {"width":"16px", "height":"16px", "margin-bottom":"3px"},
        fill: "currentColor",
        class: "bi bi-link fancy",
        viewBox: "0 0 16 16"
    }, [
        m("path", {
            d: "M6.354 5.5H4a3 3 0 0 0 0 6h3a3 3 0 0 0 2.83-4H9q-.13 0-.25.031A2 2 0 0 1 7 10.5H4a2 2 0 1 1 0-4h1.535c.218-.376.495-.714.82-1z"
        }),
        m("path", {
            d: "M9 5.5a3 3 0 0 0-2.83 4h1.098A2 2 0 0 1 9 6.5h3a2 2 0 1 1 0 4h-1.535a4 4 0 0 1-.82 1H12a3 3 0 1 0 0-6z"
        })
    ])
}

function gearIcon(){
    return m("svg", {
        xmlns: "http://www.w3.org/2000/svg",
        // width: "16",
        // height: "16",
        style: {"width":"16px", "height":"16px", "margin-bottom":"3px"},
        fill: "currentColor",
        class: "bi bi-gear",
        viewBox: "0 0 16 16"
    }, [
        m("path", {
            d: "M8 4.754a3.246 3.246 0 1 0 0 6.492 3.246 3.246 0 0 0 0-6.492M5.754 8a2.246 2.246 0 1 1 4.492 0 2.246 2.246 0 0 1-4.492 0"
        }),
        m("path", {
            d: "M9.796 1.343c-.527-1.79-3.065-1.79-3.592 0l-.094.319a.873.873 0 0 1-1.255.52l-.292-.16c-1.64-.892-3.433.902-2.54 2.541l.159.292a.873.873 0 0 1-.52 1.255l-.319.094c-1.79.527-1.79 3.065 0 3.592l.319.094a.873.873 0 0 1 .52 1.255l-.16.292c-.892 1.64.901 3.434 2.541 2.54l.292-.159a.873.873 0 0 1 1.255.52l.094.319c.527 1.79 3.065 1.79 3.592 0l.094-.319a.873.873 0 0 1 1.255-.52l.292.16c1.64.893 3.434-.902 2.54-2.541l-.159-.292a.873.873 0 0 1 .52-1.255l.319-.094c1.79-.527 1.79-3.065 0-3.592l-.319-.094a.873.873 0 0 1-.52-1.255l.16-.292c.893-1.64-.902-3.433-2.541-2.54l-.292.159a.873.873 0 0 1-1.255-.52zm-2.633.283c.246-.835 1.428-.835 1.674 0l.094.319a1.873 1.873 0 0 0 2.693 1.115l.291-.16c.764-.415 1.6.42 1.184 1.185l-.159.292a1.873 1.873 0 0 0 1.116 2.692l.318.094c.835.246.835 1.428 0 1.674l-.319.094a1.873 1.873 0 0 0-1.115 2.693l.16.291c.415.764-.42 1.6-1.185 1.184l-.291-.159a1.873 1.873 0 0 0-2.693 1.116l-.094.318c-.246.835-1.428.835-1.674 0l-.094-.319a1.873 1.873 0 0 0-2.692-1.115l-.292.16c-.764.415-1.6-.42-1.184-1.185l.159-.291A1.873 1.873 0 0 0 1.945 8.93l-.319-.094c-.835-.246-.835-1.428 0-1.674l.319-.094A1.873 1.873 0 0 0 3.06 4.377l-.16-.292c-.415-.764.42-1.6 1.185-1.184l.292.159a1.873 1.873 0 0 0 2.692-1.115z"
        })
    ])
}

function trashIcon(){
    return m("svg", {
        xmlns: "http://www.w3.org/2000/svg",
        style: {"width":"9px", "height":"9px"},
        fill: "currentColor",
        class: "bi bi-trash",
        viewBox: "0 0 16 16"
    }, [
        m("path", {
            d: "M5.5 5.5A.5.5 0 0 1 6 6v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m2.5 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m3 .5a.5.5 0 0 0-1 0v6a.5.5 0 0 0 1 0z"
        }),
        m("path", {
            d: "M14.5 3a1 1 0 0 1-1 1H13v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V4h-.5a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1H6a1 1 0 0 1 1-1h2a1 1 0 0 1 1 1h3.5a1 1 0 0 1 1 1zM4.118 4 4 4.059V13a1 1 0 0 0 1 1h6a1 1 0 0 0 1-1V4.059L11.882 4zM2.5 3h11V2h-11z"
        })
    ])
}

function explodeButtonDropdown(){
    // Just limit to trace explosion on SetValues for now.
    let explodableConsts = Object.keys(model.specConstVals).filter(k => model.specConstVals[k] instanceof SetValue);

    if(explodableConsts.length === 0){
        return ""
    }

    return m("div", {class:"btn-group", role:"group"}, [
        m("button", { 
            class: "btn btn-sm btn-outline-primary " + (model.explodedConstantExpr === null ? " dropdown-toggle" : ""), 
            "data-bs-toggle": "dropdown",
            "aria-expanded": false,
            onclick: function(){
                // Unexplode.
                if(model.explodedConstantExpr !== null){
                    model.explodedConstantExpr = null;
                    updateTraceRouteParams();
                }
            }
        }, model.explodedConstantExpr === null ? "Explode" : "Unexplode"),
        m("ul", {"class": "dropdown-menu", hidden: model.explodedConstantExpr !== null}, explodableConsts.map(k => {
            return m("span", {
                style:"cursor:pointer;",
                onclick: function(){
                    model.explodedConstantExpr = k;
                    updateTraceRouteParams();

                }
            }, [m("li", {class: "dropdown-item"}, k)])
        }))
    ])
}

function toggleTracePaneButton(){
    return m("button", {
        class: "btn btn-sm btn-outline-primary", 
        hidden: (model.debug !== 1),
        onclick: () => {
            model.tracePaneHidden = !model.tracePaneHidden;
        }
    }, "Toggle Pane")
}

function componentButtonsContainer() {
    return [m("div", {class: "btn-toolbar", role:"toolbar"}, [
        m("div", { id: "trace-buttons", class:"btn-group mr-2", role:"group" }, [
            m("button", { 
                class: "btn btn-sm btn-outline-primary button-bagse", 
                id: "trace-back-button", 
                disabled: model.currTrace.length <= 1,
                onclick: traceStepBack 
            }, "Back"),
            m("button", { 
                class: "btn btn-sm btn-outline-primary button-bagse", 
                id: "trace-forward-button", 
                disabled: model.forwardHistory.length === 0,
                onclick: traceStepForward 
            }, "Forward"),
            m("button", { 
                class: "btn btn-sm btn-outline-primary button-bagse", 
                id: "trace-reset-button", 
                "data-testid": "trace-reset-button",
                onclick: resetTrace 
            }, "Reset"),
            // Explode dropdown.
            explodeButtonDropdown(),
            m("button", { 
                class: "btn btn-sm btn-outline-primary button-bagse" + (model.copyLinkPressCooldown ? " disabled" : ""), 
                id: "trace-refset-button", 
                style: {"opacity": model.copyLinkPressCooldown ? "0.6" : "1"},
                onclick: (e) => {
                    copyTraceLinkToClipboard();
                    this.innerHTML = "coped"
                    model.copyLinkPressCooldown = true;
                    setTimeout(() => {model.copyLinkPressCooldown = false;m.redraw();}, 900)
                }
            }, [linkIcon(), model.copyLinkPressCooldown ? 
                                m("span", {class: "", style: {}}, " Copy Link") : 
                                m("span", {class: "fancy"}, " Copy Link")]
                            ),
            m("button", { 
                class: "btn btn-sm btn-outline-primary", 
                disabled: model.traceExprInputText.length === 0,
                id: "trace-reset-button", 
                onclick: () => addTraceExpr(model.traceExprInputText) 
            }, "Add trace expression"),
            m("input", {
                class: "form-control form-control-sm",
                style: "font-family:monospace;width:230px;font-size:11px",
                id: "trace-expr-infput",
                placeholder: "Enter TLA+ trace expression.",
                value: model.traceExprInputText,
                oninput: e => { model.traceExprInputText = e.target.value }
            }),
            // toggleTracePaneButton(),
            // m("br"),
            // m("div", {}, model.hiddenStateVars.map(v => m("div", v)))
        ]),
        

    ])
        
        

    // m("div", { id: "trace-buttons", class:"input-group mb-3" }, [


];
}

function componentHiddenStateVars(hidden) {
    let titleElem = m("span", { style: "font-weight:bold" }, model.hiddenStateVars.length === 0 ? "" : "Hidden variables:")
    let hiddenStateVarElems = model.hiddenStateVars.map(vname => {
        return m("span", {
            class: "hidden-state-var",
            style: "padding-left:3px;",
            onclick: function () {
                _.remove(model.hiddenStateVars, (x) => x === vname);
                updateTraceRouteParams();
            },
        }, vname)
    })

    // Button to unhide all hidden state vars at once.
    let unhideAllElem = m("span", {
        class: "",
        style: "padding-left:3px;cursor:pointer;",
        onclick: function () { model.hiddenStateVars = []; updateTraceRouteParams(); }
    }, "(Unhide All)");

    return m("div", { id: "hidden-state-vars", hidden: hidden }, [titleElem].concat(hiddenStateVarElems).concat([unhideAllElem]))
}

// function chooseConstantsPane() {
    // return componentChooseConstants();
    // return m("div", { id: "choose-constants-container" }, componentChooseConstants());
// }

function specEditorPane(hidden){
    return m("div", { id: "code-input-pane", hidden:hidden }, [
        m("div", { id: "code-container" }, [
            m("textarea", { id: "code-input" })
        ])
    ]);
}

function stateSelectionPane(hidden){

    let fullNextStatesSwitch = m("div", { class: "form-check form-switch show-full-next-states-switch", hidden: model.currTrace.length === 0 }, [
        m("input", {
            class: "form-check-input",
            type: "checkbox",
            role: "switch",
            id: "fullNextStatesSwitchCheck",
            onclick: function (event) {
                model.showStateDiffsInSelection = !model.showStateDiffsInSelection;
            }
        }),
        m("label", {
            class: "form-check-label",
            for: "fullNextStatesSwitchCheck",
            role: "switch"
        }, "Show full next states")
    ]);

    let fetchingInProgress = model.rootModName.length === 0 && !model.loadSpecFailed;

    // return m("div", {id:"mid-pane", hidden: hidden}, 
    return m("div", {id: "state-choices-pane", hidden: hidden}, [
        // chooseConstantsPane(),
        fullNextStatesSwitch,
        // m("h5", { id: "poss-next-states-title", class: "" }, (model.currTrace.length > 0) ? "Choose Next Action" : "Choose Initial State"),
        m("div", { id: "initial-states", class: "tlc-state" }, [
            model.currTrace.length === 0 && model.nextStatePred !== null ? m("div", {style: "padding:10px;", id:"choose-initial-state-title"}, "Choose Initial State") : m("span"),
            model.nextStatePred === null && !fetchingInProgress ? m("div", {style: "padding:20px;"}, "No transition relation found. Spec can be explored in the REPL.") : m("span"),
            componentNextStateChoices()
        ]),
    ]);    
}

function loadSpecBox(hidden){
    let loadFailedErrMsg = "Error fetching spec from given URL. Make sure the link is to a raw TLA+ file.";

    // return m("div", { id: "load-spec-box", hidden: !model.showLoadFileBox}, [
    return m("div", { id: "load-spec-box", hidden: hidden}, [
        m("h4", "Load a specification"),
        m("h5", "Examples"),
        m("ul", {}, Object.keys(exampleSpecs).map( function(k) {
            return m("li", {}, m("a",{onclick: () => {
                clearRouteParams();
                model.specPath = exampleSpecs[k].specpath;
                model.currTrace = [];
                model.currNextStates = [];
                model.allInitStates = [];
                model.traceExprs = [];
                model.rootModName = "";
                model.explodedConstantExpr = null;
                updateTraceRouteParams();
                loadSpecFromPath(model.specPath)
                if(exampleSpecs[k].constant_vals !== undefined){
                    for(const constDecl in exampleSpecs[k].constant_vals){
                        model.specConstInputVals[constDecl] = exampleSpecs[k].constant_vals[constDecl];
                    }
                    setConstantValues();
                }
                model.showLoadFileBox = !model.showLoadFileBox;
            }
            }, k));
        })),
        m("h5", "From local file"),
        m("div", { class: "input-group mb-3" }, [
            m("input", {
                id: "formFile", 
                type: "file", 
                text: "file upload",
                class: "form-control form-control-sm",
                onchange: e => {
                    file = e.target.files[0];
                    reader = new FileReader();
                    reader.onload = (e) => {
                        model.rootModName = "";
                        let specText = e.target.result;
                        let specPath = null;
                        model.specPath = specPath
                        loadSpecText(specText, specPath)
                        model.showLoadFileBox = !model.showLoadFileBox;
                        // Clear the current trace.
                        model.currTrace = [];
                        model.specConstInputVals = {};
                        updateTraceRouteParams();
                    };
                    reader.readAsText(file);
                }
            }, "File upload:"),
        ]),
        m("h5", "From URL"),
        m("div", { class: "input-group mb-3" }, [
            m("button", {
                id:"load-spec-urfl-button", 
                class: "btn btn-sm btn-secondary",
                "data-testid": "load-spec-button",
                onclick: () => {
                    model.rootModName = "";
                    model.specPath = model.specUrlInputText;
                    model.specConstInputVals = {};
                    updateTraceRouteParams();
                    loadSpecFromPath(model.specPath);
                    // reloadSpec();
                    model.showLoadFileBox = !model.showLoadFileBox;
                }
            }, "Load"),
            m("input", {
                type:"text", 
                text:"file upload", 
                class:"form-control form-control-sm" + (model.loadSpecFailed ? " is-invalid" : ""),
                placeholder: "URL to .tla file.",
                "data-testid": "load-spec-url-input",
                oninput: e => { model.specUrlInputText = e.target.value }
            }, "From URL upload:"),
        ]),
        m("div", model.loadSpecFailed ? loadFailedErrMsg : "")
    ])
}

function headerTabBar() {
    let activeClasses = "nav-link active";
    let tabs = [
        m("li", {
            // id: "state-selection-tab-button",
            class: "nav-item",
            onclick: () => model.selectedTab = Tab.StateSelection,
            // style: "background-color:" + ((model.selectedTab === Tab.StateSelection) ? "lightgray" : "none")
        }, m("a", {class: model.selectedTab === Tab.StateSelection ? "nav-link active" : "nav-link"}, "Actions")),
        m("li", {
            // id: "state-selection-tab-button",
            class: "nav-item",
            hidden: _.isEmpty(model.specConsts),
            onclick: () => model.selectedTab = Tab.Constants,
            // style: "background-color:" + ((model.selectedTab === Tab.StateSelection) ? "lightgray" : "none")
        }, m("a", {class: model.selectedTab === Tab.Constants ? "nav-link active" : "nav-link"}, "Constants")),
        m("li", {
            // id: "spec-editor-tab-button", 
            class: "nav-item",
            onclick: () => model.selectedTab = Tab.SpecEditor,
            // style: "background-color:" + ((model.selectedTab === Tab.SpecEditor) ? "lightgray" : "none")
        }, m("a", {class: model.selectedTab === Tab.SpecEditor ? "nav-link active" : "nav-link"}, "Spec")),
        m("li", {
            // id: "spec-editor-tab-button", 
            class: "nav-item",
            onclick: () => model.selectedTab = Tab.Load,
            // style: "background-color:" + ((model.selectedTab === Tab.SpecEditor) ? "lightgray" : "none")
        }, m("a", {class: model.selectedTab === Tab.Load ? "nav-link active" : "nav-link"}, "Load"))
    ]
    let debug_tabs = [
        m("div", {
            // id: "eval-graph-tab-button", 
            class: "nav-item",
            onclick: () => {
                model.selectedTab = Tab.EvalGraph;
                model.tracePaneHidden = true;
            }
            // style: "background-color:" + ((model.selectedTab === Tab.EvalGraph) ? "lightgray" : "none")
        }, m("a", {class: model.selectedTab === Tab.EvalGraph ? "nav-link active" : "nav-link"}, "Eval Graph")),
    ]
    if (model.debug === 1) {
        tabs = tabs.concat(debug_tabs);
    }

    // tabs = tabs.concat(specName);
    
    // TODO: Enable this spec loading button and box.
    // tabs = tabs.concat(loadFile);

    let navStyle = "nav-tabs";
    // let navStyle = "nav-pills";
    return m("div", {}, [
        m("ul", { class: `nav ${navStyle}` }, tabs)
    ]);
}

function loadPane(hidden){
    // let specName = m("div", { id: "spec-name-header" }, "Root spec: " + model.rootModName + ".tla")
    let loadFile = m("div", { id: "load-spec-button", onclick: () => model.showLoadFileBox = true }, "Load spec");
    // return m("div", {}, [loadFile]);
    return loadSpecBox(hidden);
}

function midPane() {
    let tabs = [
        headerTabBar(),
        stateSelectionPane(model.selectedTab !== Tab.StateSelection),
        componentChooseConstants(model.selectedTab !== Tab.Constants),
        specEditorPane(model.selectedTab !== Tab.SpecEditor),
        loadPane(model.selectedTab !== Tab.Load)
    ];
    let debug_tabs = [
        componentEvalGraphPane(model.selectedTab !== Tab.EvalGraph)
    ];
    if (model.debug === 1) {
        tabs = tabs.concat(debug_tabs);
    }
    return [
        m("div", { 
            id: "mid-pane", 
            style: {width: model.tracePaneHidden ? "90%" : "40%"} 
        }, tabs)
    ];
}

// 
// Event handlers for pane resizing.
// 

let resize_initial_pos_x = null;
function resize_mousemove(e){
    const leftPane = document.querySelector("#mid-pane");
    const rightPane = document.querySelector("#trace-container");
    const panelContainer = document.querySelector(".panel-container");

    // Expand/contract left and right panes.
    leftPane.style.width = e.x - leftPane.getBoundingClientRect().left + 'px';
    rightPane.style.width = panelContainer.getBoundingClientRect().width - e.x + 'px';
}

function resize_mouseup(e){
    // Remove all resizing event listeners.
    window.removeEventListener('mousemove', resize_mousemove);
    window.removeEventListener('mouseup', resize_mouseup);
}

function tracePane() {
    let tabs = [
        m("li", {
            class: "nav-item",
            onclick: () => model.selectedTraceTab = TraceTab.Trace,
            ondblclick: () => {
                model.tracePaneHidden = true;
            },
        }, m("a", {class: model.selectedTraceTab === TraceTab.Trace ? "nav-link active" : "nav-link"}, "Trace")),
        m("li", {
            class: "nav-item",
            onclick: () => model.selectedTraceTab = TraceTab.REPL,
        }, m("a", {class: model.selectedTraceTab === TraceTab.REPL ? "nav-link active" : "nav-link"}, "REPL"))
    ]

    if (model.animationExists) {
        let animTab = m("li", {
            class: "nav-item",
            onclick: function () {
                model.selectedTraceTab = TraceTab.Animation;
                model.enableAnimationView = true;
            },
        }, m("a", { class: model.selectedTraceTab === TraceTab.Animation ? "nav-link active" : "nav-link" }, "Animation"));
        tabs.push(animTab);
    }

    // Add invariant checking tab.
    tabs.push(
        m("li", {
            class: "nav-item",
            onclick: () => model.selectedTraceTab = TraceTab.Check,
        }, [
            m("a", {class: model.selectedTraceTab === TraceTab.Check ? "nav-link active" : "nav-link"}, [
                "Check",
                m("img", {
                    style: {"width": "17px", "height": "17px", "margin-left": "5px", "margin-bottom": "3px"},
                    // class: "hide-var-icon",
                    hidden: !model.invariantCheckerRunning,
                    src: "assets/gear-spinner.svg",
                })
            ])
        ])
    )


    // tabs = tabs.concat(specName);
    
    // TODO: Enable this spec loading button and box.
    // tabs = tabs.concat(loadFile);

    let navStyle = "nav-tabs";
    // let navStyle = "nav-pills";
    tabs =  m("div", {}, [
        m("ul", { class: `nav ${navStyle}` }, tabs)
    ]);


    // return 
    // m("span", [
        // m("div", { id: "poss-next-states-title", class: "pane-title" }, (model.currTrace.length > 0) ? "Choose Next State" : "Choose Initial State"),
        // m("div", { id: "initial-states", class: "tlc-state" }, componentNextStateChoices()),
    
    let otherTabs = [
        componentTraceViewer(model.selectedTraceTab !== TraceTab.Trace),
        replPane(model.selectedTraceTab !== TraceTab.REPL),
        checkPane(model.selectedTraceTab !== TraceTab.Check)
    ]

    if(model.animationExists){
        otherTabs.push(animationPane(model.selectedTraceTab !== TraceTab.Animation));   
    }

    if(model.tracePaneHidden){
        return toggleTracePaneButton();
    }

    return m("div", { 
            id: "trace-container", 
            style: {width: model.tracePaneHidden ? "5%" : "60%"}
        }, [
        tabs,
        otherTabs
    ]);
}

function replResult(){
    if(model.replResult !== null && model.replError === false){
        return model.replResult.toString();
    } else{
        return "";
    }
}

function traceStateCounter(){
    let style = {"font-size": "14px"};
    if(model.forwardHistory.length > 0){
        return m("div", {style: style}, `Trace state ${model.currTrace.length} / ${model.currTrace.length + model.forwardHistory.length}`);
    } else{
        return m("div", {style: style}, `Trace state ${model.currTrace.length}`);
    }
}

function animationPane(hidden) {
    if (model.animationExists && model.enableAnimationView && model.currTrace.length > 0) {
        // Last state in trace.
        let state = model.currTrace[model.currTrace.length - 1]["state"];
        // If hidden, no need to compute the animation view.
        viewSvgObj = m("span", "");
        if(!hidden){
            viewSvgObj = animationViewForTraceState(state);
        }

        if(viewSvgObj === null){
            return m("div", { hidden: hidden }, [
                componentButtonsContainer(),
                m("div", { id: "anim-div", style: "color:red;" }, `Error evaluating animation view expression: '${model.animViewDefName}'.`)
            ]);
        }

        return m("div", { hidden: hidden }, [
            componentButtonsContainer(),
            traceStateCounter(),
            m("div", { id: "anim-div" }, m("svg", { width: "100%", height: "100%", viewBox: "0 0 200 240" }, [viewSvgObj]))
        ]);
    }
}


function replPane(hidden) {
    let replErrColor = (!model.replError || model.replInput === "" ? "" : "#FF9494");
    return m("div", {hidden: hidden}, [
        // m("h4", { id: "repl-title", class: "panje-title" }, "REPL Input"),
        m("div", { id: "repl-container" }, [
            m("input", {
                class: "replf-input form-control",
                id: `repl-input`,
                size: 50,
                style:{"background-color": replErrColor},
                oninput: (e) => {
                    model.replInput = e.target.value
                    model.replError = false;
                    let ctx = new Context(null, new TLAState({}), model.specDefs, {}, model.specConstVals);
                    try {
                        // All definitions in the root module should be accessible.
                        ctx["defns_curr_context"] = _.keys(model.spec.spec_obj["op_defs"]);
                        ctx.setGlobalDefTable(model.spec.globalDefTable);
                        ctx.setSpecObj(model.spec);
                        let res = evalExprStrInContext(ctx, model.replInput);
                        model.replResult = res;
                    } catch (error) {
                        // swallow parse errors here.
                        model.replError = true;
                        console.log("swallowing parse errors during repl evaluation.", error);
                    }
                },
                value: model.replInput,
                placeholder: "Enter TLA+ expression."
            }),
            m("h5", { id: "repl-tifftle", class: "panje-title", style:"margin-top:20px" }, "Result"),
            m("div", { id: "repl-result" }, replResult())
        ])
    ]);
}

function checkPane(hidden) {
    let invCheckStatesExplored = 0;
    if(model.invariantCheckingResponse !== undefined){
        invCheckStatesExplored = model.invariantCheckingResponse.numStatesExplored; 
    }
    return m("div", {hidden: hidden, style: {margin: "20px"}}, [
        m("div", {style: {display: "flex", gap: "10px"}}, [
            m("input", {
                class: "form-control",
                placeholder: "Enter TLA+ state predicate.",
                value: model.invariantExprToCheck,
                style: {width: "500px", "font-family": "monospace", "font-size": "14px"},
                oninput: (e) => model.invariantExprToCheck = e.target.value
            }),
            m("button", {
                class: "btn btn-primary",
                disabled: model.invariantExprToCheck === "" || model.invariantCheckerRunning,
                onclick: () => {
                    console.log(`Starting web worker for checking invariant expression: '${model.invariantExprToCheck}'.`)
                    model.invariantViolated = false;
                    startCheckInvariantWebWorker(model.invariantExprToCheck);
                }
            }, [
                gearIcon(),
                " Check Invariant"
            ]),
            m("button", {
                class: "btn btn-primary btn-danger",
                disabled: !model.invariantCheckerRunning,
                onclick: () => {
                    console.log(`Stopping web worker for checking invariant expression: '${model.invariantExprToCheck}'.`)
                    model.invariantViolated = false;
                    model.invariantCheckerRunning = false;
                    invCheckerWebWorker.terminate();
                    m.redraw();
                }
            }, [
                "Stop"
            ]),
        ]),
        m("div", {hidden: !model.invariantViolated, style: {color: "red"}}, [
            `Invariant violated in ${model.invariantCheckingDuration.toFixed(0)}ms, ${invCheckStatesExplored} distinct states explored (`,
            m("a", {
                style: {cursor: "pointer", textDecoration: "underline"},
                onclick: () => model.selectedTraceTab = TraceTab.Trace
            }, "View Trace"),
            ")"
        ]),
        m("div", {hidden: !(!model.invariantViolated && model.invariantCheckingDuration > 0 && !model.invariantCheckerRunning), style: {color: "green"}}, [
            `Invariant passed in ${model.invariantCheckingDuration.toFixed(0)}ms, ${invCheckStatesExplored} distinct states explored.`,
        ])
    ]);
}
// To be used for selecting different panes when/if we add that UI functionality.
function componentPaneSelector() {
    return m("div", { id: "pane-selector" }, [
        m("table", { id: "pane-button-container", style: "margin:0 auto;" }, [
            m("tr", {}, [
                m("td", {
                    class: "pane-select-button " + (model.currPane === Pane.Constants ? "selected" : ""),
                    onclick: () => model.currPane = Pane.Constants
                }, "Constants"),
                m("td", {
                    class: "pane-select-button " + (model.currPane === Pane.Trace ? "selected" : ""),
                    onclick: () => model.currPane = Pane.Trace
                }, "Trace"),
            ])
        ])
    ])
}

function resizeGutter() {
    return m("div", { 
        class: "resize-gutter",
        onmousedown: (e) => {
            // resizer(e)
            e.preventDefault()
            resize_initial_pos_x = e.x;
            window.addEventListener('mousemove', resize_mousemove);
            window.addEventListener('mouseup', resize_mouseup);
        },
        onmouseup: (e) => {
            window.removeEventListener('mousemove', resize_mousemove);
        },
        ondragstart : function() { return false; }
    }
    // , m("img", {
    //     class: "resize-gutter-handle",
    //     style: {
    //         position: "absolute", 
    //         top: "50%", 
    //         transform: "translateY(-50%)", 
    //         "text-align": "center",
    //         "opacity": 0.8
    //     },
    //     "src": "assets/drag-handle-svgrepo-com.svg",
    //     onmousedown: (e) => {
    //         // resizer(e)
    //         resize_initial_pos_x = e.x;
    //         window.addEventListener('mousemove', resize_mousemove);
    //         window.addEventListener('mouseup', resize_mouseup);
    //     },
    //     onmouseup: (e) => {
    //         window.removeEventListener('mousemove', resize_mousemove);
    //     },
    //     ondragstart : function() { return false; }
    // }, "O")
)
}

function componentExplorerPane() {

    // TODO: Work out pane UI.
    // let paneElem = m("span", "EMPTY PANE");
    // if(model.currPane === Pane.Trace){
    //     paneElem = tracePane();
    // } 
    // if(model.currPane === Pane.Constants){
    //     paneElem = chooseConstantsPane();
    // }

    // Only show REPL pane in repl mode.
    if(model.replMode){
        return m("div", { id: "explorer-pane" }, [
            replPane()
        ]);     
    }

    return m("div", { id: "explorer-pane" }, [
        // chooseConstantsPane(),
        midPane(),
        tracePane()
    ])
}

function componentEvalGraphPane(hidden){
    // Eval graph pane.
    let actionSelectButtons = [];
    if(model.actions &&model.actions.length > 1){
        actionSelectButtons = model.actions.map(action => m("button", {class: "btn btn-sm btn-outline-primary", onclick: () => {
            displayEvalGraph(evalNodeGraphsPerAction[action.id]);
        }}, action.name));
    }
    
    return m("div", {hidden: hidden}, [
        m("div", {class: "btn-group", role: "group", style: {"margin-left": "10px", "margin-bottom": "20px", "margin-top": "8px"}}, actionSelectButtons),
        m("div", { id: "eval-graph-pane", hidden: hidden }, [
            m("h4", {style: {margin:"10px"}}, "Eval graph pane"),
            m("div", { id: "eval-graph" })
        ])
    ])
}

function addTraceExpr(newTraceExpr) {
    // TODO: Also check for evaluation errors.
    if (newTraceExpr.length) {
        model.traceExprs.push(newTraceExpr);
        // Clear the input text.
        model.traceExprInputText = "";

        updateRouteParams({traceExprs: model.traceExprs});
    }
}

// function checkInv(invExpr) {
//     let interp = new TlaInterpreter();
//     let res = interp.computeReachableStates(model.specTreeObjs, model.specConstVals, invExpr);
//     if (!res["invHolds"]) {
//         let badState = res["invFirstViolatingState"];
//         console.log("bad state:", badState);
//         console.log("trace hash:", res["hashTrace"]);
//         resetTrace();
//         for (const stateHash of res["hashTrace"]) {
//             chooseNextState(stateHash);
//         }
//     }
// }

// Load any state encoded in route parameters after parsing/loading a spec.
function loadRouteParamsState() {
    // Load trace expression if given.
    let traceExpressions = m.route.param("traceExprs")
    if (traceExpressions) {
        model.traceExprs = traceExpressions;
    }

    // Load hidden state vars if given.
    let hiddenVarsStr = m.route.param("hiddenVars");
    if (hiddenVarsStr) {
        model.hiddenStateVars = hiddenVarsStr.split(",");
    }

    // Load hidden state vars if given.
    let explodedConstantExprStr = m.route.param("explodedConstantExpr");
    if (explodedConstantExprStr) {
        model.explodedConstantExpr = explodedConstantExprStr;
    }

    // Check for animation parameter and switch to animation tab if available
    let animParam = m.route.param("anim");
    if (animParam === true && model.animationExists) {
        model.selectedTraceTab = TraceTab.Animation;
        model.enableAnimationView = true;
    }

    // Feature flag to use web worker for trace loading.
    const useWebWorkerLoad = true;

    // Load trace if given.
    let traceParamStr = m.route.param("trace")
    if (traceParamStr) {
        let traceParams = traceParamStr.split(",");

        if(useWebWorkerLoad){
            loadTraceWebWorker(traceParams);
            return;
        }

        // 
        // Older way of simply re-computing full trace directly in this thread.
        // Keeping around in case we want to revert at any point.
        // 

        for (const stateHash of traceParams) {
            // Check each state for possible quant bounds hash,
            // if it has one.
            let stateAndQuantBounds = stateHash.split("_");
            let rethrow = true;
            if (stateAndQuantBounds.length > 1) {
                let justStateHash = stateAndQuantBounds[0];
                let quantBoundHash = stateAndQuantBounds[1];
                chooseNextState(justStateHash, quantBoundHash, rethrow);
            } else {
                chooseNextState(stateHash, undefined, rethrow);
            }
        }
    }
}

//
// Load spec from given spec text and reload it in the editor pane and UI.
// Given 'specPath' may be null if spec is loaded from a file directly.
//
function loadSpecText(text, specPath) {
    const $codeEditor = document.querySelector('.CodeMirror');
    spec = text;
    model.specText = spec;
    model.specPath = specPath;
    model.traceExprs = [];
    model.loadSpecFailed = false;
    model.invariantViolated = false;
    model.invariantCheckingDuration = 0;
    model.invariantCheckerRunning = false;
    model.traceLoadingError = null;

    let parsedChanges = m.route.param("changes");

    let oldParams = m.route.param();
    let newParams = Object.assign(oldParams, { specpath: model.specPath });
    // May not have a specpath if we've loaded from a file, so no need to record 
    // anything in the URL.
    if (newParams["specpath"] === null) {
        delete newParams["specpath"];
    }
    m.route.set("/home", newParams);

    console.log("Retrieved spec:", specPath);
    if ($codeEditor) {
        $codeEditor.CodeMirror.setSize("100%", "100%");
        $codeEditor.CodeMirror.on("changes", () => {
            // CodeMirror listeners are not known to Mithril, so trigger an explicit redraw after
            // processing the code change.
            handleCodeChange().then(function () {
                loadRouteParamsState();
                m.redraw();
            })
        });
        $codeEditor.CodeMirror.setValue(spec);

        // Load changes if given.
        // TODO: Enable once working out concurrency subtleties.
        // if (parsedChanges) {
        //     model.specEditorChanges = parsedChanges;
        //     for(const change of parsedChanges){
        //         // $codeEditor.CodeMirror.
        //         console.log(change);
        //         $codeEditor.CodeMirror.replaceRange(change.text[0], change.from, change.to, change.origin);
        //     }
        // }

        model.selectedTab = Tab.StateSelection;
        model.selectedTraceTab = TraceTab.Trace;
    }
}

// Fetch spec from given path (e.g. URL) and reload it in the editor pane and UI.
function loadSpecFromPath(specPath){
    model.errorObj = null;
    // Download the specified spec and load it in the editor pane.
    return m.request(specPath, { responseType: "text" }).then(function (specText) {
        loadSpecText(specText, specPath);
    }).catch(function(e) {
        console.log("Error loading file ", specPath, e);
        model.loadSpecFailed = true;
    });
}

async function loadApp() {

    // Download example spec.
    // model.specPath = "./specs/simple2.tla";
    // let specPath = "./specs/simple2.tla";
    // model.specPath = "./specs/lockserver.tla";
    // let specPath = "./specs/LamportMutex.tla";
    // let specPath = "./specs/lockserver_nodefs.tla";
    // let specPath = "./specs/lockserver_nodefs_anim.tla";
    // let specPath = "./specs/MongoLoglessDynamicRaft.tla";
    // let specPath = "./specs/Paxos.tla";
    model.specPath = "./specs/TwoPhase.tla";
    // let specPath = "./specs/simple_test.tla";
    // model.specPath = "./specs/simple_lockserver.tla";


    //
    // Mithril app setup.
    //
    var root = document.body

    App = {
        count: 1,
        oncreate: function () {
            // Initialized code editor on creation of app pane.
            const codeInput = document.getElementById('code-input');
            if(codeInput){
                codeEditor = CodeMirror.fromTextArea(codeInput, {
                    lineNumbers: true,
                    showCursorWhenSelecting: true,
                    fontSize: "11px",
                    theme: "default",
                    // TODO: Work out tlaplus mode functionality for syntax highlighting.
                    // mode:"tlaplus"
                });
                // Set font size using CSS
                codeEditor.getWrapperElement().style.fontSize = "11px";
            }
        },
        onupdate: function () {
            // Keep trace viewer scrolled to bottom.
            let trace = document.getElementById("trace");
            if(trace !== null){
                trace.scrollTo(0, trace.scrollHeight);
            }

            // let oldParams = m.route.param();
            // let traceParamObj = traceHashed.length > 0 ? { trace: traceHashed.join(",") } : {}
            // let newParams = Object.assign(oldParams, {specpath: model.specPath});
            // m.route.set("/home", newParams);
        },
        view: function () {
            let fetchingInProgress = model.rootModName.length === 0 && !model.loadSpecFailed;
            let isParseErr = model.errorObj != null && model.errorObj.hasOwnProperty("parseError");

            let spinner = fetchingInProgress ? m("div", {class:"spinner-border spinner-border-sm"}) : m("span");
            let fetchingText = fetchingInProgress ? "Fetching spec... " : "";
            if(model.generatingInitStates){
                fetchingText = "(Generating initial states...) ";
                spinner = m("div", {class:"spinner-border spinner-border-sm"});
            }
            let parseError = isParseErr ? m("span", {class:"bi-exclamation-triangle", style:{"color":"red", "margin-left":"5px"}}, " Parse error.") : m("span");

            return [
                // Header.
                m("nav", { class: "navbar bg-body-tertiary border-bottom mb-2" }, [
                    m("div", { class: "container-fluid" }, [
                        m("div", [
                            m("a", {
                                id: "tla-web-explorer-title",
                                class: "navbar-brand mb-0 h1", href: "https://github.com/will62794/spectacle",
                                style: {
                                    "font-size": "20px",
                                    "text-decoration": "none",
                                }
                            }, [
                                "Spectacle",
                                m("img", { id: "glasses-logo", src: "assets/glasses-svgrepo-com.svg", style: { "height": "26px", "margin-left": "6px" } })
                            ])
                        ]),
                        m("span", { class: "navbar-text", href: "https://github.com/will62794/spectacle", style: "padding-right:15px" },
                            [
                                m("span", {}, [
                                    m("span", { style: "font-weight:bold", "font-size": "14px" }, "Root module:  "),
                                    m("span", {
                                        ondblclick: () => {
                                            model.debug = 1 - model.debug;
                                            enableEvalTracing = model.debug === 1;
                                            console.log("debug", model.debug);
                                            updateRouteParams({debug: model.debug});
                                            m.redraw();
                                        },
                                        style: {cursor: "pointer", "font-family": "monospace", "font-size": "14px"}
                                    },model.rootModName + (model.rootModName.length > 0 ? ".tla" : "")),
                                    m("span", { style: { opacity: 0.5, "font-size": "14px" } }, fetchingText),
                                    spinner,
                                    parseError
                                ]
                                )
                            ]
                        ),
                    ]),

                ]),
                // m("nav", { class: "navbar bg-body-tertiary", style:"height:30px;" }, [
                //     m("div", {class:"container-fluid"}, [
                //         m("span", {class:"py-0 mb-0 navbar-text", href: "https://github.com/will62794/tla-web"}, 
                //             [
                //                 m("span", "Root spec: " + model.rootModName + (model.rootModName.length > 0 ? ".tla" : "")),
                //                 model.rootModName.length === 0 ? m("div", {class:"spinner-border spinner-border-sm"}) : m("span")
                //             ]
                //         )
                //     ])
                // ]),

                // The main app panes.
                m("div", { class: "panel-container" }, [
                    // m("div", { id: "spec-name-fheader", style:"font-size:14px;margin-bottom:10px;width:100%;" }, "Root spec: " + model.rootModName + ".tla"),
                    // Display pane.
                    midPane(),
                    resizeGutter(),
                    tracePane()
                    // componentExplorerPane(),
                ])];
        }
    }

    EvalDebugGraph = {
        count: 1,
        oncreate: function () {
            // displayEvalGraph();
        },
        onupdate: function () {
            // Keep trace viewer scrolled to bottom.
            // displayEvalGraph();
        },
        view: function () {
            return [
                // TLA+ code pane.
                m("div", { id: "code-input-pane", style:"height:10%" }, [
                    m("div", { id: "code-container" }, [
                        m("textarea", { id: "code-input" })
                    ])
                ]),

                // Eval graph pane.
                m("div", { id: "explorer-pane" }, [
                    m("h1", "eval graph"),
                    m("div", { id: "eval-graph" })
                ])
            ];
        }
    }

    // m.mount(root, App)
    m.route(root, "/home",
        {
            "/home": App,
            "/eval_debug_graph": EvalDebugGraph,
        });


    let debug = parseInt(m.route.param("debug"));
    let showRewritten = parseInt(m.route.param("show_rewritten"));
    model.showRewritten = showRewritten;
    if(debug === 1){
        enableEvalTracing = debug === 1;
        model.debug = debug;
    }

    // Check for given spec in URL args.
    specPathArg = m.route.param("specpath");
    console.log("specpatharg", specPathArg);
    // specPathArg = urlParams["specpath"];

    // Check for repl mode.
    replArg = m.route.param("repl");
    console.log("replArg", replArg);
    model.replMode = replArg === true;

    // Load given spec.
    if (specPathArg !== undefined) {
        model.specPath = specPathArg;
    }

    // const codeInput = document.getElementById('code-input');
    // console.log(CodeMirror);
    // console.log(codeInput);
    // console.log(document.readyState);
    // codeEditor = CodeMirror.fromTextArea(codeInput, {
    //     lineNumbers: true,
    //     showCursorWhenSelecting: true,
    //     // TODO: Work out tlaplus mode functionality for syntax highlighting.
    //     // mode:"tlaplus"
    // });

    loadSpecFromPath(model.specPath);
}

/**
 * Main UI initialization logic. 
 */
async function init() {
    const codeInput = document.getElementById('code-input');

    await TreeSitter.init();
    parser = new TreeSitter();

    let tree = null;
    var ASSIGN_PRIMED = false;

    // let codeEditor = CodeMirror.fromTextArea(codeInput, {
    //     lineNumbers: true,
    //     showCursorWhenSelecting: true,
    //     // TODO: Work out tlaplus mode functionality for syntax highlighting.
    //     // mode:"tlaplus"
    // });

    // codeEditor.on('changes', handleCodeChange);

    // Load the tree-sitter TLA+ parser.
    let language;
    const url = `${LANGUAGE_BASE_URL}/tree-sitter-${languageName}.wasm`;
    try {
        language = await TreeSitter.Language.load(url);
    } catch (e) {
        console.error(e);
        return;
    }

    tree = null;
    parser.setLanguage(language);

    // Load Graphviz library for visualizations.
    Viz.instance().then(viz => {
        vizInstance = viz;
    });

    await loadApp()

    // Add keyboard event listener for navigation
    document.addEventListener('keydown', handleKeyboardNavigation);
}

function handleKeyboardNavigation(event) {
    // Only handle if we're not in an input field or textarea
    if (event.target.tagName === 'INPUT' || event.target.tagName === 'TEXTAREA') {
        return;
    }

    if (event.key === 'ArrowLeft' && model.currTrace.length > 1) {
        traceStepBack();
    } else if (event.key === 'ArrowRight') {
        traceStepForward();
    }
}

//
// Initialize the UI.
//
init();