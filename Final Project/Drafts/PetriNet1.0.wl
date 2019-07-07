(* ::Package:: *)

(* ::Title:: *)
(*PetriNet*)


(* ::Section:: *)
(*Section1, Petri Net set up*)


(* ::Subsection:: *)
(*petriNetQ*)


(* ::Text:: *)
(*PetriNetQ function checks if the input is a valid PetriNet*)
(*Input: <|"States" -> list1, "Transitions" -> list2,  "Arcs" -> list3|>*)
(*Output: True or False*)
(**)


applyBooleanToList[logic_, booleanList_]:= 
	Fold[logic, First @ booleanList, Rest @ booleanList]


check[s_, t_, a_]:= Module[
	{allPossible},
	allPossible = Split[Tuples[{t, s}],First[#1]===First[#2]&];
    Min[Length@Intersection[a,#] &/@ allPossible] > 0
]


petriNetQ[<|"States"-> s__,"Transitions"-> t__, "Arcs"-> a__|>]:= Module[{g},
	g = Graph[DirectedEdge @@@ a];
	applyBooleanToList[And, 
		{Intersection[s,t] == {}, 
		BipartiteGraphQ[g], 
		check[s, t, a]}]
]


(* ::Subsection:: *)
(*petriNet*)


(* ::Text:: *)
(*PetriNet returns the graph visualization of the petri net in a graph form.*)
(*Input: <|"States" -> list1, "Transitions" -> list2,  "Arcs" -> list3|>*)
(*Output: A graph is the input is a valid Petri Net, or tagged Failed is the input is not a Petri Net.*)


petriNet[<|"States"->s__,"Transitions"->t__, "Arcs"-> a__|>] := If[petriNetQ[<|"States"->s,"Transitions"->t, "Arcs"-> a|>], 
	{Graph[ Join[s,t], DirectedEdge @@@ a, VertexShapeFunction -> Join[Thread[s->"Circle"],Thread[t-> "Square"]],
	VertexLabels->"Name", VertexStyle-> Transparent, VertexSize->Large,GraphLayout->"BipartiteEmbedding"], 
	s,t,DirectedEdge @@@ a}, $Failed; Print["Fail!"]]


(* ::Subsection:: *)
(*petriNetInit*)


(* ::Text:: *)
(*TODO:// petriNetRun[petriNet, initial-tokens]*)
(*input: A petriNet and number of tokens in each places*)
(*output: dynamic visualization of how tokens move from state to state.*)


textDot[vertex_, n_, coordinatesDict_]:= Text[StringRepeat["\[FilledSmallCircle]", n], coordinatesDict[vertex]]


buildDotsList[coordinateDict_, vertexWeightDict_, vertices_]:= Module[
	{res = {}},
	Scan[AppendTo[res,textDot[#, vertexWeightDict[#], coordinateDict]]&, vertices];
	res
]


petriNetInit[pnet_,init_]:= Module[
	{g, coordinatesDict, vertexWeightDict, graphData, vertexWeight, vertexWeightsDict, epilog},
	g = Graph[First @ pnet, VertexWeight -> Join[Thread[Part[pnet,2] -> init], Thread[Part[pnet,3] -> 0]]];
	graphData = ToExpression @ StringReplace[(ToString[FullForm[g]]), "Graph" -> "List"];
	vertexWeight = Last @ (Last @ graphData[[3]]);
	coordinatesDict = Association @ Thread[graphData[[1]] -> VertexCoordinates /. AbsoluteOptions[g, VertexCoordinates]];
	vertexWeightsDict = Association @ Thread[graphData[[1]] -> vertexWeight];
	epilog = buildDotsList[coordinatesDict, vertexWeightsDict, graphData[[1]]];
	Graph[g, Epilog -> epilog]
]


(* ::Subsection:: *)
(*petriNetAnimate*)


(* ::Text:: *)
(*TODO:// petriNetAnimate[petriNet, initial-tokens, steps]*)
(*input: A petriNet and number of tokens in each places, and the steps that the user wants to run.*)
(*output: dynamic visualization of how tokens move from state to state in the first n steps.*)


checkFiring[pnet_, transition_, current_]:= Module[
	{tokenList},
	tokenList = Length@EdgeList[First@pnet, # \[DirectedEdge] transition] &/@ Part[pnet, 2];
	AllTrue[current - tokenList, NonNegative]
]


makeFiring[pnet_, transition_, current_]:= Module[
	{tokenDeleteList,tokenAddList},
	tokenDeleteList = Length@EdgeList[First@pnet, #\[DirectedEdge]transition] &/@ Part[pnet,2];
	tokenAddList = Length@EdgeList[First@pnet, transition\[DirectedEdge]#] &/@ Part[pnet,2];
	current - tokenDeleteList + tokenAddList
]


updateFiring[pnet_][current_]:= Module[
	{index},
	index = First @ RandomChoice[Position[checkFiring[pnet, #, current] &/@ pnet[[3]], True]];
	If[IntegerQ[index], 
	makeFiring[pnet, pnet[[3,index]], current], 
	Print["Dead!"]; Abort[]]
]


petriNetRun[pnet_, init_, step_Integer]:= Module[
	{current = init},
	current = Nest[updateFiring[pnet],current, step];
	petriNetInit[pnet,current]
]


(* ::Subsection:: *)
(*PetriNetData-User column*)


(* ::Text:: *)
(*These helper functions are used to generate and animate petri net when a user input some data that matches the petri net data format.*)


ClearAll[makeMultipleEdges];
makeMultipleEdges[<|"from"->in_,"to"->out_,"numbers"->num_|>]:= Module[{l={}},
	For[i=1,i<=num,i++, AppendTo[l,{in,out}]]; 
	l
]


ClearAll[inputTranslator];
inputTranslator[<|"Places" -> placeList_, "Transitions" -> transitionList_, "Arcs" -> arcList_, 
"Initial States"-> <|"e.g: 0,0,1"->init_|>, "Steps"-><|"Input the steps you want to animate"-> steps_|>|>]:=Module[
	{initialState},
	initialState = ToExpression /@ StringSplit[init,","];
	{<|"States"-> First /@ Values /@ placeList, 
	"Transitions"-> First/@ Values /@ transitionList,
	"Arcs"->Join @@ makeMultipleEdges /@ arcList|>, initialState, steps}
]


ClearAll[makePetriNetFromInput];
makePetriNetFromInput[input_]:= Module[
	{inputPnetData, initState, steps, pnet},
	{inputPnetData, initState, steps} = inputTranslator[input];
	pnet = petriNet[inputPnetData];
	ListAnimate[Table[petriNetRun[pnet,initState, n],{n, steps}], AnimationRate->1.5]
]


ClearAll[PetriNetGeneral];
PetriNetGeneral[]:=Module[
	{petriNet},
	petriNet = FormFunction[<|"Places" -> RepeatingElement[CompoundElement[<|"Circles"-> "String"|>]],"Transitions" -> RepeatingElement[CompoundElement[<|"Squares"-> "String"|>]],
	"Arcs" -> RepeatingElement[CompoundElement[<|"from"-> "String","to"-> "String","numbers"-> "Integer"->1|>]],
	"Initial States" -> CompoundElement[{"e.g: 0,0,1"->"String"}],
	"Steps" -> CompoundElement[{"Input the steps you want to animate"-> "Integer"->10}]|>,makePetriNetFromInput];
	petriNet[]
]


(* ::Subsection:: *)
(*Interpret chemical reactions from Wolfram Alpha and make PetriNet simulation*)


(* ::Text:: *)
(*These functions are going to make Petri Net animation by using chemical reactions as an input.*)


ClearAll[reduceParentheses];
reduceParentheses[st_String]:= Module[
	{s},
	If[StringPart[st,1] ==="(", s = StringDrop[st,1], s = st];
	If[StringPart[s,-1] ===")", s = StringDrop[s,-1], s];
	s
]


getChemicals[st_String]:= First @ StringCases[st, "[" ~~Shortest[c__]~~"]"->c]


ClearAll[getStoichiometry];
getStoichiometry[st_String]:=If[StringContainsQ[st,"^"],ToExpression@First@StringCases[st, "^" ~~number__ ->number],1]


ClearAll[inputTranslatorHelper];
inputTranslatorHelper[list_List]:= List @@@ Thread[getChemicals/@list-> getStoichiometry/@list]


ClearAll[waChemicalReaction];
waChemicalReaction[chemicalReaction_String]:= Module[
	{s,string},
	s = WolframAlpha[chemicalReaction,{{"ReactionKineticsConstant:ChemicalReactionData",1},"ComputableData"}];
	s = StringDrop[s,StringLength["K_c  =  "]];
	s = StringSplit[s, "/"];
	s = reduceParentheses/@ s;
	s = StringSplit[s," "];
	string = getChemicals/@Flatten @ s;
	s = inputTranslatorHelper /@ s;
	{s, string}
]


ClearAll[getPlaces];
getPlaces[Chem_List]:= Association /@ Thread["Circles" -> Chem]


ClearAll[getTransitions];
getTransitions[{leftChem_List,rightChem_List}] := {<|"Squares"->"T1"|>}


ClearAll[getArcs];
getArcs[{leftChems_List, rightChem_List}]:= Module[
	{left, right},
	left = Join @@ Map[{<|"from"-> "T1","to"-> #[[1]],"numbers"-> #[[2]]|>}&, leftChems];
	right = Join @@ Map[{<|"from"-> #[[1]],"to"-> "T1","numbers"-> #[[2]]|>}&, rightChem];
	Join @@ {left, right}
]


TranslateFromChemToGeneral[<|"Reactions"->{<|"Input the reactions"->st_|>},
	"Initial States"-><|"e.g: 0,0,1"->init_|>,
	"Steps"-><|"Input the steps you want to animate"->steps_|>|>]:= Module[
	{reactants, chemicals,input, inputPnetData, pnet},
	{reactants, chemicals} = waChemicalReaction[st];
	input = buildPetriNet[reactants, chemicals, init, steps];
	makePetriNetFromInput[input]
]


ClearAll[PetriNet];
PetriNetChemistry[]:=Module[
	{PetriNet},
	PetriNet=FormFunction[<|"Reactions" -> RepeatingElement[CompoundElement[<|"Input the reactions"-> "String"|>]],
	"Initial States" -> CompoundElement[{"e.g: 0,0,1"->"String"}],
	"Steps" -> CompoundElement[{"Input the steps you want to animate"-> "Integer"->10}]|>,TranslateFromChemToGeneral];
	PetriNet[]
]


(* ::Section:: *)
(*Section 2, Petri Net properties*)


(* ::Subsection:: *)
(*PetriNetReachableQ*)


(* ::Text:: *)
(*TODO:// PetriNetReachableQ[ Neural Net n, Node m]*)
(*return True if m is reachable or false if m is not reachable.*)
