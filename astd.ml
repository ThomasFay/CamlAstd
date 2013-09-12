exception AddStateToElemAstd;;
exception ElemAllreadyInAstd;;
exception ElemAllreadyDFState;;
exception ElemAllreadySFState;;
exception ElemNotInStateList;;
exception AddTransitionToNonAutomaton;;
exception OneOfTheStatesNotInAstd;;
exception AddStateToQSynchAstd;;
exception DefineInitialStateQSynch;;
exception AddStateToKleeneAstd;;
exception DefineInitialStateKleene;;

type guard = string;;

type nameOf = string;;

type finale = bool;;

type transition =
|Loc of nameOf * (string list) * string * string * guard * finale 
|Tsub of nameOf * (string list) * string * string * string * guard * finale
|Fsub of nameOf * (string list) * string * string * string * guard * finale;;

type astd =
|Elem of string
|Automaton of string * astd list * transition list * astd list * astd list * astd
|QSynch of string * string * string * (string list) * astd
|Kleene of string * astd;;
(*
let rec getNameOfAstdContState_aux s astd nameSup nameResult = match astd with
  |Elem e -> if s=e then nameSup else nameResult
  |Automaton (na,stateList,_,_,_,_) -> if na = s then nameSup else (getNameOfAstdContStateLst_aux s stateList na nameResult)
  |QSynch (na,_,_,a) -> if na = s then nameSup else (getNameOfAstdContState_aux s a na nameResult)
and getNameOfAstdContStateLst_aux s stLst nameSup nameResult = match stLst with
  |[] -> nameResult
  |h::t -> getNameOfAstdContStateLst_aux s t nameSup (getNameOfAstdContState_aux s h nameSup nameResult);;

let getNameOfAstdContState s astd = getNameOfAstdContState_aux s astd "" "";;
*)
let getNameOf astd = match astd with
  |Elem e -> e
  |Automaton (name,_,_,_,_,_) -> name
  |QSynch (name,_,_,_,_) -> name
  |Kleene (name,_) -> name;;

let rec inList elem listElem = match listElem with
  |[] -> false
  |h::t-> (h=elem) or (inList elem t);;

let rec addStateToStateList elem stateList = match stateList with
  |[] -> [elem]
  |h::t -> if (h = elem) then
      stateList
    else
      h :: (addStateToStateList elem t);;

let rec addState elem astd = match astd with
  |Elem _ -> raise AddStateToElemAstd
  |Automaton (name,stateList,transitionList, sfList,dfList,initialState) -> if inList elem stateList then
      raise ElemAllreadyInAstd
    else
      Automaton (name,elem::stateList,transitionList,sfList,dfList,initialState)
  |QSynch (_,_,_,_,_) -> raise AddStateToQSynchAstd
  |Kleene (_,_) -> raise AddStateToKleeneAstd;;

let rec addFinalState elem astd = match astd with
  |Elem _ -> raise AddStateToElemAstd
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) -> if inList elem stateList then
      raise ElemAllreadyInAstd
    else
      (if inList elem dfList then
	  raise ElemAllreadyDFState
      else
	  Automaton (name,elem::stateList, transitionList,elem::sfList,dfList,initialState))
  |QSynch (_,_,_,_,_) -> raise AddStateToQSynchAstd
  |Kleene (_,_) -> raise AddStateToKleeneAstd;;


let rec addDeepFinalState elem astd = match astd with
  |Elem _ -> raise AddStateToElemAstd
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) -> if inList elem stateList then
      raise ElemAllreadyInAstd
    else
      if inList elem sfList then
	raise ElemAllreadySFState
      else
	Automaton(name,elem::stateList,transitionList,sfList,elem::dfList,initialState)
  |QSynch (_,_,_,_,_) -> raise AddStateToQSynchAstd
  |Kleene (_,_) -> raise AddStateToKleeneAstd;;

let rec defineInitialState elem astd = match astd with
  |Elem e -> Elem e
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) -> if inList elem stateList then
      Automaton(name,stateList,transitionList,sfList,dfList,elem)
    else
      raise ElemNotInStateList
  |QSynch (_,_,_,_,_) -> raise DefineInitialStateQSynch
  |Kleene (_,_) -> raise DefineInitialStateKleene;;

let newAstd elem nameAstd = Automaton (nameAstd,[elem],[],[],[],elem);;

let qSynch name astd var varType delta = QSynch (name,var,varType,delta,astd);;

let rec isInAstd nameState astd = match astd with
  |Elem s -> nameState = s
  |Automaton (name,stateList,_,_,_,_) -> name = nameState or isInStateList nameState stateList
  |QSynch (_,_,_,_,sAstd) -> isInAstd nameState sAstd
  |Kleene (_,sAstd) -> isInAstd nameState sAstd
and isInStateList nameState stateList = match stateList with
    |[] -> false
    |h::t -> isInAstd nameState h or isInStateList nameState t;;

let rec addLocTransition nameTransition params stateFrom stateTo guardd isFinal astd = if isInAstd stateFrom astd &&
    isInAstd stateTo astd then
	match astd with
	|Elem _ -> raise AddTransitionToNonAutomaton
	|Automaton (nameAutomaton,stateList,transitionList,sfList,dfList,initialState) ->
	  Automaton (nameAutomaton,stateList,Loc (nameTransition,params,stateFrom,stateTo,guardd,isFinal)::transitionList,sfList,dfList,initialState)
	|QSynch (_,_,_,_,_) -> raise AddTransitionToNonAutomaton
	|Kleene (_,_) -> raise AddTransitionToNonAutomaton
  else
    raise OneOfTheStatesNotInAstd;;


let rec addFSubTransition nameTransition params stateFrom stateFromSub stateTo guardd isFinal astd = if isInAstd stateFrom astd && isInAstd stateFromSub astd && isInAstd stateTo astd then
    match astd with
    |Elem _ -> raise AddTransitionToNonAutomaton
    |Automaton (nameAutomaton,stateList,transitionList,sfList,dfList,initialState) ->
      Automaton (nameAutomaton,stateList,Fsub (nameTransition,params,stateFrom,stateFromSub,stateTo,guardd,isFinal)::transitionList,sfList,dfList,initialState)
    |QSynch (_,_,_,_,_) -> raise AddTransitionToNonAutomaton
    |Kleene (_,_) -> raise AddTransitionToNonAutomaton
  else
    raise OneOfTheStatesNotInAstd;;


let rec addTSubTransition nameTransition params stateFrom stateTo stateToSub guardd isFinal astd = if isInAstd stateFrom astd && isInAstd stateTo astd && isInAstd stateToSub astd then
    match astd with
    |Elem _ -> raise AddTransitionToNonAutomaton
    |Automaton (nameAutomaton,stateList,transitionList,sfList,dfList,initialState) ->
      Automaton (nameAutomaton,stateList,Tsub (nameTransition,params,stateFrom,stateTo,stateToSub,guardd,isFinal)::transitionList,sfList,dfList,initialState)
    |QSynch (_,_,_,_,_) -> raise AddTransitionToNonAutomaton
    |Kleene (_,_) -> raise AddTransitionToNonAutomaton
  else
    raise OneOfTheStatesNotInAstd;;

