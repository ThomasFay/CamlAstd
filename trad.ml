(*exception AddOpNonValide;;

let rec getStateList astd = match astd with
  |Elem e -> [Elem e]
  |Automaton (_,stateL,_,_,_,_) -> stateL
  |QInter (_,_,_,sAstd) -> getStateList sAstd;;

let rec addEltSetList e name setsList = match setsList with
  |[] -> ("AutState_" ^ name,[e])::setsList
  |(n,l)::t -> if n = "AutState_" ^ name then (n,(e::l))::t else ((n,l)::(addEltSetList e name t));; 

let rec getSets_aux stateList name setsList = match stateList with
  |[] -> setsList
  |h::t -> (match h with
    |Elem e -> addEltSetList e name (getSets_aux t name setsList)
    |Automaton (n,stateL,_,_,_,_) ->
      getSets_aux stateL n (addEltSetList n name (getSets_aux t name setsList)));;

let getSets stateList name = getSets_aux stateList name [];;

let rec addVarToVarList name varList = match varList with
  |[] -> ["State_" ^ name]
  |h::t -> if h = "State_" ^ name then h::t else h::(addVarToVarList name t);;

let rec getVariables_aux stateList name varList=  match stateList with
  |[] -> varList
  |h::t -> (match h with
    |Elem e -> addVarToVarList name varList
    |Automaton (n,stateL,_,_,_,_) -> getVariables_aux stateL n (addVarToVarList name (getVariables_aux t name varList)))

let getVariables stateList name = getVariables_aux stateList name [];;

let rec addInvToInvList name invList = match invList with
  |[] -> ("State_" ^ name,[],"AutState_" ^ name)::invList
  |(n,l,t)::tail -> if n = "State_" ^ name then (n,l,t)::tail else (n,l,t)::(addInvToInvList name tail);;

let rec getInvariants_aux stateList name invList = match stateList with
  |[] -> invList
  |h::t -> (match h with
    |Elem e -> addInvToInvList name invList
    |Automaton (n,stateL,_,_,_,_) -> getInvariants_aux stateL n (addInvToInvList name (getInvariants_aux t name invList)));;

let getInvariants stateList name = getInvariants_aux stateList name [];;

let rec addInitToInitList name initVal initList = match initList with
  |[] -> ("State_" ^ name,[],initVal)::initList
  |(n,l,v)::tail -> if n = "State_" ^ name then (n,l,v)::tail else (n,l,v)::(addInitToInitList name initVal tail);;

let rec getInit_aux stateList name initList = match stateList with
  |[] -> initList
  |h::t -> (match h with
    |Elem e -> initList
    |Automaton (n,stateL,_,_,_,init) -> getInit_aux stateL n (addInitToInitList n (getNameOf init) (getInit_aux t name initList)));;

let getInit stateList name = getInit_aux stateList name [];;

(*let rec addOpToOpList opList name pre post gu fi = match opList with
  |[] -> if gu = "" 
    then [(name,[],pre,Select [pre,post])] 
    else [(name,[],And (pre,Guard gu),Select [And (pre,Guard gu),post])]
  |(na,p,pr,subs)::t -> if name = na then
      if gu = "" then
	(na,p,(Or (pre,pr)),(Select ((pre,post)::subs)))::t
      else
	(na,p,(Or (And (pre,Guard gu),pr)),(Select ((And (pre,Guard gu), post)::subs)))::t
    else (na,p,pr,subs)::(addOpToOpList t name pre post gu fi);;
*)

let rec addOpToOpList opList name pre post gu fi =
  let preco = if gu = "" then pre else And (pre, Guard gu) in
  match opList with
  |[] -> [(name,[],preco,Select [(preco,post)])]
  |(na,p,pr,subs)::t -> if (name = na) then
      begin
	match subs with
	|Affectation [_,_,_] -> raise AddOpNonValide
	|Select l -> (na,p,Or (preco,pr),Select ((preco,post)::l))::t
      end
    else
      (na,p,pr,subs)::(addOpToOpList t name pre post gu fi);;

let rec getOperationsTransList_aux transitionList astd opList = match transitionList with
  |[] -> opList
  |h::t -> (match h with
    |Loc (name,sfrom,sto,gu,fi) ->
      getOperationsTransList_aux t astd
	(addOpToOpList opList 
	   name 
	   (Comparison ("State_" ^ (getNameOfAstdContState sfrom astd),[],sfrom)) 
	   (Affectation [("State_" ^ (getNameOfAstdContState sto astd),[],sto)])
	   gu
	   fi)
    |Tsub (name,sfrom,stoG,stoS,gu,fi) -> 
      getOperationsTransList_aux t astd
	(addOpToOpList 
	   opList
	   name 
	   (Comparison ("State_" ^ (getNameOfAstdContState sfrom astd),[],sfrom))
	   (Affectation [("State_" ^ (getNameOfAstdContState stoG astd),[],stoG);(stoG,[],stoS)])
	   gu
	   fi)
    |Tfrom (name,sfromG,sfromS,sto,gu,fi) ->
      getOperationsTransList_aux t astd
	(addOpToOpList
	   opList
	   name
	   (And ((Comparison ("State_" ^ (getNameOfAstdContState sfromG astd),[],sfromG)),
		 (Comparison ("State_" ^ sfromG,[],sfromS))))
	   (Affectation [("State_" ^ (getNameOfAstdContState sto astd),[],sto)])
	   gu
	   fi));;

let rec addParamInv invariants var = [];;

let rec addParamInit init var = [];;

let rec addParamOpes operations var = [];;

let addParameter var  typeVar machine = {machine = machine.machine;
				sets = (typeVar,[])::machine.sets;
				variables = machine.variables;
				invariants = addParamInv (machine.invariants) var;
				initialisation = addParamInit (machine.initialisation) var;
				operations = addParamOpes machine.operations var};;

let rec getOperationsStateList stateList astd astdG opList = match stateList with
  |[] -> opList
  |h::t -> getOperationsStateList t astd astdG (getOperations_aux h opList astdG)
and getOperations_aux astd opList astdG =match astd with
  |Elem e -> opList
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) ->
    getOperationsStateList stateList astd astdG (getOperationsTransList_aux transitionList astdG opList);;



let getOperations astd = getOperations_aux astd [] astd;;

let rec traduction astd = match astd with
  |Elem e -> {machine = e;
	      sets = [];
	      variables = [];
	      invariants = [];
	      initialisation = [];
	      operations = []}
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) ->
    {machine = name;
     sets = getSets stateList name;
     variables = getVariables stateList name;
     invariants = getInvariants stateList name;
     initialisation = addInitToInitList name (getNameOf initialState) (getInit stateList name);
     operations = getOperations astd}
  |QSynch (name,var,typeVar,sAstd) -> addParameter var typeVar (traduction sAstd);;
*)
exception TheAstdIsNotWellFounded;;
exception AddParamToNonExistentVariable;;


let rec addSetToSetList nameAstdSup name setsList =
  if name = nameAstdSup then setsList else
    match setsList with
    |[] -> [("AutState_" ^ nameAstdSup),[name]]
    |(nameType,values)::tail ->
      if nameType = "AutState_" ^ nameAstdSup
      then (nameType,(name::values))::tail
      else (nameType,values)::(addSetToSetList nameAstdSup name tail);;

let rec addVarToVarList name varList initValue = match varList with
  |[] -> [("State_" ^ name,[],"AutState_" ^ name,initValue)]
  |(varName,params,setType,initValueVar)::tail -> 
    if varName = "State_" ^  name 
    then
      varList
    else
      (varName,params,setType,initValueVar)::(addVarToVarList name tail initValue);;

let rec addOpToOpList_aux name param pre post opList = match opList with
  |[] -> [(name,param,pre,Select [pre,post])]
  |(nameOp,paramOp,preOp,Select l)::tail -> if name = nameOp then
      (if paramOp = param then
	(nameOp,paramOp,Or (preOp,pre),Select ((pre,post)::l))::tail
       else
	  raise TheAstdIsNotWellFounded)
    else
      ((nameOp,paramOp,preOp,(Select l))::(addOpToOpList_aux name param pre post tail));;


let addOpToOpList nameAstd trans opList = match trans with
  |Loc (name,param,from,toS,gu,finale) -> 
    let pre = (if gu = ""
      then
	Comparison ("State_" ^ nameAstd,[],from) 
      else
	And (Guard gu,Comparison("State_" ^ nameAstd,[],from))) in
    let post = Affectation [("State_" ^ nameAstd,[],toS)] in
    addOpToOpList_aux name param pre post opList
  |Tsub (name,param,from,toSup,toState,gu,finale) ->
    let pre = (if gu = ""
      then
	Comparison ("State_" ^ nameAstd,[],from)
      else
	And (Guard gu,Comparison ("State_" ^ nameAstd,[],from)))
    in
    let post = Affectation [("State_" ^ nameAstd,[],toSup);("State_" ^ toSup,[],toState)]
    in
    addOpToOpList_aux name param pre post opList
  |Fsub (name,param,fromSup,fromState,toS,gu,finale) ->
    let pre = (if gu = ""
      then
	And (Comparison ("State_" ^ nameAstd,[],fromSup),(Comparison ("State_" ^ fromSup,[],fromState)))
      else
	And (Guard gu,And (Comparison ("State_" ^ nameAstd,[],fromSup),(Comparison ("State_" ^ fromSup,[],fromState)))))
    in
    let post = Affectation ["State_" ^ nameAstd,[],toS]
    in addOpToOpList_aux name param pre post opList;;

let rec getOperationList nameAstd transList opList = match transList with
  |[] -> opList
  |trans::tail -> getOperationList nameAstd tail (addOpToOpList nameAstd trans opList);;

let rec addParamToVarList var typeVar nameAstd varList = match varList with
  |[] -> raise AddParamToNonExistentVariable
  |(name,params,setType,initValue)::tail ->
    if name = "State_" ^ nameAstd then (name,typeVar::params,setType,initValue)::tail
    else (name,params,setType,initValue)::(addParamToVarList var typeVar nameAstd tail);;

let rec isInStringList name strList = match strList with
  |[] -> false
  |head::tail -> head = name or isInStringList name tail;;

let rec modifyQSynchOperation op = op;;

let rec addParamToExpr exp var paramVar = match exp with
  |And (expr1,expr2) -> And ((addParamToExpr expr1 var paramVar),(addParamToExpr expr2 var paramVar))
  |Or (expr1,expr2) -> Or ((addParamToExpr expr1 var paramVar),(addParamToExpr expr2 var paramVar))
  |Guard s -> Guard s
  |Comparison (name,params,value) -> if name = paramVar then Comparison (name,(var::params),value) else Comparison (name,params,value);;

let rec addParamToAffectationList affList var paramVar = match affList with
  |[] -> raise AddParamToNonExistentVariable
  |(name,params,value)::tail -> if name = paramVar then (name,(var::params),value)::tail else (name,params,value)::(addParamToAffectationList affList var paramVar);;

let rec addParamToSubstitution sub var paramVar = match sub with
  |Affectation l -> Affectation (addParamToAffectationList l var paramVar)
  |Select l -> Select (addParamToSelectList l var paramVar)
and addParamToSelectList list var paramVar = match list with
  |[] -> []
  |(expr,subs)::tail -> (addParamToExpr expr var paramVar, addParamToSubstitution subs var paramVar)::addParamToSelectList tail var paramVar;;

let rec addSynchToOp var delta nameOfAstd opeList = match opeList with
  |[] -> []
  |(name,param,pre,post)::tail -> if isInStringList name delta then (modifyQSynchOperation (name,param,pre,post))::addSynchToOp var delta nameOfAstd tail else (name,param,addParamToExpr pre var ("State_" ^ nameOfAstd),addParamToSubstitution post var ("State_" ^ nameOfAstd))::(addSynchToOp var delta nameOfAstd tail);;

let rec addNonEnumerateSet set setList = match setList with
  |[] -> [set,[]]
  |(nameSet,value)::tail -> if set = nameSet then (nameSet,value)::tail else (nameSet,value)::addNonEnumerateSet set tail;;

let addKleeneSet setList = ("KleeneState",["started";"notstarted"])::setList;;

let addKleeneVar varList name = ("StateKleene_" ^ name,[],"KleeneState","notstarted")::varList;;

let rec final astd = Guard "L'ASTD est final";;

let rec initOf exp nameOfSAstd initStateVal = match exp with
  |And (exp1,exp2) -> And (initOf exp1 nameOfSAstd initStateVal,initOf exp2 nameOfSAstd initStateVal)
  |Or (exp1,exp2) -> Or (initOf exp1 nameOfSAstd initStateVal,initOf exp2 nameOfSAstd initStateVal)
  |Guard gu -> Guard gu
  |Comparison (name,param,value) -> if name = "State_" ^ nameOfSAstd then Comparison (initStateVal,[],value) else Comparison (name,param,value);;

let rec modifyExprKleene exp astd name nameOfSAstd initStateVal= Or (And (Or (final astd,Comparison ("StateKleen_" ^ name,[],"notstarted")),initOf exp nameOfSAstd initStateVal), exp);;

let rec modifyPostKleene post = post;;

let rec addKleeneCondition opList astd name nameOfSAstd initStateVal= match opList with
  |[] -> []
  |(name,param,pre,post)::tail -> (name,param,modifyExprKleene pre astd name nameOfSAstd initStateVal,modifyPostKleene post)::(addKleeneCondition tail astd name nameOfSAstd initStateVal);;

let rec getInitOf astd = match astd with
  |Elem e -> Elem e
  |Automaton (_,_,_,_,_,init) -> init
  |QSynch (_,_,_,_,sastd) -> getInitOf sastd
  |Kleene (_,sastd) -> getInitOf sastd;;

let getInitNameOf astd = getNameOf (getInitOf astd);;

let rec traduction_aux astd nameAstdSup setsList varList opeList= match astd with
  |Elem e -> (addSetToSetList nameAstdSup e setsList),[],[]
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) ->
    let (setsListInd,varListInd,opeListInd) =
      traductionStateList stateList name setsList varList opeList in
      ((addSetToSetList nameAstdSup name setsListInd),
      (addVarToVarList name varListInd (getNameOf initialState)),
      (getOperationList name transitionList opeListInd))
  |QSynch (name,var,typeVar,delta,sAstd) -> 
    let (setsListInd,varListInd,opeListInd) = traduction_aux sAstd name setsList varList opeList in
    (addNonEnumerateSet typeVar setsListInd,addParamToVarList var typeVar (getNameOf sAstd) varListInd,addSynchToOp var delta (getNameOf sAstd) opeListInd)
  |Kleene (name,sAstd) ->
    let (setsListInd,varListInd,opeListInd) = traduction_aux sAstd name setsList varList opeList in
    ((addKleeneSet setsListInd),(addKleeneVar varListInd name),addKleeneCondition opeList sAstd name (getNameOf sAstd) (getInitNameOf sAstd))
and traductionStateList stateList nameAstdSup setsList varList opeList = match stateList with
  |[] -> setsList,varList,opeList
  |head::tail -> let (setsListInd,varListInd,opeListInd) =
		   traductionStateList tail nameAstdSup setsList varList opeList in
		 traduction_aux head nameAstdSup setsListInd varListInd opeListInd;;

let rec getInfoFromVarList varList = match varList with
  |[] -> [],[],[]
  |(varName,params,setType,initValue)::tail ->
    let varList,invList,initList = getInfoFromVarList tail in
    (varName::varList,(varName,params,setType)::invList,(varName,params,initValue)::initList);;

let traduction astd machineName= 
  let 
      setsList,varList,opeList = traduction_aux astd (getNameOf astd) [] [] []
  in
  let varList,invList,initList = getInfoFromVarList varList in
  {machine = machineName;
   sets = setsList;
   variables = varList;
   invariants = invList;
   initialisation = initList;
   operations = opeList};;
