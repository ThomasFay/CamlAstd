#use "astd.ml"
#use "b.ml"

exception TheAstdIsNotWellFounded;;
exception AddParamToNonExistentVariable;;
exception NoFinalState;;
exception NotFound;;
exception NotAnAutomaton;;

(*
Fonction addSetToSetList
Objectif :
Ajouter des éléments pour la clause SET de la machine. Elle ajoute l'élément <name> à l'énumération de l'ensemble AutState_<nameAstdSup>
Arguments :
- nameAstdSup : Nom de l'automate dont on rempli l'ensemble
- name : Nom de l'état de l'automate qu'on souhaite ajouter à l'ensemble
- setsList : Liste de la forme (string1 * string2 list) list qui liste chaque ensemble (string1) et les différentes valeurs énumérées de cet ensemble (string2 list)
*)

let rec addSetToSetList nameAstdSup name setsList =
  if name = nameAstdSup then setsList else
    match setsList with
    |[] -> [("AutState_" ^ nameAstdSup),[name]]
    |(nameType,values)::tail ->
      if nameType = "AutState_" ^ nameAstdSup
      then (nameType,(name::values))::tail
      else (nameType,values)::(addSetToSetList nameAstdSup name tail);;

(*
Fonction addVarToVarList :
Objectif :
Construire la liste des variables nécessaire aux clauses VARIABLES, INVARIANT et INITIALISATION de la machine B. Elle ajoute si elle n'y est pas déjà la variable name à la liste de variable <varList> en lui donnant la valeur <initValue>.
Arguments :
- name : nom de la variable
- varList : Liste de la forme (string1 * string2 list * string3 * string4) qui représentent :
  - string1 : Le nom de la variable
  - string2 list : les éventuels paramètres de la variable (dans le cas des astd quantifiés)
  - string3 : Le type à donner à la variable
  - string4 : La valeur initiale de cette variable
- initValue : La valeur initiale à donner à la variable
*)

let rec addVarToVarList name varList initValue = match varList with
  |[] -> [("State_" ^ name,[],"AutState_" ^ name,initValue)]
  |(varName,params,setType,initValueVar)::tail -> 
    if varName = "State_" ^  name 
    then
      varList
    else
      (varName,params,setType,initValueVar)::(addVarToVarList name tail initValue);;

(*
Fonction addOpToOpList_aux :
Objectif : Fonction auxiliaire de addOpToOpList. Elle permet d'ajouter à la liste des opérations <opList> déjà constituée l'opération de nom <name>, de paramètres <param>, donc la précondition est <pre> et la substitution est <post>
Arguments :
- name : nom de l'opération (obtenu grace au nom de la transition)
- param : éventuels paramètres de l'opération (obtenus dans la transition)
- pre : précondition de la forme d'une expression (cf b.ml)
- post : postcondition de type sublstitution (cf b.ml)
- opList : liste des opérations déjà construites
*)

let rec addOpToOpList_aux name param pre post opList = match opList with
  |[] -> [(name,param,pre,Select [pre,post])]
  |(nameOp,paramOp,preOp,Select l)::tail -> if name = nameOp then
      (if paramOp = param then
	(nameOp,paramOp,Or (preOp,pre),Select ((pre,post)::l))::tail
       else
	  raise TheAstdIsNotWellFounded)
    else
      ((nameOp,paramOp,preOp,(Select l))::(addOpToOpList_aux name param pre post tail));;


let rec isInStringList name strList = match strList with
  |[] -> false
  |head::tail -> head = name or isInStringList name tail;;

let rec final astd name = match astd with
  |Elem s -> Comparison (("State_" ^ name),[],s)
  |Automaton (nameAstd,_,_,fState,dFState,_) -> match (fState,dFState) with
    |[],[] -> raise NoFinalState
    |[],listDFState -> getFinalFromFinalStateList listDFState nameAstd
    |listFState, [] -> getFinalFromFinalStateList listFState nameAstd
    |fState,dFState -> And (getFinalFromFinalStateList fState nameAstd,getFinalFromFinalStateList dFState nameAstd)
and getFinalFromFinalStateList fStateList name = match fStateList with
  |[fState] -> final fState name
  |head::tail -> And (final head name,getFinalFromFinalStateList tail name);;

let rec getAstdFromStateList stateList name = match stateList with
  |[] -> raise NotFound
  |astd::tail -> match astd with
    |Elem s -> if s = name then Elem s else getAstdFromStateList tail name
    |Automaton (nameAstd,_,_,_,_,_) -> if name = nameAstd then astd else getAstdFromStateList tail name;;

let rec getAstdFromName nameAstd astd = match astd with
  |Elem s -> raise NotAnAutomaton
  |Automaton (name,stateList,_,_,_,_) -> getAstdFromStateList stateList nameAstd;;

(*
Fonction addOpToOpList :
Objectif : Ajouter à la liste des opérations <opList> l'opération correspondant à la transition <trans> dans l'ASTD de nom <nameAstd>. Elle construit également les éléments pour la construction des arguments <pre> et <post> de la fonction addOpToOpList
Arguments :
- nameAstd : nom de l'ASTD dans lequel se situe l'opération
- trans : la transition issue de la liste des transition de l'ASTD
*)

let addOpToOpList nameAstd trans opList astd = match trans with
  |Loc (name,param,from,toS,gu,finale) -> 
    let pre = (if gu = ""
      then
	  Comparison ("State_" ^ nameAstd,[],from)
      else
	And (Guard gu,Comparison("State_" ^ nameAstd,[],from))) in
    let pre = if finale then And (final (getAstdFromName from astd) from,pre)
      else pre
    in
    let post = AffectationSub [VarAffect ("State_" ^ nameAstd,[],toS)] in
    addOpToOpList_aux name param pre post opList
  |Tsub (name,param,from,toSup,toState,gu,finale) ->
    let pre = (if gu = ""
      then
	Comparison ("State_" ^ nameAstd,[],from)
      else
	And (Guard gu,Comparison ("State_" ^ nameAstd,[],from)))
    in
    let pre = if finale then And (final (getAstdFromName from astd) from, pre)
      else pre
    in
    let post = AffectationSub [VarAffect ("State_" ^ nameAstd,[],toSup);VarAffect ("State_" ^ toSup,[],toState)]
    in
    addOpToOpList_aux name param pre post opList
  |Fsub (name,param,fromSup,fromState,toS,gu,finale) ->
    let pre = (if gu = ""
      then
	And (Comparison ("State_" ^ nameAstd,[],fromSup),(Comparison ("State_" ^ fromSup,[],fromState)))
      else
	And (Guard gu,And (Comparison ("State_" ^ nameAstd,[],fromSup),(Comparison ("State_" ^ fromSup,[],fromState)))))
    in
    let pre = if finale then And (final (getAstdFromName fromState (getAstdFromName fromSup astd)) fromState,pre)
      else pre
    in
    let post = AffectationSub [VarAffect ("State_" ^ nameAstd,[],toS)]
    in addOpToOpList_aux name param pre post opList;;

(*
Fonction getOperationList
Objectif :
Permet de récupérer à partir de la liste des transitions <transList> la liste des opérations <opList>.
Argument :
- nameAstd : Le nom de l'ASTD dans lequel on veut récupérer les transitions
- transList : la liste des transition de cet ASTD
- opList : La liste de opérations qu'on souhaite construire
*)

let rec getOperationList nameAstd transList opList astd = match transList with
  |[] -> opList
  |trans::tail -> getOperationList nameAstd tail (addOpToOpList nameAstd trans opList astd) astd;;

let rec initOf exp nameOfSAstd initStateVal = match exp with
  |And (exp1,exp2) -> And (initOf exp1 nameOfSAstd initStateVal,initOf exp2 nameOfSAstd initStateVal)
  |Or (exp1,exp2) -> Or (initOf exp1 nameOfSAstd initStateVal,initOf exp2 nameOfSAstd initStateVal)
  |Guard gu -> Guard gu
  |Comparison (name,param,value) -> if name = "State_" ^ nameOfSAstd then Comparison (initStateVal,[],value) else Comparison (name,param,value);;

let rec getInitOf astd = match astd with
  |Elem e -> Elem e
  |Automaton (_,_,_,_,_,init) -> init
  |QSynch (_,_,_,_,sastd) -> getInitOf sastd
  |Kleene (_,sastd) -> getInitOf sastd;;

let getInitNameOf astd = getNameOf (getInitOf astd);;

let rec traduction_aux astd nameAstdSup setsList varList opeList= match astd with
  |Elem e -> (addSetToSetList nameAstdSup e setsList),varList,opeList
  |Automaton (name,stateList,transitionList,sfList,dfList,initialState) ->
    let (setsListInd,varListInd,opeListInd) =
      traductionStateList stateList name setsList varList opeList in
      ((addSetToSetList nameAstdSup name setsListInd),
      (addVarToVarList name varListInd (getNameOf initialState)),
      (getOperationList name transitionList opeListInd astd))
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
