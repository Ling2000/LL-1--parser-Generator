open Proj2_types;;

let eo = SymbolSet.empty;;
let eo = SymbolSet.add "eof" eo;;

let getStartSymbol (g : grammar) : string =match g with
| (a,b) -> a
;;

let rec getN ls =match ls with
| [] -> [""]
| [(x,y)]->[x]
| h::t->getN [h] @ getN t
;;

let getNonterminals (g : grammar) : string list =
match g with
| (a,b)-> getN b
;;

let ad a b= SMap.add b SymbolSet.empty a;;
let adc a b= SMap.add b eo a;;

let getInitFirstSets (g : grammar) : symbolMap =
List.fold_left ad SMap.empty (getNonterminals g)
;;

let getInitFollowSets (g : grammar) : symbolMap =
let cd a b=if b=(getStartSymbol g)
then adc a b
else ad a  b in
  List.fold_left cd SMap.empty (getNonterminals g)
;;

let rec computeFirstSet (first : symbolMap) (symbolSeq : string list) : SymbolSet.t =
 match symbolSeq with
 | [] -> SymbolSet.add "eps" SymbolSet.empty
 | [x] -> if SMap.mem x first then SMap.find x first else SymbolSet.add x SymbolSet.empty
 | h::t -> if SMap.mem h first
then
if SymbolSet.mem "eps" (SMap.find h first) then SymbolSet.union (SymbolSet.remove "eps" (SMap.find h first)) (computeFirstSet first t) else (SMap.find h first)
else SymbolSet.add h SymbolSet.empty
;;

let recurseFirstSets (g : grammar) (first : symbolMap) firstFunc : symbolMap =
let rec rfs m (n:string * string list): symbolMap=
let af a b c= SMap.add b c a in
match n with
| (x,y) -> af m x (SymbolSet.union (firstFunc first y) (SMap.find x m))
in
match g with
| (a,b)-> List.fold_left rfs first b
;;

let rec getFirstSets (g : grammar) (first : symbolMap) firstFunc : symbolMap =
if SMap.equal (SymbolSet.equal) (first) (recurseFirstSets g first computeFirstSet) then recurseFirstSets g first computeFirstSet else
getFirstSets g (recurseFirstSets g first computeFirstSet) computeFirstSet;;

let rec updateFollowSet (first : symbolMap) (follow : symbolMap) (nt : string) (symbolSeq : string list) : symbolMap =
  match symbolSeq with
| [] -> follow
| [x] -> if SMap.mem x follow then SMap.add x (SymbolSet.union (SMap.find x follow) (SMap.find nt follow)) follow else follow
| h::t -> if SMap.mem h follow then
if SymbolSet.mem "eps" (computeFirstSet first t)
then SMap.add h ( SymbolSet.union ( SymbolSet.union (SymbolSet.remove "eps" (computeFirstSet first t)) (SMap.find nt follow) ) (SMap.find h follow)) follow
else SMap.add h  (SymbolSet.union (computeFirstSet first t) (SMap.find h follow)) follow
  else updateFollowSet first follow nt t
;;

let recurseFollowSets (g : grammar) (first : symbolMap) (follow : symbolMap) followFunc : symbolMap =
let rec rfos m (n:string * string list): symbolMap=
match n with
| (x,y) -> followFunc first m x y
in
match g with
| (a,b)-> List.fold_left rfos follow b
;;

let rec getFollowSets (g : grammar) (first : symbolMap) (follow : symbolMap) followFunc : symbolMap =
if SMap.equal (SymbolSet.equal) (follow) (recurseFollowSets g first follow followFunc) then recurseFollowSets g first follow updateFollowSet else
getFollowSets g first (recurseFollowSets g first follow updateFollowSet) updateFollowSet;;

let rec getPredictSets (g : grammar) (first : symbolMap) (follow : symbolMap) firstFunc : ((string * string list) * SymbolSet.t) list =
let rec gPs n=
match n with
| (x,y) ->
if SymbolSet.mem "eps" (firstFunc first y) then
((x,y),SymbolSet.union (SymbolSet.remove "eps" (firstFunc first y)) (SMap.find x follow))
else
 ((x,y),firstFunc first y)
in
match g with
| (a,b)-> List.map gPs b
;;

let rec mTT a token p=
match p with
| [] -> false
| [(x,y),z] -> if a=x then if SymbolSet.mem token z then true else false else false
| ((x,y),z)::t -> if a=x then if SymbolSet.mem token z then true else mTT a token t else mTT a token t
;;

let rec mT a token p=
match p with
| [] -> [""]
| [(x,y),z] -> y
| ((x,y),z)::t -> if a=x then if SymbolSet.mem token z then y else mT a token t else mT a token t
;;

let rec tD (g : grammar) (inputStr : string list)(parse : string list): bool =
let pt= getPredictSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getFollowSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getInitFollowSets g) updateFollowSet) computeFirstSet
in
match inputStr with
| [] -> if List.mem (List.hd parse) (getNonterminals g)
then tD g inputStr ((mT (List.hd parse) "eof" pt) @ (List.tl parse))
else if (List.hd parse) = "eof" then true else false
| _ -> if  List.mem (List.hd parse) (getNonterminals g) then
 if mTT (List.hd parse) (List.hd inputStr) pt then tD g inputStr ((mT (List.hd parse) (List.hd inputStr) pt) @ (List.tl parse)) else false
else
if(List.hd parse)=(List.hd inputStr) then tD g (List.tl inputStr) (List.tl parse) else false
;;

let tryDerive (g : grammar) (inputStr : string list) : bool =
let parse = [getStartSymbol g; "eof"] in
tD g inputStr parse
;;



let rec tDntsl (g : grammar) (inp : string list)(par : string list): string list =
let pt= getPredictSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getFollowSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getInitFollowSets g) updateFollowSet) computeFirstSet
in
match par with
| [] -> inp
| _ ->
if  List.mem (List.hd par) (getNonterminals g) then
  tDntsl g inp ((mT (List.hd par) (List.hd inp) pt) @ (List.tl par))
else
 tDntsl g (List.tl inp) (List.tl par)
;;

let rec tDtt (g : grammar) (inputStr : string list)(parse : string list): parseTree list =
let pt= getPredictSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getFollowSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getInitFollowSets g) updateFollowSet) computeFirstSet
in
let rec tDnt (g : grammar) (inp : string list)(par : string)=
 Nonterminal(par, tDtt g inp (mT par (List.hd inp) pt) )
in
match parse with
| [] -> []
| [ x ] -> if List.mem (x) (getNonterminals g)
then [Nonterminal(x, [])] else [Terminal x]
| _::_ -> if  List.mem (List.hd parse) (getNonterminals g) then
   [tDnt g inputStr (List.hd parse)]@(tDtt g (tDntsl g inputStr [(List.hd parse)]) (List.tl parse) )
else
 [Terminal (List.hd parse)]@(tDtt g (List.tl inputStr) (List.tl parse) )
;;


let tryDeriveTree (g : grammar) (inputStr : string list) : parseTree =
let parse = [getStartSymbol g; ] in
let pt= getPredictSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getFollowSets g (getFirstSets g (getInitFirstSets g) computeFirstSet) (getInitFollowSets g) updateFollowSet) computeFirstSet
in
match inputStr with
| [] -> Nonterminal(getStartSymbol g, [])
| _ -> Nonterminal((List.hd parse), tDtt g inputStr ((mT (List.hd parse) (List.hd inputStr) pt) @ (List.tl parse)) )
;;

let genParser g = tryDerive g;;
let genTreeParser g = tryDeriveTree g;;
