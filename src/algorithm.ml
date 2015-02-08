(*
 * =====================================================================================
 *
 *      Filename:  algorithm.ml
 *
 *   Description:  the witness building algorithm
 *
 *        Author:  MYSTERY MAN, 
 *       Company:  SOMEWHERE IT
 *
 * =====================================================================================
 *)

open Mini
open Modules
open MiniMLMod
open Typechecker
open Traces
open Printer

(*-----------------------------------------------------------------------------
 *  Exceptions
 *-----------------------------------------------------------------------------*)

exception PathException of string
exception TraceException of string
exception AlgoException of string


(*-----------------------------------------------------------------------------
 *  Types
 *-----------------------------------------------------------------------------*)

(* a function is a module path and has a set of argument types and a return type *)
type func = { path : Modules.path ; types : MiniML.simple_type list }

(* the traces are converted into a triple : function, stepnumber, actions taken  *)
type action = { func : func option ; step : int ; actions : MiniML.term list }

(* the actions are combined into implementations of module value members *)
type comb_val = { path : Modules.path option ; content : MiniML.term }

(* identify the tree structure of the module *)
and comb_str = { path : Modules.path; mutable strct : member list }
and member = Value of comb_val | Module of comb_str

(* the functor calls *)
type funccall = { mutable name : Modules.path option; cont : MiniMLMod.mod_term }


(*-----------------------------------------------------------------------------
 *  Helper functions
 *-----------------------------------------------------------------------------*)

(* convert a path into a list of strings *)
let rec convert_path = (function Pident id -> [Ident.name id]
  | Pdot (p,str) -> str :: (convert_path p))

let rec convert_in = (function [x] -> Pident (Ident.create x) 
 | x :: xs -> let p = (convert_in xs) in Pdot (p,x)
 | _ -> raise (PathException "Cannot convert into Pdot"))

(* an hd that doesn't suck *)
let hd = function [] -> None | x::xs -> Some x


(*-----------------------------------------------------------------------------
 *  store path type associations (In the future update to objects)
 *-----------------------------------------------------------------------------*)
module PathTbl =
struct

  (* a table is a simple list of tuples *)
  let emptytbl = []

  (* compare paths *)
  let equal p1 p2 = (path_equal p1 p2)

  (* add *)
  let add (p : Modules.path) (data : MiniML.simple_type) tbl = (p, data) :: tbl

  (* find a pth *)
  let rec find p1 = function
    | [] -> raise Not_found
    | (p2,data) :: xs -> if equal p1 p2 
      then data
      else (find p1 xs)

  (* search until you have a base *)
  let rec findbase p1 tbl = match (find p1 tbl) with
    | MiniML.LambdaType _ as ty -> ty
    | MiniML.Typeconstr(p2,_) -> (findbase p2 tbl)

end


(*-----------------------------------------------------------------------------
 *  Module that deals with the interaction between M and the witness
 *-----------------------------------------------------------------------------*)
module Interaction =
struct

  let id = Ident.create "M" 

  let path = Pident id

  (* fetch the outside *)
  let open_m = let id = Ident.create "M" in 
    (Open_str id)

  (* call a module element *)
  let call p ls = 

    (* attach two paths *)
    let attach p1 p2 = let n1 = (convert_path p1)
      and n2 = (convert_path p2) in
      (convert_in (n2 @ n1))
    in
    let target = (MiniML.Longident (attach path p)) in

    (* build the application *)
    let rec build = function
      | [] -> target
      | [x] -> MiniML.Apply (target,x)
      | x::xs -> MiniML.Apply ((build xs),x)
    in
    (build ls)
    
  (* call a module element without args *)
  let fetch p = (call p [])
    
end


(*-----------------------------------------------------------------------------
 *  Module that deals with the steps tracking
 *-----------------------------------------------------------------------------*)
module Steps =
struct

  let id = Ident.create "counter" 

  let long = MiniML.Longident (Pident id)

  (* check the value *)
  let deref = (MiniML.Deref long)

  (* add a step *)
  let increment = MiniML.Assign(long,(MiniML.Prim ("+",[deref;(Constant 1)])))

  (* create the reference for inclusion in the module *)
  let value = 
    let cont = (MiniML.Ref (Constant 0)) in
    Value_str(id,cont)

end


(*-----------------------------------------------------------------------------
 *  Module that produce diverging calls and module members
 *-----------------------------------------------------------------------------*)
module Diverge =
struct

  let id = Ident.create "diverge" 

  let call i x = MiniML.Apply((MiniML.Longident (Pident i)),x) 

  let diverge = (call id (MiniML.Boolean true))

  (* create diverging value *)
  let value =  
    let did = Ident.create "div" 
    and var = Ident.create "x" in
    let icall x = MiniML.Apply((MiniML.Longident (Pident did)),x) in
    let func = MiniML.Function(var,MiniML.bool_type,(icall (MiniML.Longident (Pident var)))) in
    let arrty = (MiniML.arrow_type MiniML.bool_type MiniML.bool_type) in
    let div = MiniML.Letrec (did,arrty,func,(call did (MiniML.Boolean true))) in
    Value_str(id,div)

  let terminate = MiniML.Unit 

end


(*-----------------------------------------------------------------------------
 *  Module that handles the witness behaviour 
 *-----------------------------------------------------------------------------*)
module Behaviour =
struct
    
  let var = Ident.create "x"

  let seq a b = MiniML.Sequence(a,b)

  let make_let a b = MiniML.Let(var,a,b)

  (* produce a default value for each type *)
  let default_val ptbl ty = 
    let rec convert = function
      | MiniML.LambdaType(TBool,[]) -> MiniML.Boolean true
      | MiniML.LambdaType(TUnit,[]) -> MiniML.Unit
      | MiniML.LambdaType(TInt,[]) -> MiniML.Constant 0
      | MiniML.LambdaType(TRef,[ty]) -> MiniML.Ref (convert ty)
      | MiniML.LambdaType(TIgnore,[]) -> MiniML.Unit (* Todo this is deprecated *)
      | MiniML.LambdaType(TPair,[ty1;ty2]) -> MiniML.Pair(convert ty1,convert ty2)
      | MiniML.LambdaType(TArrow,[ty1;ty2]) -> MiniML.Function(var,ty1,convert ty2)
      | MiniML.Typeconstr(path,_) -> convert (PathTbl.findbase path ptbl)
    in
    (convert ty)

  (* default implementation of abstract type *)
  let def_absty = MiniML.LambdaType(TInt,[])

  (* create main function *)
  let main x =
    let id = Ident.create "main" in
    Value_str(id,x)

  (* combine the actions *)
  let rec combine = function
    | [x] -> x
    | x :: xs -> (match x with
      | MiniML.Let (v,a,b) -> MiniML.Let(v,a,(combine xs))
      | _ -> (seq Steps.increment (make_let x (combine xs))))
    | _ -> raise (AlgoException "Cannot combine empty list")

  (* compare ret's *)
  let compare a = 
    let comp = (MiniML.Prim ("==",[(Longident (Pident var));a])) in
    MiniML.If (comp,Diverge.diverge,Diverge.terminate)

  (* combine if statements for steps *)
  let combine_if stp resp cont = 
    let rec combo = function  [x] -> x
      | x :: xs -> (seq Steps.increment (make_let x (combo xs)))
      | _ -> raise (AlgoException "Cannot combine empty list")
    in
    let comp = MiniML.Prim ("==",[Steps.deref;Constant (stp - 1)]) in
    (seq Steps.increment (MiniML.If (comp,(combo resp),cont)))

  (* make a function*)
  let rec make_f t = function
    | [] -> t
    | ty::tys -> let var = Ident.create "y" in
      (make_f (MiniML.Function (var,ty,t)) tys)

end

(* 
 * ===  FUNCTION  ======================================================================
 *         Name:  diff_types
 *  Description:  build a witness if the types or different 
 * =====================================================================================
 *)
let diff_types ty1 ty2 =
  try
    (MiniMLModTyping.modtype_match MiniMLEnv.empty ty1 ty2);
    None
  with Error s -> 
    let ident = Ident.create "X" 
    and aident = Ident.create "Break" in
    let functr =  Functor (ident,ty1,Longident (Pident ident)) in
    let functorapp = Module_str (aident,MiniMLMod.Apply(functr, Longident Interaction.path)) 
    and dist = (Behaviour.main Diverge.diverge) in
    Some (Structure [ Interaction.open_m; functorapp ; Diverge.value ; dist ])


(* 
 * ===  FUNCTION  ======================================================================
 *     Name: find_argtype
 *  Description: find a functors argument type  
 * =====================================================================================
 *)
let rec find_argtype ty path = 

  (* build a dummy module that the outside can apply to the module *)
  let build_dummy mty =

    (* side affects all around *)
    let ptbl = ref PathTbl.emptytbl in

    (* convert a signature into a sequence of modules *)
    let rec convert = function [] -> []
      | x :: xs -> (match x with
        | Value_sig (id,vty) -> Value_str(id,(Behaviour.default_val !ptbl vty.body)) 
        | Type_sig (id,decl) -> let nty = (match decl.manifest with
          | None -> Behaviour.def_absty
          | Some dft -> dft.defbody) in
          ptbl := PathTbl.add (Pident id) nty !ptbl;
          let dty = { MiniML.params = []; MiniML.defbody = nty }
          and knd = { MiniML.arity = 0} in
          Type_str(id,knd,dty)
        | Module_sig (id,mty) -> Module_str(id,convertm mty)) :: (convert xs)
    
    and convertm = function
      | Signature sls -> let strs = convert sls in (Structure strs)
      | _ -> raise (TraceException "Cannot apply outside functor to the module")
    in
    (convertm mty)
  in
    

  (* extract the functor arg *) 
  let extract = function
    | Functor_type (_,ml1,_) -> ml1
    | _ -> raise (PathException "Wrong type path: points to module")
  in

  (* find a string in a mod_type *)
  let rec find str mty = 
    (* find the type declaration *)
    let rec find_decl = function [] -> raise (PathException "Cannot find type path")
      | x::xs -> match x with
        | Value_sig(id, vty) when (Ident.name id) = str -> raise (PathException "Wrong type path: points to val")
        | Type_sig(id, decl) when (Ident.name id) = str -> raise (PathException "Wrong type path: points to type decl")
        | Module_sig(id,mty) when (Ident.name id) = str -> mty
        | _ ->  (find_decl xs)
    in
    match mty with 
      | Signature sls -> (find_decl sls)
      | Functor_type(arg,ml1,_) -> raise (PathException "Functor search not supported")
  in

  (* top level *)
  let process typ = build_dummy (extract typ) in
  match path with | [] -> (process ty)
    | str :: [] -> (process (find str ty))
    | str :: ls -> let mty = (find str ty) in
      (find_argtype mty ls)


(* 
 * ===  FUNCTION  ======================================================================
 *         Name:  diff_traces
 *  Description:  find the difference between the traces and defer as needed
 * =====================================================================================
 *)
let rec diff_traces ty m1 m2 tr1 tr2 = 

  (* feed me side effects *)
  let fctr_ls = ref [] 
  and modstr_ls = ref [] in

 (*-----------------------------------------------------------------------------
  *  parse the different traces
  *-----------------------------------------------------------------------------*)
  let rec parse pathls step tr1 tr2  =  

    (* to make things easier *)
    let make_rec ls =  
      {func = (hd pathls) ; step = step; actions = ls;}
    in
    
    (* implement context action - always the same *)
    let rec witness_action a  =
      (* parse trace call contents *)
      let rec parse_call = function
        | MiniML.Longident p -> (Interaction.fetch p)
        | MiniML.Apply(x,y) -> MiniML.Apply((parse_call x),y)
        | _ -> raise (TraceException "Mistake in trace specification") 
      in
      match a with
      | Ret (Value t1) -> ((List.tl pathls),t1) 
      | Call (Regular x) -> (pathls, (parse_call x))
      | Call (Dynamic x) -> (pathls, (parse_call x))
      | Call (ApplyLoc id) -> let var = Pident (Ident.create ("ref"^(string_of_int id))) in
        let nv = MiniML.Longident var in
        (pathls, (MiniML.Deref nv))
      | Call (ApplyCl (id,x)) -> let var = Pident (Ident.create ("id"^(string_of_int id))) in
        let appl = MiniML.Apply((MiniML.Longident var),x) in
        ( pathls,appl)
      | Call (ApplyFu (p1,opt)) -> 
        let arg = match opt with
          | Known p2 -> p2
          | New i -> let id = Ident.create ("Witn"^(string_of_int i))
            and mt = (find_argtype ty (convert_path p1)) in
            modstr_ls := Module_str(id,mt) :: !modstr_ls;
            (Pident id)
        in
        let app = MiniMLMod.Apply((MiniMLMod.Longident p1),(MiniMLMod.Longident arg)) in
        let fc = { name = None; cont = app } in
        fctr_ls := fc :: !fctr_ls;
        (pathls,MiniML.Unit)
      | _ -> raise (TraceException "Mistake in trace specification")
    in

    (* module call parse : path & count *)
    let rec mod_call tyls = function
      | Regular r -> (match r with
        | MiniML.Longident p -> Some { path = p; types = tyls;  }
        | MiniML.Apply(x,y) -> 
          let typ = (MiniMLTyping.type_term MiniMLEnv.empty y) in (* improve env *)
          (mod_call (typ.body::tyls) (Regular x) ))
      | _ -> raise (TraceException "Module cannot call preset entries")
    in

    (* module return *)
    let rec mod_ret = function
      | Traces.Value t -> None
      | Traces.Identifier id -> let var = (Ident.create ("id"^(string_of_int id))) 
        and nvar = MiniML.Longident (Pident (Ident.create "x")) in
        Some (MiniML.Let(var,nvar,MiniML.Unit))
      | Traces.Ref id -> let var = (Ident.create ("ref"^(string_of_int id))) 
        and nvar = MiniML.Longident (Pident (Ident.create "x")) in
        Some (MiniML.Let(var,nvar,MiniML.Unit))
      | Traces.Newpath p -> let fc = List.hd !fctr_ls in
        fc.name <- (Some p);
        None
    in

    (* deal with the final module action in different length trace *)
    let final_module_action my otheraction  =
      let other = match otheraction with
        | Exclamation x -> x
        | _ -> raise (TraceException "Mistake in final trace specification") in
      let (npath,action) = (witness_action my) in
      let quickrec f s = { func = f;step = s ; actions = [Diverge.terminate] } in
      let ends = match other with
        | Ret _ -> (quickrec (hd npath) step)
        | Call y -> let f = (mod_call [] y) in 
          (quickrec f (step+1)) 
      in
      (make_rec [action]) :: ends :: [] 
    in

    (* capture the final tick *)
    let capture_action = function
      | Ret _ -> [make_rec [Diverge.diverge]]
      | Call x -> let f = (mod_call [] x) in
        [{ func = f; step = (step +1); actions = [Diverge.diverge]}]
    in

    (* parse top level *)
    match (tr1,tr2) with  ([],[]) -> raise (TraceException "Traces are not different")

    (* Witness action *)
    | ((Question x)::xs,(Question y)::ys) -> (match (xs,ys) with
      | ([],[]) -> raise (TraceException "Traces are equal") 

      (* Traces of Different length  *) 
      | ([],o::ys) -> (final_module_action x o)
      | (o::xs,[]) -> (final_module_action y o)

      (* respond and move on *)
      | _ -> let (npath,action) = (witness_action x) in 
        (make_rec [action]) :: (parse npath (step + 1) xs ys))

    (* Module actions *)
    | ((Exclamation x)::xs,(Exclamation y)::ys) -> (match (x,y) with
      | (Ret (Value a),Ret (Value b)) when a != b -> (make_rec [(Behaviour.compare a)]) :: []
      | (Ret a,Ret _) -> (match (mod_ret a) with
          | None -> (parse pathls (step + 1) xs ys) 
          | Some t -> (make_rec [t]) :: (parse pathls (step + 1) xs ys))
      | (Call a,Call b) -> let Some f1 = (mod_call [] a)
        and Some f2 = (mod_call [] b) in
        (match (f1,f2) with
        | ({path = p1;_},{path = p2;_}) when not (path_equal p1 p2) ->
          let call1 = { func = Some f1; step = step ; actions = [Diverge.diverge]} 
          and call2 = { func = Some f2; step = step ; actions = [Diverge.terminate]} in
          call1 :: call2 :: []
        | _ -> (parse (f1 :: pathls) (step + 1) xs ys))
      | (Call a, Ret b) -> (make_rec [Diverge.terminate]) :: (capture_action x)
      | (Ret a, Call b) -> (make_rec [Diverge.terminate]) :: (capture_action y))

    (* Ticks - if the module stops in one case but does not in the other  *)
    | (Tick :: [], (Exclamation y)::ys) -> (capture_action y) 
    | ((Exclamation x)::xs, Tick::[]) -> (capture_action x) 

    (* Traces are off *)
    | _ -> raise (TraceException "Traces are wrong or not different")
    
  in

 (*-----------------------------------------------------------------------------
  *  compress parse result 
  *-----------------------------------------------------------------------------*)
  let rec compress ls =

    (* sort the list *)
    let sort_ls ls =

      (* make a string from a path *)
      let make_str p = match p with [] -> ""
        | lst -> (String.concat "_" (List.rev lst)) 
      in

      (* compare records *)
      let cmp_rec a b = match (a,b) with
        | ({func = None; step = s1; _},{func= None; step = s2; _}) -> (Pervasives.compare s1 s2)
        | ({func = None; _},{func = Some {path = p; _}; _}) -> -1
        | ({func = Some {path = p;_}; _},{func = None; _}) -> 1
        | ({func = Some {path = p1;_}; _},{func = Some {path = p2;_}; _}) -> let lp1 = convert_path p1
          and lp2 = convert_path p2 in
          if ((List.length lp1) == (List.length lp2))
          then (String.compare (make_str lp1) (make_str lp2))
          else (Pervasives.compare (List.length lp1) (List.length lp2))
      in
      (List.sort cmp_rec ls)
    in

    (* compress the values *)
    let rec compress_values current ls = 
      (* pump into compact format *)
      let next ignore = ignore; match current with 
        | { func = Some {path = cp; types = tys }; step = _; actions = [cont] } -> 
          { path = Some cp; content = (Behaviour.make_f cont tys) }
        | { func = None; step = _ ; actions = a } -> 
          { path = None; content = (Behaviour.make_f (Behaviour.combine a) []) }
      in
      match ls with [] -> [(next ())]

      (* The main function  *)
      | { func = None; step = s; actions = rep } :: xs -> 
        (match current with
          | { func = None; step = _ ; actions = con} -> let nactions = (con @ rep) in
            (compress_values { func = current.func; step = s; actions = nactions } xs)
          | _ -> raise (AlgoException "Logic fail in value compression"))

      (* targetted calls *)
      | { func = Some{path = p1; types = tyls}; step = stp; actions = rep } :: xs -> 
        (* helper to build new current *)
        let ncurrent term = 
            let nactions = [(Behaviour.combine_if stp rep term)] in
            {func= Some{path = p1; types = tyls}; step = stp; actions = nactions}
        in
        match current with
        | { func = Some{ path = cp ; _}; step = _; actions = [cont] } -> 
          if (path_equal p1 cp) 
          then let ncurr = ncurrent cont in
            (compress_values ncurr xs)
          else let ncurr = ncurrent MiniML.Unit in 
            (next ()) :: (compress_values ncurr xs)
        (* close up the main function *)
        | { func = None; step = _ ; actions = a } -> 
          let ncurr = ncurrent MiniML.Unit in
          (next ()) :: (compress_values ncurr xs)
      in

    (* compress the modules *)
    let rec compress_strct top = function [] -> []
      | x :: xs -> match x with 
        | { path = None ; content = c } -> (Value x) :: (compress_strct top xs)
        | { path = Some (Pident i); content = c } -> (Value x) :: (compress_strct top xs)
        | { path = Some p; content = c } -> let cp = (convert_path p) in
          (* to find a module *)
          let rec pred_rec a b =  
            match (a,b) with
            | (Module {path = p1; strct = ls },p2) -> if (not (path_equal p1 p2))
              then (List.exists (fun x -> (pred_rec x b)) ls)
              else true
            | _ -> false
          in
          (* create the modules *)
          let rec create target elem = function
            | [x] -> let id = Ident.create x in
              elem.strct <- ((Value {path = Some (Pident id); content = c}):: elem.strct) 
            | x::xs -> let pp = (convert_in (x::target)) in
              let Module newelem = 
                try
                  let found = (List.find (fun x -> (pred_rec x pp)) top.strct) in 
                  found 
                with _ -> let found = Module { path = pp ; strct = [] } in 
                  match target with
                  | [] -> top.strct <- found :: top.strct; found
                  | _ -> elem.strct <- found :: elem.strct; found
              in 
              (create (x::target) newelem xs)
          in
          (create [] top (List.rev cp)); 
          (compress_strct top xs)
    in

    (* clean up compression to produces nice modules *) 
    let rec clean = function [] -> []
      | x :: xs -> match x with
        | Value { path = None; content = c}  -> (Value_str((Ident.create "main"),c)) :: (clean xs)
        | Value { path = Some (Pident i); content = c} -> Value_str(i,c) :: (clean xs)
        | Module {path = p; strct = ls } -> let id = (match p with
          | Pident i -> i
          | Pdot (_,i) -> (Ident.create i)) in
          let defs = (clean ls) in
          Module_str(id,(Structure defs)) :: (clean xs)
    in

    (* top level compress *)
    let coms = compress_values { func = None; step = 0 ; actions = []} (sort_ls ls) in
    let dummy = {path = Pident (Ident.create "M"); strct = []} in
    let vlist = compress_strct dummy coms in
    let result = (clean vlist) @ (clean dummy.strct) in
    result
 in

 (*-----------------------------------------------------------------------------
  *  Top Level
  *-----------------------------------------------------------------------------*)
   
  let setup = [Interaction.open_m; Steps.value ; Diverge.value] 
  and strls = (compress (parse [] 0 tr1 tr2)) in
  let fcalls = List.map (function { name = Some (Pident n); cont = c} -> Module_str(n,c)) !fctr_ls in
  let main = List.hd strls in
  let comm = List.tl strls in
  (Structure (!modstr_ls @ comm @ setup @ fcalls @ [main]))


(* 
 * ===  FUNCTION  ======================================================================
 *         Name:  build
 *  Description:  build a witness for the given modules and traces
 * =====================================================================================
 *)
let build mt1 mt2 tr1 tr2 = 

  (* return if first member is not none *)
  let seq e1 e2 = match e1 with
    | Some x -> x
    | None -> e2
  in

  (* top level *)
  let (m1,ty1) = mt1
  and (m2,ty2) = mt2 in
  let case1 = (diff_types ty1 ty2) in
  match case1 with
  | Some x -> x
  | None -> (diff_traces ty1 m1 m2 tr1 tr2) 
  

