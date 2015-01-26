(*
 * =====================================================================================
 *
 *      Filename:  algorithm.ml
 *
 *   Description:  the witness building algorithm
 *
 *        Author:  Adriaan Larmuseau, ajhl
 *       Company:  Uppsala IT
 *
 * =====================================================================================
 *)

open Mini
open Modules
open MiniMLMod
open Typechecker
open Traces

(*-----------------------------------------------------------------------------
 *  Exceptions
 *-----------------------------------------------------------------------------*)

exception PathException of string
exception TraceException of string
exception AlgoException of string


(*-----------------------------------------------------------------------------
 *  Types
 *-----------------------------------------------------------------------------*)

type mcall = { path : Modules.path option ; step : int ; response : MiniML.term list }
type combv = { path : Modules.path option ; content : MiniML.term }
and  combt = { path : Modules.path; mutable strct : strct list }
and  strct = Value of definition | Module of combt

(*-----------------------------------------------------------------------------
 *  Helper functions
 *-----------------------------------------------------------------------------*)

(* convert a path into a list of strings *)
let rec convert_path = (function Pident id -> [Ident.name id]
  | Pdot (p,str) -> str :: (convert_path p))

let rec convert_in = (function [x] -> Pident (Ident.create x) 
 | x :: xs -> let p = (convert_in xs) in Pdot (p,x)
 | _ -> raise (PathException "Cannot convert into Pdot"))


(*-----------------------------------------------------------------------------
 *  Module that deals with the interaction
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

  (* combine if statements for steps *)
  let combine stp resp cont = 
    let rec combo = function  [x] -> x
      | x :: xs -> MiniML.Sequence(increment, MiniML.Let(Ident.create "x", x, (combo xs)))
      | _ -> raise (AlgoException "Cannot combine empty list")
    in
    let comp = MiniML.Prim ("==",[deref;Constant stp]) in
    MiniML.If (comp,(combo resp),cont)
    
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
 *  Module that handles the module behaviour 
 *-----------------------------------------------------------------------------*)
module Behaviour =
struct
    
  let var = Ident.create "x"

  let seq a b = MiniML.Sequence(a,b)

  let make_let a b = MiniML.Let(var,a,b)

  (* create main function *)
  let main x =
    let id = Ident.create "main" in
    Value_str(id,x)

  (* combine the actions *)
  let rec combine = function
    | [x] -> x
    | x :: xs -> (seq Steps.increment (make_let x (combine xs)))
    | _ -> raise (AlgoException "Cannot combine empty list")

  (* compare ret's *)
  let compare a = 
    let comp = (MiniML.Prim ("==",[(Longident (Pident var));a])) in
    MiniML.If (comp,Diverge.diverge,Diverge.terminate)

end


(* 
 * ===  FUNCTION  ======================================================================
 *         Name:  diff_types
 *  Description:  build Some witness if the types or different 
 * =====================================================================================
 *)
let diff_types ty1 ty2 =
  try
    (MiniMLModTyping.modtype_match MiniMLEnv.empty ty1 ty2);
    None
  with _ -> 
    let ident = Ident.create "X" 
    and aident = Ident.create "Break" in
    let functr =  Functor (ident,ty1,Longident (Pident ident)) in
    let functorapp = Module_str (aident,MiniMLMod.Apply(functr, Longident Interaction.path)) 
    and dist = (Behaviour.main Diverge.diverge) in
    Some (Structure [ Interaction.open_m; functorapp ; Diverge.value ; dist ])


(* 
 * ===  FUNCTION  ======================================================================
 *         Name:  diff_traces
 *  Description:  find the difference between the traces and defer as needed
 * =====================================================================================
 *)
let rec diff_traces m1 m2 tr1 tr2 = 

 (*-----------------------------------------------------------------------------
  *  parse the different traces
  *-----------------------------------------------------------------------------*)
  let rec parse pathls step tr1 tr2  =  

    (* to make things easier *)
    let make_rec ls =  
      let conv_path = (match pathls with
        | [] -> None
        | x :: xs -> Some x) in
      { path = conv_path ; step = step; response = ls;}
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
      | Ret t1 -> ((List.tl pathls),t1) 
      | Call x -> (pathls, (parse_call x))
    in

    (* deal with the final module action in different length trace *)
    let final_module_action my otheraction  =
      let other = match otheraction with
        | Exclamation x -> x
        | _ -> raise (TraceException "Mistake in final trace specification") in
      let (npath,response) = (witness_action my) in
      let quickrec p s = { path = Some p ; step = s ; response = [Diverge.terminate] } in
      let ends = match other with
        | Ret t1 -> (quickrec (List.hd npath) step)
        | Call (Longident p) -> (quickrec p (step+1)) in
      (make_rec [response]) :: ends :: [] 
    in

    (* capture the final tick *)
    let capture_action = function
      | Ret _ -> [make_rec [Diverge.diverge]]
      | Call (Longident p) -> [{ path = Some p; step = (step +1); response = [Diverge.diverge]}]
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
      | _ -> let (npath,response) = (witness_action x) in 
        (make_rec [response]) :: (parse npath (step + 1) xs ys))

    (* Module actions *)
    | ((Exclamation x)::xs,(Exclamation y)::ys) -> (match (x,y) with
      | (Ret a,Ret b) when a != b -> (make_rec [(Behaviour.compare a)]) :: []
      | (Ret _,Ret _) -> (parse pathls (step + 1) xs ys) 
      | (Call (Longident p1),Call (Longident p2)) when not (path_equal p1 p2) -> 
        let call1 = { path = Some p1; step = step ; response = [Diverge.diverge]} 
        and call2 = { path = Some p2; step = step ; response = [Diverge.terminate]} in
        call1 :: call2 :: []
      | (Call (Longident p),_) -> (parse (p :: pathls) (step + 1) xs ys)
      | _ -> raise (AlgoException "Not implemented yet"))

    (* Ticks - if the module stops in one case but does not in the other  *)
    | (Tick :: [], (Exclamation y)::[]) -> (capture_action y) 
    | ((Exclamation x):: [], Tick::[]) -> (capture_action x) 

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
        | ({path = None; step = s1; _},{path = None; step = s2; _}) -> (Pervasives.compare s1 s2)
        | ({path = None; _},{path = Some p; _}) -> 1
        | ({path = Some p; _},{path = None ; _}) -> (-1)
        | ({path = Some p1; _},{path = Some p2; _}) -> let lp1 = convert_path p1
          and lp2 = convert_path p2 in
          if ((List.length lp1) == (List.length lp2))
          then (String.compare (make_str lp1) (make_str lp2))
          else (Pervasives.compare (List.length lp1) (List.length lp2))
      in
      (List.sort cmp_rec ls)
    in

    (* compress the values *)
    let rec compress_values current = function  [] -> [] 
      | { path = None ; step = _; response = rep } :: xs ->  (match current with
        | { path = None; content = con} ->  let sequ = (Behaviour.seq Steps.increment con) in
          let ncon = (Behaviour.make_let sequ rep) in
          compress_values { path = None; content = ncon } xs
        | _ -> raise (AlgoException "Logic fail in value compression"))
      | { path = Some p1 ; step = stp; response = rep } :: xs -> match current with
        | { path = Some cp ; content = cont } -> 
          if (path_equal p1 cp) 
          then (compress_values {path = cp; content = (Steps.combine stp rep cont)} xs)
          else current :: (compress_values {path = p1; content = rep} xs)
        | { path = None ; content = cont } -> current :: (compress_values {path = p1; content = rep} xs)
      in

    (* I love side effects *)
    let str_lst = ref [] in

    (* compress the modules *)
    let rec compress_strct top = function [] -> []
      | x :: xs -> match x with 
        | { path = None ; content = c } -> (Value (Value_str((Ident.create "main"),c))) :: (compress_strct xs)
        | { path = Some (Pident i); content = c } -> (Value (Value_str(i,c))) :: (compress_strct xs)
        | { path = Some p; content = c } -> let cp = (convert_path p) in
          (* to find a module *)
          let pred_rec a b =  match (a,b) with
            | ({path = p1; _},p2) -> (path_equal p1 p2)
          in
          (* create the modules *)
          let rec create target elem = function
            | [x] -> let id = Ident.create x in
              elem.strct <- ( (Value (Value_str(id,c)) ):: elem.strct) 
            | x::xs -> let pp = (convert_in (x::target)) in
              let newelem = 
                try
                  let found = (List.find (fun x -> (pred_rec x pp)) !str_lst) in 
                  found 
                with _ -> let found = { path = pp ; strct = [] } in 
                  match target with
                  | [] -> str_lst := (Module found) :: !str_lst; found
                  | _ -> elem.strct <- (Module found) :: elem.strct; found
              in 
              (create (x::target) newelem xs)
          in
          (create [] top); 
          (compress_strct xs)
    in

    (* clean up compression to produces nice modules *) 
    let rec clean = function [] -> []
      | x :: xs -> match x with
        | Value v ->  v :: (clean xs)
        | Module {path = p; strct = ls } -> let id = (match p with
          | Pident i -> i
          | Path (pp,i) -> (Ident.create i)) in
          let defs = (clean ls) in
          Module_str(id,defs) :: (clean xs)
    in

    (* top level compress *)
    let coms = compress_values (sort_ls ls) in
    let dummy = {path = Pident (Ident.create "M"); strct = []} in
    let vlist = compress_strct dummy coms in
    let result = (clean vlist) @ (clean dummy.strct) in
    results
 in

 (*-----------------------------------------------------------------------------
  *  Top Level
  *-----------------------------------------------------------------------------*)
   
  let setup = [Interaction.open_m; Steps.value ; Diverge.value] 
  and strls = (compress (parse tr1 tr2)) in
  let main = List.hd strls in
  let comm = List.tl strls in
  (Structure (comm @ setup @ [main]))


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
  | None -> (diff_traces m1 m2 tr1 tr2) 
  

