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
 *  Helper functions
 *-----------------------------------------------------------------------------*)

exception PathException of string
exception TraceException of string
exception AlgoException of string


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

  (* struct member list *)
  let strls = ref [] in


  (* parse the traces *)
  let rec parse tr1 tr2  =  
    
    (* implement context action - always the same *)
    let rec my_action a =
      (* parse trace call contents *)
      let rec parse_call = function
        | MiniML.Longident p -> (Interaction.fetch p)
        | MiniML.Apply(x,y) -> MiniML.Apply((parse_call x),y)
        | _ -> raise (TraceException "Mistake in trace specification") 
      in
      match a with
      | Ret t1 -> t1
      | Call x -> (parse_call x)
    in

    (* parse top level *)
    match (tr1,tr2) with  ([],[]) -> raise (TraceException "Traces are not different")

    (* My action *)
    | ((Question x)::xs,(Question y)::ys) -> (match (xs,ys) with
      | ([],[]) -> raise (TraceException "Traces are equal") 

      (* Traces of Different length  *)
      | ([],ys) -> (my_action x) :: Diverge.terminate :: [] 
      | (xs,[]) -> (my_action y) :: Diverge.terminate :: []

      (* recurse *)
      | _ -> (my_action x) :: (parse xs ys))

    (* Module actions *)
    | ((Exclamation x)::xs,(Exclamation y)::ys) -> (match (x,y) with
      | (Ret a,Ret b) when a != b -> (Behaviour.compare a) :: []
      | (Ret _,Ret _) -> (parse xs ys) 
      | (Call (Longident p1),Call (Longident p2)) when not (path_equal p1 p2) -> raise (AlgoException "Not implemented yet")
      | (Call (Longident p),_) -> raise (AlgoException "Not implemented yet")
      | _ -> raise (AlgoException "Not implemented yet"))

    (* Ticks - if the  *)
    | (Tick :: [], (Question y)::[]) -> Diverge.diverge :: []
    | ((Question x):: [], Tick::[]) -> Diverge.diverge :: []

    (* Traces are off *)
    | _ -> raise (TraceException "Traces are wrong or not different")
    
  in

  (* top level *)
  let setup = [Interaction.open_m; Steps.value ; Diverge.value ] 
  and start = Behaviour.main (Behaviour.combine (parse tr1 tr2)) in
  (Structure (!strls @ setup @ [start]))


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
  

