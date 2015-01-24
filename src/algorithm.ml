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

(* fetch the outside *)
let open_m = let id = Ident.create "M" in
  (Open_str id)

(* create main function *)
let main x =
  let id = Ident.create "main" in
  Value_str(id,x)


(*-----------------------------------------------------------------------------
 *  Module that produce diverging calls and module members
 *-----------------------------------------------------------------------------*)
module Diverge =
struct

  let id = Ident.create "diverge" 

  let call x = MiniML.Apply((MiniML.Longident (Pident id)),x) 

  (* create diverging value *)
  let value =  
    let did = Ident.create "div" 
    and var = Ident.create "x" in
    let icall x = MiniML.Apply((MiniML.Longident (Pident did)),x) in
    let func = MiniML.Function(var,MiniML.bool_type,(icall (MiniML.Longident (Pident var)))) in
    let div = MiniML.Letrec (did,func,(call (MiniML.Boolean true))) in
    Value_str(id,div)

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
    and mident = Ident.create "M" 
    and aident = Ident.create "Break" in
    let functr =  Functor (ident,ty1,Longident (Pident ident)) in
    let functorapp = Module_str (aident,MiniMLMod.Apply(functr, Longident (Pident mident))) 
    and dist = (main (Diverge.call (MiniML.Boolean true))) in
    Some (Structure [ open_m; functorapp ; Diverge.value ; dist ])


(* 
 * ===  FUNCTION  ======================================================================
 *         Name:  diff_traces
 *  Description:  find the difference between the traces and defer as needed
 * =====================================================================================
 *)
 let rec diff_traces m1 m2 tr1 tr2 = (Structure [])


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
  seq (diff_types ty1 ty2) (diff_traces m1 m2 tr1 tr2) 
  

