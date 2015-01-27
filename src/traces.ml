(*
 * =====================================================================================
 *
 *      Filename:  traces.ml
 *
 *   Description:  traces spec
 *
 *        Author:  Adriaan Larmuseau, ajhl
 *       Company:  Uppsala IT
 *
 * =====================================================================================
 *)

open Mini
open MiniMLMod

(*-----------------------------------------------------------------------------
 *  Traces
 *-----------------------------------------------------------------------------*)

type entry =
  | Regular of MiniML.term
  | Dynamic of MiniML.term
  | ApplyCl of int * MiniML.term
  | ApplyFu of Modules.path * Modules.path
  | ApplyLoc of int

type return =
  | Value of MiniML.term
  | Identifier of int
  | Ref of int
  | Newpath of Modules.path

type action =
  | Call of entry 
  | Ret of return

and alpha = 
  | Question of action
  | Exclamation of action
  | Tick

and trace = alpha list

(* for the parser *)
let end_of_trace = Tick :: []

