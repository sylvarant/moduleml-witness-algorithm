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


(*-----------------------------------------------------------------------------
 *  Traces
 *-----------------------------------------------------------------------------*)

type action =
  | Call of MiniML.term
  | Ret of MiniML.term

and alpha = 
  | Question of action
  | Exclamation of action
  | Tick

and trace = alpha list

(* for the parser *)
let end_of_trace = Tick :: []

