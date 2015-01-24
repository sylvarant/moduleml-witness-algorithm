(*
 * =====================================================================================
 *
 *       Filename:  main.ml
 *
 *    Description:  Boot up the parser feed typechecker, scoper, compiler
 *
 *         Author:  Adriaan Larmuseau, ajhl
 *        Company:  Uppsala IT
 *
 * =====================================================================================
 *)

open Modules
open Mini
open Traces
open MiniMLMod
open Typechecker
open Scoping
open Printer

(*-----------------------------------------------------------------------------
 *  Exceptions
 *-----------------------------------------------------------------------------*)
 
exception CommandlineArg of string


(*
 * ===  FUNCTION ======================================================================
 *         Name:  commandline
 *  Description:  process the command line arguments
 * =====================================================================================
 *)
let commandline = 
  let arguments = (List.tl (Array.to_list Sys.argv)) in
  match arguments with
  | m1::m2::tr1::tr2::ls -> let outf = (match ls with 
    | x::[] -> x
    | _ -> "witness.ml") in 
    ((m1,m2),(tr1,tr2),outf)
  | _ -> raise (CommandlineArg "Incorrect Arguments")


(*
 * ===  FUNCTION ======================================================================
 *         Name:  parse_module
 *  Description:  parse and typecheck an incoming module, return the type aswell
 * =====================================================================================
 *)
let parse_module file =
  Printf.eprintf "Parsing module :: %s\n" file;
  let input = Pervasives.open_in file in
  let lexbuf = Lexing.from_channel input in
  let prog = Parser.implementation Lexer.token lexbuf in
  let scoped_prog = MiniMLModScoping.scope_module Scope.empty prog in
  let mty = MiniMLModTyping.type_module MiniMLEnv.empty scoped_prog in
  (scoped_prog,mty)


(*
 * ===  FUNCTION ======================================================================
 *         Name:  parse_trace
 *  Description:  obtain a trace sequence from the parser
 * =====================================================================================
 *)
let parse_trace file =
  Printf.eprintf "Parsing trace :: %s\n" file;
  let input = Pervasives.open_in file in
  let lexbuf = Lexing.from_channel input in
  let traces = Parser.traces Lexer.token lexbuf in
  traces 


(*
 * ===  FUNCTION ======================================================================
 *         Name:  main
 *  Description:  feeds the lexer from stdin and then parses and compiles it
 * =====================================================================================
 *)
let main() =

  (* get the arguments *)
  let ((mf1,mf2),(trf1,trf2),outf) = commandline in

  (* parse and type check *)
  let m1 = parse_module mf1
  and m2 = parse_module mf2
  and tr1 = parse_trace trf1
  and tr2 = parse_trace trf2
  in

  (* party time *)
  let witness = Algorithm.build m1 m2 tr1 tr2 in
  let chan = open_out outf in
  Format.set_formatter_out_channel chan;
  (Pretty.print_module witness);
  Format.print_newline();
  exit 0

let _ = main()

