(* Copyright (C) 2022 Eric Sotack and Matthew Fluet
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

 (*
  * TODO documentation
  *)

functor EqualitySaturation (S: SSA_TRANSFORM_STRUCTS): SSA_TRANSFORM =
struct

open S

open Exp Transfer

type id = int

(* These identify the different operators a node can have *)
structure Oper:
   sig
      datatype t =
         Bottom
       | Eval
       | Pass
       | Theta
       | Const of Const.t
       | ConApp of Con.t
       | Tuple
       | Select of int
       | PrimApp of Prim.t
       (* TODO possibly add in stateful PrimApps?*)
       (*
       | PrimAppPure of Prim.t
       | PrimAppR of Prim.t
       | PrimAppRW of Prim.t
       *)
       (* FEG specific things *)
       | Identity
       | Param of Var.t
       | InitState
       | Call of Func.t
       | Return
       | Raise
       | Exit
       | CPhi
       | CMDefault
       | CMCons of Con.t
       | WPhi
       | WMDef
       | WMCons of WordX.t
       | ExtractReturn of int
       | ExtractException of int
       | IsReturn
       | IsException
       | DeCon of Con.t * int
       | RhoState
       | RhoResult
   end

structure ExpNode:
   sig
      datatype t = T of {oper: Oper.t,
                         children: id vector}

      fun new0 oper = T {oper = oper, children = Vector.new0 ()}
      fun new1 (oper, child) = T {oper = oper, children = Vector.new1 child}
   end

structure Feg: 
   sig
      datatype t = T of (int * ExpNode.t) vector
   end

fun transform (Program.T {globals, datatypes, functions, main}) =
   let
      fun leastDominatorThrough () (): () =
         ()

      fun decide () () () (): () =
         ()

      fun transFunction (f: Function.t) : Feg.t =
         let
            val nextNodeId = let val ctr = Counter.new 0 in fn () => Counter.next ctr end
            val nodes: (int * ExpNode.t) list ref = ref []
            fun addNode (id, node) = List.push(nodes, (id, node))

            val {args, start, ...} = Function.dest f

            val {get = varInfo: Var.t -> {nodeIdAt: Label.t list -> int},
               set = setVarInfo, ...} =
               Property.getSetOnce(Var.plist, Property.initRaise ("EqualitySat.varInfo"))

            val {get = labelInfo: Label.t -> {passNode: id option},
               set = setLabelfo, ...} =
               Property.getSetOnce(Label.plist, Property.initRaise ("EqualitySat.labelInfo"))

            fun varNodeIdAt (x, ls) = #nodeIdAt (varInfo x) ls
            val lf: Block.T DirectedGraph.LoopForest.t =
               let val {graph, labelNode, nodeBlock} = Function.controlFlow f
               in DirectedGraph.loopForestSteensgaard (graph, {start = labelNode start, nodeValue = nodeBlock})
               end
            val setVarInfo = fn (x, ls_def) =>
               let
                  val nodeIds = List.tabulate (List.length ls_def + 1, fn _ => nextNodeId ())
                  val nodeIdAt = fn ls_use =>
                     let
                        fun loop (ls_def, ls_use, len) =
                           case (ls_def, ls_use, len) of
                              ([], _) => len
                            | (_, []) => len
                            | (ld::ls_def, lu::ls_use) =>
                                 if Label.equals (ld, lu)
                                    then loop (ls_def, ls_use, len + 1)
                                    else len
                     in
                        List.nth (nodeIds, loop (ls_def, ls_use))
                     end
               in
                  setVarInfo (x, {nodeIdAt = nodeIdAt})
               end
            val () = Vector.foreach(args, fn arg => setVarInfo (arg, []))
            fun setVarInfoLoop (lf, ls) =
               let
                  fun setVarInfoBlock (b, ls) = Block.foreachVar(b, fn x => setVarInfo (x, ls))
                  val {loops, notInLoop} = DirectedGraph.LoopForest.dest lf
                  val _ = Vector.foreach (notInLoop, fn b => setVarInfoBlock (b, ls))
                  val _ = Vector.foreach (loops, fn {headers, child} =>
                                          let
                                             val header = Vector.first headers (* abandon if not singleton *)
                                             val ls = ls @ [Block.label header]
                                             val _ = setVarInfoBlock (header, ls)
                                             val _ = setVarInfoLoop (child, ls)
                                          in
                                             ()
                                          end)
               in
                  ()
               end
            val _ = setVarInfoLoop (lf, [])

            fun transVar (var: Var.t, ls: Label.t list) : int =
               varNodeAt (arg, ls)
            fun transVars (vars: Var.t vector, ls: Label.t list) : int vector =
               Vector.map (vars, fn var => transVar (var, ls))
            fun transExp (exp: Exp.t, ls: Label.t list) : ExpNode.t =
               case exp of
                  ConApp {con, args} =>
                     ExpNode.T {oper = Oper.ConApp con,
                                children = transVars (args, ls)}
                | Const c =>
                     ExpNode.new0 (Oper.Const c)
                | PrimApp {prim, targs, args} =>
                     ExpNode.T {oper = Oper.ConApp con,
                                children = transVars (args, ls)}
                | Profile _ => Error.bug "EqualitySaturation.transExp: Profile"
                | Tuple args =>
                     ExpNode.T {oper = Oper.Tuple,
                                children = transVars (args, ls)}
                | Select {offset, tuple} =>
                     ExpNode.T {oper = Oper.Select offset,
                                children = Vector.new1 (transVar (tuple, ls))}
                | Var arg =>
                     ExpNode.T {oper = Oper.Identity,
                                children = Vector.new1 (transVar (arg, ls))}
            fun addNodeStatement (stmt: Statement.t ls: Label.t list) : unit =
               let
                  val Statement.T {var, exp, ...} stmt
               in
                  case var of
                     NONE => ()
                   | SOME var => addNode (varNodeAt (var, ls), transExp (exp, ls))
               end
            fun addNodesBlock (b: Block.t, ls: Label.t list): unit =
               let
                  val Block.T {label, args, statements, transfer} = b
                  val _ = Vector.app (statements, fn stmt => addNodeStatement (stmt, ls))
               in
                  ()
               end
               
            val _ = Vector.foreach(args, fn arg =>
                                   addNode (varNodeIdAt (arg, []),
                                            ExpNode.new0 (Oper.Param arg)))
            fun addNodesLoop (lf, ls) =
               let
                  val {loops, notInLoop} = DirectedGraph.LoopForest.dest lf
                  val _ = Vector.foreach (notInLoop, fn b => addNodeBlock (b, ls))
                  val _ = Vector.foreach (loops, fn {headers, child} =>
                                          let
                                             val header = Vector.first headers (* abandon if not singleton *)
                                             val ls = ls @ [Block.label header]
                                             val _ = addNodesBlock (header, ls)
                                             val _ = addNodesLoop (child, ls)
                                          in
                                             ()
                                          end)
               in
                  ()
               end
            val _ = addNodesLoop (lf, [])
         in
            Feg.T (Vector.fromList (!nodes))
         end

      fun transStatement (nodes: ExpNode.t list) (st: Statement.t): (int * ExpNode.t list) =
         (* input: list of preexisting nodes to allow transExp, statement to be trans
          * output: ind of newly added node and updated list of ndoe
          *)
         case st of
            Statement {exp, ty, var} =>
               case var of
                  NONE => () (* still need to keep it around for side effects on state *)
                | SOME var => () (* side effects and updated map aka store it in the Property*)
   in
      Program.T {globals = globals,
                 datatypes = datatypes,
                 functions = functions,
                 main = main}
  end

end