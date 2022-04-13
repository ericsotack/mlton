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
      datatype t = ExpNode of {oper: Oper.t,
                               children: id vector}
   end

structure Feg: 
   sig
      (* create this as a list and then convert to vector when we are encoding it *)
      datatype t = Feg of (int * ExpNode.t) vector
   end

fun transform (Program.T {globals, datatypes, functions, main}) =
   let
      fun leastDominatorThrough () (): () =
         ()

      fun decide () () () (): () =
         ()

      fun transFunction (f: Function.t) : Feg.t =
         let
            val {args, start, ...} = Function.dest f
            val nextNodeId = let val ctr = Counter.new 0 in fn () => Counter.next ctr end
            val nodes: (int * ExpNode.t) list ref = ref []
            val {get = varInfo: Var.t -> {defNodeId: int,
                                          useNodeId: Label.t list -> int},
               set = setVarInfo, ...} =
               Property.getSetOnce(Var.plist, Property.initRaise ("EqualitySat.varInfo"))
            fun varUse (x, ls) = #useNodeId (varInfo x) ls
            fun varDef x = #defNodeId (varInfo x)
            val lf: Block.T DirectedGraph.LoopForest.t =
               let val {graph, labelNode, nodeBlock} = Function.controlFlow f
               in DirectedGraph.loopForestSteensgaard (graph, {start = labelNode start, nodeValue = nodeBlock})
               end
            val setVarInfo = fn (x, ls_def) =>
               let
                  val defNodeId = nextNodeId ()
                  val useNodeId = fn ls_use => ...
               in
                  setVarInfo (x, {defNodeId = defNodeId, useNodeId = useNodeId})
               end

            val () = Vector.foreach(args, fn arg => setVarInfo (arg, []))
            fun setVarInfoLoop (lf, ls) =
            let
               fun setVarInfoBlock (b, ls) = Block.foreachVar(b, fn x => setVarInfo (x, ls))
               val {loops, notInLoop} = DirectedGraph.LoopForest.dest lf
               val _ = Vector.foreach (notInLoop, fn b => setVarInfoBlock (b, ls))
               val _ = Vector.foreach (loops, fn {headers, child} =>
                  let val header = Vector.first headers (* abandon if not singleton *)
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

            val _ = Vector.foreach(args, fn arg => List.push (nodes, (varDef arg, ExpNode.T {oper = Oper.Param(args), children = Vector.new0())}))


            (* but, needs to be done over loop forest to know the loop nesting *)
            val _ = Function.foreachVar(f, fn x => setVarInfo (x, {defNodeId = nextNodeId ()}))
         in
            Feg.Feg (Vector.fromList (!nodes))
         end

      fun transExp (nodes: ExpNode.t list) (exp: Exp.t) : int * ExpNode.t list = 
         (* input: the existing node list and the current exp
          * output: (id corresponding to location of node, the updated list of nodes)
          * NOTE: the children nodes should all already exist and just need to have their id looked up
          *)
         case exp of
            ConApp {con, args} =>
               let
                  val expOp = Oper.ConApp(con)
                  val children = Vector.map
                     (fn x => let val (childId, _) = transExp(x) in childId end) 
                     args
                  val newExpNode = ExpNode.ExpNode {oper: expOp, children: children}
                  val expId = List.length nodes
               in
                  (expId, newExpNode::nodes)
               end
          | Const expConst => 
               let
                  val expOp = Oper.Const(expConst)
                  val children = Vector.fromList []
                  val newExpNode = ExpNode.ExpNode {oper: expOp, children: children}
                  val expId = List.length nodes
               in
                  (expId, newExpNode::nodes)
               end
          | PrimApp {prim, targs, args} =>
               let 
                  val expOp = Oper.PrimApp prim
                  val children = Vector.map
                     (fn x => let val (childId, _) = transExp(x) in childId end) 
                     args
                  val newExpNode = ExpNOde.ExpNode {oper: expOp, children: children}
                  val expId = List.length nodes
               in
                  (expId, newExpNode::nodes)
               end
          | Select {offset, tuple} =>
               let
                  val expOp = Oper.Select(offset)
                  val (childId, _) = transExp nodes tuple
                  val children = Vector.fromList [childId]
                  val newExpNode = ExpNode.ExpNode {oper: expOp, children: children}
                  val expId = List.length nodes
               in
                  (expId, newExpNode::nodes)
               end
          | Tuple items =>
               let 
                  val expOp = Oper.Tuple
                  val children = Vector.map
                     (fn x => let val (childId, _) = transExp(x) in childId end) 
                     args
                  val newExpNode = ExpNOde.ExpNode {oper: expOp, children: children}
                  val expId = List.length nodes
               in
                  (expId, newExpNode::nodes)
               end
          | Var varName => () (* TODO do lookup in the property of the variable, nodes shouldn't change *)
          | Profile profExp => () (* TODO raise an exception here for unhandled *)

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