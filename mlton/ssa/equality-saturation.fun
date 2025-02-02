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
structure Oper =
   struct
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
       (* possibly add in stateful PrimApps? *)
       (*
       | PrimAppPure of Prim.t
       | PrimAppR of Prim.t
       | PrimAppRW of Prim.t
       *)
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
      
      fun layout oper =
         let
            open Layout
         in
            case oper of
               Bottom => str "Bottom"
             | Eval => str "Eval"
             | Pass => str "Pass"
             | Theta => str "Theta"
             | Const c => seq [str "Const", str " ", Const.layout c]
             | ConApp con => seq [str "ConApp", str " ", Con.layout con]
             | Tuple => str "Tuple"
             | Select i => seq [str "Select", str " ", str (Int.toString i)]
             | PrimApp prim => seq [str "PrimApp", str " ", Prim.layout prim]
             | Identity => str "Identity"
             | Param var => seq [str "Param", str " ", Var.layout var]
             | InitState => str "InitState"
             | Call func => seq [str "Call", str " ", Func.layout func]
             | Return => str "Return"
             | Raise => str "Raise"
             | Exit => str "Exit"
             | CPhi => str "CPhi"
             | CMDefault => str "CMDefault"
             | CMCons con => seq [str "CMCons", str " ", Con.layout con]
             | WPhi => str "WPhi"
             | WMDef => str "WMDef"
             | WMCons wordx => seq [str "WMCons", str " ", WordX.layout (wordx, {suffix=true})]
             | ExtractReturn i => seq[str "ExtractReturn", str " ", str (Int.toString i)]
             | ExtractException i => seq[str "ExtractException", str " ", str (Int.toString i)]
             | IsReturn => str "IsReturn"
             | IsException => str "IsException"
             | DeCon (con, i) => seq [str "DeCon", str " ", Con.layout con, str " ", str (Int.toString i)]
             | RhoState => str "RhoState"
             | RhoResult => str "RhoResult"
         end
   end

structure ExpNode =
   struct
      datatype t = T of {oper: Oper.t,
                         children: id vector}

      fun new0 oper = T {oper = oper, children = Vector.new0 ()}
      fun new1 (oper, child) = T {oper = oper, children = Vector.new1 child}
      fun layout' layoutChild en =
         let
            open Layout
            fun layoutChildren cs = Vector.layout layoutChild cs
         in
            case en of
               T {oper, children} => seq [str "(", Oper.layout oper, str ")", str ", ", layoutChildren children]
         end
      fun layout en = layout' (fn i => str (Int.toString i)) en
   end

structure Feg =
   struct
      datatype t = T of (int * ExpNode.t) vector
      fun layout f =
         let
            open Layout
            fun layoutItem (i, node) = seq [str "{", str "idx: ", str (Int.toString i), str ", node: ", ExpNode.layout node, str "}"]
         in
            case f of
               T nodes => Vector.layout layoutItem nodes
         end
   end

fun transform (Program.T {globals, datatypes, functions, main}) =
   let
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
               set = setLabelInfo, ...} =
               Property.getSetOnce(Label.plist, Property.initRaise ("EqualitySat.labelInfo"))

            fun varNodeIdAt (x, ls) = #nodeIdAt (varInfo x) ls
            val lf: Block.T DirectedGraph.LoopForest.t =
               let val {graph, labelNode, nodeBlock} = Function.controlFlow f
               in DirectedGraph.loopForestSteensgaard (graph, {root = labelNode start, nodeValue = nodeBlock})
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
               varNodeAt (var, ls)
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
                     ExpNode.T {oper = Oper.PrimApp prim,
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
            fun addNodeStatement (stmt: Statement.t, ls: Label.t list) : unit =
               let
                  val Statement.T {var, exp, ...} = stmt
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

      val _ = () (* TODO: for function in program, make FEG and output it *)
   in
      Program.T {globals = globals,
                 datatypes = datatypes,
                 functions = functions,
                 main = main}
  end

end