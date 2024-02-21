module AS = ArduinoSyntax.AutomatonSyntax
module S = ArduinoSyntax.Syntax
open Graph

module Vertex = struct (* states are just labels *)
  type t = string 
  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc = struct 
    type t = AS.bform
    let compare = Stdlib.compare
    let default = AS.True
end


module PVertex = struct (* easier with one label per merged node *)
  type t = string * string 


  let compare (t1l,t1r) (t2l,t2r) = match String.compare t1l t2l with 0 -> String.compare t1r t2r | c -> c 
  let hash (lt,rt) = String.hash (lt^rt)
  let equal (t1l,t1r) (t2l,t2r) = String.equal t1l t2l && String.equal t1r t2r
end


(* to make the synchronised product of the rely and guarantee formula automaton, 
   we need to remember when merging arcs which formula is the precondition and which is the postcondition *)
module PArc = struct 
  type t = AS.bform S.hoare_pair
  let compare = Stdlib.compare
  let default = S.{requires = AS.True ; ensures =  AS.True}
end


(* synchronized product is of type G -> G -> PG *)
module G = Imperative.Digraph.ConcreteLabeled(Vertex)(Arc)
module PG = Imperative.Digraph.ConcreteLabeled(PVertex)(PArc)


module Buchi = struct 
  include G

  let create ((states,arcs):AS.buchi_automaton) : t =
    let g = create ~size:(List.length states) () in
    List.iter (fun (s1,f,s2) -> 
      let e = E.create s1 f s2 in
      add_edge_e g e
    ) arcs;
    g
end


module BuchiProd = struct 
  include PG

  let create ~rely_a:(a1 : G.t) ~guarantee_a:(a2 : G.t) : PG.t = 
    let res = PG.create ~size:G.(nb_vertex a1 + nb_vertex a2) () in

    G.iter_edges_e (fun rely -> 
      G.iter_edges_e (fun guarantee -> 
        let label = S.{requires = G.E.label rely ; ensures = G.E.label guarantee} in

        let src = G.E.(src rely,src guarantee) in
        let dest = G.E.(dst rely,dst guarantee ) in

        let edge = PG.E.create src label dest in
        add_edge_e res edge
      ) a2
    ) a1
    ;
    res
end


module CommonDot = struct
  let default_vertex_attributes _ = [`Shape `Circle; `Fixedsize true; `Height 0.8; `Fontsize 10]
  let default_edge_attributes _ =  [`Fontsize 10]   
    
  let get_subgraph _ = None
  let graph_attributes _g = []
end


module BuchiDot(G : Graph.Sig.I)(P : 
    sig 
      val acceptant : G.V.t -> bool 
      val string_of_vertex : G.V.label -> string 

      val string_of_edge : G.E.label -> string 
    end
  ) = struct 

    include Graph.Graphviz.Dot (
    struct
      include G
      include CommonDot


      let vertex_name (v:vertex) = "\"" ^ P.string_of_vertex (V.label v) ^ "\""

      let edge_attributes e = [`Label (E.label e |> P.string_of_edge)]

      let vertex_attributes v = if P.acceptant v then [`Shape `Doublecircle] else []
      
    end
  ) 
  end