type 'a arc_data = { arc_f : 'a FrontParser.ProgramSyntax.hoare_pair; }
type vertex_data = { v_min_nb_instants : FrontParser.InstantSyntax.min_nb_instants; }

module Make : (G : BuchiSig.S) -> BuchiSig.S with 
    type init_val = G.t * G.t and 
    type E.label =  G.E.label arc_data and 
    type vdata = vertex_data 