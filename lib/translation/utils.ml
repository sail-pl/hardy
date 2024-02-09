(* add unique location to each node for easier debugging *)

module H =  Why3.Ptree_helpers
module P = Why3.Mlw_printer

let expr = H.expr ~loc:(P.next_pos ())
let econst = H.econst ~loc:(P.next_pos ())
let evar = H.evar ~loc:(P.next_pos ())
let ident = H.ident ~loc:(P.next_pos ())
let term = H.term ~loc:(P.next_pos ())
let eapply = H.eapply ~loc:(P.next_pos ())
let eapp = H.eapp ~loc:(P.next_pos ())
let use = H.use ~loc:(P.next_pos ())
let pat = H.pat ~loc:(P.next_pos ())