(** Basic terminal UI to show proof progress *)
module F :
  (I : Sig.S) ->
    sig
      val prove : I.program -> I.triples -> unit
    end
