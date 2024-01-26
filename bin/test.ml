let rec at_time_range : type a. (a list) ->  unit =
  fun l -> match l with
    | [] -> ()
    | _ :: l1 -> at_time_range l1

let rec at_time_range_inv : type a. (a list) ->  unit =
  fun l -> match l with
    | [] -> ()
    | _ :: l1 -> at_time_range_inv l1

type var_t = {
  mutable var_state: Z.t;
  }

type env_t = {
  input_val: Z.t;
  input_set: Z.t;
  mutable output_val: (Z.t) option;
  }

type h_env_t = {
  h_var_state: Z.t;
  h_input_val: Z.t;
  h_input_set: Z.t;
  h_output_val: Z.t;
  }

type history_t = {
  mutable h_envs: h_env_t list;
  }

let duplicate_env (env: env_t) (var: var_t) : h_env_t =
  match env.output_val with
  | None -> assert false (* absurd *)
  | Some v ->
    { h_var_state = var.var_state; h_input_val = env.input_val; h_input_set =
      env.input_set; h_output_val = v }

let store_history (h: history_t) (env: env_t) (var: var_t) : unit =
  h.h_envs <- duplicate_env env var :: h.h_envs


let main (_: unit) : unit =
  let _history = { h_envs = []  } in
  let _var = { var_state = Z.zero } in
  _var.var_state <- Z.zero;
  while true do
    let _env = { input_val = Z.(random_int ~$10); input_set = Z.(one - ~$2 * (random_int ~$2)); output_val = None  } in
    if Z.gt _env.input_set Z.zero then _var.var_state <- _env.input_val;
    _env.output_val <- Some _var.var_state;
    store_history _history _env _var;
    Unix.sleep 1;
    print_string (Format.sprintf "[i : %i | input : %i | set : %i | output : %s]\n" 
      (List.length _history.h_envs - 1)
      (Z.to_int _env.input_val)
      (Z.to_int _env.input_set) 
      (match _env.output_val with None -> "/" | Some z -> Format.sprintf "%i" (Z.to_int z)));
    flush stdout;
    
  done


let () = main ()