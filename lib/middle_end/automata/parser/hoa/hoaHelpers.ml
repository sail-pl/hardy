open HoaSyntax

exception Missing_item of string

let [@warning "-4"] get_props hoa = 
  List.filter_map (function Properties n -> Some n | _ -> None) hoa.header.items |> List.flatten

let [@warning "-4"] get_acceptance hoa = 
  try List.find_map (function Accept (n,s) -> Some (n,s) | _ -> None) hoa.header.items |> Option.get
  with Invalid_argument _ -> raise @@ Missing_item "Acceptance" 

let [@warning "-4"] get_atoms hoa =
  try List.find_map (function Atomic (_,l) -> Some l | _ -> None) hoa.header.items |> Option.get |> List.mapi (fun i x -> (i,x))
  with Invalid_argument _ -> raise @@ Missing_item "Atoms" 

let [@warning "-4"] get_start hoa = 
  List.filter_map (function Start l -> Some l | _ -> None ) hoa.header.items |> List.flatten

let [@warning "-4"] get_num_states hoa = 
List.find_map (function States n -> Some n | _ -> None) hoa.header.items