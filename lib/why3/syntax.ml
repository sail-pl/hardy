

type ident = string 
type qualid = string 
type constant = int option

type pty = 
  | PTtyapp of qualid * pty list 
  | PTref of pty

type param = ident * pty

type binder = ident list * pty

type binop = Plus | Minus | Mult

type term = 
  | Ttrue 
  | Tfalse 
  | Tconst of constant 
  | Tident of qualid 
  | Tidapp of qualid * term list 
  | Tapply of term * term 
  | Tinfix of term * ident * term 
    | TAnd of term * term 
  | TOr of term * term
  | TImp of term * term
  | Tnot of term 
  | TForall of binder list * term 
  | TExists of binder list * term

type invariant = term list 
type variant = term list 
type pre = term 
type post = term 
type spec = {
  sp_pre : pre;
  sp_post : post
}

type expr = 
	| Etrue
  | Efalse
  | Econst of constant 
  | Eident of qualid
  | Eapply of expr * expr 
  | Einfix of expr * ident * expr 
  | Elet of ident * expr * expr 
  | Erecord of (qualid * expr) list 
  | Eassign of expr * qualid option * expr  
  | Esequence of expr * expr 
  | Eif of expr * expr * expr 
  | EWhile of expr * invariant * variant * expr 
  | Eand of expr * expr 
  | Eor of expr * expr 
  | Enot of expr 
  | Eassert of term 

type fundef = 
  {
    fun_id : ident;
    fun_params :  binder list;
    fun_spec : spec;
    fun_body : expr
  } 

type field = {
  f_ident : ident;
  f_pty : pty
}

type type_decl = {
  td_ident : ident;
  td_params : ident list 
}

type logic_decl = {
  ld_ident : ident;
  ld_params : param list;
  ld_type : pty option;
  ld_def : term option
}

type decl = 
  | Dtype of type_decl list 
  | Dlogic of logic_decl 
  | DLet of ident * expr
  | Drec of fundef list 

type why3module = 
{
  m_types : type_decl list;
  m_logic : logic_decl list;
  m_let : (ident * expr) list;
  m_rec : fundef list
}
