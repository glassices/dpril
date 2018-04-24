let safe_map f mes =
  let rec mapf l =
    match l with
      h::t -> (try let y = f h in
                   y::(mapf t)
               with Failure s when s = mes -> mapf t)
    | [] -> [] in
  mapf;;

let rec rm x l =
  match l with
    h::t -> if x = 0 then t
            else h::(rm (x-1) t)
  | [] -> [];;

let fst_map f =
  let rec fst_mapf l =
    match l with 
      [] -> []
    | (a,b)::t -> (f a,b)::(fst_mapf t) in
  fst_mapf;;

let pmap f =
  let rec pmapf l =
    match l with
      [] -> []
    | (a,b)::t -> (f a,f b)::(pmapf t) in
  pmapf;;

let rec pop p l =
  match l with
    [] -> failwith "pop"
  | h::t -> if p(h) then h,t
            else let x,s = pop p t in x,(h::s);;

let rec tm_size tm =
  match tm with
    Comb(f,x) -> (tm_size f) + (tm_size x)
  | Abs(_,bod) -> tm_size bod
  | _ -> 1;;

let has_prefix s1 s2 =
  let l1 = String.length s1 and l2 = String.length s2 in
  l1 >= l2 && (String.sub s1 0 l2) = s2;;

(*
 * Input: `:A->B->C->D`
 * Output: ([`:A`; `:B`; `:C`], `:D`)
 *)
let rec dest_fun ty : hol_type list * hol_type =
  try let a,b = dest_fun_ty ty in
      let tyl,apex = dest_fun b in
      (a::tyl),apex
  with Failure "dest_fun_ty" -> [],ty;;

(*
 * Input: ([`:A`; `:B`; `:C`], `:D`)
 * Output: `:A->B->C->D`
 *)
let rec mk_fun (tyl,apex) : hol_type =
  match tyl with
    h::t -> mk_fun_ty h (mk_fun (t,apex))
  | [] -> apex;;

(*
 * Input: `f` [`x`; `y`]
 * Output: `f x y`
 *)
let rec mk_lcomb (f : term) (args : term list) : term =
  match args with
    h::t -> mk_lcomb (mk_comb(f,h)) t
  | [] -> f;;

let (beta_conv : conv) = TOP_DEPTH_CONV BETA_CONV;;

let (eta_conv : conv) = TOP_DEPTH_CONV ETA_CONV;;

let (top_eta_conv : conv) = TRY_CONV ETA_CONV;;

let (beta_eta_conv : conv) = (TOP_DEPTH_CONV BETA_CONV) THENC (TOP_DEPTH_CONV ETA_CONV);;

let (beta_eta_term : term -> term) = rand o concl o beta_eta_conv;;

let (eta_term : term -> term) = rand o concl o eta_conv;;

let conv_term (cnv : conv) = rand o concl o cnv;;

(* conv the concl of a theorem *)
let conv_concl (cnv : conv) (th : thm) : thm =
  EQ_MP (cnv (concl th)) th;;

(* Conv assumptions and the conclusion of a theorem *)
let conv_thm (cnv : conv) (th : thm) : thm =
  let asl,c = dest_thm th in
  let work a th =
    let eth = cnv a in
    let gth = EQ_MP (SYM eth) (ASSUME (rand (concl eth))) in
    EQ_MP (DEDUCT_ANTISYM_RULE gth th) gth in
  conv_concl cnv (itlist work asl th);;

(* get bound variables and remain term
 * Input: `\x y z. f x y z`
 * Output: ([`x`; `y`; `z`], `f x y z`)
 * DONE CHECKING
 *)
let rec get_bound (tm : term) : term list * term =
  match tm with
    Abs(bvar,bod) -> let tml,tm' = get_bound bod in (bvar::tml),tm'
  | _ -> [],tm;;

(* decompose a beta-eta normal term into bound_vars,(head symbol,args)
 * DONE CHECKING
 *)
let decompose (tm : term) : term list * (term * term list) =
  let bvars,ctm = get_bound tm in
  bvars,strip_comb ctm;;

(*
 * mk_term [x1;x2;x3] t = \x1 x2 x3. t
 * DONE CHECKING
 *)
let rec mk_term bvars bod =
  match bvars with
    [] -> bod
  | h::t -> mk_abs(h,mk_term t bod);;

let safe_index x =
  let rec ind n l =
    match l with
      [] -> -1
    | (h::t) -> if Pervasives.compare x h = 0 then n else ind (n + 1) t in
  ind 0;;

(* get the index of bvar, -1 if not bounded
 * find from the tail, e.g.
 * bindex x [x;x;x] = 2
 * bindex x [x;x;y] = 1
 * bindex x [x;y;y] = 0
 * bindex x [y;y;y] = -1
 * DONE CHECKING
 *)
let bindex (var : term) (bvars : term list) : int =
  try let ret = index var (rev bvars) in
      (length bvars) - ret - 1
  with Failure "index" -> -1;;

(* string_of_term without spaces and newlines *)
let ss_term tm =
  let s = string_of_term tm in
  let ls = map (fun x -> if x = "\n" then " " else x) (explode s) in
  let rec work ls =
    match ls with
      a::(b::t) -> if a = " " then
                     if b = " " then work (b::t)
                     else a::b::(work t)
                   else a::(work (b::t))
    | _ -> ls in
  String.concat "" (work ls);;

(* string_of_thm without spaces and newlines *)
let ss_thm th =
  let asl,c = dest_thm th in
  (if asl <> [] then
     (rev_itlist (fun tm s -> s ^ ", " ^ (ss_term tm)) (tl asl) (ss_term (hd asl))) ^ " "
   else ""
  ) ^ "|- " ^ (ss_term c);;

let rec ord_of_type ty =
  let tyl,_ = dest_fun ty in
  (itlist (fun ty x -> max (ord_of_type ty) x) tyl 0) + 1;;

let ord_of_term tm = ord_of_type (type_of tm);;

let is_fun = function (Tyapp("fun",_)) -> true | _ -> false;;

let rec sariant s avoid =
  if mem s avoid then sariant (s ^ "'") avoid
  else s;;

(* expand a term to its long eta form with de bruijn index w1,w2,...
 * NOTE that w* is only preserved for this usage, tm should have have w*
 * as free variables
 * NOTE tm might have w* has bound variables
 *)
let eta_expand tm =
  let rec work pos tm =
    match tm with
      Abs(bvar,bod) -> let v = mk_var("w" ^ (string_of_int pos),type_of bvar) in
                       mk_abs(v,work (pos+1) (vsubst [v,bvar] bod))
    | _ ->  let tyl,_ = dest_fun (type_of tm) in
           let extra = List.mapi (fun i ty -> mk_var("w" ^ (string_of_int (pos+i)),ty)) tyl in
           mk_term extra (mk_lcomb tm extra) in

  let tm' = work 1 tm in
  if alphaorder (eta_term tm') (eta_term tm) <> 0 then (
    print_endline ((ss_term tm) ^ "\t" ^ (ss_term tm'));
    failwith "eta_expand"
  ) else tm';;
