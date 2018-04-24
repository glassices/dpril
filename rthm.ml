needs "dpril/unification.ml";;

let hins = ref (([],[]) : instor);;

module type Rthm_kernel =
  sig
    type rthm

    val dest_rthm : rthm -> term list * term * (term * term) list * (term * string) list
    val rhyp : rthm -> term list
    val rconcl : rthm -> term
    val rpairs : rthm -> (term * term) list
    val rrsl : rthm -> (term * string) list

    val reset_rcount : unit -> unit
    val mk_rthm : thm -> rthm
    val req_mp : rthm -> rthm -> rthm
    val rtrans : rthm -> rthm -> rthm
    val rmk_comb : rthm -> rthm -> rthm
    val rdeduct : rthm -> rthm -> int -> int -> rthm
    val rabs : rthm -> rthm

    val rmatch : rthm -> (term list * term) -> instor * thm

end;;

module Rthm : Rthm_kernel = struct

  type rthm = Rhythm of (term list * term * (term * term) list * (term * string) list * (instor -> thm))


  let dest_rthm (Rhythm(asl,c,pairs,rsl,_)) = asl,c,pairs,rsl

  let rhyp (Rhythm(asl,_,_,_,_)) = asl

  let rconcl (Rhythm(_,c,_,_,_)) = c

  let rpairs (Rhythm(_,_,pairs,_,_)) = pairs

  let rrsl (Rhythm(_,_,_,rsl,_)) = rsl


  (* xx1, xx2, xx3, ... *)
  let nfvars = ref 0
  (* C1, C2, C3, ... *)
  let nftys = ref 0
  (* mc1, mc2, mc3, ... *)
  let nbvars = ref 0

  let new_fvar() = (nfvars := !nfvars+1; "xx" ^ (string_of_int !nfvars))

  let new_fty() = (nftys := !nftys+1; "C" ^ (string_of_int !nftys))

  let new_bvar() = (nbvars := !nbvars+1; "mc" ^ (string_of_int !nbvars))

  let reset_rcount() = (nfvars := 0; nftys := 0; nbvars := 0)

  let is_print = ref true

  let print_on() = is_print := true

  let print_off() = is_print := false

  let mk_rthm th =
    let th = conv_thm beta_eta_conv th in
    let ftys = itlist (union o type_vars_in_term) ((concl th)::(hyp th)) [] in
    let tyins = map (fun fty -> (mk_vartype(new_fty())),fty) ftys in
    let fvars = map (inst tyins) (freesl ((concl th)::(hyp th))) in
    let tmins = map (fun fvar -> (mk_var(new_fvar(),type_of fvar)),fvar) fvars in
    let th = inst_thm (tyins,tmins) th in
    let asl,c = dest_thm th in
    Rhythm(asl,c,[],[],fun ins -> conv_thm beta_eta_conv (inst_thm ins th))

  let distill (asl,c,pairs,rsl,invoke) =
    try let pairs,rsl,ins1 = init_data [] [] pairs rsl in
        let pairs,rsl,ins2 = simplify [] [] pairs rsl in
        let ins = merge_ins ins1 ins2 in
        Rhythm(map (beta_eta_term o (inst_term ins)) asl,
               beta_eta_term (inst_term ins c),
               pairs,rsl,
               fun ins' -> invoke (merge_ins ins ins'))
    with Failure s when s = "init_data" || s = "simplify" -> failwith "distill"

  let req_mp (Rhythm(asl1,c1,pairs1,rsl1,invoke1)) (Rhythm(asl2,c2,pairs2,rsl2,invoke2)) =
    let v = mk_var(new_fvar(),bool_ty) in
    distill(asl1 @ asl2,v,(c1,mk_eq(c2,v))::(pairs1 @ pairs2),rsl1 @ rsl2,
            fun ins -> let th1 = invoke1 ins and th2 = invoke2 ins in
                       let th = EQ_MP th1 th2 in
                       (if !is_print then print_endline ("EQ_MP\t" ^ (ss_thm th) ^ "\t" ^ (ss_thm th1) ^ "\t" ^ (ss_thm th2)) else (); th))

  let rtrans (Rhythm(asl1,c1,pairs1,rsl1,invoke1)) (Rhythm(asl2,c2,pairs2,rsl2,invoke2)) =
    let aty = mk_vartype(new_fty()) in
    let x = mk_var(new_fvar(),aty) in
    let y = mk_var(new_fvar(),aty) in
    let z = mk_var(new_fvar(),aty) in
    distill(asl1 @ asl2,mk_eq(x,z),
            (c1,mk_eq(x,y))::(c2,mk_eq(y,z))::(pairs1 @ pairs2),rsl1 @ rsl2,
            fun ins -> let th1 = invoke1 ins and th2 = invoke2 ins in
                       let th = TRANS th1 th2 in
                       (if !is_print then print_endline ("TRANS\t" ^ (ss_thm th) ^ "\t" ^ (ss_thm th1) ^ "\t" ^ (ss_thm th2)) else (); th))

  let rmk_comb (Rhythm(asl1,c1,pairs1,rsl1,invoke1)) (Rhythm(asl2,c2,pairs2,rsl2,invoke2)) =
    let aty = mk_vartype(new_fty()) and bty = mk_vartype(new_fty()) in
    let s = mk_var(new_fvar(),mk_fun_ty aty bty) and t = mk_var(new_fvar(),mk_fun_ty aty bty) in
    let u = mk_var(new_fvar(),aty) and v = mk_var(new_fvar(),aty) in
    distill(asl1 @ asl2,mk_eq(mk_comb(s,u),mk_comb(t,v)),
            (c1,mk_eq(s,t))::(c2,mk_eq(u,v))::(pairs1 @ pairs2),rsl1 @ rsl2,
            fun ins -> let th1 = invoke1 ins and th2 = invoke2 ins in
                       let th = conv_thm beta_eta_conv (MK_COMB (th1,th2)) in
                       (if !is_print then print_endline ("MK_COMB\t" ^ (ss_thm th) ^ "\t" ^ (ss_thm th1) ^ "\t" ^ (ss_thm th2)) else (); th))

  let rdeduct (Rhythm(asl1,c1,pairs1,rsl1,invoke1)) (Rhythm(asl2,c2,pairs2,rsl2,invoke2)) mask1 mask2 =
    let rec work asl c mask : (term list * (term * term) list) =
      match asl with
        h::t -> let rm,ps = work t c ((lsr) mask 1) in
                if (land) mask 1 = 1 then rm,(h,c)::ps
                else h::rm,ps
      | [] -> [],[] in

    let asl1,ps1 = work asl1 c2 mask1 in
    let asl2,ps2 = work asl2 c1 mask2 in
    distill(asl1 @ asl2,mk_eq(c1,c2),ps1 @ ps2 @ pairs1 @ pairs2,rsl1 @ rsl2,
            fun ins -> let th1 = invoke1 ins and th2 = invoke2 ins in
                       let th = DEDUCT_ANTISYM_RULE th1 th2 in
                       (if !is_print then print_endline ("DEDUCT\t" ^ (ss_thm th) ^ "\t" ^ (ss_thm th1) ^ "\t" ^ (ss_thm th2)) else (); th))

  let rabs (Rhythm(asl,c,pairs,rsl,invoke)) =
    let aty = mk_vartype(new_fty()) and bty = mk_vartype(new_fty()) in
    let u = mk_var(new_fvar(),mk_fun_ty aty bty) and v = mk_var(new_fvar(),mk_fun_ty aty bty) in
    let name = new_bvar() in
    let mc = mk_var(name,aty) in
    distill(asl,mk_eq(u,v),(c,mk_eq(mk_comb(u,mc),mk_comb(v,mc)))::pairs,
            (map (fun x -> x,name) (u::v::asl)) @ rsl,
            fun ins -> let th' = invoke ins in
                       let th = conv_thm eta_conv (ABS (inst_term ins mc) th') in
                       (if !is_print then print_endline ("ABS\t" ^ (ss_thm th) ^ "\t" ^ (ss_thm th')) else (); th))

  (* Higher-order semi-matching
   * I guess this procedure might be decidable
   * NOTE: preserved names of free vars: xx*, mc*, z* (inside unification), w* (De Brujin names for expand_eta)
   *       preserved names of free typevars: C*, Z* (inside unification)
   *)
  let rmatch (Rhythm(asl,c,pairs,rsl,invoke)) (asl',c') =
    let fvars = freesl (c'::asl') and ftys = itlist (union o type_vars_in_term) (c'::asl') [] in
    let const_var = List.sort_uniq Pervasives.compare (map name_of fvars) in
    let const_ty = List.sort_uniq Pervasives.compare (map dest_vartype ftys) in
    let rec work csl csl' pairs =
      match csl with
        h::t -> (match csl' with
                   h'::t' -> let ins = work t asl' ((h,h')::pairs) in
                             if ins = [] then work csl t' pairs else ins 
                 | [] -> []
                )
      | [] -> hol_unify const_ty const_var pairs rsl in
    let insl = work asl asl' ((c,c')::pairs) in
    let ins = if insl <> [] then Some(hd insl) else None in
    match ins with
      Some(ins) -> ins,invoke ins
    | None -> failwith "rmatch"

end;;

include Rthm;;

let string_of_rthm rth =
  let asl,tm,pairs,rsl = dest_rthm rth in
  (if not (asl = []) then
     (rev_itlist (fun tm s -> s ^ ", " ^ (ss_term tm)) (tl asl) (ss_term (hd asl)))
     ^ " "
   else "") ^
  "|- " ^ (ss_term tm) ^
  (if not (pairs = []) then
     let tm,tm' = hd pairs in
     let s = (ss_term tm) ^ "," ^ (ss_term tm') in
     " [" ^
     (rev_itlist (fun (tm1,tm2) s -> s ^ "; " ^ (ss_term tm1) ^ "," ^ (ss_term tm2)) (tl pairs) s)
     ^ "]"
   else "") ^
  (if not (rsl = []) then
     let tm,name = hd rsl in
     let s = (ss_term tm) ^ "," ^ name in
     " {" ^
     (rev_itlist (fun (tm,name) s -> s ^ "; " ^ (ss_term tm) ^ "," ^ name) (tl rsl) s)
     ^ "}"
   else ""
  );;

let pp_print_rthm fmt rth =
  let asl,tm,pairs,rsl = dest_rthm rth in
  (if not (asl = []) then
    (if !print_all_thm then
      (pp_print_string fmt (ss_term (hd asl));
       do_list (fun x -> pp_print_string fmt ",";
                         pp_print_space fmt ();
                         pp_print_string fmt (ss_term x))
               (tl asl))
     else pp_print_string fmt "...";
     pp_print_space fmt ())
   else ();
   pp_open_hbox fmt();
   pp_print_string fmt "|- ";
   pp_print_string fmt (ss_term tm);
   if not (pairs = []) then (
     pp_print_space fmt ();
     pp_print_string fmt "[";
     pp_print_string fmt (ss_term (fst (hd pairs)));
     pp_print_string fmt ",";
     pp_print_string fmt (ss_term (snd (hd pairs)));
     do_list (fun x -> pp_print_string fmt ";";
                       pp_print_space fmt ();
                       pp_print_string fmt (ss_term (fst x));
                       pp_print_string fmt ",";
                       pp_print_string fmt (ss_term (snd x)))
             (tl pairs);
     pp_print_string fmt "]";
   ) else ();
   if not (rsl = []) then (
     pp_print_space fmt ();
     pp_print_string fmt "{";
     pp_print_string fmt ((ss_term (fst (hd rsl))) ^ "," ^ (snd (hd rsl)));
     do_list (fun x -> pp_print_string fmt ";";
                       pp_print_space fmt ();
                       pp_print_string fmt ((ss_term (fst x)) ^ "," ^ (snd x)))
             (tl rsl);
     pp_print_string fmt "}";
   ) else ();
   pp_close_box fmt ());;

let print_rthm = pp_print_rthm std_formatter;;
#install_printer print_rthm;;

