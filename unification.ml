(*
 * Let's do some crazy stuff here.
 * Let's support fully complete polymorphic higher-order unification
 * Godel please bless this project with your speed-up theorem
 *)
needs "dpril/kit.ml";;

type instor =
  (hol_type * hol_type) list * (term * term) list;;

let inst_term (tyins,tmins) tm =
  vsubst tmins (inst tyins tm);;

let inst_thm (tyins,tmins) th =
  INST tmins (INST_TYPE tyins th);;

let update_tyins i theta =
  map (fun (a,b) -> type_subst [i] a,b) theta;;

let update_tmins i theta =
  map (fun (a,b) -> beta_eta_term (vsubst [i] a),b) theta;;

let insert_tyins i theta =
  i::(map (fun (a,b) -> type_subst [i] a,b) theta);;

let insert_tmins i theta =
  i::(map (fun (a,b) -> beta_eta_term (vsubst [i] a),b) theta);;

let safe_tyins (x,y) theta =
  if exists (fun (a,b) -> Pervasives.compare b y = 0) theta then
    map (fun (a,b) -> type_subst [x,y] a,b) theta
  else (x,y)::(map (fun (a,b) -> type_subst [(x,y)] a,b) theta);;

let safe_tmins (x,y) theta =
  if exists (fun (a,b) -> Pervasives.compare b y = 0) theta then
    map (fun (a,b) -> beta_eta_term (vsubst [x,y] a),b) theta
  else (x,y)::(map (fun (a,b) -> beta_eta_term (vsubst [x,y] a),b) theta);;

let merge_ins (tyins1,tmins1) (tyins2,tmins2) =
  itlist update_tyins tyins2 tyins1,
  itlist update_tmins tmins2 (pmap (inst tyins2) tmins1);;


module type Hunify_kernel =
  sig

    val type_unify : string list -> (hol_type * hol_type) list -> (hol_type * hol_type) list
    val init_data : string list -> string list -> (term * term) list -> (term * string) list -> (term * term) list * (term * string) list * instor
    val simplify : string list -> string list -> (term * term) list -> (term * string) list -> (term * term) list * (term * string) list * instor
    val hol_unify : string list -> string list -> (term * term) list -> (term * string) list -> instor list 
    val hol_quick_check : (term * term) list -> (term * string) list -> bool

end;;

module Hunify : Hunify_kernel = struct

  (*
   * const_ty : the set of const types which are not allowed to be instantiated
   *)
  let type_unify const_ty =
    let is_free_ty = function (Tyvar(name)) -> not (mem name const_ty) | _ -> false in

    let rec tfree_in t ty =
      if is_vartype ty then Pervasives.compare t ty = 0
      else exists (tfree_in t) (snd (dest_type ty)) in

    let rec unify ty1 ty2 sofar =
      let ty1 = rev_assocd ty1 sofar ty1 and ty2 = rev_assocd ty2 sofar ty2 in
      let ty1,ty2 = if is_free_ty ty2 then ty2,ty1 else ty1,ty2 in
      if is_free_ty ty1 then
        let ty2 = type_subst sofar ty2 in
        if Pervasives.compare ty1 ty2 = 0 then sofar
        else if tfree_in ty1 ty2 then failwith "type_unify"
        else insert_tyins (ty2,ty1) sofar
      else if is_type ty1 && is_type ty2 then
        let op1,args1 = dest_type ty1 and op2,args2 = dest_type ty2 in
        if op1 = op2 then itlist2 unify args1 args2 sofar
        else failwith "type_unify"
      else if Pervasives.compare ty1 ty2 = 0 then sofar
      else failwith "type_unify" in

    fun task ->
      let task = filter (fun (u,v) -> Pervasives.compare u v <> 0) task in
      let lst,rst = unzip task in
      itlist2 unify lst rst []

  let init_data const_ty const_var pair rsl =
    let tml = (let l,r = unzip pair in l @ r) @ (fst (unzip rsl)) in
    let fvars = filter (fun v -> not (mem (name_of v) const_var)) (freesl tml) in
    let ftys = filter (fun t -> not (mem (dest_vartype t) const_ty)) (itlist (union o type_vars_in_term) tml []) in
    let fvnames = List.sort_uniq Pervasives.compare (map (fun x -> name_of x) fvars) in
    if length fvars <> length fvnames then failwith "init_data[fatal]: different free vars have same name"
    else try let tmp = type_unify const_ty (pmap type_of pair) in
             let tyins = map (fun t -> type_subst tmp t,t) ftys in
             let tmins = map (fun v -> let v' = inst tmp v in v',v') fvars in
             let pair = pmap (inst tmp) pair in
             let rsl = fst_map (inst tmp) rsl in
             pair,rsl,(tyins,tmins)
         with Failure "type_unify" -> failwith "init_data"

  (* test whether the head symbol is a free variable of a term
   * DONE CHECKING
   *)
  let head_free const_var (tm : term) : bool =
    let bvars,tm = get_bound tm in
    let hsym = repeat rator tm in
    let name = name_of hsym in
    not (is_const hsym) && not (mem hsym bvars) && not (mem name const_var) && not (has_prefix name "mc")

  let vcounter = ref 0
  let new_vname() =
   (vcounter := !vcounter + 1;
    "z" ^ (string_of_int !vcounter))

  let imitate fv c =
    let tyl1 = fst (dest_fun (type_of fv)) and tyl2,apx2 = dest_fun (type_of c) in
    let bvars = map (fun ty -> mk_var(new_vname(),ty)) tyl1 in
    let args = map (fun ty -> mk_lcomb (mk_var(new_vname(),mk_fun(tyl1,ty))) bvars) tyl2 in
    mk_term bvars (mk_lcomb c args),fv

  (* fv:A1->A2->A3->A4->apex and idx = 2
   * fv := \u1 u2 u3 u4. fv u1 u3 u4
   *)
  let eliminate fv idx =
    let rec remove lst idx =
      match lst with
        h::t -> if idx = 0 then t
                else h::(remove t (idx-1))
      | [] -> [] in
    let tyl,apx = dest_fun (type_of fv) in
    let bvars = List.mapi (fun i ty -> let name = "u" ^ (string_of_int (i+1)) in
                                       if name <> name_of fv then mk_var(name,ty)
                                       else mk_var(name ^ "'",ty)) tyl in
    let new_ty = mk_fun(remove tyl idx,apx) in
    mk_term bvars (mk_lcomb (mk_var(name_of fv,new_ty)) (remove bvars idx)),fv

  (* the type of every pairs in pairs must be matched
   * the input might not be in normal forms
   *)
  let simplify const_ty const_var =
    let is_free_var = function (Var(name,_)) -> not (mem name const_var) && not (has_prefix name "mc")
                              | _ -> false in

    (*
     * Strip off the binder \x where x does not occur in both terms
     * Then do eta-conversion to the remaining part, since bound-vars stripping
     * may generate new eta-redex
     * DONE CHECKING
     *)
    let rec bound_eta_norm (tm1,tm2) : term * term =
      match tm1,tm2 with
        Abs(bv1,bod1),Abs(bv2,bod2) ->
          let bod1,bod2 = bound_eta_norm (bod1,bod2) in
          if not (vfree_in bv1 bod1) && not (vfree_in bv2 bod2) then bod1,bod2
          else (try let f1,x1 = dest_comb bod1 in
                    if Pervasives.compare bv1 x1 = 0 && not (vfree_in bv1 f1) then f1
                    else mk_abs(bv1,bod1)
                with Failure _ -> mk_abs(bv1,bod1)),
               (try let f2,x2 = dest_comb bod2 in
                    if Pervasives.compare bv2 x2 = 0 && not (vfree_in bv2 f2) then f2
                    else mk_abs(bv2,bod2)
                with Failure _ -> mk_abs(bv2,bod2))
      | _ -> tm1,tm2 in

    (* remove unused bvars *)
    let rec remove_dummy_bvar tm =
      match tm with
        Abs(bv,bod) ->
          let bod = remove_dummy_bvar bod in
          if not (vfree_in bv bod) then bod
          else (try let f,x = dest_comb bod in
                    if Pervasives.compare bv x = 0 && not (vfree_in bv f) then f
                    else mk_abs(bv,bod)
                with Failure _ -> mk_abs(bv,bod))
      | _ -> tm in

    (* try to check rigid-rigid pairs
     * if rigid head not match then raise exception
     * else return type of pairs of const if type not match
     * DONE CHECKING
     *)
    let rec check_rr (pairs : (term * term) list) : (hol_type * hol_type) list =
      match pairs with
        (tm1,tm2)::t -> let bv1,(hs1,_) = decompose tm1 and bv2,(hs2,_) = decompose tm2 in
                        let bin1 = bindex hs1 bv1 and bin2 = bindex hs2 bv2 in
                        let rigid1 = is_const hs1 || bin1 >= 0 || (mem (name_of hs1) const_var) || (has_prefix (name_of hs1) "mc") in
                        let rigid2 = is_const hs2 || bin2 >= 0 || (mem (name_of hs2) const_var) || (has_prefix (name_of hs2) "mc") in
                        if rigid1 && rigid2 then
                          if bin1 < 0 && bin2 < 0 then
                            (* constant or const_var *)
                            if is_const hs1 then
                              if is_const hs2 then
                                if name_of hs1 <> name_of hs2 then failwith "check_rr"
                                else (type_of hs1,type_of hs2)::(check_rr t)
                              else failwith "check_rr"
                            else if Pervasives.compare hs1 hs2 <> 0 then failwith "check_rr"
                                 else check_rr t
                          else if bin1 <> bin2 then failwith "check_rr"
                               else check_rr t
                        else check_rr t
      | [] -> [] in

    (* pairs and tmins must be in bete-eta normal form
     * since domain and codomain of substitution may have the overlap namespace
     * so we use safe_tmins here
     *)
    (* TODO buggy: add const_ty and const_var check *)
    let rec work pairs rsl (tyins,tmins) =
      (* Normalization
       * TODO: don't normalize in every loop, too expensive
       *)
      let pairs = pmap beta_eta_term pairs in
      let pairs = map bound_eta_norm pairs in
      let rsl = fst_map beta_eta_term rsl in
      let rsl = fst_map remove_dummy_bvar rsl in
      let rsl = List.sort_uniq Pervasives.compare rsl in
      (*
      List.iter (fun (u,v) -> Printf.printf "2\t%s\t%s\n%!" (ss_term u) (ss_term v)) pairs;
      List.iter (fun (u,v) -> Printf.printf "3\t%s\t%s\n%!" (ss_term u) v) rsl;
      print_endline "";
      *)
      (* Delete rule *)
      let pairs = filter (fun (u,v) -> alphaorder u v <> 0) pairs in
      (* Bind rule *)
      try let (fv,tm),pairs = try pop (fun (u,v) -> is_free_var u && not (vfree_in u v)) pairs
                              with Failure "pop" ->
                                let (tm,fv),pairs = pop (fun (u,v) -> is_free_var v && not (vfree_in v u)) pairs in
                                (fv,tm),pairs in
          let tmins = safe_tmins (tm,fv) tmins in
          work (pmap (vsubst [tm,fv]) pairs) (fst_map (vsubst [tm,fv]) rsl) (tyins,tmins)
      with Failure "pop" -> 
      (* Decompose rule *)
      try let tmp_ins = type_unify const_ty (check_rr pairs) in
          if length tmp_ins > 0 then
            let tyins = itlist insert_tyins tmp_ins tyins in
            let tmins = pmap (inst tmp_ins) tmins in
            work (pmap (inst tmp_ins) pairs) (fst_map (inst tmp_ins) rsl) (tyins,tmins) else
          (* step S: match one rigid-rigid pair *)
          try let (tm1,tm2),pairs = pop (fun (u,v) -> not (head_free const_var u) && not (head_free const_var v)) pairs in
              let tm1 = eta_expand tm1 and tm2 = eta_expand tm2 in
              let bv1,(_,args1) = decompose tm1 and bv2,(_,args2) = decompose tm2 in
              let pairs = itlist2 (fun u1 u2 t -> (mk_term bv1 u1,mk_term bv2 u2)::t) args1 args2 pairs in
              work pairs rsl (tyins,tmins)
          with Failure "pop" ->
          (* detect the case when x and (a = x) = y which is impossible to unify
           * check whether tm1 is a sub-term of equality tree of tm2
           * x,(\u. w) = (\u. x)
           * x,\u v. x v = x v
           * general rules
           * tm1 = \u1 ... un. x {bvars} {mc} (x can't create (=) as head symbol without explicitly imitate it
           * tm2 = \u1 ... un. (=) () ... (() ... (x...) ... ()) and have x as a head symbol as bound scope
           *)
          let sub_term tm1 tm2 =
            let rec work env fv tm =
              match tm with
                Abs(bvar,bod) -> work (bvar::env) fv bod
              | _ -> let _,(hs,args) = decompose tm in
                     if is_const hs || has_prefix (name_of hs) "mc" || mem hs env || mem (name_of hs) const_var then
                       exists (work env fv) args
                     else Pervasives.compare fv hs = 0 in

            if head_free const_var tm1 then
              let bvs1,(hs1,args1) = decompose tm1 and bvs2,(hs2,args2) = decompose tm2 in
              if is_const hs2 && (name_of hs2) = "=" && 
                 forall (fun arg -> is_var arg && (has_prefix (name_of arg) "mc" || mem arg bvs1)) args1 then
                work [] hs1 tm2
              else false
            else false in

          if exists (fun (u,v) -> sub_term u v || sub_term v u) pairs then failwith "work" else
          (* dealing with rsl *)
          (* rigid head decomposition *)
          try let (tm,name),rsl = pop (fun (tm,_) -> not (head_free const_var tm)) rsl in
              let bvs,(hs,args) = decompose tm in
              if is_var hs && not (mem hs bvs) && has_prefix (name_of hs) name then failwith "work"
              else let rsl = itlist (fun arg t -> (mk_term bvs arg,name)::t) args rsl in
                   work pairs rsl (tyins,tmins)
          with Failure "pop" ->
          (* x mc/mc, x := \u. y u *)
          let cond1 (tm,mc) =
            try let f,x = dest_comb tm in
                is_var x && name_of x = mc
            with Failure _ -> false in
          try let (tm,mc),rsl = pop cond1 rsl in
              let fv = rator tm in
              let tya,tyb = dest_fun_ty (type_of fv) in
              let bvar = if name_of fv = "u" then mk_var("v",tya) else mk_var("u",tya) in
              let tm = mk_abs(bvar,mk_var(name_of fv,tyb)) in
              let tmins = safe_tmins (tm,fv) tmins in
              work (pmap (vsubst [tm,fv]) pairs) (fst_map (vsubst [tm,fv]) rsl) (tyins,tmins)
          with Failure "pop" ->
          (* x mc and y mc, x/mc, y/mc  y := x
           * no need to check whether x and y are free
           *)
          let cond2 (tm1,tm2) =
            try let f1,x1 = dest_comb tm1 and f2,x2 = dest_comb tm2 in
                if is_var f1 && is_var x1 && is_var f2 && is_var x2 && (name_of x1) = (name_of x2) then
                  let name = name_of x1 in
                  has_prefix name "mc" && mem (f1,name) rsl && mem (f2,name) rsl
                else false
            with Failure _ -> false in
          try let (tm1,tm2),pairs = pop cond2 pairs in
              let f1 = rator tm1 and f2 = rator tm2 in
              let tmins = safe_tmins (f1,f2) tmins in
              work (pmap (vsubst [f1,f2]) pairs) (fst_map (vsubst [f1,f2]) rsl) (tyins,tmins)
          with Failure "pop" ->
          (* imitation x mc and (=) u v
           * no need to check whether x is free
           * NOTE some other cases found in do_it [assume;refl] 5
           * \u. x and \u. y mc u = y mc u
           * general case formalization
           * \u1 u2 ... un. x {ui} {mc} and \u1 u2 ... un. (=) () ... ()
           *)
          let cond3 (tm1,tm2) =
            if head_free const_var tm1 then
              let bvs1,(_,args1) = decompose tm1 and _,(hs2,_) = decompose tm2 in
              forall (fun arg -> is_var arg && (has_prefix (name_of arg) "mc" || mem arg bvs1)) args1 &&
              is_const hs2 && (name_of hs2) = "="
            else false in
          try let tm1,tm2 = try find cond3 pairs
                            with Failure "find" ->
                              let tm2,tm1 = find (fun (v,u) -> cond3 (u,v)) pairs in
                              tm1,tm2 in
              let _,(f,_) = decompose tm1 in
              let _,(hsym,_) = decompose tm2 in
                let iv = imitate f hsym in
                let tmins = safe_tmins iv tmins in
                work (pmap (vsubst [iv]) pairs) (fst_map (vsubst [iv]) rsl) (tyins,tmins)
          with Failure "find" ->
          (* [y mc,\u. x]
           * [y mc,\u. x mc]
           * in long-term normal form, if there exists a bound variable bb that
           * is not contained in the body of tm2, and bb is contained in tm1 and all
           * args of tm1 are wither a single bvar or mc
           *)
          let cond4 (tm1,tm2) =
            if head_free const_var tm1 then
              (* by de bruijn index we guarantee bvars of tm1 tm2 have same names *)
              let tm1,tm2 = eta_expand tm1,eta_expand tm2 in
              let bvs1,bod1 = get_bound tm1 and bvs2,bod2 = get_bound tm2 in
              (* check whether args of bod1 are either single bvar or mc *)
              let hs,args = strip_comb bod1 in
              if forall (fun arg -> is_var arg && (has_prefix (name_of arg) "mc" || mem arg bvs1)) args then
                exists (fun arg -> not (has_prefix (name_of arg) "mc") && not (vfree_in arg bod2)) args
              else false
            else false in
          try let tm1,tm2 = try find cond4 pairs
                            with Failure "find" -> let tm2,tm1 = find (fun (v,u) -> cond4 (u,v)) pairs in
                                                   tm1,tm2 in
              let tm1,tm2 = eta_expand tm1,eta_expand tm2 in
              let bvs1,bod1 = get_bound tm1 and bvs2,bod2 = get_bound tm2 in
              (* check whether args of bod1 are either single bvar or mc *)
              let hs,args = strip_comb bod1 in
              let idx = find (fun i -> let arg = el i args in
                                       not (has_prefix (name_of arg) "mc") && not (vfree_in arg bod2)) (0--((length args)-1)) in
              let it = eliminate hs idx in
              let tmins = safe_tmins it tmins in
              work (pmap (vsubst [it]) pairs) (fst_map (vsubst [it]) rsl) (tyins,tmins)
          with Failure "find" ->
            pairs,rsl,(tyins,tmins)
      with Failure s when s = "check_rr" || s = "type_unify" -> failwith "work" in

    fun pairs rsl ->
      try work pairs rsl ([],[])
      with Failure "work" -> failwith "simplify"

  let is_correct const_ty const_var pairs rsl ((tyins,tmins) as ins) =
    let rec mc_free_in name env tm =
      match tm with
        Comb(f,x)  -> mc_free_in name env f || mc_free_in name env x
      | Abs(v,bod) -> mc_free_in name (v::env) bod
      | Var(n,_)   -> not (mem tm env) && n = name
      | Const(_,_) -> false in

    if exists (fun (_,v) -> mem (name_of v) const_var) tmins then false
    else if exists (fun (_,t) -> mem (dest_vartype t) const_ty) tyins then false
    else if exists (fun (tm1,tm2) -> alphaorder (beta_eta_term (inst_term ins tm1))
                                                (beta_eta_term (inst_term ins tm2)) <> 0) pairs then false
    else if exists (fun (tm,name) -> mc_free_in name [] tm) rsl then false
    else true

  let max_poly = ref 1

  let hol_unify (const_ty : string list) (const_var : string list) =
    let tcounter = ref 0 in
    let new_tname() =
     (tcounter := !tcounter + 1;
      "Z" ^ (string_of_int !tcounter)) in

    let history = ref ([] : ((term * term) list * (term * string) list) list) in

    let rec type_match vty cty sofar =
      if is_vartype vty && not (mem (dest_vartype vty) const_ty) then
         try if Pervasives.compare (rev_assoc vty sofar) cty = 0 then sofar
             else failwith "type_match"
         with Failure "find" -> (cty,vty)::sofar
      else if is_type vty && is_type cty then
         let vop,vargs = dest_type vty and cop,cargs = dest_type cty in
         if vop = cop then itlist2 type_match vargs cargs sofar
         else failwith "type_match"
      else if Pervasives.compare vty cty = 0 then sofar
           else failwith "type_match" in

    (* try to instantiate tm1 that match tm2 *)
    let rec hol_match env1 env2 tm1 tm2 (tyins,tmins) =
      match tm1,tm2 with
        Comb(f1,x1),Comb(f2,x2) -> hol_match env1 env2 x1 x2 (hol_match env1 env2 f1 f2 (tyins,tmins))
      | Abs(v1,bod1),Abs(v2,bod2) -> (try let tyins = type_match (type_of v1) (type_of v2) tyins in
                                          hol_match (v1::env1) (v2::env2) bod1 bod2 (tyins,tmins)
                                      with Failure "type_match" -> failwith "hol_match")
      | Var(n1,ty1),_ -> let idx1 = safe_index tm1 env1 in
                         if idx1 >= 0 then if is_var tm2 && safe_index tm2 env2 = idx1 then tyins,tmins
                                           else failwith "hol_match"
                         else (
                           try let tyins = type_match ty1 (type_of tm2) tyins in
                               if not (mem n1 const_var) && not (has_prefix n1 "mc") then
                                 if exists (fun v -> vfree_in v tm2) env2 then failwith "hol_match"
                                 else try if Pervasives.compare (rev_assoc tm1 tmins) tm2 = 0 then tyins,tmins
                                          else failwith "hol_match"
                                      with Failure "find" -> tyins,(tm2,tm1)::tmins
                               else if is_var tm2 && (name_of tm1) = (name_of tm2) then tyins,tmins
                                    else failwith "hol_match"
                           with Failure "type_match" -> failwith "hol_match")
      | Const(n1,t1),Const(n2,t2) -> if n1 = n2 then (
                                       try let tyins = type_match t1 t2 tyins in tyins,tmins
                                       with Failure "type_match" -> failwith "hol_match")
                                     else failwith "hol_match"
      | _ -> failwith "hol_match" in


    (* Whether task1 can be instantiated to task2
     * This is a pretty naive duplication check
     *)
    let task_match (pairs1,rsl1) (pairs2,rsl2) =
      if length pairs1 <> length pairs2 || length rsl1 <> length rsl2 then false
      else try let ins = itlist2 (fun (tm1,tm1') (tm2,tm2') ins ->
                           hol_match [] [] tm1' tm2' (hol_match [] [] tm1 tm2 ins))
                           pairs1 pairs2 ([],[]) in
               let _ = itlist2 (fun (tm1,name1) (tm2,name2) ins ->
                         if name1 <> name2 then failwith "hol_match"
                         else hol_match [] [] tm1 tm2 ins)
                         rsl1 rsl2 ins in
               true
               (*
               (print_endline "duplicate";
                List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) (ss_term v)) pairs1;
                List.iter (fun (u,v) -> Printf.printf "1\t%s\t%s\n%!" (ss_term u) v) rsl1;
                List.iter (fun (u,v) -> Printf.printf "2\t%s\t%s\n%!" (ss_term u) (ss_term v)) pairs2;
                List.iter (fun (u,v) -> Printf.printf "3\t%s\t%s\n%!" (ss_term u) v) rsl2;
                print_endline "";
                true)
               *)
           with Failure "hol_match" -> false in

    let is_duplicate task = exists (fun his -> task_match his task) !history in

    (* range(fv) and range(fv.k) should be the same *)
    let project fv k =
      let tyl1,apx1 = dest_fun (type_of fv) in
      let bvars = map (fun ty -> mk_var(new_vname(),ty)) tyl1 in
      let pvar = el k bvars in
      let tyl2,apx2 = dest_fun (type_of pvar) in
      try let tyins = type_unify const_ty [apx1,apx2] in
          let args = map (fun ty -> mk_lcomb (mk_var(new_vname(),mk_fun(tyl1,ty))) bvars) tyl2 in
          let tm = mk_term bvars (mk_lcomb pvar args) in
          tyins,(inst tyins tm,inst tyins fv)
      with Failure "type_unify" -> failwith "project" in

    (* each pair of pairs must have matched type *)
    let rec work dep pairs rsl (tyins,tmins) sofar : (instor list) =
      (* simplification *)
      try let pairs,rsl,ins = simplify const_ty const_var pairs rsl in
          if exists (fun (a,b) -> (tm_size a) >= 50 || (tm_size b) >= 50) pairs then sofar else
          if exists (fun (a,b) -> (tm_size a) >= 10) tmins then sofar else (
          (*
          if is_duplicate (pairs,rsl) then sofar else (
          history := (pairs,rsl)::(!history);
          *)
          let tyins,tmins = merge_ins (tyins,tmins) ins in
          (*
          Printf.printf "%d\n%!" dep;
          List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) (ss_term v)) pairs;
          List.iter (fun (u,v) -> Printf.printf "1\t%s\t%s\n%!" (ss_term u) v) rsl;
          List.iter (fun (u,v) -> Printf.printf "2\t%s\t%s\n%!" (string_of_type u) (string_of_type v)) tyins;
          print_endline "";
          *)
          try let tm1,tm2 = try find (fun (u,v) -> not (head_free const_var v)) pairs
                            with Failure "find" ->
                              let tm2,tm1 = find (fun (u,v) -> not (head_free const_var u)) pairs in
                              tm1,tm2 in
              let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
              (* step I: imitation *)
              let sofar =
                if is_const hs2 || (mem (name_of hs2) const_var) || (has_prefix (name_of hs2) "mc") then
                  let apex = snd (dest_fun (type_of hs2)) in
                  if is_type apex || mem (dest_vartype apex) const_ty then
                    (* don't need to do type instantiation *)
                    let iv = imitate hs1 hs2 in
                    let tmins = update_tmins iv tmins in
                    work (dep+1) (pmap (vsubst [iv]) pairs) (fst_map (vsubst [iv]) rsl) (tyins,tmins) sofar
                  else (
                    (* instantiate a polymorphic type...... *)
                    rev_itlist (fun n sofar ->
                      let new_tyl = map (fun _ -> mk_vartype(new_tname())) (0--n) in
                      let tyl = tl new_tyl and apx = hd new_tyl in
                      let it = mk_fun(tyl,apx),apex in
                      let iv = imitate (inst [it] hs1) (inst [it] hs2) in
                      let tyins' = update_tyins it tyins in
                      let tmins' = update_tmins iv (pmap (inst [it]) tmins) in
                      work (dep+1) (pmap (inst_term ([it],[iv])) pairs) (fst_map (inst_term ([it],[iv])) rsl) (tyins',tmins') sofar
                  ) (0--(!max_poly)) sofar)
                else sofar in
              (* step T_P and P: projection *)
              (* the apex of fv is fixed *)
              let head_fix fv its sofar =
                let tyl1 = fst (dest_fun (type_of fv)) in
                let noname (k : int) sofar =
                  let pty = el k tyl1 in
                  let apx2 = snd (dest_fun pty) in
                  if is_type apx2 || mem (dest_vartype apx2) const_ty then
                    try let its',iv = project fv k in
                        let its = itlist insert_tyins its' its in
                        let tyins' = itlist update_tyins its tyins in
                        let tmins' = update_tmins iv (pmap (inst its) tmins) in
                        work (dep+1) (pmap (inst_term (its,[iv])) pairs) (fst_map (inst_term (its,[iv])) rsl) (tyins',tmins') sofar
                    with Failure "project" -> sofar
                  else (
                    rev_itlist (fun n sofar ->
                      let new_tyl = map (fun _ -> mk_vartype(new_tname())) (0--n) in
                      let tyl = tl new_tyl and apx = hd new_tyl in
                      let it = mk_fun(tyl,apx),apx2 in
                      let its = insert_tyins it its in
                      let its',iv = project (inst [it] fv) k in
                      let its = itlist insert_tyins its' its in
                      let tyins' = itlist update_tyins its tyins in
                      let tmins' = update_tmins iv (pmap (inst its) tmins) in
                      work (dep+1) (pmap (inst_term (its,[iv])) pairs) (fst_map (inst_term (its,[iv])) rsl) (tyins',tmins') sofar
                    ) (0--(!max_poly)) sofar) in
                itlist noname (0--((length tyl1)-1)) sofar in
              let apex = snd (dest_fun (type_of hs1)) in
              if is_type apex || mem (dest_vartype apex) const_ty then head_fix hs1 [] sofar
              else (
                rev_itlist (fun n sofar ->
                  let new_tyl = map (fun _ -> mk_vartype(new_tname())) (0--n) in
                  let tyl = tl new_tyl and apx = hd new_tyl in
                  let it = mk_fun(tyl,apx),apex in
                  head_fix (inst [it] hs1) [it] sofar
                ) (0--(!max_poly)) sofar)
          with Failure "find" -> (
            let tml = (let ps1,ps2 = unzip pairs in ps1 @ ps2) @ (let sl,_ = unzip rsl in sl) in
            let fvars = filter (fun v -> not (has_prefix (name_of v) "mc")) (freesl tml) in
            let constantize v =
              let tyl,apex = dest_fun (type_of v) in
              let bvs = List.mapi (fun i ty -> mk_var("u" ^ (string_of_int i),ty)) tyl in
              let hs = mk_var("z",apex) in
              mk_term bvs hs in
            let tmins = itlist (fun v tmins -> update_tmins (constantize v,v) tmins) fvars tmins in
            (tyins,tmins)::sofar))
      with Failure "simplify" -> sofar in

    fun (pairs : (term * term) list) (rsl : (term * string) list) ->
      try let pairs,rsl,ins = init_data const_ty const_var pairs rsl in
          (try let pairs',rsl',ins' = simplify const_ty const_var pairs rsl in
               List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) (ss_term v)) pairs';
               List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (ss_term u) v) rsl';
               print_endline ""
           with Failure _ -> ());
          let sofar = work 0 pairs rsl ins [] in
          if forall (fun ins -> is_correct const_ty const_var pairs rsl ins) sofar then sofar
          else failwith "hol_unify[fatal]: produce incorrect instor"
      with Failure "init_data" -> []

  let hol_quick_check pairs rsl =
    try let pairs,rsl,ins = init_data [] [] pairs rsl in
        (ignore (simplify [] [] pairs rsl); true)
    with Failure s when s = "init_data" || s = "simplify" -> false

end;;

include Hunify;;
