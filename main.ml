needs "dpril/rthm.ml";;

let refl() = mk_rthm(REFL `x:A`);;

let assume() = mk_rthm(ASSUME `x:bool`);;

let t_def() = mk_rthm(T_DEF);;

let and_def() = mk_rthm(AND_DEF);;

let hrth = ref (mk_rthm(T_DEF));;

let lsym() = 
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(ASSUME `x:bool`) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  r4,rmatch r4 ([`(p:A)=q`],`(q:A)=p`);;

let lsym'() = 
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(ASSUME `x:bool`) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  r4,rmatch r4 ([`(p:A)=q`],`(\(u:B). (q:A)) = (\(u:B). p)`);;

let lsym''() = 
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(ASSUME `x:bool`) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  let r5 = rabs r4 in
  r5,rmatch r5 ([`(p:A)=q`],`(\(u:B). (q:A)) = (\(u:B). p)`);;

let ltruth() =
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(T_DEF) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  let r5 = rabs (mk_rthm(REFL `x:A`)) in
  let r6 = req_mp r4 r5 in
  r6,rmatch r6 ([],`T`);;

let land_elim() =
  reset_rcount();
  let r5 = rmk_comb (refl()) (mk_rthm(T_DEF)) in
  let r6 = req_mp r5 (refl()) in
  let r7 = req_mp r6 (refl()) in
  let r93 = rmk_comb (mk_rthm(AND_DEF)) (refl()) in
  let r100 = rmk_comb r93 (refl()) in
  let r107 = req_mp r100 (assume()) in
  let r109 = rmk_comb r107 (refl()) in
  let r136 = rmk_comb (refl()) r109 in
  let r137 = rmk_comb r136 (refl()) in
  let r138 = req_mp r137 (refl()) in
  let r139 = req_mp r138 r7 in
  r139,rmatch r139 ([`p /\ q`],`p:bool`);;

let land_intro() =
  reset_rcount();
  let r7() =
    let r4 = rmk_comb (mk_rthm(REFL `x:A`)) (mk_rthm(T_DEF)) in
    let r5 = rmk_comb r4 (mk_rthm(REFL `x:A`)) in
    let r6 = req_mp r5 (mk_rthm(REFL `x:A`)) in
    req_mp r6 (mk_rthm(REFL `x:A`)) in

  let r68() =
    let r9 = rdeduct (mk_rthm(ASSUME `x:bool`)) (r7()) 0 0 in
    let r13 = rmk_comb (mk_rthm(REFL `x:A`)) (mk_rthm(ASSUME `x:bool`)) in
    let r14 = rmk_comb r13 (mk_rthm(REFL `x:A`)) in
    let r15 = req_mp r14 (mk_rthm(REFL `x:A`)) in
    let r16 = req_mp r15 (r7()) in
    let r17 = rdeduct r16 r9 1 1 in
    req_mp r17 (mk_rthm(ASSUME `x:bool`)) in

  let r70 = rmk_comb (mk_rthm(REFL `x:A`)) (r68()) in
  let r71 = rmk_comb r70 (r68()) in
  let r74 = rmk_comb (mk_rthm(AND_DEF)) (mk_rthm(REFL `x:A`)) in
  let r76 = rmk_comb r74 (mk_rthm(REFL `x:A`)) in
  let r87 = rmk_comb (mk_rthm(REFL `x:A`)) r76 in
  let r88 = rmk_comb r87 (mk_rthm(REFL `x:A`)) in
  let r89 = req_mp r88 (mk_rthm(REFL `x:A`)) in
  let r90 = req_mp r89 (rabs r71) in
  r90,rmatch r90 ([`p:bool`;`q:bool`],`p /\ q`);;


let search goal axioms max_dep =
  let count = ref 0 in

  let rec work n_rem lst =
    if n_rem + 1 < (length lst) then None
    else if n_rem = 0 then
      let rth = hd lst in
      count := !count + 1;
      if !count mod 10000 = 0 then printf "%d\n%!" !count else ();
      (*
      try (print_endline (string_of_rthm rth); let _,th = rmatch rth goal in Some(th))
      *)
      hrth := rth;
      try let _,th = rmatch rth goal in Some(th)
      with Failure "rmatch" -> None
    else (
      (* add new axioms *)
      let rec traverse axioms =
        match axioms with
          h::t -> let res = work n_rem ((h())::lst) in
                  if res <> None then res else traverse t
        | [] -> None in
      let res = traverse axioms in
      if res <> None then res else
      (* eq_mp *)
      let res = if length lst >= 2 then
                  let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
                  try let rth = req_mp h2 h1 in
                      work (n_rem-1) (rth::t)
                  with Failure "distill" -> None
                else None in
      if res <> None then res else
      (* mk_comb *)
      let res = if length lst >= 2 then
                  let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
                  try let rth = rmk_comb h2 h1 in
                      work (n_rem-1) (rth::t)
                  with Failure "distill" -> None
                else None in
      if res <> None then res else
      (* trans *)
      let res = if length lst >= 2 then
                  let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
                  try let rth = rtrans h2 h1 in
                      work (n_rem-1) (rth::t)
                  with Failure "distill" -> None
                else None in
      if res <> None then res else
      (* abs *)
      let res = if length lst >= 1 then
                  let h,t = hd lst,tl lst in
                  try let rth = rabs h in
                      work (n_rem-1) (rth::t)
                  with Failure "distill" -> None
                else None in
      if res <> None then res else
      (* deduct *)
      let res = if length lst >= 2 then
                  let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
                  let n2 = length (rhyp h2) and n1 = length (rhyp h1) in
                  itlist (fun v res -> if res <> None then res else
                                       let v2 = (lsr) v n1 and v1 = (land) v (((lsl) 1 n1)-1) in
                                       try let rth = rdeduct h2 h1 v2 v1 in
                                           work (n_rem-1) (rth::t)
                                       with Failure "distill" -> None)
                         (0--(((lsl) 1 (n2+n1))-1)) None
                else None in
      res
    ) in

  work max_dep [];;

let falsify goal axioms max_dep =
  let valid = ref 0 in
  let count = ref 0 in
  let oc = open_out "out" in

  let rec work n_rem lst : unit =
    if n_rem + 1 < (length lst) then ()
    else if n_rem = 0 then
      let rth = hd lst in
      count := !count + 1;
      if !count mod 10000 = 0 then printf "%d\n%!" !count else ();
      let asl,c,pairs,rsl = dest_rthm rth and asl',c' = goal in
      let fvars = freesl (c'::asl') and ftys = itlist (union o type_vars_in_term) (c'::asl') [] in
      let const_var = List.sort_uniq Pervasives.compare (map name_of fvars) in
      let const_ty = List.sort_uniq Pervasives.compare (map dest_vartype ftys) in
      let rec work csl csl' pairs =
        match csl with
          h::t -> (match csl' with
                     h'::t' -> (work t asl' ((h,h')::pairs);
                                work csl t' pairs)
                   | [] -> ())
        | [] -> try let pairs,rsl,_ = simplify const_ty const_var pairs rsl in
                    let fvars = freesl (let tmp1,tmp2 = unzip pairs in tmp1 @ tmp2) in
                    let max_ord = itlist (fun tm x -> max (ord_of_term tm) x) fvars 0 in
                    valid := !valid + 1;
                    Printf.fprintf oc "count:%d\tord:%d\n%!" !valid max_ord;
                    Printf.fprintf oc "%s\n%!" (string_of_rthm rth);
                    List.iter (fun (u,v) -> Printf.fprintf oc "0\t%s\t%s\n%!" (ss_term u) (ss_term v)) pairs;
                    List.iter (fun (u,v) -> Printf.fprintf oc "1\t%s\t%s\n%!" (ss_term u) v) rsl;
                    Printf.fprintf oc "\n%!"
                with Failure "simplify" -> () in
      work asl asl' ((c,c')::pairs)
    else (
      (* add new axioms *)
      let rec traverse axioms =
        match axioms with
          h::t -> work n_rem ((h())::lst); traverse t
        | [] -> () in
      traverse axioms;
      (* eq_mp *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        try let rth = req_mp h2 h1 in
            work (n_rem-1) (rth::t)
        with Failure "distill" -> ()
      else ();
      (* mk_comb *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        try let rth = rmk_comb h2 h1 in
            work (n_rem-1) (rth::t)
        with Failure "distill" -> ()
      else ();
      (* trans *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        try let rth = rtrans h2 h1 in
            work (n_rem-1) (rth::t)
        with Failure "distill" -> ()
      else ();
      (* abs *)
      if length lst >= 1 then
        let h,t = hd lst,tl lst in
        try let rth = rabs h in
            work (n_rem-1) (rth::t)
        with Failure "distill" -> ()
      else ();
      (* deduct *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        let n2 = length (rhyp h2) and n1 = length (rhyp h1) in
        do_list (fun v -> let v2 = (lsr) v n1 and v1 = (land) v (((lsl) 1 n1)-1) in
                          try let rth = rdeduct h2 h1 v2 v1 in
                              work (n_rem-1) (rth::t)
                          with Failure "distill" -> ())
                (0--(((lsl) 1 (n2+n1))-1))
      else ()
    ) in

  work max_dep [];
  close_out oc;;

(* no aim, just try different trees *)
let doit axioms max_dep least_abs =
  let valid = ref 0 in
  let count = ref 0 in

  let rec work n_rem n_abs lst : unit =
    if n_rem-n_abs+1 < (length lst) then ()
    else if n_rem = 0 then
      let rth = hd lst in
      count := !count + 1;
      if !count mod 10000 = 0 then printf "%d\n%!" !count else ();
      let s = string_of_rthm rth in
      try let lt = String.index s '[' in
          let rt = String.index s ']' in
          let ss = String.sub s lt (rt-lt+1) in
          if exists (fun i -> (String.sub ss i 2) = "mc") (0--((String.length ss)-2)) then
            print_endline s
          else ()
      with Not_found -> ()
    else (
      (* add new axioms *)
      let rec traverse axioms =
        match axioms with
          h::t -> work n_rem n_abs ((h())::lst); traverse t
        | [] -> () in
      traverse axioms;
      (* eq_mp *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        try let rth = req_mp h2 h1 in
            work (n_rem-1) n_abs (rth::t)
        with Failure "distill" -> ()
      else ();
      (* mk_comb *)
      (*
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        try let rth = rmk_comb h2 h1 in
            work (n_rem-1) n_abs (rth::t)
        with Failure "distill" -> ()
      else ();
      *)
      (* trans *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        try let rth = rtrans h2 h1 in
            work (n_rem-1) n_abs (rth::t)
        with Failure "distill" -> ()
      else ();
      (* abs *)
      if length lst >= 1 then
        let h,t = hd lst,tl lst in
        try let rth = rabs h in
            work (n_rem-1) (n_abs-1) (rth::t)
        with Failure "distill" -> ()
      else ();
      (* deduct *)
      if length lst >= 2 then
        let h1,h2,t = hd lst,hd (tl lst),tl (tl lst) in
        let n2 = length (rhyp h2) and n1 = length (rhyp h1) in
        do_list (fun v -> let v2 = (lsr) v n1 and v1 = (land) v (((lsl) 1 n1)-1) in
                          try let rth = rdeduct h2 h1 v2 v1 in
                              work (n_rem-1) n_abs (rth::t)
                          with Failure "distill" -> ())
                (0--(((lsl) 1 (n2+n1))-1))
      else ()
    ) in

  work max_dep least_abs [];;

(* limit=20, minimum n = 3 *)
let task1 n =
  let axioms = [refl;assume;(fun () -> mk_rthm(T_DEF))] in
  search ([],`T`) axioms n;;

(* limit=20, minimum n = 2 *)
let task2 n =
  let axioms = [refl;assume] in
  search ([`(p:A)=(q:A)`],`(q:A)=(p:A)`) axioms n;;

(* 12 in humans' proof *)
(* limit=20, *)
let task3 n =
  let axioms = [refl;assume;(fun () -> mk_rthm(T_DEF));(fun () -> mk_rthm(AND_DEF))] in
  search ([`p /\ q`],`p:bool`) axioms n;;

let task4 n =
  let axioms = [refl;assume;(fun () -> mk_rthm(T_DEF))] in
  search ([],`(T = ((p = T) = T)) = (T = p)`) axioms n;;

(* limit=20, n = 4, 450000 steps *)
let task5 n =
  let axioms = [refl;assume;(fun () -> mk_rthm(T_DEF))] in
  search ([`p:bool`],`p = T`) axioms n;;

(* amazing n = 2, limit = 20 proof
 * using TRANS rule
 * minumum n = 3 without TRANS, which is also amazing
 *)
let task6 n =
  let axioms = [refl;assume;(fun () -> mk_rthm(T_DEF))] in
  search ([`p:bool`],`T = p`) axioms n;;

let task7 n =
  let axioms = [refl;assume;(fun () -> mk_rthm(T_DEF));(fun () -> mk_rthm(AND_DEF))] in
  falsify ([],`p:bool`) axioms n;;

let unify1() =
  hol_unify [] ["p"] [`(x4:bool->bool) mc`,`(x5:bool->bool) mc`;`(x3:(bool->bool)->bool) x4`,concl T_DEF;`(x3:(bool->bool)->bool) x5`,`p:bool`]
  [`(x4:bool->bool)`,"mc";`(x5:bool->bool)`,"mc"];;

let unify2() =
  hol_unify [] [] [`(x:q->bool) (y:q)`,`(z:e)=z`;`(x:q->bool) (y:q)`,`T`] [];;
