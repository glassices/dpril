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
  mk_term bvars (mk_lcomb (mk_var(name_of fv,new_ty)) (remove bvars idx)),fv;;
