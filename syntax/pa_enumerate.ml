open StdLabels

open Camlp4
open PreCast
open Ast
open Pa_type_conv

module List = struct
  include List

  (* All functions copied from core_list.ml (except for [invalid_argf], which is copied
     from core_printf.ml. *)
  let invalid_argf fmt = Printf.ksprintf (fun s () -> invalid_arg s) fmt

  let init n ~f =
    if n < 0 then invalid_argf "List.init %d" n ();
    let rec loop i accum =
      assert (i >= 0);
      if i = 0 then accum
      else loop (i-1) (f (i-1) :: accum)
    in
    loop n []
  ;;

  let split_n t_orig n =
  if n <= 0 then
    ([], t_orig)
  else
    let rec loop n t accum =
      if n = 0 then
        (List.rev accum, t)
      else
        match t with
        | [] -> (t_orig, []) (* in this case, t_orig = List.rev accum *)
        | hd :: tl -> loop (n - 1) tl (hd :: accum)
    in
    loop n t_orig []

  let take t n = fst (split_n t n)
  let drop t n = snd (split_n t n)

  let rev_mapi l ~f =
    let rec loop i acc = function
      | [] -> acc
      | h :: t -> loop (i + 1) (f i h :: acc) t
    in
    loop 0 [] l

  let mapi l ~f = List.rev (rev_mapi l ~f)
end

let fail () = failwith "pa_enumerate error"

let name_of_type_name = function
  | "t" -> "all"
  | type_name -> "all_of_" ^ type_name
let name_of_type_variable str =
  "_" ^ name_of_type_name str

(* Utility functions *)
let enumeration_type_of_td ~loc ~type_name ~tps =
  let tps = List.map tps ~f:Gen.drop_variance_annotations in
  let init =
    let tp = List.fold_left tps ~init:(TyId (loc, (IdLid (loc, type_name))))
               ~f:(fun acc tp -> TyApp (loc,acc,tp))
    in
    <:ctyp< list $tp$ >>
  in
  List.fold_right tps ~init
    ~f:(fun tp acc -> <:ctyp< list $tp$ -> $acc$ >>)

let rec sig_of_td = function
  | TyDcl (loc, type_name, tps, _rhs, _cl) ->
    let enumeration_type = enumeration_type_of_td ~loc ~type_name ~tps in
    let name = name_of_type_name type_name in
    <:sig_item< value $lid: name$ : $enumeration_type$>>
  | TyAnd (loc, tp1, tp2) ->
      <:sig_item< $sig_of_td tp1$; $sig_of_td tp2$ >>
  | _ -> fail ()

let () = add_sig_generator "enumerate" (fun _rec td -> sig_of_td td)

let gensym = Pa_type_conv.Gen.gensym ~prefix:"enumerate"

let tuple loc exprs =
  assert (List.length exprs >= 2);
  ExTup (loc, exCom_of_list exprs)
let patt_tuple loc pats =
  assert (List.length pats >= 2);
  PaTup (loc, paCom_of_list pats)
let apply e el = Gen.exApp_of_list (e :: el)

let replace_variables_by_underscores =
  (Ast.map_ctyp (function
    | <:ctyp@loc< '$_$ >> -> <:ctyp@loc< _ >>
    | ctyp -> ctyp))#ctyp

let list_map loc l ~f =
  let element = gensym () in
  let applied = f <:expr<$lid:element$>> in
  <:expr<
    let rec map l acc = match l with [
      [] -> List.rev acc
    | [$lid:element$::l] ->
      map l [$applied$ ::acc]
    ]
    in
    map $l$ []
  >>

(* [cartesian_product_map l's f loc] takes a list of expressions of type list, and
   returns code generating the Cartesian product of those lists, with [f] applied to each
   tuple.
*)
let cartesian_product_map l's ~f loc =
  match l's with
  | [] -> failwith "cartesian_product_map passed list of zero length"
  | [l] -> list_map loc l ~f:(fun x -> f [x])
  | _ ->
    let lid x =  <:expr< $lid:x$ >> in
    let patt_lid x = <:patt< $lid:x$ >> in
    let alias_vars = List.map l's ~f:(fun _ -> gensym ()) in
    let init =
      let len = List.length l's in
      let hd_vars = List.map l's ~f:(fun _ -> gensym ()) in
      let args_vars = List.map l's ~f:(fun _ -> gensym ()) in
      let tl_var = gensym () in
      let base_case =
        let patts =
          List.rev (<:patt<[]>> :: List.init (len - 1) ~f:(fun _ -> <:patt<_>>))
        in
        <:match_case< $patt_tuple loc patts$ -> List.rev acc>>
      in
      let apply_case =
        let patts = List.mapi hd_vars ~f:(fun i x ->
          <:patt< [$lid:x$::$if i = 0 then patt_lid tl_var else <:patt<_>>$] >>)
        in
        <:match_case< $patt_tuple loc patts$ -> $
          apply <:expr< loop [ $f (List.map hd_vars ~f:lid)$ :: acc ] >>
            (<:expr<$lid:tl_var$>> :: List.map (List.tl args_vars) ~f:lid)
        $ >>
      in
      let decrement_cases =
        List.init (len - 1) ~f:(fun i ->
          let patts = List.init i ~f:(fun _ -> <:patt<_>>)
                      @ [ <:patt<[]>>; <:patt< [_ :: $lid:tl_var$] >> ]
                      @ List.init (len - i - 2) ~f:(fun _ -> <:patt<_>>)
          in
          <:match_case< $patt_tuple loc patts$ -> $
            apply <:expr< loop acc >>
              (List.map ~f:lid (List.take alias_vars (i + 1))
               @ <:expr<$lid:tl_var$>> :: (List.map ~f:lid (List.drop args_vars (i + 2))))
          $ >>)
      in
      <:expr<
        let rec loop acc = $
          Gen.abstract loc (List.map args_vars ~f:patt_lid)
            (<:expr< match $tuple loc (List.map args_vars ~f:lid)$ with [
              $list:base_case :: apply_case :: decrement_cases$
            ] >>) $
        in
        $apply <:expr< loop [] >> (List.map ~f:lid alias_vars)$
        >>
    in
    List.fold_right2 alias_vars l's ~init ~f:(fun alias_var input_list acc ->
      <:expr< let $lid:alias_var$ = $input_list$ in $acc$ >>)

let enum_val_of_id loc id =
  let path = Gen.get_rev_id_path id [] in
  Gen.ident_of_rev_path loc (
    name_of_type_name (List.hd path)
    :: List.tl path
  )

(* Here we do two things: simplify append on static lists, to make the generated code more
   readable and rewrite (List.append (List.append a b) c) as (List.append a (List.append b
   c)), to avoid a quadratic behaviour with long nesting to the left. *)
let rec list_append loc l1 l2 =
  match l2 with
  | <:expr< [] >> -> l1
  | _ ->
    match l1 with
    | <:expr< [] >> -> l2
    | <:expr< [ $hd$ :: $tl$ ] >> -> <:expr< [ $hd$ :: $list_append loc tl l2$ ] >>
    | <:expr< List.append $ll$ $lr$ >> -> list_append loc ll (list_append loc lr l2)
    | _ -> <:expr@loc< List.append $l1$ $l2$ >>

let rec enum ~main_type = function
  | <:ctyp@loc< bool >> -> <:expr< [False; True] >>
  | <:ctyp@loc< unit >> -> <:expr< [()] >>
  | <:ctyp@loc< option $tp$ >> ->
    <:expr< [None :: $list_map loc (enum ~main_type:tp tp)
            ~f:(fun e -> <:expr<Some $e$>>)$] >>
  | <:ctyp@loc< $lid:id$ >> ->
    let all = enum_val_of_id loc <:ident<$lid:id$>> in
    <:expr<$id:all$>>
  | <:ctyp@loc< $tp1$ | $tp2$ >> ->
    let enum1 = variant_case loc tp1 ~main_type in
    let enum2 = variant_case loc tp2 ~main_type in
    list_append loc enum1 enum2
  | <:ctyp@loc< $uid:cnstr$ >> ->
    <:expr< [ $uid:cnstr$ ] >>
  | <:ctyp@loc< `$cnstr$ >> ->
    <:expr< [ `$cnstr$ ] >>
  | <:ctyp@loc< $uid:cnstr$ of $tps$ >> ->
    product loc tps (fun x ->
      List.fold_left x ~init:<:expr<$uid:cnstr$>>
        ~f:(fun acc x -> <:expr<$acc$ $x$>>))
  | <:ctyp@loc< `$uid:cnstr$ of $tp$ >> ->
    list_map loc (enum tp ~main_type:tp) ~f:(fun e -> <:expr< `$uid:cnstr$ $e$ >>)
  | TyTup (loc,tps) ->
    product loc tps (fun exprs -> tuple loc exprs)
  | TyRec (loc,fields) ->
    let field_names, types = List.split (
      List.map (list_of_ctyp fields []) ~f:(function
      | <:ctyp< $lid:f1$ : $t1$>> -> (f1,t1)
      | _ -> assert false
      )
    )
    in
    product loc (tyAnd_of_list types) (function l ->
      let fields = List.map2 field_names l ~f:(fun field_name x ->
        <:rec_binding< $lid:field_name$ = $x$>>
      )
      in
      <:expr< { $rbSem_of_list fields$ } >>
    )
  | TyNil loc ->
    <:expr< [] >>
  | TyId (loc,id) ->
    let all = enum_val_of_id loc id in
    <:expr< $id:all$ >>
  | <:ctyp@loc< '$lid:id$ >> -> <:expr<$lid:name_of_type_variable id$>>
  | (<:ctyp< [ $alts$ ] >> | <:ctyp< [= $alts$ ]>>) -> enum alts ~main_type
  | <:ctyp@loc< $t1$ $t2$ >> -> <:expr< $enum t1 ~main_type:t1$ $enum t2 ~main_type:t2$ >>
  | ctyp -> Loc.raise (loc_of_ctyp ctyp) (Failure "unsupported type")

and variant_case loc tp ~main_type =
  let result = enum tp ~main_type in
  match tp with
  | <:ctyp< [ $_$ ] >> | <:ctyp< [= $_$ ]>>
  | <:ctyp< $_$ | $_$ >>
  | <:ctyp< `$_$ >> | <:ctyp< `$_$ of $_$ >>
  | <:ctyp< $uid:_$ >> | <:ctyp< $uid:_$ of $_$ >> | <:ctyp< $uid:_$ : $_$ >>
    -> result
  | _ -> <:expr< ($result$ :> list $replace_variables_by_underscores main_type$) >>

and product loc tps f =
    let all = List.map (list_of_ctyp tps []) ~f:(fun tp -> enum ~main_type:tp tp) in
    cartesian_product_map all loc ~f

let quantify loc vars typ =
  match vars with
  | [] -> typ
  | first :: rest ->
    let quantifier =
      List.fold_left rest ~init:<:ctyp< $first$ >>
        ~f:(fun acc typ -> <:ctyp@loc< $acc$ $typ$ >>)
    in
    <:ctyp< ! $quantifier$. $typ$ >>

let enum_of_td = function
  | TyDcl (loc, type_name, tps, rhs, _cl) ->
    let tps = List.map tps ~f:Gen.drop_variance_annotations in
    let all =
      let main_type =
        List.fold_left tps ~init:<:ctyp@loc< $lid:type_name$ >>
          ~f:(fun acc _ -> <:ctyp@loc< $acc$ _ >>)
      in
      match rhs with
      | <:ctyp< $_$ == $tp$ >> -> enum tp ~main_type
      | tp ->
        enum tp ~main_type
    in
    let name = name_of_type_name type_name in
    let args = List.map tps ~f:(fun tp ->
      let name = name_of_type_variable (Gen.get_tparam_id tp) in
      let loc = Ast.loc_of_ctyp tp in
      <:patt<$lid:name$>>
    )
    in
    let enumeration_type =
      let typ = enumeration_type_of_td ~loc ~type_name ~tps in
      quantify loc tps typ
    in
    let body = Gen.abstract loc args all in
    <:str_item@loc< value $lid:name$ : $enumeration_type$ = $body$; >>
  | _ -> fail ()

let () = add_generator "enumerate" (fun _rec td -> enum_of_td td)

let () = Syntax.Quotation.add "all"
           Syntax.Quotation.DynAst.expr_tag
           (fun loc _loc_name_opt cnt_str ->
              Pa_type_conv.set_conv_path_if_not_set loc;
              let ctyp = Gram.parse_string Syntax.ctyp_quot loc cnt_str in
              enum ctyp ~main_type:ctyp
           )
