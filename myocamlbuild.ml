(* OASIS_START *)
(* OASIS_STOP *)

let dispatch = function
  | After_rules ->
    flag ["ocaml"; "compile"; "locfix"] & S[A"-ppopt"; A "-locloc"];
    flag ["ocaml"; "ocamldep"; "locfix"] & S[A"-ppopt"; A "-locloc"];
    flag ["ocaml"; "doc"; "locfix"] & S[A"-ppopt"; A "-locloc"];
  | _ ->
    ()

let () = Ocamlbuild_plugin.dispatch (fun hook -> dispatch hook; dispatch_default hook)
