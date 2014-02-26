type t = A | B with enumerate
TEST = all = [A; B]

type s = C | D with enumerate
TEST = all_of_s = [C; D]

type u = E | F of s with enumerate
TEST = all_of_u = [E; F C; F D]

module V = struct
  type v = G of t | H of u with enumerate
  TEST = all_of_v = [G A; G B; H E; H (F C); H (F D)]
end

type w = I of V.v with enumerate
TEST = all_of_w = [I (V.G A); I (V.G B); I (V.H E); I (V.H (F C)); I (V.H (F D))]

type x = [`A | `B of t] with enumerate
TEST = all_of_x = [`A; `B A; `B B]

(* variant with multiple arguments are not special *)
type xx = [ `A of s * s ] with enumerate
TEST = all_of_xx = [`A (C, C); `A (D, C); `A (C, D); `A (D, D)]

type variant_inclusion = [ x | `C | x ] with enumerate
TEST = all_of_variant_inclusion = all_of_x @ [ `C ] @ all_of_x

type y = J of t * s with enumerate
TEST = all_of_y = [J (A,C); J (B,C); J (A,D); J (B,D)]

type z = t * s with enumerate
TEST = all_of_z = [(A,C); (B,C); (A,D); (B,D)]

type a = {foo : t; bar : s} with enumerate
TEST = all_of_a = [{foo = A; bar = C}; {foo = B; bar = C};
                 {foo = A; bar = D}; {foo = B; bar = D}]

type b = K of t * t * s with enumerate
TEST = all_of_b = [K (A,A,C); K (B,A,C); K (A,B,C); K (B,B,C);
                 K (A,A,D); K (B,A,D); K (A,B,D); K (B,B,D);
                ]

type c = t * t * s with enumerate
TEST = all_of_c = [(A,A,C); (B,A,C); (A,B,C); (B,B,C);
                 (A,A,D); (B,A,D); (A,B,D); (B,B,D);
                ]

type d = { a : t; b : t; c : s} with enumerate
TEST = all_of_d = [{a=A;b=A;c=C}; {a=B;b=A;c=C}; {a=A;b=B;c=C}; {a=B;b=B;c=C};
                 {a=A;b=A;c=D}; {a=B;b=A;c=D}; {a=A;b=B;c=D}; {a=B;b=B;c=D};
                ]
type e = { foo : t } with enumerate
module M = struct
  type nonrec e = { bar : e } with enumerate
end
TEST = M.all_of_e = [{M.bar = {foo = A}}; {M.bar = {foo = B}}]

type f = L of [`A | `B] with enumerate
TEST = all_of_f = [L `A; L `B]

type g = f with enumerate
TEST = all_of_g = all_of_f

type h = M | N
type i = h = M | N with enumerate
TEST = all_of_i = [M; N]

type 'a j = 'a with enumerate
type k = i j with enumerate
TEST = all_of_k = [M; N]

TEST = <:all<[`A of [`B | `C] | `D of [`E of [`F]]]>> =
       [`A `B; `A `C; `D (`E `F)]

type l = { baz : bool; quux : unit } with enumerate
TEST = all_of_l = [{baz = false; quux = ()}; {baz = true; quux = ()}]

type o = [`A] option with enumerate
TEST = all_of_o = [None; Some `A]

(* Check that enumerations are only computed once *)
type 'a count = 'a
let number_of_computations = ref 0
let all_of_count all_of_a =
  incr number_of_computations;
  all_of_a
type p = { baz : bool count; quux : unit count } with enumerate
TEST = !number_of_computations = 2

let () = number_of_computations := 0
type p_nested = [ `A of [ `B of unit count * unit count ] * [ `C of unit count * unit count ] ]
with enumerate
TEST = !number_of_computations = 4

(* checking the lack of unused value warning *)
type 'a phantom_variable = unit with enumerate
type empty
TEST = all_of_phantom_variable ([] : empty list) = [()]

module Check_sigs = struct
  module type S1 = sig
    type t = A | B with enumerate
  end

  module type S2 = sig
    type t = A | B
    val all : t list
  end

  let _ (module M : S1) =
    let module M : S2 = M in
    let module M : S1 = M in
    ()
end

module Check_sigs_with_params_and_variance = struct
  module type S1 = sig
    type (+'a, 'b) t = A of 'a | B of 'b with enumerate
  end

  module type S2 = sig
    type ('a, +'b) t = A of 'a | B of 'b
    val all : 'a list -> 'b list -> ('a, 'b) t list
  end

  let _ (module M : S1) =
    let module M : S2 = M in
    let module M : S1 = M in
    ()
end
