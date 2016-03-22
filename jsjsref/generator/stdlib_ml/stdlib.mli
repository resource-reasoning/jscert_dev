
(*--------------------*)
(* number operations *)

(* todo : factorize and clean up *)

val ( ~+ ) : int -> int
val ( ~- ) : int -> int
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( * ) : int -> int -> int
val ( / ) : int -> int -> int

(* Alan: I don't think fpclass is needed. To compare numbers, we can use
   - isNaN https://es5.github.io/#x15.1.2.4
   - === with Number.POSITIVE_INFINITY or NUMBER.NEGATIVE_INFINITY
   - === to 0 *)

type fpclass =
  | FP_normal
  | FP_subnormal
  | FP_zero
  | FP_infinite
  | FP_nan

(* Alan: these can be implemented directly, using Number.NaN,
   Number.POSITIVE_INFINITY, Number.NEGATIVE_INFINITY *)

val nan : float
val infinity : float
val neg_infinity : float

(* Alan: Do we need these ? If so, they are Number.MAX_VALUE and
   Number.MIN_VALUE *)

val max_float : float
val min_float : float

(* Alan: these should all be implemented along with the int operations as the JS
   ones. ** is Math.pow *)

val ( ~+. ) : float -> float
val ( ~-. ) : float -> float
val ( +. ) : float -> float -> float
val ( -. ) : float -> float -> float
val ( *. ) : float -> float -> float
val ( /. ) : float -> float -> float
val ( ** ) : float -> float -> float

(* Alan: Math.abs, if we need it *)

val abs_float : float -> float

(* Alan: % infix *)

val mod_float : float -> float -> float

(* Alan: Why do we need these? If need be, they are all in Math *)

val atan : float -> float
val exp : float -> float
val log : float -> float
val floor : float -> float
val min : float -> float -> float
val max : float -> float -> float

(* Alan: do we need this? *)

val classify_float : float -> fpclass

val int_abs : int -> int

(* Alan: Ideally we would add these to the spec, but for the moment conversion
   to a string is doing a foo+"", and conversion to an int is doing +foo *)

val float_of_int : int -> float
val float_of_string : string -> float
val int_of_char : char -> int
val int_of_float : float -> int
val string_of_float : float -> string
val string_of_int : int -> string


(* no need to implement those in stdlib.js because JS has them already *)
val ( = ) : float -> float -> bool
val ( < ) : float -> float -> bool
val ( > ) : float -> float -> bool
val ( <= ) : float -> float -> bool 
val ( >= ) : float -> float -> bool

(*val compare : 'a -> 'a -> int*)

val int_eq : int -> int -> bool
val int_lt : int -> int -> bool
val int_ge : int -> int -> bool

val float_eq : float -> float -> bool
val float_lt : float -> float -> bool
val float_le : float -> float -> bool
val float_compare : float -> float -> int
(** val number_comparable : number coq_Comparable **)
val number_comparable : float -> float -> bool  (* = (fun n1 n2 -> int_eq 0  (float_compare n1 n2)) *)

(** val of_int : float -> number **)
val of_int : float -> float (* = fun x -> x *)

val number_of_int : int -> float  (* = fun x -> float_of_int x *)

val nat_eq : int -> int -> bool (* nat_eq x y = int_eq x y  *)


(* Alan: why are these here? *)

val pi : float
val e : float
val ln2 : float

val float_neg : float -> float (* ~-.*)

val lt_bool : float -> float -> bool (*   (<) *)
val add : float -> float -> float (*  (+.) *)
val sub : float -> float -> float (*  (-.) *)
val mult : float -> float -> float (*  ( *. ) *)
val div : float -> float -> float (*  (/.) *)
val fmod : float -> float -> float (*  mod_float *)
val float_exp : float -> float -> float (* ( ** ) *)


(*--------------------*)
(* bool operations *)

val bool_eq : bool -> bool -> bool (* should be "===" in  JS *)
val ( && ) : bool -> bool -> bool  (* beware of strict vs lazy semantics: todo discuss*)
val not : bool -> bool


(*--------------------*)
(* string operations *)

(* todo : factorize and clean up *)

val string_eq : string -> string -> bool

val string_concat : string -> string -> string

val (^) : string -> string -> string

(* let string_dec s1 s2 = (string_eq s1 s2) *)
val string_dec : string -> string -> bool

(* let append s1 s2 = String.append s1 s2 *)
val strappend : string -> string -> string 

(* let strlength s = String.length s *)
val strlength : string -> int

(* let substring n m s = String.sub s n m *)
val substring : int -> int -> string -> string



(*--------------------*)
(* for future use for the global heap *)

val ref : 'a -> 'a ref
val (:=) : 'a ref -> 'a -> unit
val (!) : 'a ref -> 'a


(*--------------------*)
(* special operations *)

(* We use this to compare types that are not known by stdlib, like Native_error;
  should be implemented in JS by comparing the objects, to see if they have the same
  "tag" fields (there should be no other fields, except perhaps "type") *)
val ( === ) : 'a -> 'a -> bool


(*--------------------*)
(* todo: remove when JsNumber.ml becomes .mli file *)

(* Alan: I'll do this *)

module Int32 : sig
  val logand : int32 -> int32 -> int32
  val lognot : int32 -> int32
  val logor : int32 -> int32 -> int32
  val logxor : int32 -> int32 -> int32
  val of_float : float -> int32
  val shift_left : int32 -> int -> int32
  val shift_right : int32 -> int -> int32
  val shift_right_logical : int32 -> int -> int32
  val to_float : int32 -> float
end


(*--------------------*)
(* JSRef specific functions, useful for debugging *)

val print_endline : string -> unit
val __LOC__ : string

val prerr_string : string -> unit
val prerr_newline : unit -> unit
val prerr_endline : string -> unit

val raise : exn -> 'a
val stuck : string -> 'a

