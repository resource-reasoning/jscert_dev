Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Renegade inversion principles for expressions          *)

Lemma inv_red_expr_spec_prim_new_object : 
  forall (S : state) (C : execution_ctx) (a1 : prim) (oo : out)
         (P : state -> execution_ctx -> prim -> out -> Prop),
    (red_expr S C (spec_prim_new_object a1) oo ->
       out_of_ext_expr (spec_prim_new_object a1) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_prim_new_object a1)) ->
       P S C a1 oo) ->
    (red_expr S C (spec_prim_new_object a1) oo ->
       forall l S' (b : bool),
       let O1 := object_new prealloc_bool_proto "Boolean" in
       let O := object_with_primitive_value O1 b in
       (l, S') = object_alloc S O ->
       a1 = prim_bool b -> oo = out_ter S' l ->
       P S C a1 oo) ->
    (red_expr S C (spec_prim_new_object a1) oo ->
       forall l S' S'' (s : string),
       let O2 := object_new prealloc_string_proto "String" in
       let O1 := object_with_get_own_property O2 builtin_get_own_prop_string in
       let O := object_with_primitive_value O1 s in
       (l, S') = object_alloc S O ->
       object_set_property S' l "length" (attributes_data_intro_constant (JsNumber.of_int (String.length s))) S'' ->
       a1 = prim_string s -> oo = out_ter S'' l ->
       P S C a1 oo) ->
    (red_expr S C (spec_prim_new_object a1) oo ->
       forall l S' (n : number),
       let O1 := object_new prealloc_number_proto "Number" in
       let O := object_with_primitive_value O1 n in
       (l, S') = object_alloc S O ->
       a1 = prim_number n -> oo = out_ter S' l ->
       P S C a1 oo) ->
    red_expr S C (spec_prim_new_object a1) oo -> P S C a1 oo.
Proof.
  introv IH_abort IH_bool IH_string IH_number Hr;  
  specializes IH_abort Hr; specializes IH_bool Hr; 
  specializes IH_string Hr; specializes IH_number Hr.
  inversion Hr; substs*.
Admitted. (* Faster *)

Lemma inv_red_expr_spec_construct_bool_1 : 
  forall (S : state) (C : execution_ctx) (a1 : out) (oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
    (red_expr S C (spec_construct_bool_1 a1) oo ->
       out_of_ext_expr (spec_construct_bool_1 a1) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_construct_bool_1 a1)) ->
       P S C a1 oo) ->
    (red_expr S C (spec_construct_bool_1 a1) oo ->
       forall (b : bool) l S' S'',
       let O1 := object_new prealloc_bool_proto "Boolean" in
       let O := object_with_primitive_value O1 b in
       (l, S'') = object_alloc S' O ->
       a1 = out_ter S' b -> oo = out_ter S'' l ->
       P S C a1 oo) ->
    red_expr S C (spec_construct_bool_1 a1) oo -> P S C a1 oo.
Proof.
  introv IH_abort IH_bool Hr;  
  specializes IH_abort Hr; specializes IH_bool Hr.
  inversion Hr; substs*.
Admitted. (* Faster *)

Lemma inv_red_expr_spec_construct_number_1 : 
  forall (S : state) (C : execution_ctx) (a1 : out) (oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
    (red_expr S C (spec_construct_number_1 a1) oo ->
       out_of_ext_expr (spec_construct_number_1 a1) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_construct_number_1 a1)) ->
       P S C a1 oo) ->
    (red_expr S C (spec_construct_number_1 a1) oo ->
       forall (v : value) l S' S'',
       let O1 := object_new prealloc_number_proto "Number" in
       let O := object_with_primitive_value O1 v in
       (l, S'') = object_alloc S' O ->
       a1 = out_ter S' v -> oo = out_ter S'' l ->
       P S C a1 oo) ->
    red_expr S C (spec_construct_number_1 a1) oo -> P S C a1 oo.
Proof.
  introv IH_abort IH_number Hr;  
  specializes IH_abort Hr; specializes IH_number Hr.
  inversion Hr; substs*.
Admitted. (* Faster *)

Lemma inv_red_expr_spec_creating_function_object_proto_1 : 
  forall (S : state) (C : execution_ctx) (a1 : object_loc) (a2 : out) (oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
    (red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo ->
       out_of_ext_expr (spec_creating_function_object_proto_1 a1 a2) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_creating_function_object_proto_1 a1 a2)) ->
       P S C a1 a2 oo) ->
    (red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo ->
       forall S' l o o1 lproto,
       let A := attributes_data_intro (value_object l) true false true in
       red_expr S' C (spec_object_define_own_prop lproto "constructor" A false) o1 ->
       red_expr S' C (spec_creating_function_object_proto_2 l lproto o1) o ->
       a2 = out_ter S' lproto -> oo = o ->
       P S C a1 a2 oo) ->
    red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo -> P S C a1 a2 oo.
Proof.
  introv IH_abort IH Hr;  
  specializes IH_abort Hr; specializes IH Hr.
  inversion Hr; substs*.
Admitted. (* Faster *)

Lemma inv_red_expr_spec_creating_function_object_proto_2 : 
  forall (S : state) (C : execution_ctx) (a1 : object_loc) (a2 : object_loc) (a3 : out) (oo : out)
         (P : state -> execution_ctx -> object_loc -> object_loc -> out -> out -> Prop),
    (red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo ->
       out_of_ext_expr (spec_creating_function_object_proto_2 a1 a2 a3) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_creating_function_object_proto_2 a1 a2 a3)) ->
       P S C a1 a2 a3 oo) ->
    (red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo ->
       forall S' l o (b : bool) lproto,
       let A := attributes_data_intro (value_object a2) true false false in
       red_expr S' C (spec_object_define_own_prop l "prototype" A false) o ->
       a2 = lproto -> a3 = out_ter S' b -> oo = o ->
       P S C a1 a2 a3 oo) ->
    red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.
Proof.
  introv IH_abort IH Hr;  
  specializes IH_abort Hr; specializes IH Hr.
  inversion Hr; substs*.
Admitted. (* Faster *)

