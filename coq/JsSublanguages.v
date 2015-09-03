Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Implicit Types -- copied from JsPreliminary *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type ty : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.
Implicit Type ct : codetype.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.

Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.

Implicit Type T : Type.

(**************************************************************)
(** ** Speeding up inversion                                  *)

Ltac inverts_tactic_general T H :=
  let rec go :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh in intro H;
                           first [ subst x | subst y | injects H ];
                           go 
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go 
    | |- (?P -> ?Q) => intro; go 
    | |- (forall _, _) => intro; go 
    end in
  generalize ltac_mark; T H; go;
  unfold eq' in *.

Ltac red_prog_hnf e := 
match (eval hnf in e) with
  | prog_basic ?e1 =>
      let e1' := (eval hnf in e1) in
      constr:(prog_basic e1')
  | ?e1 => constr:e1
end.

Derive Inversion inv_red_prog_intro      with (forall S C str els oo, red_prog S C (prog_intro str els) oo) Sort Prop.
Derive Inversion inv_red_prog_javascript with (forall S C o1  p   oo, red_prog S C (javascript_1 o1 p)  oo) Sort Prop.
Derive Inversion inv_red_prog_prog_1     with (forall S C el      oo, red_prog S C (prog_1 oo el)       oo) Sort Prop.
Derive Inversion inv_red_prog_prog_2     with (forall S C o1  rv  oo, red_prog S C (prog_2 rv o1)       oo) Sort Prop.

Tactic Notation "invert" "keep" "red_prog" hyp(H) := 
match type of H with
  | red_prog ?S ?C (?e) ?oo => 
    let eh := red_prog_hnf e in
    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); 
    match eh with
      | prog_basic (prog_intro _ _) => inversion H using inv_red_prog_intro
      | javascript_1 _ _ => inversion H using inv_red_prog_javascript
      | prog_1 _ _ => inversion H using inv_red_prog_prog_1
      | prog_2 _ _ => inversion H using inv_red_prog_prog_2
    end
end; tryfalse; clear H; intro H.

Tactic Notation "inverts" "keep" "red_prog" hyp(H) := 
  inverts_tactic_general ltac:(fun H => invert keep red_prog H) H. (* tryfalse. *)

Tactic Notation "inverts" "red_prog" hyp(H) := 
  inverts keep red_prog H; clear H.

(**************************************************************)
(** ** Discharging exception difficulties                     *)

Ltac false_exception := 
try match goal with 
 | H : out_of_ext_prog _ = _ |- _ => 
   try solve [simpls; inverts* H]; 
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]
 | H : out_of_ext_stat _ = _ |- _ => 
   try solve [simpls; inverts* H];
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]

 | H : out_of_ext_spec _ = _ |- _ => 
   try solve [simpls; inverts* H];
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]

 | H : out_of_ext_expr _ = _ |- _ => 
   try solve [simpls; inverts* H];
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]
end.

(**************************************************************)
(** ** Auxiliary inversions on the semantics                  *)

Lemma red_stat_expr_literal : forall S C (l : literal) o,
  red_stat S C (expr_literal l) o -> o = out_ter S (convert_literal_to_prim l).
Proof with false_exception.
  introv Hr. inverts Hr...
  inverts H0... inverts H2...
  inverts H6... inverts H5... 
  inverts~ H3...
Admitted. (* Faster *)

Lemma red_expr_expr_literal : forall S C (l : literal) o,
  red_expr S C (expr_literal l) o -> o = out_ter S (convert_literal_to_prim l).
Proof with false_exception.
  introv Hr. inverts~ Hr...
Admitted. (* Faster *)

Lemma red_spec_spec_to_primitive_auto_prim : forall S C (p : prim) o,
  red_expr S C (spec_to_primitive_auto p) o -> o = out_ter S p.
Proof with false_exception.
  introv Hr; inverts~ Hr...
Admitted. (* Faster *)

Lemma red_expr_spec_to_number_number : forall S C n o,
  red_expr S C (spec_to_number n) o -> o = out_ter S n.
Proof with false_exception.
  introv Hr. inverts~ Hr...
Admitted. (* Faster *)

Ltac invert_jscert :=
match goal with
 | H : red_stat _ _ (stat_basic (stat_expr (expr_literal _))) ?o |- _ => 
   lets Hsubst : red_stat_expr_literal (rm H); subst o
 | H : red_expr _ _ (expr_basic (expr_literal _)) ?o |- _ => 
   lets Hsubst : red_expr_expr_literal (rm H); subst o
 | H : red_expr _ _ (spec_to_primitive_auto (value_prim _)) ?o |- _ => 
   lets Hsubst : red_spec_spec_to_primitive_auto_prim (rm H); subst o
 | H : red_expr _ _ (spec_to_number (value_prim (prim_number _))) ?o |- _ => 
   lets Hsubst : red_expr_spec_to_number_number (rm H); subst o
end.

Ltac clear_binop :=
repeat match goal with
 | H : regular_binary_op _     |- _ => inverts H
 | H : lazy_op           _ _   |- _ => inverts H
 | H : puremath_op       _ _   |- _ => inverts H
 | H : shift_op          _ _ _ |- _ => inverts H
 | H : inequality_op     _ _ _ |- _ => inverts H
 | H : bitwise_op        _ _   |- _ => inverts H
end.

Ltac invert_jscert_on_two Hyp :=
match type of Hyp with
 | red_spec _ _ _ _ => inverts* Hyp
 | red_expr _ _ _ _ => inverts* Hyp
 | red_stat _ _ _ _ => inverts* Hyp
 | red_prog _ _ _ _ => inverts red_prog Hyp
end; jauto; false_exception; clear_binop; repeat invert_jscert.

Ltac invert_jscert_on Hyp :=
 inverts* Hyp; false_exception; clear_binop; repeat invert_jscert.

Ltac JesusTakeTheWheel :=
try match goal with 
 | H : red_spec _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; JesusTakeTheWheel) || (invert_jscert_on H; fail)
 | H : red_expr _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; JesusTakeTheWheel) || (invert_jscert_on H; fail)
 | H : red_stat _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; JesusTakeTheWheel) || (invert_jscert_on H; fail)
 | H : red_prog _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; JesusTakeTheWheel) || (invert_jscert_on H; fail)
end.

(**************************************************************)
(** ** Toy sublanguage #1 - just numbers                      *)

Definition sub_numbers_elem (e : element) : Prop := 
match e with
  | element_stat t =>
      match t with
        | stat_expr e => 
            match e with
              | expr_literal i =>
                  match i with
                    | literal_number n => True
                    | _ => False
                  end
              | _ => False
            end
        | _ => False
      end
  | _ => False 
end.

Definition sub_numbers_prog (p : prog) : Prop :=
match p with
  | prog_intro _ le => Forall (fun (e : element) => sub_numbers_elem e) le
end.
       
Theorem sub_numbers_characterization : 
  forall p S C o, 
    red_prog S C p o -> 
    sub_numbers_prog p -> 
    exists S' n, o = (out_ter S' n).
Proof with JesusTakeTheWheel.
  destruct p as (s & le). gen s.
  induction le using list_ind_last; introv Hr Hs...

  + apply last_eq_nil_inv in H0. false~.

  + apply last_eq_last_inv in H0; destruct H0; subst.
    apply Forall_last_inv in Hs. destruct Hs as (Hs & Ha).
    specializes IHle (rm H3) (rm Hs).
    destruct a; try solve [false*].
    destruct s0; try solve [false*].
    destruct e; try solve [false*].
    destruct l; try solve [false*]...
Admitted. (* Faster *)

(**************************************************************)
(** ** Toy sublanguage #1 - numbers and +                     *)

Fixpoint sub_numplus_expr (e : expr) : Prop :=
match e with
 | expr_literal i =>
   match i with
    | literal_number n => True
    | _ => False
   end
 | expr_binary_op e1 binop e2 => 
   sub_numplus_expr e1 /\ sub_numplus_expr e2 /\ 
   match binop with
    | binary_op_add  => True
    | _ => False
   end
 | _ => False
end.
  
Fixpoint sub_numplus_elem (e : element) : Prop := 
match e with
  | element_stat t =>
      match t with
        | stat_expr e => sub_numplus_expr e           
        | _ => False
      end
  | _ => False 
end.

Definition sub_numplus_prog (p : prog) : Prop :=
match p with
  | prog_intro _ le => Forall (fun (e : element) => sub_numplus_elem e) le
end.

Lemma red_sub_numplus_expr : forall (e : expr),
  sub_numplus_expr e -> forall S C o, 
    red_expr S C e o -> exists (n : number), o = out_ter S n.
Proof with JesusTakeTheWheel.
  induction e; introv Hsub; introv Hr; try solve [false*].

  destruct l; try solve [false*]... 
  eexists; reflexivity.

  simpls; destruct b; try solve [false*].
  destruct Hsub as (He1 & He2 & _).
  specializes IHe1 He1 S C. specializes IHe2 He2 S C...
  lets (n1 & Heq1) : IHe1 H1; subst...
  lets (n2 & Heq2) : IHe2 H2; subst...
  invert_jscert_on H7; [simpls; intuition; false* | ]... 
Admitted. (* Faster *)

Theorem sub_numplus_characterization : 
  forall p S C o, 
    red_prog S C p o -> 
    sub_numplus_prog p -> 
    exists S' n, o = (out_ter S' n).
Proof with JesusTakeTheWheel.
  destruct p as (s & le). gen s.
  induction le using list_ind_last; introv Hr Hs...

  + apply last_eq_nil_inv in H0. false~.

  + apply last_eq_last_inv in H0; destruct H0; subst.
    apply Forall_last_inv in Hs. destruct Hs as (Hs & Ha).
    specializes IHle (rm H3) (rm Hs).
    destruct IHle as (S' & n & Heq); subst.
    destruct a; try solve [false*].
    destruct s0; try solve [false*].
    destruct e; try solve [false*].

    - destruct l; try solve [false*]...

    - simpls; destruct b; try solve [false*]...
      apply red_sub_numplus_expr in H1; jauto.
      simpls. inverts H. destruct H1 as (n1 & Heq).
      destruct y1; inverts H4; subst...
      apply red_sub_numplus_expr in H3; jauto.
      destruct H3 as (n2 & Heq); subst...
      invert_jscert_on H10; [simpls; intuition; false* | ]...
Admitted.














































(*
(**************************************************************)
(** ** Characterization of lists via tail                     *)

Lemma list_characterize_tail : forall T (l : list T),
  l = nil \/ (exists (t : T) (l' : list T), l = l' & t).
Proof.
  intro T; induction l using (measure_induction length); destruct l; auto.
  right. destruct (H l); subst. rew_length; nat_math.
  exists t (@nil T). rewrite~ app_nil_l.
  destruct H0 as (t' & l' & Heq); subst.
  exists t' (t :: l'). rewrite~ app_cons.
Qed.

Lemma list_tail_singleton : forall T (t t' : T) (l : list T), 
  l & t = t' :: nil -> l = nil /\ t = t'.
Proof.
  destruct l; introv Heq.
  + splits*. unfold append in Heq; simpls. inverts~ Heq.
  + rewrite app_cons in Heq. inverts Heq. apply last_eq_nil_inv in H1. false.
Qed.

(**************************************************************)
(** ** Forward reduction rules for programs                   *)

Inductive ext_prog_fwd :=
  | prog_fwd_basic   : prog     -> ext_prog_fwd
  | prog_fwd_main    : out      -> elements     -> ext_prog_fwd 
  | prog_fwd_element : out      -> element      -> ext_prog_fwd
  | prog_fwd_rewrite : resvalue -> out          -> ext_prog_fwd
  | javascript_fwd_1 : out      -> prog         -> ext_prog_fwd
.

Definition out_of_ext_prog_fwd (p : ext_prog_fwd) : option out :=
match p with
 | prog_fwd_basic   _   => None
 | prog_fwd_main    o _ => Some o
 | prog_fwd_element o _ => Some o
 | prog_fwd_rewrite _ o => Some o 
 | javascript_fwd_1 o _ => Some o
end.

Inductive abort_intercepted_prog_fwd : ext_prog_fwd -> Prop := 
  | abort_intercepted_prog_fwd_rewrite : forall S R rv,
      abort_intercepted_prog_fwd (prog_fwd_rewrite rv (out_ter S R)). 

Coercion prog_fwd_basic : prog >-> ext_prog_fwd.

Inductive red_prog_fwd : state -> execution_ctx -> ext_prog_fwd -> out -> Prop :=

  (** Abort rule for programs *)

  | red_prog_fwd_abort : forall S C extp o,
      out_of_ext_prog_fwd extp = Some o ->
      abort o ->
      ~ abort_intercepted_prog_fwd extp ->
      red_prog_fwd S C extp o

  (** Program *)

  | red_javascript_intro_1 : forall S S' C p o,
      red_prog_fwd S' C p o ->
      red_prog_fwd S  C (javascript_fwd_1 (out_void S') p) o

  | red_prog_fwd_main : forall S C str els o,
      red_prog_fwd S C (prog_fwd_main (out_ter S resvalue_empty) els) o -> 
      red_prog_fwd S C (prog_intro str els) o

  | red_prog_fwd_nil : forall S S' C R,
      red_prog_fwd S C (prog_fwd_main (out_ter S' R) nil) (out_ter S' R)

  | red_prog_fwd_cons : forall S S' C el els o1 o rv,
      red_prog_fwd S' C (prog_fwd_element (out_ter S' rv) el) o1 -> 
      red_prog_fwd S' C (prog_fwd_main o1 els) o ->
      red_prog_fwd S  C (prog_fwd_main (out_ter S' rv) (el :: els)) o

  | red_prog_fwd_funcdecl : forall S S' C rv name args bd,
      red_prog_fwd S C (prog_fwd_element (out_ter S' rv) (element_func_decl name args bd)) (out_ter S' rv)

  | red_prog_fwd_stat : forall S S' C t rv o1 o,
      red_stat S' C t o1 ->
      red_prog_fwd S' C (prog_fwd_rewrite rv o1) o ->
      red_prog_fwd S  C (prog_fwd_element (out_ter S' rv) (element_stat t)) o

  | red_prog_fwd_rewrite : forall S S' C R R' rv,
      R' = (res_overwrite_value_if_empty rv R) ->
      red_prog_fwd S C (prog_fwd_rewrite rv (out_ter S' R)) (out_ter S' R').

(**************************************************************)
(** ** Append reduction rules for programs                    *)

Inductive ext_prog_app :=
  | prog_app_basic   : prog     -> ext_prog_app
  | prog_app_main    : out      -> elements     -> ext_prog_app
  | prog_app_rewrite : resvalue -> out          -> ext_prog_app
  | javascript_app_1 : out      -> prog         -> ext_prog_app
.

Definition out_of_ext_prog_app (p : ext_prog_app) : option out :=
match p with
 | prog_app_basic   _   => None
 | prog_app_main    o _ => Some o
 | prog_app_rewrite _ o => Some o 
 | javascript_app_1 o _ => Some o
end.

Inductive abort_intercepted_prog_app : ext_prog_app -> Prop := 
  | abort_intercepted_prog_app_rewrite : forall S R rv,
      abort_intercepted_prog_app (prog_app_rewrite rv (out_ter S R)). 

Coercion prog_app_basic : prog >-> ext_prog_app.

Inductive red_prog_app : state -> execution_ctx -> ext_prog_app -> out -> Prop :=

  (** Abort rule for programs *)

  | red_prog_app_abort : forall S C extp o,
      out_of_ext_prog_app extp = Some o ->
      abort o ->
      ~ abort_intercepted_prog_app extp ->
      red_prog_app S C extp o

  (** Program *)

  | red_javascript_app : forall S S' C p o,
      red_prog_app S' C p o ->
      red_prog_app S  C (javascript_app_1 (out_void S') p) o

  | red_prog_app_main : forall S C str els o,
      red_prog_app S C (prog_app_main (out_ter S resvalue_empty) els) o -> 
      red_prog_app S C (prog_intro str els) o

  | red_prog_app_nil : forall S S' C R,
      red_prog_app S C (prog_app_main (out_ter S' R) nil) (out_ter S' R)

  | red_prog_app_split : forall S S' C el1 el2 els o1 o rv,
      els = (el1 ++ el2)%list ->
      length el1 > 0 -> length el2 > 0 ->
      red_prog_app S C (prog_app_main (out_ter S' rv) el1) o1 -> 
      red_prog_app S C (prog_app_main o1 el2) o ->
      red_prog_app S C (prog_app_main (out_ter S' rv) els) o

  | red_prog_app_funcdecl : forall S S' C rv name args bd,
      red_prog_app S C (prog_app_main (out_ter S' rv) (element_func_decl name args bd :: nil)) (out_ter S' rv)

  | red_prog_app_stat : forall S S' C t rv o1 o,
      red_stat S' C t o1 ->
      red_prog_app S' C (prog_app_rewrite rv o1) o ->
      red_prog_app S  C (prog_app_main (out_ter S' rv) (element_stat t :: nil)) o

  | red_prog_app_rewrite : forall S S' C R R' rv,
      R' = (res_overwrite_value_if_empty rv R) ->
      red_prog_app S C (prog_app_rewrite rv (out_ter S' R)) (out_ter S' R').

Lemma red_prog_app_characterization_in : forall els S C o o',
  red_prog_app S C (prog_app_main o els) o' -> 
    (exists S', exists (rv : resvalue), o = out_ter S' rv) \/ 
    (exists extp, out_of_ext_prog_app extp = Some o /\ abort o /\ ~ abort_intercepted_prog_app extp).
Proof.
  induction els using (measure_induction length).
  destruct x as [ | e els]; introv Hr.
  inverts Hr. simpls*. inverts* H0.
  right. exists* (prog_app_main o' nil). 

  
Qed.

Lemma red_prog_app_composition : forall S C o0 el0 o1 el1 o,
  red_prog_app S C (prog_app_main o0 el0) o1 ->
  red_prog_app S C (prog_app_main o1 el1) o  ->
  red_prog_app S C (prog_app_main o0 (el0 ++ el1)%list) o.
Proof with (try match goal with 
             | H : out_of_ext_prog_app _ = _ |- _ => try solve [simpls; inverts* H] 
            end).
  introv Ht1 Ht2.
  
  destruct el0. rewrite app_nil_l. inverts~ Ht1... 
  apply nil_eq_app_inv in H1. inverts H1; substs.  
  rew_length in *; nat_math.
  
  destruct el1. rewrite app_nil_r. inverts~ Ht2... 
  apply nil_eq_app_inv in H1. inverts H1; substs.  
  rew_length in *; nat_math.
  
  lets Ho0 : red_prog_app_characterization_in Ht1.
  inverts Ho0 as Ho0.
  destruct Ho0 as (S' & rv & Heq); subst.
  eapply red_prog_app_split. reflexivity.
  rew_length; nat_math. rew_length; nat_math.
  eassumption. eassumption.

  destruct Ho0 as (extp & Ho0).
  inverts Ht1. simpls. inverts H.
  inverts Ht2. simpls. inverts~ H.
  applys* red_prog_app_abort. introv Hyp; inverts Hyp.
  inverts H0. false*. inverts H0. false*. inverts H0. false*.
  inverts Ho0. inverts H0. inverts H4. false*.
  inverts Ho0. inverts H0. inverts H1. false*.
  inverts Ho0. inverts H0. inverts H1. false*.  
Qed.

Lemma red_prog_app_main_decomposition : forall els str S C o el0 el1,
  els = (el0 ++ el1)%list -> 
  red_prog_app S C (prog_intro str els) o ->
    exists o0, red_prog_app S C (prog_app_main (out_ter S resvalue_empty) el0) o0 /\
               red_prog_app S C (prog_app_main o0 el1) o.
Proof with (try match goal with 
             | H : out_of_ext_prog_app _ = _ |- _ => try solve [simpls; inverts* H] 
            end).
  induction els using (measure_induction length); introv Heq Hr.

  destruct el0 as [ | e0]. rewrite app_nil_l in Heq; subst.
  exists (out_ter S resvalue_empty). splits.
  apply red_prog_app_nil. inverts~ Hr... 
  destruct el1 as [ | e1]. rewrite app_nil_r in Heq; subst.
  exists o. splits. inverts~ Hr...

  admit.

(*  
  apply red_prog_app_characterization in Hr. inverts Hr as Hr.
  destruct Hr as (S' & rv & Heq); subst. apply red_prog_app_nil.
  destruct Hr as (extp & Heq). applys* red_prog_app_abort.
  introv Hyp; inverts Hyp. *)

  inverts Hr... inverts H5.
  simpls. inverts H0. inverts H1. false*.
  apply nil_eq_app_inv in H0. inverts H0. inverts H1.

  Focus 2. rewrite app_cons in H0. inverts H0.
  destruct el0. rewrite app_nil_l in H3. inverts H3.
  rewrite app_cons in H3. inverts H3.

  Focus 2. rewrite app_cons in H0. inverts H0.
  destruct el0. rewrite app_nil_l in H3. inverts H3.
  rewrite app_cons in H3. inverts H3.
  
  assert (Hl0 : length (e0 :: el0) > 0) by (rew_length; nat_math).
  assert (Hl1 : length (e1 :: el1) > 0) by (rew_length; nat_math).
  remember (e0 :: el0) as el0'. clear dependent e0. clear dependent el0.
  remember (e1 :: el1) as el1'. clear dependent e1. clear dependent el1.
  lets Hdec : lt_eq_lt_dec (length el0') (length el2).
  inverts Hdec as Hdec. inverts Hdec as Hdec.

  assert (exists el', el2 = (el0' ++ el')%list).
  {
    clear - H0 Hdec. gen el2 el3 el1'. 
    induction el0' using (measure_induction length). 
    destruct el0'; introv Hl Heq.
    
    + exists el2. rewrite~ app_nil_l.
    + destruct el2. rew_length in *. nat_math.
      do 2 rewrite app_cons in Heq. inverts Heq.
      specializes H H2. rew_length; nat_math.
      rew_length in *; nat_math.
      destruct H as (el' & Heq); subst.
      eexists. rewrite app_cons. fequals.
  } destruct H1 as (el' & Heq); subst.

  assert (el1' = (el' ++ el3)%list).  
  {
    rewrite app_assoc in H0. clear - H0.
    inductions el0'. repeat rewrite~ app_nil_l in H0.
    repeat rewrite app_cons in H0. inverts H0.
    applys* IHel0'.
  } subst. clear H0.

  assert (Hl' : length el' > 0) by (rew_length in *; nat_math). clear Hdec Hl1 H4.
  
  apply red_prog_app_main with (str := str) in H10.
  lets IH : H H10. rew_length; nat_math. reflexivity.
  destruct IH as (o0 & Ht0 & Ht1). exists o0; splits*.
  eapply red_prog_app_composition; try eassumption.

  

Admitted.


(**************************************************************)
(** ** Connecting append and specification                    *)

Lemma red_prog_red_prog_app_aux : forall (e : element) S C o1 o,
   red_prog S C (prog_1 o1 e) o <-> red_prog_app S C (prog_app_main o1 (e :: nil)) o.
Proof.
  introv; splits; destruct e as [t | name args bd]; introv Hr; inverts Hr.
  
  + simpls. inverts H.
    applys* red_prog_app_abort.
    introv Hyp. inverts Hyp.

  + inverts H5. simpls. inverts H.
    eapply red_prog_app_stat; try eassumption.
    applys* red_prog_app_abort. introv Hyp; apply H1.
    inverts Hyp. constructor.
    applys* red_prog_app_stat. applys* red_prog_app_rewrite.

  + simpls. inverts H.
    applys* red_prog_app_abort. 
    introv Hyp; inverts Hyp.

  + apply red_prog_app_funcdecl.
    
  + simpls. inverts H.
    applys* red_prog_abort.
    introv Hyp; inverts Hyp.

  + destruct el1. false; rew_length in *; nat_math.
    rewrite app_cons in H1. inverts H1.
    apply nil_eq_app_inv in H4. inverts H4; substs.
    rew_length in *; nat_math.

  + inverts H5; simpls. 
    inverts H; eapply red_prog_1_stat; try eassumption.
    applys* red_prog_abort. introv Hyp; apply H1.
    inverts Hyp. constructor.
    eapply red_prog_1_stat; try eassumption.
    applys~ red_prog_2.

  + simpls. inverts H.
    applys* red_prog_abort.
    introv Hyp; inverts Hyp.

  + destruct el1. false; rew_length in *; nat_math.
    rewrite app_cons in H1. inverts H1.
    apply nil_eq_app_inv in H4. inverts H4; substs.
    rew_length in *; nat_math.

  + apply red_prog_1_funcdecl.
Qed.

Theorem red_prog_equiv_red_prog_app : forall p S C o,
  red_prog S C p o <-> red_prog_app S C p o.
Proof.

  introv; splits.

  (* -> *)
  destruct p as (str & els). gen str S C o. 
  induction els using (measure_induction length). 
  destruct els; introv Hr.
  
  (* Empty program *)
  inverts Hr. 
  simpls. inverts H0.
  apply red_prog_app_main. apply red_prog_app_nil.
  apply last_eq_nil_inv in H1. false.

  (* Less empty program *)
  lets Hyp : list_characterize_tail (e :: els).
  inverts Hyp as Hyp. inverts Hyp.
  destruct Hyp as (e' & l & Heq).
  rewrite Heq in *; clear dependent e; clear dependent els.
  inverts Hr. simpls. inverts H0.
  apply nil_eq_last_inv in H4. false~.
  apply last_eq_last_inv in H1. destruct H1; subst.
  rewrite red_prog_red_prog_app_aux in H6.
  specializes H (rm H4). rew_length; nat_math.
  destruct l. inverts H. simpls. inverts H0. 
  inverts H5. simpls. inverts H.
  inverts H0. false*.     
  unfold append; simpls~. applys* red_prog_app_main.    
  apply nil_eq_app_inv in H2. inverts H2; substs.
  rew_length in *; nat_math.
  apply red_prog_app_main. eapply red_prog_app_split.
  reflexivity. rew_length; nat_math. rew_length; nat_math.
  inverts H. simpls. inverts H0. eassumption. auto.

  (* <- *)
  destruct p as (str & els). gen str S C o. 
  induction els using (measure_induction length). 
  destruct els; introv Hr.

  (* Empty program *)
  inverts Hr. simpls; inverts H0.
  inverts H5. simpls. inverts H0. 
  inverts H1. false*.
  apply red_prog_nil.
  apply nil_eq_app_inv in H3. inverts H3; substs.
  rew_length in *; nat_math.
  
  (* Less empty program *)
  inverts Hr. simpls. inverts H0.
  inverts H5. simpls. inverts H0.
  inverts H1. false*.

  lets Hyp : list_characterize_tail (e :: els).
  inverts Hyp as Hyp. inverts Hyp.
  destruct Hyp as (e' & l & Heq).
  rewrite Heq in *; clear dependent e; clear dependent els.

  assert (Hneql : l <> nil).
  {
    destruct l. 
    unfold append in H3 at 1. simpls.
    destruct el1; destruct el2.
    rewrite app_nil_l in H3. inverts H3.
    rewrite app_nil_l in H3. inverts H3.
    rew_length in *; nat_math.
    rewrite app_cons in H3. inverts H3. 
    rewrite app_nil_r in H2. subst.
    rew_length in *; nat_math.
    rewrite app_cons in H3. inverts H3.
    destruct el1. rewrite app_nil_l in H2. inverts H2.
    rewrite app_cons in H2. inverts H2.
    introv Hyp; inverts Hyp.
  }

  assert (exists o2, red_prog_app S C (prog_app_main (out_ter S resvalue_empty) l)

  


  replace (element_func_decl name args bd :: nil) with (nil & element_func_decl name args bd) by (unfold append; simpls~).  
  eapply red_prog_cons. apply red_prog_nil.
  apply red_prog_1_funcdecl.

  replace (element_stat t :: nil) with (nil & element_stat t) by (unfold append; simpls~).  
  eapply red_prog_cons. apply red_prog_nil.
  eapply red_prog_1_stat; try eassumption.
  inverts H9. simpls. inverts H0.
  applys* red_prog_abort. introv Hyp; apply H2.
  inverts Hyp; constructor.
  applys~ red_prog_2.
Qed. *)
