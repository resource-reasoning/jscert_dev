Require Tracejs.

Section test.
  Theorem plus_n_0 : forall m n : nat,
    n = m -> n + n = m + m.
  Proof.
    intros n m H.
    tracejs_hyp H.
    tracejs_code H.    (* Expects n *)
    tracejs_code lhs H.(* Expects n *)
    tracejs_code rhs H.(* Expects m *)
    tracejs_code m.    (* Expected no output -- error case *)
  Abort.
End test.

