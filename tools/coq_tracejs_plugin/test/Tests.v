Require Tracejs.

Section test.
  Theorem plus_n_0 : forall m n : nat,
    m = n -> m + m = n + n.
  Proof.
    intros m n HR.
    tracejs_hyp HR.
    tracejs_code.       (* Expects n *)
    tracejs_code HR.    (* Expects n *)
    tracejs_code <- HR. (* Expects m *)
    tracejs_code -> HR. (* Expects n *)
    tracejs_code m.     (* Expected no output -- error case *)
  Abort.
End test.

