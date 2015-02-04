Require Tracejs.

Section test.
  Variable A B C D G : Prop.
  Hypothesis H : A -> B -> C -> D.
    Goal G.
    tracejs "Test goal G".
    tracejs_hyp H.
  Abort.
End test.

