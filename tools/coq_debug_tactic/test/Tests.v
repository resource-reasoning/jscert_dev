Add Rec LoadPath "../src/" as Debug.
Add ML Path "../src/".

Require Debug.

Section test.
  Variable A B C D G : Prop.
  Hypothesis H : A -> B -> C -> D.
    Goal G.
    Show Proof.
    debug.
  Abort.
End test.

