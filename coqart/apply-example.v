Section Apply_example.

Variables P Q R T : Prop.

Theorem apply_example : (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
Proof.
  intros H H0 p.
  apply H.
  exact (H0 p).
Qed.

End Apply_example.
