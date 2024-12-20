Section Minimal_propositional_logic.

  Variables P Q R T : Prop.

  Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p.
    apply H'.
    apply H.
    assumption.
  Qed.

  Theorem imp_trans2 : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    auto.
  Qed.

End Minimal_propositional_logic.
