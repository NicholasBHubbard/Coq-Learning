Section First_proofs.

Variables P Q R T : Prop.

Lemma id_P : P -> P.
Proof.
  intros p.
  assumption.
Qed.

Lemma id_PP : (P -> P) -> (P -> P).
Proof.
  intros H p.
  assumption.
Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H0 H1 p.
  apply H1.
  apply H0.
  assumption.
Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros H0 H1 p.
  apply H0.
  apply p.
  apply H1.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros H p q.
  apply H.
  assumption.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros H p.
  apply H.
  assumption.
  assumption.
Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof.
  intros H0 p.
  apply H0.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros H0 H1 H2 p.
  apply H2.
  apply H0.
  assumption.
  apply H1.
  assumption.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros H0.
  apply H0.
  intros H1.
  apply H1.
  intros p.
  apply H0.
  intros H2.
  apply H2.
  intros p'.
  apply H0.
  intros p''.
  assumption.
Qed.

end First_proofs.
