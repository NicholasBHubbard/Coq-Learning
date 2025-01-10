Section Nat_proofs.

Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint add (a b: nat) : nat :=
  match a with
  | O => b
  | S n => add n (S b)
  end.

Theorem add_O_id : forall n, add O n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


End Nat_proofs.
