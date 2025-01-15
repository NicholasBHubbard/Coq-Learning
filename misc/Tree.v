Require Import List.

Section Binary_Tree.

Inductive binary_tree (A : Set) : Set :=
  | Leaf (v : A) : binary_tree A
  | Node (v : A) (lchild : binary_tree A) (rchild : binary_tree A) : binary_tree A.

Fixpoint traverse_preorder (A : Set) (t : binary_tree A) : list A :=
  match t with
    | Leaf _ val => cons val nil
    | Node _ val lchild rchild => (val :: nil) ++ (traverse_preorder A lchild) ++ (traverse_preorder A rchild)
  end.

Fixpoint traverse_inorder (A : Set) (t : binary_tree A) : list A :=
  match t with
    | Leaf _ val => val :: nil
    | Node _ val lchild rchild => (traverse_inorder A lchild) ++ (val :: nil) ++ (traverse_inorder A rchild)
  end.

Fixpoint traverse_postorder (A : Set) (t : binary_tree A) : list A :=
  match t with
    | Leaf _ val => val :: nil
    | Node _ val lchild rchild => (traverse_postorder A lchild) ++ (traverse_postorder A rchild) ++ (val :: nil)
  end.

Fixpoint count (A : Set) (t : binary_tree A) : nat :=
  match t with
    | Leaf _ _ => 1
    | Node _ _ lchild rchild => 1 + count A lchild + count A rchild
  end.

Lemma length_cons : forall (A : Set) (l : list A) a, length (a :: l) = S (length l).
Proof.
  intros A l a.
  simpl.
  trivial.
Qed.

Lemma length_cons_nil : forall (A : Set) (a : A), length (a :: nil) = 1.
Proof.
  auto.
Qed.

Lemma S_plus_1 : forall n : nat, S n = n + 1.
Proof.
  intros n.
  induction n as [| n' IHn].
  - trivial.
  - simpl.
    auto.
Qed.

Theorem eq_length_traversals:
  forall (A : Set) (t : binary_tree A),
    length (traverse_preorder A t) = length (traverse_inorder A t) /\
    length (traverse_inorder  A t) = length (traverse_postorder A t).
Proof.
  intros A t.
  split.
  induction t.
  - simpl.
    trivial.
  - simpl.
    repeat rewrite length_app.
    rewrite length_cons.
    rewrite IHt1.
    rewrite IHt2.
    auto.
  - induction t.
    simpl.
    trivial.
    simpl.
    repeat rewrite length_app.
    rewrite IHt1.
    rewrite <- IHt2.
    rewrite length_cons.
    rewrite length_cons_nil.
    rewrite S_plus_1.
    trivial.
Qed.

Theorem count_length_traversal:
  forall (A : Set) (t : binary_tree A),
    count A t = length (traverse_preorder A t).
Proof.
  intros A t.
  induction t.
  - simpl.
    trivial.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    rewrite length_app.
    trivial.
Qed.

End Binary_Tree.
