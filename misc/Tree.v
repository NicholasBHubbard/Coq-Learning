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

Theorem count_length_traversal:
  forall (A : Set) (t : binary_tree A), count A t = length (traverse_preorder A t).
Proof.
  intros.
  induction t.
  { simpl.
    trivial.
  }
  {
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    rewrite length_app.
    trivial.
  }
Qed.

End Binary_Tree.
