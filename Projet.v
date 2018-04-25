(**Les entiers binaires*)

Inductive bin : Set :=
|Zero : bin
|Double : bin -> bin
|DoubleOne : bin -> bin.



(** question 1*)


(** g équivalent à une fonction bin to nat*)

Fixpoint g (n : bin) := match n with
  |Zero => 0
  |Double n => (g n) + (g n)
  |DoubleOne n => (g n) + (g n)+1
end.




Print well_founded.
Print Acc.
Print lt.



Fixpoint Succ (x : bin) := match x with
  |Zero => DoubleOne Zero
  |Double x => DoubleOne x
  |DoubleOne x => Double (Succ x)
end.




Fixpoint f (n : nat) := match n with
  |O => Zero
  |S m => Succ (f m)
end.


Eval compute in g (f 5).

(**question 2*)
Require Import Omega.



Lemma inter1 : forall (n:bin), g (Succ n) = S ( g n ).
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  omega.
  simpl.
  rewrite IHn.
  omega.
Qed.



Lemma composition : forall (n : nat), g(f(n)) = n.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  rewrite inter1.
  rewrite IHn.
  reflexivity.
Qed.


(**question 3*)

Eval compute in f (g (Double(Double Zero))).


Fixpoint h (b : bin) := match b with
  |Zero => Zero
  |Double Zero => Zero
  |Double b => match (h b) with 
                     |Zero => Zero
                     |_ => Double (h b)
               end
  |DoubleOne b => DoubleOne (h b)
end.

Eval compute in h (Double(DoubleOne(Double(Double Zero)))).
Eval compute in g(h(Double(DoubleOne(Double(Double Zero))))).
Eval compute in g(Double(DoubleOne(Double(Double Zero)))).
Eval compute in f(g(h(Double(DoubleOne(Double(Double Zero)))))).

(*question 4*)

Lemma inter2 : forall (b:bin), g b = g (h b).
Proof.
induction b.
- reflexivity.
- simpl.
  destruct (h b).
  + rewrite IHb.
    destruct IHb.
Qed.


Lemma inter3 :  forall (b:bin), b = Zero -> h (Double b) = Zero.
Proof.
  intro b.
  induction b.
  reflexivity.
  easy.
  simpl.
  easy.
Qed.

Lemma inter11 : forall (b:bin), Double b = h (Double b).
Proof.
intros.
induction b.
- simpl.
  + .
Qed.


Lemma fsteq : forall (b : bin), g b = g (h b).
Proof.
  induction b.
  - easy.
  - now apply inter3.


 -simpl.
  rewrite IHb.
  destruct (h b).
  simpl.
  
Qed.






Lemma inter5 : forall (b:bin), b = h b.
Proof.
  intros.
  induction b.
  reflexivity.
  rewrite IHb.
  rewrite inter3.


 Qed.



Lemma inter4 : forall (b:bin), Succ b = h (Succ b).
Proof.
  intros.
  induction b.
  reflexivity.
  simpl.
  
  .
Qed.







Lemma inter2 : forall (b:bin), Succ (h b) = h (Succ b).
Proof.
  intro b.
  induction b.
  reflexivity.
  destruct ( h (Double b)) eqn:hyp.
Qed.


