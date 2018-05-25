(**LES ENTIERS BINAIRES*)

Inductive bin : Set :=
|Zero : bin
|Double : bin -> bin
|DoubleOne : bin -> bin.



(*question 1*)


(*g équivalent à une fonction bin to nat*)

Fixpoint g (n : bin) := match n with
  |Zero => 0
  |Double n => (g n) + (g n)
  |DoubleOne n => (g n) + (g n)+1
end.


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

(*question 2*)
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


(*question 3*)

Eval compute in f (g (Double(Double Zero))).
(* f composée avec g ne donne pas l'identité,
 en effet les Doubles directement autour du Zero interne ne sont pas supprimés *)

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

(*Lemma inter2 : forall (b:bin), g b = g (h b).
Proof.
induction b.
- reflexivity.
- simpl.
  destruct (h b).
  + rewrite IHb.
    destruct IHb.
Qed.*)


Lemma inter3 :  forall (b:bin), b = Zero -> h (Double b) = Zero.
Proof.
  intro b.
  induction b.
  reflexivity.
  easy.
  simpl.
  easy.
Qed.


(*Lemma fsteq : forall (b : bin), g b = g (h b).
Proof.
  induction b.
  - easy.
  - now apply inter3.


 -simpl.
  rewrite IHb.
  destruct (h b).
  simpl.
  
Qed.
*)



(*Lemma inter5 : forall (b:bin), b = h b.
Proof.
  intros.
  induction b.
  reflexivity.
  rewrite IHb.
  rewrite inter3.


 Qed.
*)

(*Lemma inter2 : forall (b:bin), Succ (h b) = h (Succ b).
Proof.
  intro b.
  induction b.
  reflexivity.
  destruct ( h (Double b)) eqn:hyp.
Qed.*)












(**RAJOUTER LA LOGIQUE CLASSIQUE*)

Require Import Bool.

(*question 1*)
Definition pierce := forall (P Q : Prop), ((P -> Q) -> P) -> P.

Definition elimdoublneg := forall (P: Prop), ~~P -> P.

Definition tiersexclu := forall (P:Prop), ~P \/ P.

Definition implication := forall (P Q : Prop), (P -> Q) -> ~P \/ Q.

Definition demorgan := forall (P Q : Prop), ~(~P/\~Q) -> P\/Q.

Definition doubleneg := forall (P : Prop), (~P -> P) -> P.








(*Loi de Pierce => Double négation *)
Lemma one : pierce -> doubleneg.
Proof.
intros.
unfold pierce in H.
unfold doubleneg.
intro P.
intro hyp.
apply H with (Q:=False).
intro hyp1.
apply hyp.
assumption.
Qed.



(*Définition classique de l'implcation => le tiers-exclu*)
Lemma two : implication -> tiersexclu.
Proof.
intros.
unfold implication in H.
unfold tiersexclu.
intro P.
apply H.
intro hyp.
assumption.
Qed.


(* Double négation => Elimination de la double négation*)
Lemma three : doubleneg -> elimdoublneg.
Proof.
intros.
unfold doubleneg in H.
unfold elimdoublneg.
intro P.
intro hyp.
apply H.
intro hyp1.
apply hyp in hyp1.
easy.
Qed.




(* Le tiers-exclu => la loi de De Morgan *)
Lemma four : tiersexclu -> demorgan.
Proof.
intros.
unfold tiersexclu in H.
unfold demorgan.
intro P.
intro Q.
intro hyp.
pose proof (H P).
destruct H0.
pose proof (H Q).
destruct H1.
exfalso.
apply hyp.
split.
assumption.
assumption.
right.
assumption.
left.
assumption.
Qed.



(* La loi de De Morgan => la définition classique de l'implication*)
Lemma five1 : demorgan -> implication.
Proof.
intros.
unfold demorgan in H.
unfold implication.
intros.
apply H.
intro hyp.
destruct hyp.
apply H1.
intro hyp1.
apply H2.
apply H0 in hyp1.
easy.
Qed.



(* La loi de Pierce => l'élimination de la double négation*)
Lemma six : pierce -> elimdoublneg.
Proof.
intros A B H.
now apply A with False.
Qed.




(* Le tiers-exclu => la loi de Pierce*)
Lemma seven : tiersexclu -> pierce.
Proof.
intros hyp A B H.
destruct (hyp A).
+ now apply H.
+ easy.
Qed.




(* L'élimination de la double négationn => le tiers-exclu *)
Lemma eight : elimdoublneg -> tiersexclu.
Proof.
intros.
unfold elimdoublneg in H.
unfold tiersexclu.
intros.
apply (H (~P \/ P)).
intro hyp1.
cut (~~P /\ ~P).
- intro hyp2.
 now destruct hyp2.
- split; intro; apply hyp1.
 now left.
 now right.
Qed.


(*question 2*)

(*Les 4 implications de De Morgan sont les suivantes :
 ~(A \/ B) -> ~A /\ ~B
 ~A /\ ~B -> ~(A \/ B)
 ~(A /\ B) -> ~A \/ ~B    : faux en logique intuitionniste donc pas prouvable en Coq
 ~A \/ ~B -> ~(A /\ B)    : 
*)


Definition deMorgan1 := forall (P Q : Prop), ~(P /\ Q ) <-> ~P \/ ~ Q.
Definition deMorgan2 := forall (P Q : Prop), ~(P \/ Q ) <-> ~P /\ ~Q.


Lemma deMorgan_equi : deMorgan2.
Proof.
unfold deMorgan2.
split.
- intros.
  split.
  + intro; apply H; left; easy.
  + intro; apply H; right; easy.
- intros.
  destruct H.
  intro.
  destruct H1.
  now apply H in H1.
  now apply H0 in H1.
Qed.

Lemma deMorgan1_notdirect : forall (P Q : Prop), ~P \/ ~Q -> ~(P /\ Q).
Proof.
intros.
destruct H.
- intro H0.
  apply H.
  destruct H0.
  easy.
- intros H0.
  apply H.
  destruct H0.
  easy.
Qed.


(* question 3 *)

(* ~(P /\ Q ) -> ~P \/ ~ Q  est faux en logique intuitionniste, de ce fait,
   cette implication n'est pas prouvable en Coq*)

(* question 4 *)

(* question 5 *)














(**LE PRINCIPE DES TIROIRS*)

Require Import List.

(*question 1*)


Inductive repeats {X : Type} : list X -> Prop :=
  |l : forall (x : X) (l1 : list X), (In x l1) -> (repeats (x::l1))
  |l0 :forall (x : X) (l1 : list X), (repeats l1) -> (repeats (x::l1)).


(*question 2*)

(*l0 partage un ou plusieurs élément(s) avec l1  *)
Definition sharesElements (X : Type) (l0 l1 : list X) := (forall n : X, (In n l0) -> (In n l1)).
Definition drawers (X : Type) (l0 l1 : list X) := (sharesElements X l0 l1) /\ ((length l1) < (length l0)) -> repeats l0.

(*question 3*)

Axiom tiersExclu : tiersexclu.


Lemma deleteLists : forall (X:Type) (x a : X) (l1 l2: list X), x<>a -> In x (l1 ++ (a::l2)) -> In x (l1++l2).
Proof.
intros.
induction l1.
- simpl in H0.
  destruct H0.
  + symmetry in H0.
    contradiction.
  + simpl.
    easy.
- destruct (tiersExclu (a0 = x)).
  + right.
    apply IHl1.
    destruct H0.
    contradiction.
    easy.
  + left.
    easy.
Qed.



(* concatlists montre que, si x est dans une liste l, alors on peut réécrire l comme une liste concaténée à une autre liste, dont la tête est x *)

Lemma concatlists : forall (X: Type) (l : list X) (x : X), (In x l) -> (exists (l1 l2 : list X), l = l1++(x::l2)).
Proof.
intros.
induction l1.
- easy.
- destruct H.
  + rewrite H.
    (exists nil, l1).
    easy.
  + apply IHl1 in H.
    destruct H.
    destruct H.
    (exists (a::x0), x1).
    rewrite H.
    easy.
Qed.


(* Malgrè les lemmes intermédiaires, je ne suis pas parvenue à montrer le lemme des tiroirs non constructif*)


(*Lemma proofDrawers : forall X l0 l1, drawers X l0 l1.
Proof.
unfold drawers.
unfold sharesElements.
induction l1.
intros.
- easy.
- intros.
  destruct (tiersExclu (In a l1)).
   + right.
     destruct H.
     destruct H0.
     destruct H1.
     ++ pose proof concatlists.
        pose proof (H0 X l2 a).
        destruct H1.
        +++ . 


Qed.*)




(*question 4*)



Inductive noRepeats {X : Type } : list X -> Prop :=
| initialisation: noRepeats nil
| induction : forall x l, noRepeats l -> ~ In x l -> noRepeats (x::l).


Definition repeat (X :Type) (l : list X) := ~ noRepeats l.



Definition drawerConstr (X : Type) (l0 l1 : list X) := (sharesElements X l0 l1) -> ((length l1) < (length l0)) -> repeat X l0.


(* on utilise ce lemme pour montrer que si un élément x est dans une liste l,
 si on ajoute un nouvel élément à l, x est encore dans l*)
Lemma inclTriviale: forall (X: Type) (x n : X) (l : list X), (In x l) -> (In x (n::l)).
Proof.
intros.
simpl.
right.
easy.
Qed.


Axiom removeS : forall x y, x < S y -> x <= y.


Theorem drawerConstru : forall (X : Type) (l0 l1 : list X), drawerConstr X l0 l1.
Proof.
unfold drawerConstr.
unfold sharesElements.
intros.
induction l1.
- easy.
- unfold repeat.
  intros; intro.
  inversion H1.
  subst a.
  assert (H' := H).
  apply (concatlists X l2 x) in H'.
  destruct H' as [l4 [l5 H']].
  apply (IHl1).
  + intros.
    apply H.
    destruct H'.
    apply (inclTriviale X n x l1) in H2.
    easy.
  + rewrite H' in H0.
    simpl in H0.
    apply removeS in H0.
  +
  +
Qed.
(* pour les 2 subgoals qui restent: *)
(* noRepeats l1 se prouve directement par H4, de ce fait, easy suffit *)
(* In x (x :: l1) se démontre aussi quasi directement, car x::l1 contient x *)
















