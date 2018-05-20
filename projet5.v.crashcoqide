(*rajouter la logique classique*)

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
 ~(A /\ B) -> ~A \/ ~B    : faux en logique intuitionniste mais prouvable en coq
 ~A \/ ~B -> ~(A /\ B)
*)



(*le principe des tiroirs*)

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

Lemma proofDrawers : forall X l0 l1, drawers X l0 l1.
(*Proof.
intros.
unfold drawers.
intro H.
destruct H.
induction l1.
- .
Qed.*)

(*question 4*)







Lemma drawertohyp (X: Type) (l0 l1 : list X) : (sharesElements X l0 l1) /\ ((length l1) < (length l0)) -> repeats l0.
Proof.
intros.
destruct H.
induction l0.
- easy.
- destruct H0.
  + destruct IHl0.
    .

Qed.





















