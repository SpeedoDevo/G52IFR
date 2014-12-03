(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 3 (Predicate logic)
    published 24/10/14, deadline 3/11/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex03.v. 

    This exercise has 2 parts. In the 1st part you are supposed to
    formally define what certain relation bewteen humans are (like
    Father. brother-in-law etc). Here we use Coq only as a syntax checker. 
    In the 2nd part we play logic poker again :-) but this time for
    predicate logic. 

    You are only allowed to use the tactics introduced in the lecture
    (i.e.  exact, intro(s), apply, destruct, left, right, split,assert,
    unfold, exists and exfalso).

    Please only use the tactics in the way indicated in the script,
    otherwise you may loose upto 2 style points. A proof should always
    end with "Qed." At the end of the file, the section should end
    with "End Ex3."  and the whole file including this line has to be
    accepted by Coq.

**)

Section Ex3.

(** PART 1 (50 %) **)

Section Relations.

(* We assume as given a set of people *)
Variable People : Set.

(* And we assume that we have predicated telling us who is female and who is male. 
   Yes we should assume 
   forall x:People, ~(Male x /\ Female x)
   but we won't be concerned with this now. *)
 
Variables Male Female : People -> Prop.
(* Male x = x is a male
   Female x = x is a female
*)

(* We also assume that we know who is the Parent of whom.
   Again there are a number of conditions like 
   forall x:People,~Parent(x,x)
   but we are going to ignore them. *)
Variable Parent : People -> People -> Prop.
(* Parent x y = x is the parent of y *)

(* And we know who is married to whom *)
Variable Married : People -> People -> Prop.
(* Married x y = x is married to y *)

(** Define the following relations:
   - Mother
   - Sister
   - Halfbrother
   - Grandmother
   - FatherInLaw
   - SisterInLaw
   - Aunt
you are encourange to use auxilliary definitions to 
avoid having to repeat definitions. 

If you are unsure about the precise meaning of these words
then look them up using wiktionary, e.g. 
http://en.wiktionary.org/wiki/half_sister

As an example we define Father:
*)
Definition Father (x y : People) :=
  Male x /\ Parent x y.

Definition Mother (x y : People) :=
  Female x /\ Parent x y.

Definition ShareMother (x y : People) :=
  exists a : People, Mother a x /\ Mother a y.

Definition ShareFather (x y : People) :=
  exists a : People, Father a x /\ Father a y.

Definition Sibling (x y : People) :=
  ShareMother x y /\ ShareFather x y /\ ~(x = y).

Definition Sister (x y : People) :=
  Female x /\ Sibling x y.

Definition Halfbrother (x y : People) :=
  Male x /\ (ShareFather x y \/ ShareMother x y).

Definition Grandmother (x y : People) :=
  exists a : People, Mother x a /\ Parent a y.

Definition FatherInLaw (x y : People) :=
  exists a : People, Father x a /\ Married a y.

Definition SisterInLaw (x y : People) :=
  exists a : People, (Sister x a /\ Married a y) \/ (Female x /\ Married x a /\ Sibling a y).

Definition Aunt (x y : People) :=
  exists a : People, (Sister x a /\ Parent a y) \/ (SisterInLaw x a /\ Parent a y).


End Relations.

(** PART 2 (50 %) **)
Section Poker.

(* We assume as given some sets, a predicate and a relation. *)

Variable A B  : Set.
Variable P : A -> Prop.
Variables R : A -> B -> Prop.

(*
    Consider the following propositions

    p01 : (forall x:A, exists y : B, R x y) -> exists y : B, forall x : A, R x y
    p02 : (exists x : A,forall y : B, R x y) -> forall y : B, exists x : A, R x y
    p03 : (~ exists x : A, P x) -> forall x:A , ~ P x
    p04 : (forall x:A , ~ P x) -> ~ exists x : A, P x
    p05 : (~ forall x : A, P x) -> exists x : A, ~ P x
    p06 : (exists x : A, ~ P x) -> ~ forall x : A, P x
    p07 : ~~(forall x:A,P x) -> forall x:A,~~(P x)
    p08 : (forall x:A,~~(P x)) -> ~~(forall x:A,P x)
    p09 : (exists x:A, True) -> (exists x:A, P x) -> forall x:A, P x.
    p10 : (exists x:A, True) -> exists x:A, P x -> forall x:A, P x.

    To remind you of the rules of logic poker:

    You have to classify the propositions into
    a) provable intuitionistically (i.e. in plain coq)
    b) provable classically (using classic : P \/ ~P or NNPP : ~~P -> P) but not intuitionistically.
    c) not provable classically.
    and then you have to prove the propositions in a) and b) accordingly.

    Here is how you score:
    We start with 10 points :-)
    For any proposition which you didn't classify correctly (or not at all)
    you loose 1 point. :-(
    For any proposition which is provable but you didn't prove you loose
    1 point. :-(
    We stop subtracting points at 0. :-)

    If you want to classify a proposition into a section but you are 
    unable to prove it then put it there in comments. This applies in 
    particular to section c. In any case make sure that the file as 
    a whole is accepted by coq.

    Good luck!
**)


(* a *)

Lemma p02 : (exists x : A,forall y : B, R x y) -> forall y : B, exists x : A, R x y.
intros H y.
destruct H as [a r].
exists a.
apply r.
Qed.

Lemma p03 : (~ exists x : A, P x) -> forall x:A , ~ P x.
intros H y.
intro.
apply H.
exists y.
exact H0.
Qed.

Lemma p04 : (forall x:A , ~ P x) -> ~ exists x : A, P x.
intros.
intro.
destruct H0.
assert (np: ~P x).
apply H.
apply np.
exact H0.
Qed.

Lemma p06 : (exists x : A, ~ P x) -> ~ forall x : A, P x.
intros.
intro.
destruct H.
apply H.
apply H0.
Qed.

Lemma p07 : ~~(forall x:A,P x) -> forall x:A,~~(P x).
intros.
intro.
apply H.
intro.
apply H0.
apply H1.
Qed.

(* b *)

Require Import Coq.Logic.Classical.

Lemma p05 : (~ forall x : A, P x) -> exists x : A, ~ P x.
intros.
apply NNPP.
intro ne.
apply H.
intro a.
apply NNPP.
intro np.
apply ne.
exists a.
exact np.
Qed.

Lemma p08 : (forall x:A,~~(P x)) -> ~~(forall x:A,P x).
intros.
intro.
apply H0.
intro.
apply NNPP.
apply H.
Qed. (*b*)

Lemma p10 : (exists x:A, True) -> exists x:A, P x -> forall x:A, P x.
intros ne.
destruct (classic (forall x:A,P x)) as [alld | nalld].
destruct ne as [x _].
exists x.
intros px y.
apply alld.
assert (H : exists x:A, ~P x).
apply NNPP.
intro nne.
apply nalld.
intro a.
apply NNPP.
intro np.
apply nne.
exists a.
exact np.
destruct H as [tt nd].
exists tt.
intros ptt x.
assert (ic : False).
apply nd.
apply ptt.
destruct ic.
Qed.

(* c *)

(*
Lemma p01 : (forall x:A, exists y : B, R x y) -> exists y : B, forall x : A, R x y.

Lemma p09 : (exists x:A, True) -> (exists x:A, P x) -> forall x:A, P x.
*)

End Poker.

End Ex3.
