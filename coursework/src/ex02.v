(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 2 (Classical vs Intuitionistic Logic)
    published 20/10/14, deadline 27/10/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex02.v. 

    Consider the following propositions

    p01 : ~~~P -> ~P
    p02 : ~P -> ~~~P
    p03 : P \/ ~~P
    p04 : ~(P <-> ~P)
    p05 : (P -> Q) -> ~P \/ Q
    p06 : ~P \/ Q -> (P -> Q)
    p07 : ~(P \/ Q) -> ~P /\ ~Q
    p08 : ~P /\ ~Q -> ~(P \/ Q)
    p09 : ~(P /\ Q) -> ~P \/ ~Q
    p10 : ~P \/ ~Q -> ~(P /\ Q)

    We play the game of logic poker :-)

    You have to classify the propositions into
    a) provable intuitionistically (i.e. in plain coq)
    b) provable classically (using classic : P \/ ~P or NNPP : ~~P -> P).
    c) not provable classically.
    and then you have to prove the propositions in a) and b) accordingly.

    Here is how you score:
    We start with 10 points :-)
    For any proposition which you didn't classify correctly (or not at all)
    you loose 1 point. :-(
    For any proposition which is provable but you didn't prove you loose
    1 point. :-(
    We stop subtracting points at 0. :-)

    You are only allowed to use the tactics introduced in the lecture
    (i.e.  exact, intro(s), apply, destruct, left, right, split,assert,
    unfold and exfalso).

    Please only use the tactics in the way indicated in the script,
    otherwise you may loose upto 2 style points. A proof should always
    end with "Qed." At the end of the file, the section should end
    with "End Ex2."  and the whole file including this line has to be
    accepted by Coq.

    If you want to classify a proposition into a section but you are 
    unable to prove it then put it there in comments. This applies in 
    particular to section c. In any case make sure that the file as 
    a whole is accepted by coq.

    Good luck!
**)

(*@author: Barnabas Forgo //bxf03u*)

Section Ex2.

Variables P Q R : Prop.

(* a *)

Lemma p01 : ~~~P -> ~P.
intro nnnp.
intro p.
apply nnnp.
intro np.
apply np.
exact p.
Qed.

Lemma p02 : ~P -> ~~~P.
intros np nnp.
apply nnp.
exact np.
Qed.

Lemma p04 : ~(P <-> ~P).
intro h.
destruct h as [pnp npp].
apply pnp;
apply npp;
intro p;
apply pnp;
exact p;
exact p.
Qed.

Lemma p06 : ~P \/ Q -> (P -> Q).
intros npq p.
destruct npq as [np | q].
exfalso.
apply np.
exact p.
exact q.
Qed.

Lemma p07 : ~(P \/ Q) -> ~P /\ ~Q.
intro npq.
split.
intro p.
apply npq.
left.
exact p.
intro q.
apply npq.
right.
exact q.
Qed.

Lemma p08 : ~P /\ ~Q -> ~(P \/ Q).
intros npnq pq.
destruct npnq as [np nq].
destruct pq as [p | q].
apply np.
exact p.
apply nq.
exact q.
Qed.

(* b *)

Require Import Coq.Logic.Classical.

Lemma p05 : (P -> Q) -> ~P \/ Q.
(*apply imply_to_or. Qed.*)
intro pq.
destruct (classic P) as [p | np].
right.
apply pq.
exact p.
left.
exact np.
Qed.

Lemma p09 : ~(P /\ Q) -> ~P \/ ~Q.
(*apply not_and_or. Qed.*)
destruct (classic P) as [p | np].
intro npq.
right.
intro q.
apply npq.
split.
exact p.
exact q.
intro npq.
left.
exact np.
Qed.

Lemma p10 : ~P \/ ~Q -> ~(P /\ Q).
(*apply or_not_and. Qed.*)
intros npnq pq.
destruct pq as [p q].
destruct npnq as [np | nq].
apply np.
exact p.
apply nq.
exact q.
Qed.

(* c *)

(*Lemma p03 : P \/ ~~P.*)

End Ex2.
