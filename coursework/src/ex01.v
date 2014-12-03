(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 1 (Propositional logic)
    published 13/10/14, deadline 20/10/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex01.v. 

    Try to fill in the missing proofs, using only the basic tactics
    presented in the first lectures, i.e. exact, intro(s), apply,
    destruct, left, right, split and assert. You are not permitted to
    use to any lemmas from the prelude or the standard library.
    Please only use the tactics in the way indicated in the script,
    otherwise you may loose upto 2 style points. A proof should always
    end with "Qed." At the end of the file, the section should end
    with "End Ex1."  and the whole file including this line has to be
    accepted by Coq.

    You can get 10 points, 1 point for each proof.

    Good luck!
    @author: Barnabas Forgo (bxf03u)
**)

Section Ex1.

Variables P Q R : Prop.

Lemma l01 : P -> Q -> P.
intros p q.
exact p.
Qed.

Lemma l02 : (P -> Q -> R) -> (Q -> P -> R).
intros pqr.
intros q p.
apply pqr.
exact p.
exact q.
Qed.

Lemma l03 : P <-> True /\ P.
split.
intro p.
split.
split.
exact p.
intro tp.
destruct tp as [t p].
exact p.
Qed.

Lemma l04 : P <-> False \/ P.
split.
intro p.
right.
exact p.
intro fp.
destruct fp as [f | p].
destruct f.
exact p.
Qed.

Lemma l05 : (P -> Q /\ R) <-> (P -> Q) /\ (P -> R).
split.
intro h.
split;
intro p;
apply h;
exact p.
intros pqpr p.
split.
destruct pqpr as [pq pr].
apply pq.
exact p.
destruct pqpr as [pq pr].
apply pr.
exact p.
Qed.

Lemma l06 : (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
split.
intros pqr.
split.
intro p.
apply pqr.
left.
exact p.
intro q.
apply pqr.
right.
exact q.
intros prqr pq.
destruct prqr as [pr qr].
destruct pq as [p | q].
apply pr.
exact p.
apply qr.
exact q.
Qed.

Lemma l07 : ~(P /\ ~P).
intro pnp.
destruct pnp as [p np].
apply np.
exact p.
Qed.

Lemma l08 : P -> ~~P.
intro p.
intro np.
apply np.
exact p.
Qed.

Lemma l09 : ~~(P \/ ~P).
intro.
apply H.
right.
intro p.
apply H.
left.
exact p.
Qed.

Lemma l10 : ~~(~~P -> P).
unfold not.
intro a.
apply a.
intro pff.
assert (f : False).
apply pff.
intro p.
apply a.
intro pfff.
exact p.
destruct f.
Qed.

End Ex1.
