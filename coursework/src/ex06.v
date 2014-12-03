(** @author: Barnabas Forgo (bxf03u)
    Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 6 (Arithmetic)
    published 15/11/14, deadline 24/11/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex06.v. 

    This exercise has 2 parts. In the 1st part (60 %) you have to use
    induction to show some well-known properties of multiplication
    which entails together with what we have proven already in the
    lecture notes that the natural numbers with addition and
    multiplication form a semiring. In the 2nd part (40%) you have
    to show that the relation <= (less or equal) on the natural
    numbers is antisymmetric. Hence together with the properties we
    have already shown in the lecture (reflexive and transitive) we can
    conclude that <= is a partial order.

    We are using definitions and lemmas from the lecture notes (Arith.v). Hence 
    to solve this exercise download Arith.v and put it in the same directory as
    your solution. However, you are not supposed to change this file and you 
    don't need to submit it either.

    You may also use the pattern tactic in this coursework to focus the use of 
    rewrite. See the reference manual for details.
  
    You are only allowed to use the tactics introduced in the lecture
    (i.e.  exact, intro(s), apply, destruct, left, right, split,assert,
    unfold, exists, exfalso, reflexivity, rewrite, rewrite<-, discriminate,
    induction and pattern).
  
    Please only use the tactics in the way indicated in the script,
    otherwise you may loose up to 2 style points. A proof should always
    end with "Qed." At the end of the file, the section should end
    with "End Ex6."  and the whole file including this line has to be
    accepted by Coq. If necessary comment out parts you cannot prove.

    Good luck!
**)

Section Ex6.

(** We are using all the results from the lecture. *)
Load Arith.

(** PART 1 (60 %) **)

Section Semiring.
(*
Complete showing that nat with + and * forms a semiring by proving the following theorems.

Hints:
- you can use the results from Arith
- you may have to prove auxilliary results (lemmas)
- you may need to prove the theorems in a particular order 
  (you are allowed to reorder).
- the following tactics may be helpful:
  symmetry : turns an equation around.
  pattern t : focusses the next rewrite on a particular subterm.
  pattern t at n : focusses rewrite on the nth occurence of a subterm.
*)
Theorem mult_0_l : forall n, 0 * n = 0.
intro.
simpl.
reflexivity.
Qed.

Theorem mult_0_r : forall n, n * 0 = 0.
intro.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem mult_1_l : forall n, 1 * n = n.
intro.
simpl.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem mult_1_r : forall n, n * 1 = n.
intro.
simpl.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem mult_plus_distr_l : forall n m p, n * (m + p) = n * m + n * p.
intros.
induction n.
simpl.
reflexivity.

simpl.
rewrite IHn.
rewrite plus_assoc.
symmetry.
rewrite<- plus_assoc.
pattern (n * m + (p + n * p)).
rewrite plus_comm.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite<- plus_assoc.
pattern (n * p + n * m).
rewrite plus_comm.
rewrite plus_assoc.
reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p, (n + m) * p = n * p + m * p.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
rewrite plus_assoc.
reflexivity.
Qed.

Theorem mult_assoc : forall n m p, n * (m * p) = n * m * p.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
rewrite<- mult_plus_distr_r.
reflexivity.
Qed.

Lemma help : forall m n, m = n -> S m = S n.
intros m n e.
rewrite e.
reflexivity.
Qed.

Lemma help2 : forall m n : nat, m + (m * n) = m * S n.
intros.
induction m,n; simpl.

reflexivity.

reflexivity.

apply help.
pattern (m * 0).
rewrite mult_0_r.
rewrite<- plus_n_0.
rewrite mult_1_r.
reflexivity.

apply help.
rewrite plus_comm.
simpl.
apply help.
rewrite plus_comm in IHm.
rewrite<- IHm.
symmetry.
rewrite plus_assoc.
reflexivity.
Qed.

Theorem mult_comm : forall n m, n * m = m * n.
intros.
induction n,m;simpl.

reflexivity.

symmetry.
apply mult_0_r.

apply mult_0_r.

apply help.
rewrite IHn.

simpl.

rewrite plus_assoc.
symmetry.

pattern (m * S n).
rewrite<- help2.
rewrite plus_assoc.
pattern (n+m).
rewrite plus_comm.
reflexivity.
Qed.


End Semiring.

(** PART 2 (40 %) **)

Section Asym.

(* Show that leq is antisymmetric,
Hints: This requires proving some lemmas about addition.
       And all the hints from the 1st part apply.
*)

Notation "m <= n" := (leq m n).


(* Formulate and prove some lemmas about addition you need
   to prove the theorem below. *)

(* insert solution *)

Lemma plus_is_0 : forall n m, n + m = 0 -> n = 0 /\ m = 0.
intros.
induction m,n; split. 

reflexivity.

reflexivity.

rewrite<- plus_n_0 in H.
exact H.

reflexivity.

reflexivity.

rewrite<- plus_0_n in H.
exact H.

discriminate.

discriminate.
Qed.



Lemma destruct_wrapper : forall m x : nat, m = x + m -> 0 = x.
intros.
induction m.
rewrite<- plus_n_0 in H.
exact H.
apply IHm.
apply peano8.

rewrite plus_comm in H.
simpl in H.
rewrite plus_comm in H.

exact H.
Qed.

Lemma second_zero : forall m x : nat, m+x = 0 -> x = 0.
intros.
induction m.

rewrite<- plus_0_n in H.
exact H.

discriminate.
Qed.

Theorem le_asym : forall (m n : nat), m <= n -> n <= m -> m=n.
intros m n mn nm.
destruct mn as [a man], nm as [b nbm].
rewrite man in nbm.
rewrite plus_assoc in nbm.
apply destruct_wrapper in nbm.
rewrite man.
symmetry in nbm.
apply second_zero in nbm.
rewrite nbm.
rewrite<- plus_0_n.
reflexivity.
Qed.

End Asym.


End Ex6.
