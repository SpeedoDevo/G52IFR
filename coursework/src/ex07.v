(** @author: Barnabas Forgo (bxf03u)
    Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 7 (Lists)
    published 23/11/14, deadline 1/12/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex07.v. 

    This exercise is about dyadic binary numbers. We represent binary numbers
    as lists of booleans, using a little endian encoding, ie the least signficant
    digit comes first. Unlike the usual binary representation of numbers, the dyadic
    representation has no redundancy and leading zeros matter. Counting in dyadic
    works as follows (using bool to represent binary digits, 0 = false, 1 = true):

    0 = nil
    1 = false :: nil
    2 = true :: nil
    3 = false :: false :: nil
    4 = true :: false :: nil
    5 = false :: true :: nil
    6 = true :: true :: nil
    7 = false :: false :: false :: nil
    ...
    
    The goal is to establish an isomorphism between the natural numbers and the
    dyadic binary numbers, that is to define functions

    n2d : nat -> dyadic
    d2n : dyadic -> nat 

    and to show

    n2n : forall n : nat, d2n (n2d n) = n
    d2d : forall d : dyadic, n2d (d2n d) = d

    You are only allowed to use the tactics introduced in the lecture
    (i.e.  exact, intro(s), apply, destruct, left, right, split,assert,
    unfold, exists, exfalso, reflexivity, rewrite, rewrite<-, discriminate,
    induction and pattern). You may also use theorems proven in the lecture
    or in previous exercises by loading the appropriate file. However, only
    submit ex07.v.

    You get 2.5 marks for each of the functions and 2.5 marks for each of the
    correctness proofs. You will need to prove additional lemmas.
  
    Hints:
    
    It is a good idea to define a function
      dsucc : dyadic -> dyadic
    which calculates the dyadic successor and to show how n2d and dsucc
    interact.
    If you define and use a doubling function which is defined recursively
    you may avoid having to refer to theorems about +.
    
    Please only use the tactics in the way indicated in the script,
    otherwise you may loose up to 2 style points. A proof should always
    end with "Qed." At the end of the file, the section should end
    with "End Ex7."  and the whole file including this line has to be
    accepted by Coq. If necessary comment out parts you cannot prove.

    Good luck!
**)

Section Ex7.

Require Import Coq.Lists.List.

Open Scope list_scope.

Definition dyadic := list bool.

(* You may need some auxillary functions! *)
Definition d0 : dyadic := nil.
Definition d1 : dyadic := false :: nil.
Definition d2 : dyadic := true :: nil.
Definition d3 : dyadic := false :: false :: nil.
Definition d4 : dyadic := true :: false :: nil.
Definition d5 : dyadic := false :: true :: nil.
Definition d6 : dyadic := true :: true :: nil.
Definition d7 : dyadic := false :: false :: false :: nil.

Fixpoint dsucc (d : dyadic) : dyadic :=
  match d with 
  | nil         => false :: nil
  | false :: d' => true :: d'
  | true :: d'  => false :: dsucc d'
  end.

Fixpoint double (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => S ( S (double m))
  end.

Eval compute in dsucc d3.

Fixpoint n2d(n : nat) : dyadic :=
  match n with
  | 0 => d0
  | S m => dsucc (n2d m)
  end.

Fixpoint d2n (d : dyadic) : nat :=
   match d with
   | nil => 0
   | d :: c => 
      if d then double (S (d2n c))
           else S (double (d2n c))
   end.

(* Test cases *)
Eval compute in (d2n d5).
Eval compute in (d2n (n2d 5)).
Eval compute in (d2n (n2d 16)).

(* You may also need some lemmas! *)
Lemma dsuccToS: forall d:dyadic, d2n (dsucc d) = S (d2n d).
intros.
induction d.

reflexivity.

destruct a.

simpl.
rewrite IHd.
simpl.
reflexivity.

simpl.
reflexivity.
Qed.

Lemma n2n : forall n : nat,d2n (n2d n) = n.
intros.
induction n.
reflexivity.
simpl.

rewrite dsuccToS.
rewrite IHn.
reflexivity.
Qed.

Lemma help : forall n : nat, dsucc (dsucc (n2d (double n))) = true :: (n2d n).
intro n.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
simpl.
reflexivity.
Qed.

Lemma help1 : forall n : nat, dsucc (n2d (double n)) = false :: (n2d n).
intro n.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
simpl.
reflexivity.
Qed.

Lemma d2d : forall d : dyadic, n2d(d2n d) = d.
intros.
induction d.
simpl.
reflexivity.
destruct a.
simpl.
rewrite help.
rewrite IHd.
reflexivity.
simpl.
rewrite help1.
rewrite IHd.
reflexivity.
Qed.


End Ex7.
