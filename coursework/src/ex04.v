(** author: @bxf03u
    Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 4 (Bool)
    published 3/11/14, deadline 10/11/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex04.v. 

    This exercise has 2 parts. In the 1st part we present you some propositions
    about bool. Some are true and some are false. You have to decide which is
    which and prove the true ones and prove the negation of the false ones. That
    is in this case you proof ~(..) instead of ..
    In the 2nd part we ask you to define a function which determines wether
    two booleans are different and then prove that this function satisfies 
    its specification.

    You are only allowed to use the tactics introduced in the lecture
    (i.e.  exact, intro(s), apply, destruct, left, right, split,assert,
    unfold, exists, exfalso, reflexivity, rewrite, rewrite<- and discriminate).

    Please only use the tactics in the way indicated in the script,
    otherwise you may loose upto 2 style points. A proof should always
    end with "Qed." At the end of the file, the section should end
    with "End Ex4."  and the whole file including this line has to be
    accepted by Coq.

**)

Section Ex4.

Require Import Coq.Bool.Bool.

(** PART 1 (50 %) **)

Section AboutBool.

(*
For the following propositions decide wether they are true or false and
depending on your choice either prove the proposition or its negation (~(..)).

b01 : forall x:bool,negb (negb x) = x.
b02 : forall x : bool, exists y : bool, x <> y.
b03 : exists x : bool, forall y : bool, x <> y.
b04 : forall x y z : bool, x = y \/ x = z \/ y = z.
b05 : exists x : bool, negb x = x.
b06 : forall x y : bool, negb(x && y) = negb x || negb y.
b07 : forall y:bool,exists x:bool, negb x = y.
b08 : forall x y : bool, negb x = negb y -> x = y.
b09 : exists y : bool, forall x : bool, x || y = x && y.
b10 : forall x : bool, exists y : bool, x || y = x && y. 
*)


Lemma b01 : forall x:bool,negb (negb x) = x.
intros.
destruct x.
reflexivity.
reflexivity.
Qed.

Lemma b02 : forall x : bool, exists y : bool, x <> y.
intro.
destruct x.
exists false.
intro.
discriminate H.
exists true.
intro.
discriminate.
Qed.

(*Lemma b03 : exists x : bool, forall y : bool, x <> y.*)

Lemma b03' : ~(exists x : bool, forall y : bool, x <> y).
intro.
destruct H.
destruct x.
assert (k: true <> true).
apply H.
apply k.
reflexivity.
assert (k: false <> false).
apply H.
apply k.
reflexivity.
Qed.

Lemma b04 : forall x y z : bool, x = y \/ x = z \/ y = z.
intros.
destruct x, y, z.
left; reflexivity.
left; reflexivity.
right; left; reflexivity.
right; right; reflexivity.
right; right; reflexivity.
right; left; reflexivity.
left; reflexivity.
left; reflexivity.
Qed.

(*Lemma b05 : exists x : bool, negb x = x.*)

Lemma b05' : ~(exists x : bool, negb x = x).
intro.
destruct H.
destruct x.
discriminate H.
discriminate H.
Qed.

Lemma b06 : forall x y : bool, negb(x && y) = negb x || negb y.
intros.
destruct x,y;
reflexivity.
Qed.

Lemma b07 : forall y:bool,exists x:bool, negb x = y.
intro.
destruct y.
exists false.
reflexivity.
exists true.
reflexivity.
Qed.

Lemma b08 : forall x y : bool, negb x = negb y -> x = y.
intros x y.
destruct x,y.
intro.
reflexivity.
intro.
discriminate H.
intro.
discriminate H.
intro.
reflexivity.
Qed.

(*Lemma b09 : exists y : bool, forall x : bool, x || y = x && y.*)

Lemma b09' : ~(exists y : bool, forall x : bool, x || y = x && y).
intro.
destruct H.
destruct x.
assert (k: false || true = false && true).
apply H.
discriminate k.
assert (k: true || false = true && false).
apply H.
discriminate k.
Qed.

Lemma b10 : forall x : bool, exists y : bool, x || y = x && y.
intro.
exists x.
destruct x.
reflexivity.
reflexivity.
Qed.

End AboutBool.


(** PART 2 (50 %) **)
Section Diffb.

(* Define a function d
     diffb : bool -> bool -> bool
   s.t. diffb x y returns true, if x <> y and false otherwise.
*)

Definition diffb (b c : bool) :=
  match b with
  | true => negb c
  | false => c
  end.
(* Now prove that your function satisfies the specification. *)

Eval compute in diffb true true.

Theorem diffb_correct : forall a b : bool, 
  a <> b <-> diffb a b = true.
intros.
destruct a, b; simpl; split; intro h; unfold not in h; unfold not.
exfalso; apply h; reflexivity.
discriminate h; reflexivity.
reflexivity.
intro; discriminate.
reflexivity.
discriminate.
exfalso; apply h; reflexivity.
discriminate.
Qed.

End Diffb.

End Ex4.
