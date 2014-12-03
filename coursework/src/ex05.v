(** @author: Barnabas Forgo (bxf03u)
    Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 5 (Sets)
    published 7/11/14, deadline 17/11/14, 17:00 electronic submission

    Use moodle to submit your solution.

    Multiple submissions are allowed, up to the deadline, but only the latest  
    one will be marked. Please name your file ex05.v. 

    This exercise has 3 parts. In the 1st part you have to construct
    elements of some given set, which is like proving propositions. In
    the 2nd part we ask you to prove an isomorphism involving
    coproducts and products.  The 3rd part is only for people who
    think that they are very clever.  We ask you to prove the strange
    fact that for any function on bool it is the same if you apply it
    once or three times.

    You are only allowed to use the tactics introduced in the lecture
    (i.e.  exact, intro(s), apply, destruct, left, right, split,assert,
    unfold, exists, exfalso, reflexivity, rewrite, rewrite<-, discriminate
    and case_eq) and the term formers introduced in the lecture notes 
    (i.e. fun, match, application, (-,-), inl, inr). 

    Please only use the tactics and term formers in the way indicated
    in the script, otherwise you may loose upto 2 style points. A
    proof should always end with "Qed." At the end of the file, the
    section should end with "End Ex5."  and the whole file including
    this line has to be accepted by Coq. If necessary comment out 
    parts you cannot prove.

**)

Section Ex5.

(* Prelude *)

(* Some notational incantations and the ext axiom. *)

Open Scope type_scope.
Set Implicit Arguments.
Implicit Arguments inl [A B].
Implicit Arguments inr [A B].

Axiom ext : forall (A B : Set)
     (f g : A -> B), 
     (forall x:A,f x = g x) -> f = g.

(** PART 1 (40 %) **)

(* Find inhabitants of the following sets. Via the Curry Howard isomorphism
   this is the same as proving the corresponding proposition. However, you
   supposed to construct the proof terms by hand and not to use the interactive
   proof system.
*)

Section CurryHoward.

Variables A B C : Set.

Definition c01 : (A -> B -> C) -> (B -> A -> C) :=
fun (abc: A -> B -> C) (b: B) (a: A) => abc a b.

Definition c02 : (A -> C) -> (B -> A) -> (B -> C) :=
fun (ac: A -> C) (ba: B -> A) (b: B) => ac (ba b).

Definition c03 : ((A -> C) -> C) -> (A -> B) -> ((B -> C) -> C) :=
fun (acc : (A -> C) -> C) (ab : A -> B) (bc : B -> C) =>
  acc (fun a : A => bc (ab a)).

Definition c04 : ((A + (A -> C)) -> C) -> C :=
fun aacc : A + (A -> C) -> C =>
  aacc (inr (fun a : A => aacc (inl a))).

Definition c05 : ((A -> (A -> C)) * ((A -> C) -> A)) -> C :=
fun (p : (A -> (A -> C)) * ((A -> C) -> A)) =>
  match p with (aac, aca) =>
    aac (aca (fun a : A => aac a a)) (aca (fun a: A => aac a a))
  end.

End CurryHoward.

(** PART 2 (40 %) **)

Section Iso.

Variables A B C : Set.

(* In this section we are proving an isomosphism about conproducts and products,
   namely that (A + B) -> C is isomorphic to (A -> C) * (B -> C).
*)


Definition phi : ((A + B) -> C) -> (A -> C) * (B -> C) :=
fun (abc: (A + B) -> C) => (fun a: A => abc (inl a),fun b: B => abc (inr b)).

Definition psi : (A -> C) * (B -> C) -> ((A + B) -> C) :=
fun (p: (A -> C) * (B -> C)) (ab: A+B) =>
  match p with (ac, bc) =>
      match ab with
      | inl a => ac a
      | inr b => bc b
      end
  end.

Lemma psiphi : forall x : (A + B) -> C, psi (phi x) = x.
intros abc.
apply ext.
intro.
destruct x.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma phipsi : forall x : (A -> C) * (B -> C), phi (psi x) = x.
intro p.
destruct p as [ac bc].
unfold phi,psi.

assert ((fun a => ac a) = ac).
apply ext.
intro a.
reflexivity.

assert ((fun b => bc b) = bc).
apply ext.
intro b.
reflexivity.

rewrite H,H0.
reflexivity.
Qed.

End Iso.

(** PART 3 (20 %) **)

Section Tricky.

(* Prove the following theorem: Applying any function on booleans 
   three times is the same as applying it once. 
   To do this the tactic case_eq may be useful - case_eq t allows
   you to perform case analysis on a term t : bool. It works like
   destruct but also introduces some additional equational assumptions
   which can be useful when proving your goal.
*)

Lemma tricky : 
  forall (f:bool -> bool) (b:bool), f( f( f( b))) = f b.
intros.
destruct b;case_eq (f true);case_eq (f false);intros.

rewrite H0.
exact H0.

rewrite H0.
exact H0.

exact H0.

exact H.

rewrite H0.
exact H0.

rewrite H.
exact H.

rewrite H0.
exact H.

rewrite H.
exact H.
Qed.

End Tricky.


End Ex5.
