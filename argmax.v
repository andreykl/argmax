Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint argmax (A : Type) (default : A) (f : A -> nat) (xs : list A) : A :=
  match xs with
  | [] => default
  | [x] => x
  | x::xs => inner (f x) x f xs
  end
with inner (A : Type) (s : nat) (r : A) (f : A -> nat) (xs : list A) : A :=
       match xs with
       | [] => r
       | x::xs' => let fx := f x in
                 if s <? fx
                 then inner fx x f xs'
                 else inner s r f xs'
       end.

Eval compute in (argmax 0 (fun x => x*0) [1;2;3;4]).

Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.
                             
Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
      [ | try first [apply not_lt in H | apply not_le in H]]].

(* Theorem argmax_correct' f l r = *)
(*   l /= [] && all (<= f r) fl && firstEq (f r) l fl r *)
(*   where *)
(*     fl = map f l *)
(*     firstEq s [] [] r = False *)
(*     firstEq s (x:xs) (y:ys) r = if s == y *)
(*       then x == r *)
(*       else firstEq s xs ys r *)

Lemma argmax_nonempty : forall A d (f : A -> nat) a x xs,
    argmax d f (a :: xs) = x ->
    (xs = [] /\ x = a) \/
    (exists a' xs', xs = a'::xs' /\ inner (f a) a f (a'::xs') = x).
Proof.
  intros.
  simpl in H.
  destruct xs.
  left. auto.
  right. exists a0, xs.
  auto.
Qed.

Lemma inner_split : forall A (f : A -> nat) a a' xs' x,
    inner (f a) a f (a'::xs') = x ->
    (f a < f a' /\ inner (f a') a' f xs' = x) \/
    (f a >= f a' /\ inner (f a) a f xs' = x).
Proof.
  intros.
  simpl in H.
  bdestruct (f a <? f a').
  left; auto. right. auto.
Qed.

Lemma inner_correct : forall A (f : A -> nat) x xs a,
    inner (f a) a f xs = x ->
    (a = x /\ (forall y iy, nth_error xs iy = Some y -> f y <= f x)) \/
    (exists ix, nth_error xs ix = Some x /\ f x > f a /\
           (forall y iy, nth_error xs iy = Some y -> f y < f x \/ ix <= iy)).
Proof.
  intros f x.
  induction xs as [| x' xs' IHxs']; intros.
  - left. simpl in *. split. auto.
    intros. destruct iy; discriminate.
  - apply inner_split in H.
    destruct H as [[H H0] | [H H0]].
    + apply IHxs' in H0.
      destruct H0 as [[H0 H1] | [ix [H0 H1]]].
      * subst; right; exists 0; split; auto; split; lia; intros; right; lia.
      * right. exists (S ix). split. apply H0. split. destruct H1. lia.
        destruct H1. intros. destruct iy. injection H3 as H3. subst x'.
        left; auto. apply H2 in H3. destruct H3. left. auto.
        right; lia.
    + apply IHxs' in H0.
      * destruct H0 as [[H0 H1] | [ix [H0 [H1 H2]]]].
        left. split. auto. intros. subst a. destruct iy.
        injection H2 as H2. subst x'. auto.
        simpl in H2. apply H1 in H2. auto.
        right. exists (S ix). split. apply H0.
        split; auto. intros. destruct iy.
        injection H3 as H3. subst x'. left. lia.
        simpl in H3. apply H2 in H3. destruct H3.
        left; auto. right; lia.
Qed.

Theorem argmax_correct (A : Type) (d x : A) (f : A -> nat) (xs : list A) :
    argmax d f xs = x ->
    ((xs = [] /\ x = d) \/
     exists ix, nth_error xs ix = Some x /\
           (forall y iy, nth_error xs iy = Some y -> f y < f x \/ ix <= iy)).
Proof.
  intros. destruct xs.
  left. simpl in *; auto.
  apply argmax_nonempty in H.
  destruct H as [[H H0] | [a' [xs' [H H0]]]].
  - right. exists 0. split. subst. reflexivity.
    intros. subst xs x. destruct iy; [| destruct iy; discriminate].
    right. lia.
  - subst xs. apply inner_correct in H0.
    destruct H0 as [[H0 H1] | [ix [H0 [H1 H2]]]].
    right. subst. exists 0. split. reflexivity.
    intros. right. lia.
    right. exists (S ix). split.
    apply H0. intros. destruct iy.
    injection H as H. subst a. left. auto.
    apply H2 in H. destruct H.
    left; auto. right; lia.  
Qed.
