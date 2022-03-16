Require Import Coq.Arith.Arith .
Require Import Coq.Bool.Bool .
Require Export Coq.Strings.String .
Require Import Coq.Logic.FunctionalExtensionality .
Require Import Coq.Lists.List .
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import ZArith.
Open Scope string.

Definition reconstruct {A B: Type}
(f: A -> B) (g: B->A):= forall x:A,
x = g(f x).

Record Person := mkPerson {
  name : string;
  ssn: string;
  ss_date: string;
}.

(*****)

Record SocialSecurity' := mkSS'{
  ssn': string;
  ss_date': string;
}.

Record Person' := mkPerson' {
  name' : string;
  ss' : SocialSecurity';
}.

(****)

Definition toPerson' (p:Person) : Person' :=
 mkPerson'  ( name p ) (mkSS' (ssn p) (ss_date p)).

Definition toPerson (p':Person') : Person :=
  match p' with
  | mkPerson' n' s' => mkPerson n' (ssn' s') (ss_date' s')
end.

Definition toSS' (p:Person) : SocialSecurity' :=
 mkSS'  (ssn p) (ss_date p).


Definition eqRelDef (sl': list SocialSecurity') (pl': list Person'):= sl' = map ss' pl'.


Record CD := mkCD{
  pl : list Person;
}.

Record CDp := mkCDp{
  sl' : list SocialSecurity';
  pl' : list Person';
  eqRel : sl' = map ss' pl';
}.


Create HintDb SplitPatternDB discriminated.
Ltac myauto := simpl; auto with SplitPatternDB.
Ltac myrewrite := autorewrite with SplitPatternDB.
Ltac myunfold := autounfold with SplitPatternDB.
Ltac solvefieldlist l := 
	 induction l; [reflexivity | simpl; f_equal; assumption].



Hint Unfold reconstruct : SplitPatternDB.
Ltac destruct_record := match goal with
| [x: Person |- _] => destruct x
| [x: SocialSecurity' |- _] => destruct x
| [x: Person' |- _] => destruct x
| [x: CD |- _] => destruct x
| [x: CDp |- _] => destruct x
| [x: _*_ |- _] => destruct x
end.

Ltac destruct_all := repeat destruct_record.

Ltac destruct_list := match goal with
| [l : list _ |- _ ] => destruct l as [ | destruct_all]
end.

Ltac destruct_lists := repeat destruct_list.

Ltac solve_simple_reconstruct := intros [?]; destruct_all;  auto.

Ltac solve_list_reconstruct := intros l; induction l; 
	[auto | simpl; f_equal;  [destruct_all; myauto | auto] ].

Ltac solve_using_induction x:=
induction x; [reflexivity | simpl; f_equal;
 [myauto | assumption] ].



Hint Unfold toPerson toSS' toPerson' : SplitPatternDB.

Lemma reconstructPerson' : reconstruct toPerson' toPerson.
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructPerson : reconstruct toPerson toPerson'.
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructSS' : forall x, ss' x = toSS' (toPerson x).
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructSS: forall x, ss' (toPerson' x) = toSS' x.
Proof. solve_simple_reconstruct. Qed.


Hint Resolve reconstructPerson' reconstructPerson : SplitPatternDB.
Hint Resolve reconstructSS' reconstructSS : SplitPatternDB.
Hint Rewrite <- reconstructPerson' reconstructPerson : SplitPatternDB.
Hint Rewrite <- reconstructSS' reconstructSS : SplitPatternDB.

(*---- Reconstruct Lists of Objects ----*)
Lemma reconstructPersons' : reconstruct (map toPerson') (map toPerson).
Proof. intros x. 
induction x. 
- simpl; f_equal.
- simpl; destruct_record; f_equal. assumption.
 Qed.

Lemma reconstructPersons : reconstruct (map toPerson) (map toPerson').
Proof. intros x; solve_using_induction x. Qed.

Lemma reconstructSSs' : forall x, map ss' x = map toSS' (map toPerson x).
Proof. intros x; solve_using_induction x.
Qed.

Lemma reconstructSSs : forall x, map ss' (map toPerson' x) = map toSS' x.
Proof. intros x. 
induction x. 
- simpl; f_equal.
- simpl; f_equal. assumption.
Qed.

Hint Resolve reconstructPersons' reconstructPersons : SplitPatternDB.
Hint Resolve reconstructSSs' reconstructSSs : SplitPatternDB.

Hint Rewrite <- reconstructPersons' reconstructPersons : SplitPatternDB.
Hint Rewrite <- reconstructSSs' reconstructSSs : SplitPatternDB.


Lemma eqRelLemma : forall c,  map toSS' (pl c)  = map ss' ( map toPerson' (pl c)).
Proof.  intros. f_equal. symmetry. myauto.
Qed.

Definition toCDp (c:CD) : CDp := 
 mkCDp  ( map toSS' (pl c) )  ( map toPerson' (pl c) ) (eqRelLemma c).

Definition toCD (c:CDp) : CD := 
 mkCD  ( map toPerson (pl' c) ).

Hint Unfold toCD toCDp : SplitPatternDB.

(*---- Theorem One ----*)
Lemma th1 : reconstruct toCDp toCD.
Proof.
myunfold.
intros x.
destruct x as [xl].
destruct xl as [|x xl].
- reflexivity.
- simpl. f_equal. destruct x. now myrewrite.
Qed.

(*---- Theorem Two ----*)

Definition eqRelCast (nl' : list SocialSecurity') (pl' : list Person') := 
nl' = map ss' pl'.

Definition eqRelTransport (fn: list SocialSecurity' -> list Person' -> Type)  {b1 b2 : list SocialSecurity'}  {a1 a2 : list Person'} :
 b1 = b2 -> a1 = a2 -> fn b1 a1 -> fn b2 a2 .
Proof. intros [] ?. try(rewrite <- H). firstorder. Defined.


Lemma eqConst (cd1 cd2: CDp) 
	(p: sl' cd1 = sl' cd2)
	(q: pl' cd1 = pl' cd2) : 
	eqRelTransport eqRelCast p q (eqRel cd1) = eqRel cd2 ->
	cd1 = cd2.
Proof. 
	destruct cd1; destruct cd2. simpl in * |- *.
	destruct p. destruct q.  repeat(intros []).
	reflexivity.
Qed.

Lemma eqsl' : forall x, sl' x = sl'(toCDp (toCD x)).
Proof. intros [?]; myauto; try(myrewrite; assumption).
Qed.

Lemma eqpl' : forall x, pl' x = pl'(toCDp (toCD x)).
Proof. intros [?]; myauto; try(myrewrite; assumption).
Qed.

Lemma th2 : reconstruct toCD toCDp.
Proof. 
	unfold reconstruct. intros x. 
	pose proof (eqConst x (toCDp (toCD x))). 
	apply (H (eqsl' x) (eqpl' x));
	apply proof_irrelevance. 
Qed.

