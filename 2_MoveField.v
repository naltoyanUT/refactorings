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
 

(** --- Classes in CD and CD' --- **)

Record Car := mkCar {
  vin: string;
}.

Record Person := mkPerson {
  insurance : string;
  car : Car;
}.


Record CD := mkCD{
  cl : list Car;
  pl : list Person;
  eqRel : cl = map car pl;
}.

Record Car' := mkCar' {
  vin': string;
  insurance': string;
}.


Record Person' := mkPerson' {
  car' : Car';
}.

Record CD' := mkCD'{
  cl' : list Car';
  pl' : list Person';
  eqRel' : cl' = map car' pl';
}.

(* used to automate proofs *)
Ltac destruct_record := match goal with
| [x: Person |- _] => destruct x
| [x: Car |- _] => destruct x
| [x: Car' |- _] => destruct x
| [x: Person' |- _] => destruct x
| [x: _*_ |- _] => destruct x
end.


(* proof should pass *)
Ltac solve_simple_reconstruct := intros [?]; try(destruct_record);  auto.


Definition toCar' (a:Person) : Car' :=
 mkCar' (vin (car a)) (insurance a).
 
Definition toCar (ap:Person') : Car :=
 mkCar (vin' (car' ap)).

Definition toPerson' (a:Person) : Person' :=
 mkPerson'  (toCar' a).

Definition toPerson (ap:Person') : Person :=
 mkPerson  (insurance' (car' ap)) (toCar ap).
 

Lemma reconstructPerson' : reconstruct toPerson' toPerson.
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructPerson : reconstruct toPerson toPerson'.
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructCar'1 : forall x, car' x = toCar' (toPerson x).
Proof. solve_simple_reconstruct. Qed.


Lemma reconstructCar2 :forall x, car x = toCar (toPerson' x).
Proof. solve_simple_reconstruct. Qed.

(* person.insurance = person'.car'.insurance' *)
Lemma reconstructInsurance1 :forall x, insurance x = insurance' (car' (toPerson' x)).
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructInsurance2 :forall x, insurance (toPerson x) = insurance' (car' x).
Proof. solve_simple_reconstruct. Qed.



(*Preparing automated proof *)

Create HintDb MyDB discriminated.
Ltac myauto := simpl; auto with MyDB.
Ltac myrewrite := autorewrite with MyDB.
Ltac myunfold := autounfold with MyDB.
Ltac solveinsurancelist l := 
	 induction l; [reflexivity | simpl; f_equal; assumption].


Definition toCarList  (pl': list Person'): list Car := map toCar pl'.
Definition toCarList' (pl : list Person ):  list Car' := map toCar' pl.
Definition toPersonList' (pl : list Person): list Person' := map toPerson' pl.
Definition toPersonList  (pl': list Person') : list Person := map toPerson pl'.


Ltac destruct_all := repeat destruct_record.

Ltac destruct_list := match goal with
| [l : list _ |- _ ] => destruct l as [ | destruct_all]
end.

Ltac destruct_lists := repeat destruct_list.


Ltac solve_list_reconstruct := intros l; induction l; 
	[auto | simpl; f_equal;  [destruct_all; myauto | auto] ].

Ltac solve_using_induction x:=
induction x; [reflexivity | simpl; f_equal;
 [myauto | assumption] ].


Lemma reconstructPersonList' : reconstruct (map toPerson') (map toPerson).
Proof. solve_list_reconstruct. Qed.


Lemma reconstructPersonList : reconstruct (map toPerson) (map toPerson').
Proof. solve_list_reconstruct. Qed.

Lemma reconstructCarList' : forall x, map car' x = map toCar' (map toPerson x).
Proof. solve_list_reconstruct. Qed.

Lemma reconstructCarList : forall x, map car x = map toCar (map toPerson' x).
Proof. solve_list_reconstruct. Qed.


Lemma reconstructCar1List': forall cd', cl' cd' = toCarList' (toPersonList (pl' cd')).
Proof.
intros cd'.
destruct cd' as [CL' PL' C].
simpl.
rewrite C.
unfold toCarList', toPersonList.
apply reconstructCarList'.
Qed.


Lemma reconstructCar2List :  forall cd, cl cd = toCarList (toPersonList' (pl cd)).
Proof.
intros cd.
destruct cd as [CL PL C].
simpl.
rewrite C.
unfold toCarList, toPersonList'.
apply reconstructCarList.
Qed.


Lemma reconstructCar2List' : forall x, toCarList' x = map car' (toPersonList' x).
Proof. intros x.
induction x.
- reflexivity.
- simpl. f_equal. assumption. Qed.


Lemma reconstructCar1List : forall x, toCarList x = map car (map toPerson x).
Proof. intros x.
induction x.
- reflexivity.
- simpl. f_equal. assumption. Qed.

Definition eqRelCons (cl: list Car) (pl: list Person):= cl = map car pl.
Definition eqRelCons' (cl' : list Car') (pl': list Person') := cl' = map car' pl'.


Lemma eqRelAx: forall (cd:CD), eqRelCons' (toCarList' (pl cd)) (toPersonList' (pl cd)).
Proof.
intros cd.
unfold eqRelCons', toCarList', toPersonList'.
destruct cd as [CL PL C].
simpl.
apply reconstructCar2List'.
Qed.


Lemma eqRelAx': forall (cd':CD'), eqRelCons (toCarList (pl' cd')) (toPersonList (pl' cd')).
Proof.
intros cd'.
unfold eqRelCons, toCarList, toPersonList.
destruct cd' as [CL' PL' C'].
simpl.
apply reconstructCar1List.
Qed.

Definition toCD' (cd:CD) : CD'.
refine{|cl':= toCarList' (pl cd);  pl':= toPersonList' (pl cd)|}.
apply eqRelAx.
Defined.

Definition toCD (cd':CD') : CD.
refine{|cl:= toCarList (pl' cd'); pl:= toPersonList(pl' cd')|}.
apply eqRelAx'.
Defined.

(*---- Theorem One ----*)

Definition eqRelTransport (fn: list Car -> list Person -> Type)  {b1 b2 : list Car}  {a1 a2 : list Person} :
 b1 = b2 -> a1 = a2 -> fn b1 a1 -> fn b2 a2 .
Proof. intros [] ?. try(rewrite <- H). firstorder. Defined.


Lemma eqConst (cd1 cd2: CD) 
	(p: cl cd1 = cl cd2)
	(q: pl cd1 = pl cd2) : 
	eqRelTransport eqRelCons p q (eqRel cd1) = eqRel cd2 ->
	cd1 = cd2.
Proof. 
	destruct cd1; destruct cd2. simpl in * |- *.
	destruct p. destruct q.  repeat(intros []).
	reflexivity.
Qed.

Lemma eqCarList : forall cd, cl cd = cl(toCD (toCD' cd)).
Proof. intros cd. simpl. apply reconstructCar2List.
Qed.

Lemma eqPersonList : forall cd, pl cd = pl(toCD (toCD' cd)).
Proof. intros cd; simpl. apply reconstructPersonList'. (*myrewrite; auto.*)
Qed.

Lemma th1 : reconstruct toCD' toCD.
Proof. 
	unfold reconstruct. intros x. 
	pose proof (eqConst x (toCD (toCD' x))). 
	apply (H (eqCarList x) (eqPersonList x));
	apply proof_irrelevance. 
Qed.


(*---- Theorem Two ----*)

Definition eqRelTransport' (fn: list Car' -> list Person' -> Type)  {b1 b2 : list Car'}  {a1 a2 : list Person'} :
 b1 = b2 -> a1 = a2 -> fn b1 a1 -> fn b2 a2 .
Proof. intros [] ?. try(rewrite <- H). firstorder. Defined.


Lemma eqConst' (cd1 cd2: CD') 
	(p: cl' cd1 = cl' cd2)
	(q: pl' cd1 = pl' cd2) : 
	eqRelTransport' eqRelCons' p q (eqRel' cd1) = eqRel' cd2 ->
	cd1 = cd2.
Proof. 
	destruct cd1; destruct cd2. simpl in * |- *.
	destruct p. destruct q.  repeat(intros []).
	reflexivity.
Qed.

Lemma eqCarList' : forall x, cl' x = cl'(toCD' (toCD x)).
Proof. intros x; simpl. apply reconstructCar1List'.
Qed.

Lemma eqPersonList' : forall x, pl' x = pl'(toCD' (toCD x)).
Proof. intros x; simpl. apply reconstructPersonList.
Qed.

Lemma th2 : reconstruct toCD toCD'.
Proof. 
	unfold reconstruct. intros x. 
	pose proof (eqConst' x (toCD' (toCD x))). 
	apply (H (eqCarList' x) (eqPersonList' x));
	apply proof_irrelevance. 
Qed.
