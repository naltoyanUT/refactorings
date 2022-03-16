(************************************************************************)
(* Copyright <2018> <Najd Altoyan>                                      *)
(* <LICENSE>                                                            *)
(************************************************************************)

Require Import Coq.Arith.Arith .
Require Import Coq.Bool.Bool .
Require Export Coq.Strings.String .
Require Import Coq.Logic.FunctionalExtensionality .
Require Import Coq.Lists.List .
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.


(** ------ Original class diagram: CD ---------- *)

(** Person Class *)
Record person := mkPerson {
  name: string;
}.


(** Car Class *)
(** We need to define validity constraint first *)
Definition sameOwner (op: option person) (p:person) :=
   op <> None -> op = Some p.


Record car := mkCar {
  make: string;
  ownedBy: person;
  favoredBy: option person;
  valid: sameOwner favoredBy ownedBy
}.


(* Construct Class Diagram, CD*)
Record CD := mkCD{
 person_class: list person;
 car_class: list car
}.


(** ------ Refactored class diagram: CD' ---------- *)

(** Person' Class*)
Record person_p := mkPersonP{
  name_p: string
}.


(** Car' Class*)
Definition toPerson(p: person_p):person:=
match p with
| mkPersonP n => mkPerson n
end.

Definition toFavoredBy(b:bool) (p:person_p):option person:=
if b then (Some (toPerson p)) else None.

Record car_p := mkCarP{
  make_p: string;
  drivenBy: person_p;
  preferred: bool;
  valid_p: sameOwner (toFavoredBy preferred drivenBy) (toPerson drivenBy)
}.

(** Construct Refactored Class Diagram, CD'*)
Record CDp:= mkCDp{
personp_class: list person_p;
carp_class: list car_p
}.


(** ------ Mappings T:CD->CD' ---------- *)

Definition toPersonPrime(p:person):person_p:=
match p with
|mkPerson n => mkPersonP n
end.


Fact axToCar : forall (p:bool) (d:person_p),
toFavoredBy p d <> None -> toFavoredBy p d = Some (toPerson d).
Proof.
intros preferred drivenBy.
unfold toFavoredBy.
unfold toPerson.
destruct drivenBy.
case preferred.
-firstorder.
-firstorder.
Defined.


Definition toBool(p: option person):bool:=
match p with
|None => false
|Some _ => true
end.


Definition toCarPrime(c:car): car_p:=
match c with
|mkCar m p f _=> mkCarP m (toPersonPrime p) (toBool f) (axToCar (toBool f) (toPersonPrime p))
end.



(** ------ Mappings S:CD'->CD ---------- *)

(* "toPerson" already defined *)

Definition toCar(c: car_p):car:=
match c with
| mkCarP m d p _ => mkCar m (toPerson d) (toFavoredBy p d) (axToCar p d)
end.

(*Another way to define S:Carp->Car*)
Definition toCarDef (cp: car_p): car.
Proof.
destruct cp as [makep driver preferred valid].
refine {|make:=makep; ownedBy:=(toPerson driver); favoredBy:=(toFavoredBy preferred driver)|}.
exact valid.
Defined.


Fixpoint toPersonL (ppl: list person_p): list person:=
match ppl with
|nil => nil
|pp::ppl => toPerson pp :: toPersonL ppl
end.

Fixpoint toCarL (cpl: list car_p) : list car:=
match cpl with
|nil => nil
|cp::cpl => toCarDef cp :: toCarL cpl
end.

Definition toCD (cdp: CDp): CD:=
match cdp with
|mkCDp ppl cpl => mkCD (toPersonL ppl) (toCarL cpl)
end. 

(** ------ Sub Theorems, Lemmas, and More Mappings ---------- *)


(* S.T:Person->Person'->Person*)

Theorem reconstructPerson: forall p:person,
p = toPerson(toPersonPrime p).
Proof.
intros p.
unfold toPersonPrime.
unfold toPerson.
case p.
intros name.
reflexivity.
Qed.



Lemma a: forall t:person,
Some t <> None -> True.
Proof.
intuition.
Qed.


(*Another way to define T:Car->Car'*)
Lemma toFavoredByLemma: forall c:car,
favoredBy c = toFavoredBy (toBool (favoredBy c)) (toPersonPrime (ownedBy c)).
Proof.
intro c.
unfold toBool, toPersonPrime.
destruct c as [make owner favors valid].
vm_compute. 
vm_compute in valid.
unfold toFavoredBy.
destruct favors. unfold toPerson. destruct owner. 
- apply valid. intuition. inversion x.
- reflexivity.
Defined.


Definition toCarPrimeDef (c: car): car_p.
Proof.
destruct c as [make owns favors valid].
refine {|make_p:=make;drivenBy:=(toPersonPrime owns); preferred:=(toBool favors)|}.
replace (toPerson (toPersonPrime owns)) with owns.
- replace (toFavoredBy (toBool favors) (toPersonPrime owns)) with favors.
  +exact valid.
  +apply (toFavoredByLemma (mkCar make owns favors valid)).
-apply (reconstructPerson owns).
Defined.

Fixpoint toPersonPL (pl: list person): list person_p:=
match pl with
|nil => nil
|p::pl => toPersonPrime p :: toPersonPL pl
end.

Fixpoint toCarPL (cl: list car) : list car_p:=
match cl with
|nil => nil
|c::cl => toCarPrimeDef c :: toCarPL cl
end.

Definition toCDp (cd: CD): CDp:=
match cd with
|mkCD pl cl => mkCDp (toPersonPL pl) (toCarPL cl)
end. 


(* S.T:Car->Car'->Car*)
Theorem reconstructCar: forall (c:car),
c = toCarDef (toCarPrimeDef c).
Proof.
intro c.
destruct c as [make owns favors valid].
vm_compute toCarPrimeDef.
vm_compute toCarDef.
destruct owns.
destruct favors.
destruct p.
destruct valid.
-f_equal. apply proof_irrelevance.
-f_equal. apply proof_irrelevance.
Qed.


(* T.S:Person'->Person->Person'*)
Theorem reconstructPersonPrime: forall p:person_p,
p = toPersonPrime(toPerson p).
Proof.
intros p.
unfold toPerson.
unfold toPersonPrime.
case p.
intros name.
reflexivity.
Qed.

(* T.S:Car'->Car->Car'*)
Theorem reconstructCarPrime: forall (cp:car_p),
cp = toCarPrimeDef (toCarDef cp).
Proof.
destruct cp as [makep driver preferred valid].
unfold toCarPrimeDef.
unfold toCarDef.
unfold toPersonPrime, toPerson.
destruct driver.
unfold toBool, toFavoredBy.
induction preferred.
-f_equal. apply proof_irrelevance.
-f_equal. apply proof_irrelevance.
Qed.



Lemma axToCarL: forall cl: list car,
cl = toCarL(toCarPL cl).
Proof.
intro cl.
unfold toCarPL, toCarL.
induction cl as [|c cl].
  -reflexivity.
  -f_equal.
    +apply (reconstructCar c).
    +apply IHcl.
Qed.

Lemma axToPersonL: forall pl: list person,
pl = toPersonL(toPersonPL pl).
Proof.
intro pl.
unfold toPersonPL, toPersonL.
induction pl as [|p pl].
  -reflexivity.
  -f_equal.
    +apply (reconstructPerson p).
    +apply IHpl.
Qed.


Lemma axToCarPL: forall cpl: list car_p,
cpl = toCarPL(toCarL cpl).
Proof.
intro cpl.
unfold toCarPL, toCarL.
induction cpl as [|cp cpl].
  -reflexivity.
  -f_equal.
    +apply (reconstructCarPrime cp).
    +apply IHcpl.
Qed.

Lemma axToPersonPL: forall ppl: list person_p,
ppl = toPersonPL(toPersonL ppl).
Proof.
intro ppl.
unfold toPersonPL, toPersonL.
induction ppl as [|pp ppl].
  -reflexivity.
  -f_equal.
    +apply (reconstructPersonPrime pp).
    +apply IHppl.
Qed.

(** First Main Theorem, S.T: CD -> CD' -> CD*)
Theorem eqCD: forall (cd: CD),
cd = toCD (toCDp cd).
Proof.
intros cd.
destruct cd as [pl cl].
unfold toCD, toCDp.
induction pl as [|p pl].
  -induction cl as [|c cl].
    +reflexivity.
    +f_equal. apply (axToCarL (c::cl)).
  -induction cl as [|c cl].
    +f_equal. apply (axToPersonL (p::pl)).
    +f_equal.
      --apply (axToPersonL (p::pl)).
      --apply (axToCarL (c::cl)).
Qed.

(** Second Main Theorem, T.S: CD' -> CD -> CD'*)
Theorem eqCDp: forall (cdp: CDp),
cdp = toCDp(toCD cdp).
Proof.
intros cdp.
destruct cdp as [ppl cpl].
unfold toCDp, toCD.
induction ppl as [|pp ppl].
  -induction cpl as [|cp cpl].
    +reflexivity.
    +f_equal. apply (axToCarPL (cp::cpl)).
  -induction cpl as [|cp cpl].
    +f_equal. apply (axToPersonPL (pp::ppl)).
    +f_equal.
      --apply (axToPersonPL (pp::ppl)).
      --apply (axToCarPL (cp::cpl)).
Qed. 