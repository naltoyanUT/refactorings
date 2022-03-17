Require Import Coq.Arith.Arith .
Require Import Coq.Bool.Bool .
Require Export Coq.Strings.String .
Require Import Coq.Logic.FunctionalExtensionality .
Require Import Coq.Lists.List .
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import ZArith.
Require Import Coq.Logic.FinFun.
Open Scope string.

(* Prepare Hints *)
Create HintDb DomainArrowDb discriminated.
Ltac auto ::= auto with DomainArrowDb.
Ltac myauto := simpl; auto with DomainArrowDb.
Ltac myrewrite := autorewrite with DomainArrowDb.
Ltac myunfold := autounfold with DomainArrowDb.

Ltac solvefieldlist l := induction l; [reflexivity | simpl; f_equal; assumption].


(* uniqness of a column *)
Definition UniqueField {A B:Type} (f: A->B) (l: list A)  :=
NoDup (map f l).

(**---Original----**)

Record Domain:= mkDomain{
  d_name: string;
}.

Record Arrow:= mkArrow{
  ar_name: string;
  startsAt: Domain;
  endsAt: Domain;
}.


Record class_diagram := mkCD{
  dl: list Domain;
  al: list Arrow;
  uniqueDomainName: UniqueField d_name dl;
  uniqueArrowName: UniqueField ar_name al;
}.


(**---Refacotred----**)

Record Domain':= mkDomain'{
  d_name': string;
}.

Record Arrow':= mkArrow'{
  ar_name': string;
  domain': string;
  codomain': string;
  connects': Domain' * Domain'; 
  samestart: domain' = d_name' (fst connects');
  sameend: codomain' = d_name' (snd connects');
}.

Record class_diagram' := mkCD'{
  dl': list Domain';
  al': list Arrow';
  uniqueDomainName': UniqueField d_name' dl';
  uniqueArrowName': UniqueField ar_name' al';
}.


(**------Mappings-------**)
Definition toDomain'(d:Domain) : Domain' :=
mkDomain' (d_name d).


Lemma samestartL: forall ar,
 d_name (startsAt ar) =
 d_name'(fst (toDomain' (startsAt ar), toDomain' (endsAt ar))).
Proof. intros; reflexivity. Qed.

Lemma sameendL: forall ar,
 d_name (endsAt ar) =
 d_name'(snd (toDomain' (startsAt ar), toDomain' (endsAt ar))).
Proof. intros; reflexivity. Qed.

Definition toArrow'(ar:Arrow) : Arrow' :=
mkArrow' (ar_name ar) (d_name (startsAt ar)) (d_name (endsAt ar)) 
         ((toDomain'(startsAt ar)), (toDomain'(endsAt ar))) 
         (samestartL ar) (sameendL ar).

Lemma FieldMap: forall {A A' B: Type} {f: A -> B} {l:list A} 
{f': A' -> B} {t':A -> A'} ,
(map f l) = (map f' (map t' l)) ->
UniqueField f l = UniqueField f' (map t' l).
Proof.
intros.
unfold UniqueField.
rewrite <- H.
reflexivity.
Qed.

Lemma domainNameMap: forall dl,
(map d_name dl) = (map d_name' (map toDomain' dl)).
Proof. intros dl; solvefieldlist dl. Qed.

Lemma uniqueDomainNameL: forall cd,
 UniqueField d_name'(map toDomain' (dl cd)).
Proof.
intros.
destruct cd as [dl ? ? ?]. simpl.
rewrite <- (FieldMap (domainNameMap dl)).
assumption.
Qed.

Lemma arrowNameMap: forall al,
(map ar_name al) = (map ar_name' (map toArrow' al)).
Proof. intros al; solvefieldlist al. Qed.

Lemma uniqueArrowNameL: forall cd,
UniqueField ar_name' (map toArrow' (al cd)).
Proof.
intros.
destruct cd as [? al ? ?]. simpl.
rewrite <- (FieldMap (arrowNameMap al)).
assumption.
Qed.

Definition toCD'(cd: class_diagram) : class_diagram':=
mkCD' (map toDomain' (dl cd)) (map toArrow' (al cd)) 
      (uniqueDomainNameL cd) (uniqueArrowNameL cd).

(** S Mappings **)

Definition toDomain(d':Domain') : Domain :=
mkDomain (d_name' d'). 

Definition toArrow(ar':Arrow') : Arrow :=
mkArrow (ar_name' ar') (toDomain (fst (connects' ar'))) 
                       (toDomain (snd (connects' ar'))).


Lemma domainNameMap': forall dl',
(map d_name' dl') = (map d_name (map toDomain dl')).
Proof. intros dl; solvefieldlist dl. Qed.

Lemma uniqueDomainNameL': forall cd',
 UniqueField d_name (map toDomain (dl' cd')).
Proof.
intros cd.
destruct cd as [dl ? ? ?]. simpl.
rewrite <- (FieldMap (domainNameMap' dl)).
assumption.
Qed.

Lemma arrowNameMap': forall al',
(map ar_name' al') = (map ar_name (map toArrow al')).
Proof. intros al; solvefieldlist al. Qed.

Lemma uniqueArrowNameL': forall cd',
UniqueField ar_name (map toArrow (al' cd')).
Proof.
intros cd.
destruct cd as [? al ? ?]. simpl.
rewrite <- (FieldMap (arrowNameMap' al)).
assumption.
Qed.

Definition toCD(cd': class_diagram') : class_diagram:=
mkCD (map toDomain (dl' cd'))(map toArrow (al' cd'))
      (uniqueDomainNameL' cd') (uniqueArrowNameL' cd').

Hint Unfold toArrow toArrow' toCD toCD' toDomain toDomain'.

(**------Theorems-------**)


Ltac destruct_record :=
 match goal with
   | [d : Domain |- _] => destruct d
   | [d' : Domain' |- _] => destruct d'
   | [a : Arrow |- _] => destruct a
   | [a' : Arrow' |- _] => destruct a'
   | [p : _*_ |- _] => destruct p
 end.

Ltac destruct_all := repeat destruct_record.

Ltac destruct_list := 
  match goal with
  | [l : list _ |- _ ] => destruct l as [ | destruct_all]
  end.

Ltac destruct_lists := repeat destruct_list.

Ltac solve_simple_reconstruct := intros [?]; destruct_all;  auto.

Ltac solve_list_reconstruct := intros l; induction l; [auto | simpl; f_equal; 
                                     [destruct_all; myauto | auto] ].

Lemma reconstructDomain: forall d,
  d = toDomain (toDomain' d).
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructDomain': forall d,
  d = toDomain' (toDomain d).
Proof. solve_simple_reconstruct. Qed.

Lemma reconstructArrow: forall a,
  a = toArrow (toArrow' a).
Proof. solve_simple_reconstruct. Qed.


Lemma reconstructArrowList: forall al,
 al = map toArrow (map toArrow' al).
Proof. solve_list_reconstruct. Qed.


Lemma reconstructDomainList: forall dl,
 dl = map toDomain (map toDomain' dl).
Proof. solve_list_reconstruct. Qed.

Hint Resolve reconstructDomain reconstructDomain': DomainArrowDb.


Definition castSameStart (domain': string) (conn:Domain'*Domain'):=
domain' = d_name' (fst conn).

Definition castSameEnd (codomain': string) (conn:Domain'*Domain'):=
codomain' = d_name' (snd conn).

Definition transport (fn : string -> Domain'*Domain' -> Type) 
{s1 s2: string} {d1 d2: Domain'*Domain'}:
s1 = s2 -> d1 = d2 -> fn s1 d1 -> fn s2 d2.
Proof.
  repeat (intros []).
  firstorder.
Qed.

Print mkArrow'.

Lemma eqConst (a1 a2: Arrow')
      (n: ar_name' a1 = ar_name' a2)
      (p: domain' a1 = domain' a2)
      (q : codomain' a1 = codomain' a2)
      (r: connects' a1 = connects' a2):
  transport castSameStart p r (samestart a1) = samestart a2 ->
  transport castSameEnd   q r (sameend a1)   = sameend a2   ->
  a1 = a2.
Proof.
  destruct a1; destruct a2.
  simpl in * |- *.
  destruct n, p, q, r.
  repeat (intros []).
  f_equal; apply proof_irrelevance.
Qed.

Lemma n (a': Arrow'):
ar_name' a' = ar_name' (toArrow' (toArrow a')).
Proof. myauto. Qed.

Lemma p (a': Arrow'):
domain' a' = domain' (toArrow' (toArrow a')).
Proof. destruct a'; myauto. Qed.

Lemma q (a': Arrow'):
codomain' a' = codomain' (toArrow' (toArrow a')).
Proof. destruct a'; myauto. Qed.

Lemma r (a': Arrow'):
connects' a' = connects' (toArrow' (toArrow a')).
Proof. destruct_all. myauto. Qed.

Lemma reconstructArrow': forall a',
  a' = toArrow' (toArrow a').
Proof. intros a.
apply (eqConst a (toArrow' (toArrow a)) (n a) (p a) (q a) (r a));
apply proof_irrelevance. Qed.


Lemma reconstructArrowList': forall al',
 al' = map toArrow' (map toArrow al').
Proof. 
solve_list_reconstruct. 
apply reconstructArrow'. 
Qed.

Lemma reconstructDomainList': forall dl',
 dl' = map toDomain' (map toDomain dl').
Proof. solve_list_reconstruct. Qed.


Hint Resolve reconstructArrow reconstructArrow'
             reconstructArrowList reconstructArrowList'
             reconstructDomainList reconstructDomainList' : DomainArrowDb.


Lemma eqDomainList: forall cd,
dl cd = dl (toCD (toCD' cd)).
Proof.
intros [?]; myauto.
Qed.

Lemma eqArrowList: forall cd,
 al cd = al (toCD (toCD' cd)).
Proof. intros [?]; myauto. Qed.

Lemma eqDomainList': forall cd',
dl' cd' = dl' (toCD' (toCD cd')).
Proof. intros [?]; myauto. Qed.

Lemma eqArrowList': forall cd',
al' cd' = al' (toCD' (toCD cd')).
Proof. intros [?]; myauto. Qed.


Definition castDN (dl: list Domain):=
UniqueField d_name dl.

Definition castAN (al: list Arrow):=
UniqueField ar_name al.

Definition transportDN (fn : list Domain -> Type) 
  {d1 d2: list Domain} : 
    d1 = d2 -> fn d1-> fn d2.
Proof. intros [] ?. assumption. Defined.

Definition transportAN (fn : list Arrow -> Type) 
  {a1 a2: list Arrow} : 
    a1 = a2 -> fn a1-> fn a2.
Proof. intros[] ?. assumption. Defined.

Lemma eqCD (cd1 cd2 : class_diagram)
      (p: dl cd1 = dl cd2)
      (q : al cd1 = al cd2):
  transportDN castDN p (uniqueDomainName cd1) = uniqueDomainName cd2 ->
  transportAN castAN q (uniqueArrowName cd1) = uniqueArrowName cd2 ->
  cd1 = cd2.
Proof.
  destruct cd1, cd2.
  simpl in * |- *.
  destruct p, q.
  repeat (intros []).
  reflexivity.
Qed.


Theorem th1: forall cd:class_diagram,
  cd = toCD (toCD' cd).
Proof.
intros.
pose proof eqCD cd (toCD (toCD' cd)).
apply (H (eqDomainList cd) (eqArrowList cd)); 
apply proof_irrelevance.
Qed.


Print mkCD'.

Definition castDN' (dl':list Domain'):=
UniqueField d_name' dl'.

Definition transportDN' (fn : list Domain' -> Type) 
  {d1 d2: list Domain'} : 
    d1 = d2 -> fn d1-> fn d2.
Proof.
  intros [] ?. assumption.
Defined.

Definition castAN' (al':list Arrow'):=
UniqueField ar_name' al'.

Definition transportAN' (fn : list Arrow' -> Type) 
  {a1 a2: list Arrow'} : 
    a1 = a2 -> fn a1-> fn a2.
Proof.
  intros[] ?. assumption.
Defined.


Lemma eqCD' (cd1 cd2 : class_diagram')
      (p: dl' cd1 = dl' cd2)
      (q : al' cd1 = al' cd2):
  transportDN' castDN' p (uniqueDomainName' cd1) = uniqueDomainName' cd2 ->
  transportAN' castAN' q (uniqueArrowName' cd1) = uniqueArrowName' cd2 ->
  cd1 = cd2.
Proof.
  destruct cd1, cd2.
  simpl in * |- *.
  destruct p, q.
  repeat (intros []).
  reflexivity.
Qed.


Theorem th2: forall cd':class_diagram',
  cd' = toCD' (toCD cd').
Proof.
intros.
pose proof eqCD' cd' (toCD' (toCD cd')).
apply (H (eqDomainList' cd') (eqArrowList' cd')); 
apply proof_irrelevance.
Qed.

