Require Import String Arith List.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.

(***************************
*** T H E   M O D E L *****
***************************)

(** BA Schema -- Table Definitions *******************)
Record Bank:=mkBank{ name: string; }.  (* Bank tuple constructor *)
Record Account:=mkAccount{ owner: Bank; }.  (* Account tuple constructor *)

(** BVA Schema  -- Table Definitions *******************)
Record Bank':=mkBank'{ name': string; }.  (* Bank' tuple constructor *)
Record Vector' := mkVector'{ owner' : Bank'; }. (* Vector' tuple constructor *)
Record Account' := mkAccount'{		 (* Account' tuple constructor *)
	vector' : Vector';
	v_ownedBy := owner' vector'; (* virtual element *)
}.

(** Defining Transformations between Tables *******************)
(* Bank and Bank'*)
Definition toBank (b': Bank'): Bank := mkBank (name' b').
Definition toBank' (b: Bank): Bank' := mkBank' (name b).

(* Vector' derived from Bank *)
Definition createVector'(b:Bank): Vector' := mkVector' (toBank' b).

(* Account and Account' *)
Definition toAccount(a':Account') : Account := mkAccount (toBank (v_ownedBy a')).
Definition toAccount'(a:Account) : Account' := mkAccount' (createVector' (owner a)).


(** Database Definitions **************************************)
Record databaseBA := mkDB{  (* BA database constructor *)
	banks : list Bank;
	accounts: list Account;
	v_vectors := map createVector' banks; (*virtual tuples of vector'*)
}.

Record databaseBVA := mkDB'{  (* BVA database constructor *)
	banks' : list Bank';
	vectors' : list Vector';
	accounts' : list Account';
	cons': banks' = (map owner' vectors') ; (* other side of 1-to-1 cardinality *)
}.

(** Transformations between databaseBA and databaseBVA **********)
Definition toDB (db':databaseBVA) : databaseBA :=
	mkDB (map toBank (banks' db')) (map toAccount (accounts' db')).

(*Here we use proof mode since databaseBVA has a constraint*)
Definition toDB' (db:databaseBA) : databaseBVA.
Proof.
	destruct db as [bs acs vvs].
	refine {|banks' := map toBank' bs; vectors':= vvs ;accounts':= map toAccount' acs|}.
	induction bs as [| b bs].
	- auto.
	- simpl. f_equal. assumption.
Defined.

(***************************
*** T H E   P R O O F *****
***************************)

(** Helper Lemmas for th1 ***********************************)
Lemma reconstructBanks: forall bs, 
	bs = map toBank (map toBank' bs).
Proof.
	induction bs as [|b bs].
	-auto.
	- simpl. f_equal.
	+ destruct b. auto.
	+ assumption.
Qed.

Lemma reconstructAccounts: forall acs, 
	acs = map toAccount (map toAccount' acs).
Proof.
	induction acs as [|ac acs].
	-auto.
	- simpl. f_equal.
	+ destruct ac. destruct owner0. auto.
	+ assumption.
Qed.

(********************)
(* First theorem: th1 *)
(********************)
Theorem th1: forall db, 
	db = toDB (toDB' db).
Proof.
	destruct db as [bs acs vvs].
	simpl. unfold toDB. f_equal.
	- apply reconstructBanks.
	- apply reconstructAccounts.
Qed.

(** Helper Lemmas for th2 **********************************)
Lemma reconstructBanks': forall bs',
	bs' = map toBank' (map toBank bs').
Proof.
	induction bs' as [|b' bs'].
	- auto.
	- simpl. f_equal.
	+ destruct b'. auto.
	+ assumption.
Qed.

Lemma reconstructAccounts': forall acs', 
	acs' = map toAccount' (map toAccount acs').
Proof.
	induction acs' as [|ac' acs'].
	- auto.
	- simpl. f_equal.
	+ destruct ac'. destruct vector'0. destruct owner'0. auto.
	+ assumption.
Qed.

Lemma reconstructVectors': forall vs',
	vs' = map createVector' (map toBank (map owner' vs')).
Proof.
	induction vs' as [|v' vs'].
	-auto.
	- simpl. f_equal.
	+ destruct v' as [[n]]. auto.
	+ assumption.
Qed.

(** Dealing with databaseBVA constraint through 'transport' *************)
Definition transport {x1 x2: list Bank'} {y1 y2: list Vector'}:
	x1 = x2 -> y1 = y2 -> x1 = (map owner' y1) -> x2 = (map owner' y2).
Proof. congruence. Qed.

Definition eqDB' (db1 db2: databaseBVA) (p: banks' db1 = banks' db2)
(q: vectors' db1 = vectors' db2) (r: accounts' db1 = accounts' db2):
	transport p q (cons' db1) = cons' db2 ->
	db1 = db2.
Proof.
	destruct db1, db2.
	simpl in * |- *.
	destruct p, q, r.
	intros. 
	f_equal.
	apply proof_irrelevance.
Qed.

Lemma eqBanks': forall db',
	banks' db' = banks' (toDB' (toDB db')).
Proof.
	destruct db'; simpl; 
	apply reconstructBanks'.
Qed.

Lemma eqAccounts' : forall db',
	accounts' db' = accounts' (toDB' (toDB db')).
Proof.
	destruct db'; simpl;
	apply reconstructAccounts'.
Qed.

Lemma eqVectors' : forall db',
	vectors' db' = vectors' (toDB' (toDB db')).
Proof.
	destruct db' as [? ? ? c].
	simpl. rewrite c.
	apply reconstructVectors'.
Qed.

(**********************)
(* Second theorem: th2 *)
(**********************)
Theorem th2: forall db',
	db' = toDB' (toDB db').
Proof.
	intros db'.
	pose proof (eqDB' db' (toDB' (toDB db'))).
	apply (H (eqBanks' db') (eqVectors' db') (eqAccounts' db'));
	apply proof_irrelevance.
Qed.