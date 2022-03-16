 Require Import Coq.Arith.Arith .
Require Import Coq.Bool.Bool .
Require Export Coq.Strings.String .
Require Import Coq.Logic.FunctionalExtensionality .
Require Import Coq.Lists.List .
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import ZArith.


(* A: tuple constructors*)
Record person := mkPerson{
  pname: string
}.

Record staff := mkStaff {
  sp : person;
  jobTitle: string
}.

Record faculty := mkFaculty{
  fp: person;
  rank: string
  fpapers: list string;
}.

Record student := mkStudent{
  stname: string;
  spapers: list string;
}.


(* B: tuple constructors*)
Record staff' := mkStaff'{
  sname : string;
  sjobTitle: string;
}.

Record faculty' := mkFaculty'{
  fname : string;
  frank: string;
}.


Export ListNotations.


(* Staff to Person *)
Definition staff_toPerson (s:staff) : person := sp s.
Definition staff_toPersonList (sl: list staff) := map staff_toPerson sl.

(* Staff to Staff' *)
Definition staff_toStaff' (s:staff) : staff' := 
  match s with 
  |mkStaff (mkPerson i n) j => mkStaff' i n j
end.
Definition staff_toStaff'List (sl: list staff) := map staff_toStaff' sl.

(* Faculty to Person *)
Definition faculty_toPerson (f:faculty) : person := fp f.
Definition faculty_toPersonList (fl: list faculty) := map faculty_toPerson fl.

(* Faculty to Faculty' *)
Definition faculty_toFaculty' (f:faculty) : faculty' := 
  match f with 
  |mkFaculty (mkPerson i n) j => mkFaculty' i n j
end.
Definition faculty_toFaculty'List (fl: list faculty) := map faculty_toFaculty' fl.


(* Staff' to Person *)
Definition staff'_toPerson (s':staff') : person :=
  match s' with
  |mkStaff' i n _ => mkPerson i n
end.
Definition staff'_toPersonList (sl': list staff') := map staff'_toPerson sl'.

(* Faculty' to Person *)
Definition faculty'_toPerson (f':faculty') : person :=
  match f' with
  |mkFaculty' i n _ => mkPerson i n
end.
Definition faculty'_toPersonList (fl': list faculty') := map faculty'_toPerson fl'.


(* Staff' to Staff *)
Definition staff'_toStaff (s': staff') : staff :=
 match s' with 
  |mkStaff' i n j => mkStaff (mkPerson i n) j
end.
Definition staff'_toSaffList (sl': list staff') := map staff'_toStaff sl'.

(* Faculty' to Faculty *)
Definition faculty'_toFaculty (f': faculty') : faculty :=
 match f' with 
  |mkFaculty' i n r => mkFaculty (mkPerson i n) r
end.
Definition faculty'_toFacultyList (fl': list faculty') := 
map faculty'_toFaculty fl'.

Definition disjoint {A: Type}(l m:list A) := forall a:A, In a l -> ~ In a m.



Definition abstract (super: list person) (sub1: list person) (sub2: list person):=
 super = sub1 ++ sub2 /\ disjoint sub1 sub2.


(* A: database constructor *)
Record class_diagram := mkCD{
  person_list: list person;
  staff_list: list staff;
  faculty_list: list faculty;
  abstract_inh: abstract person_list (map sp staff_list) (map fp faculty_list);

  v_staff'_list:= (staff_toStaff'List staff_list);
  v_faculty'_list := (faculty_toFaculty'List faculty_list)
}.

(* B: database constructor *)
Record class_diagram' := mkCD'{
  staff'_list: list staff';
  faculty'_list: list faculty';
  constraint': disjoint (staff'_toPersonList staff'_list) (faculty'_toPersonList faculty'_list);
 
  v_staff_list:= (staff'_toSaffList staff'_list);
  v_faculty_list:= (faculty'_toFacultyList faculty'_list);
  v_person_list:= (staff'_toPersonList staff'_list) ++ (faculty'_toPersonList faculty'_list);
}. 

Lemma staff'List: forall sl': list staff',
staff'_toPersonList sl' = staff_toPersonList (staff'_toSaffList sl').
Proof.
intros.
induction sl'.
- reflexivity.
- simpl. f_equal.
  + destruct a as [sid sname sjobTitle]. simpl. reflexivity.
  + assumption.
Qed.

Lemma faculty'List: forall fl': list faculty',
faculty'_toPersonList fl' = faculty_toPersonList (faculty'_toFacultyList fl').
Proof.
intros.
induction fl'.
- reflexivity.
- simpl. f_equal.
  + destruct a as [fid fname frank]. simpl. reflexivity.
  + assumption.
Qed.

Lemma reconstructStaffList : forall sl: list staff,
sl = staff'_toSaffList (staff_toStaff'List sl).
Proof.
induction sl as [|s sl].
-reflexivity.
- rewrite IHsl. simpl. replace (staff'_toStaff (staff_toStaff' s)) with s.
  + f_equal. rewrite <- IHsl. assumption.
  + destruct s as [[i n] j]. reflexivity.
Qed.

Lemma reconstructFacultyList : forall fl: list faculty,
fl = faculty'_toFacultyList (faculty_toFaculty'List fl).
Proof.
induction fl as [|f fl].
-reflexivity.
- rewrite IHfl. simpl. replace (faculty'_toFaculty (faculty_toFaculty' f)) with f.
  + f_equal. rewrite <- IHfl. assumption.
  + destruct f as [[i n] r]. reflexivity.
Qed.

Lemma staffPerson: forall sl: list staff,
(staff_toPersonList sl) = (staff'_toPersonList (staff_toStaff'List sl)).
Proof.
induction sl as [| s sl].
reflexivity.
simpl.
f_equal.
- destruct s as [[pid pname] jobTitle]. simpl. reflexivity. 
- assumption.
Qed.

Lemma facultyPerson: forall fl: list faculty,
(faculty_toPersonList fl) = 
    (faculty'_toPersonList (faculty_toFaculty'List fl)).
Proof.
induction fl as [| f fl].
reflexivity.
simpl.
f_equal.
- destruct f as [[pid pname] rank]. simpl. reflexivity. 
- assumption.
Qed.

Lemma toCD'Const: forall pl sl fl,
abstract pl sl fl->
         disjoint (staff'_toPersonList (staff_toStaff'List sl))
  (faculty'_toPersonList (faculty_toFaculty'List fl)).
Proof.
intros.
unfold abstract in H.
inversion H.
rewrite <- staffPerson.
rewrite <- facultyPerson.
assumption.
Qed.

Definition toCD' (cd:class_diagram) : class_diagram' :=
  match cd with
  | mkCD pl sl fl abs vsl' vfl' => mkCD' vsl' vfl' (toCD'Const pl sl fl abs)
end.

Definition toCD'_Def (cd: class_diagram) : class_diagram'.
Proof.
destruct cd as [pl sl fl abs vsl' vfl'].
refine{|staff'_list:=vsl';  faculty'_list:=vfl'|}.
unfold abstract in abs.
inversion abs.
unfold vsl', vfl'. 
rewrite <- staffPerson.
rewrite <- facultyPerson.
assumption.
Defined.


Lemma staff'Person: forall sl': list staff',
(staff'_toPersonList sl') = (staff_toPersonList (staff'_toSaffList sl')).
Proof.
induction sl' as [| s' sl'].
reflexivity.
simpl.
f_equal.
- destruct s' as [sid sname jobTitle']. simpl. reflexivity. 
- assumption.
Qed.

Lemma faculty'Person: forall fl': list faculty',
(faculty'_toPersonList fl') = (faculty_toPersonList (faculty'_toFacultyList fl')).
Proof.
induction fl' as [| f' fl'].
reflexivity.
simpl.
f_equal.
- destruct f' as [fid fname rank']. simpl. reflexivity. 
- assumption.
Qed.


Lemma toCDConst: forall sl' fl',
disjoint (staff'_toPersonList sl')
  (faculty'_toPersonList fl') -> abstract (staff'_toPersonList sl' ++
       faculty'_toPersonList fl') (staff'_toSaffList sl')
   (faculty'_toFacultyList fl').
Proof.
intros.
unfold abstract.
split.
- rewrite <- staff'List.
  rewrite <- faculty'List.
  reflexivity.
- rewrite <- staff'Person.
  rewrite <- faculty'Person.
  assumption.
Qed.


Definition toCD (cd':class_diagram') : class_diagram :=
  match cd' with
  | mkCD' sl' fl' disj' vsl vfl vpl => mkCD vpl vsl vfl (toCDConst sl' fl' disj')
end.


Definition toCD_Def (cd': class_diagram') : class_diagram.
Proof.
destruct cd' as [sl' fl' disj' vsl vfl vpl].
refine{|person_list:= vpl; staff_list:= vsl; faculty_list:= vfl |}.
unfold abstract.
split.
- unfold vpl, vsl, vfl.
  rewrite <- staff'List.
  rewrite <- faculty'List.
  reflexivity.
- unfold vsl, vfl. 
  rewrite <- staff'Person.
  rewrite <- faculty'Person.
  assumption.
Defined.

(** Th1: CD -> CD' -> CD **)

Definition transportAbstract (fn : list person -> list staff -> list faculty -> Type) 
  {p1 p2: list person} {s1 s2 : list staff} {f1 f2: list faculty} : 
  p1 = p2 -> s1 = s2 -> f1 = f2 -> fn p1 s1 f1-> fn p2 s2 f2.
Proof.
  intros H1 H2 H3.
  rewrite <- H1; rewrite <- H2; rewrite <- H3.
  firstorder.
Defined.


Lemma eqConst (cd1 cd2 : class_diagram)
      (p: person_list cd1 = person_list cd2)
      (q : staff_list cd1 = staff_list cd2)
      (r : faculty_list cd1 = faculty_list cd2) :
  transportAbstract abstract p q r  (abstract_inh cd1) = abstract_inh cd2 ->
  cd1 = cd2.
Proof.
  destruct cd1; destruct cd2.
  simpl in * |- *.
  destruct p.
  destruct q.
  destruct r.
  intros [].
  reflexivity.
Qed.

Lemma eqPersonList: forall cd,
person_list cd = person_list (toCD (toCD' cd)).
Proof.
intros.
unfold toCD, toCD'.
destruct cd as [pl sl fl abs].
unfold person_list.
unfold abstract in abs.
inversion abs.
rewrite <- staffPerson.
rewrite <- facultyPerson.
assumption.
Qed.

Lemma eqStaffList: forall cd,
  staff_list cd = staff_list (toCD (toCD' cd)).
Proof.
intros.
unfold toCD, toCD'.
destruct cd as [pl sl fl abs].
unfold staff_list.
apply reconstructStaffList.
Qed.


Lemma eqFacultyList: forall cd,
 faculty_list cd = faculty_list (toCD (toCD' cd)).
Proof.
intros.
unfold toCD, toCD'.
destruct cd as [pl sl fl abs].
unfold faculty_list.
apply reconstructFacultyList.
Qed.


Theorem th1: forall cd:class_diagram,
  cd = toCD (toCD' cd).
Proof.
intros cd.
pose proof (eqConst cd (toCD (toCD' cd))).
apply (H (eqPersonList cd) (eqStaffList cd) (eqFacultyList cd) ).
apply proof_irrelevance.
Qed.



(** Th2: CD' -> CD -> CD' **)

Definition disjointCast (sl': list staff') (fl': list faculty'):=
disjoint (staff'_toPersonList sl') (faculty'_toPersonList fl').

Definition transportDisjoint (fn : list staff' -> list faculty' -> Type) 
  {s1 s2 : list staff'} {f1 f2: list faculty'} : 
   s1 = s2 -> f1 = f2 -> fn s1 f1-> fn s2 f2.
Proof.
  intros H1 H2.
  rewrite <- H1; rewrite <- H2.
  firstorder.
Defined.

Lemma eqConst' (cd1 cd2 : class_diagram')
      (p : staff'_list cd1 = staff'_list cd2)
      (q : faculty'_list cd1 = faculty'_list cd2) :
  transportDisjoint disjointCast p q (constraint' cd1) = constraint' cd2 ->
  cd1 = cd2.
Proof.
  destruct cd1; destruct cd2.
  simpl in * |- *.
  destruct p.
  destruct q.
  intros [].
  reflexivity.
Qed.

Lemma reconstructStaffList' : forall sl': list staff',
sl' = staff_toStaff'List (staff'_toSaffList sl').
Proof.
induction sl' as [|s' sl'].
-reflexivity.
- rewrite IHsl'. simpl. replace (staff_toStaff' (staff'_toStaff s')) with s'.
  + f_equal. rewrite <- IHsl'. assumption.
  + destruct s' as [i n j]. reflexivity.
Qed.

Lemma reconstructFacultyList' : forall fl': list faculty',
fl' = faculty_toFaculty'List (faculty'_toFacultyList fl').
Proof.
induction fl' as [|f' fl'].
-reflexivity.
- rewrite IHfl'. simpl. replace (faculty_toFaculty' (faculty'_toFaculty f')) with f'.
  + f_equal. rewrite <- IHfl'. assumption.
  + destruct f' as [i n r]. reflexivity.
Qed.

Lemma eqStaffList': forall cd',
  staff'_list cd' = staff'_list (toCD' (toCD cd')).
Proof.
intros.
unfold toCD, toCD'.
destruct cd' as [sl' fl' disj'].
unfold staff'_list.
apply reconstructStaffList'.
Qed.


Lemma eqFacultyList': forall cd',
 faculty'_list cd' = faculty'_list (toCD' (toCD cd')).
Proof.
intros.
unfold toCD, toCD'.
destruct cd' as [sl' fl' disj'].
unfold faculty'_list.
apply reconstructFacultyList'.
Qed.


Theorem th2: forall cd':class_diagram',
  cd' = toCD' (toCD cd').
Proof.
intros cd'.
pose proof (eqConst' cd' (toCD' (toCD cd'))).
apply (H (eqStaffList' cd') (eqFacultyList' cd') ).
apply proof_irrelevance.
Qed.
