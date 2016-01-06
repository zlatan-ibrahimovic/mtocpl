(* A sorting example : 
   (C) Yves Bertot, Pierre Castéran 
*)

Require Import List.
Require Import Arith.

Require Import preorder.

Import PO.

  (*Open Scope Z_scope.*)
  
(**

 Projet :

 Specifier de la facon la plus generique possible ce qu'est une fonction
 correcte de tri polymorphe sur des listes:

 Construire une version polymorphe du tri par insertion, et prouver qu'elle 
 realise la specification ci-dessus

 Afin d'illustrer la genericite de votre construction, montrer qu'elle
 permet de trier des listes de divers types de  données, et comment 
 realiser les transformations suivantes :
  + tri par ordre decroissant 
  + tri sur un produit lexicographique
  + tri selon les valeurs d'une fonction 


 *)

Section Poly.
  Variable A: Type.
  Variable leb_pol : BoolPreorder.
  Variable eqb_pol : BoolPreorder.
  Hypothesis inverse_leb : BoolReverse.
  
Fixpoint insert_pol (z:A)(l:list A) :=
  match l with 
  | nil => z :: nil
  | cons a l' => if leb_pol z a
      then z :: a :: l'
      else a :: insert_pol z  l'
 end.


 
Fixpoint insertion_sort_pol(l:list A) : list A :=
match l with 
| nil => nil
| z::l' => insert_pol z (insertion_sort_pol  l')
end.


Inductive sorted_pol  {A:Type} (leb_pol : A -> A -> bool) : list A -> Prop :=
| sorted0 : sorted_pol leb_pol nil
| sorted1 : forall z:A, sorted_pol leb_pol (z :: nil)
| sorted2 :
    forall (z1 z2:A) (l:list A),
      leb_pol z1 z2 = true->
      sorted_pol leb_pol (z2 :: l) -> sorted_pol leb_pol (z1 :: z2 :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.

Lemma sort_2357 :
 sorted_pol leb (2 :: 3 :: 5 :: 7 :: nil).
Proof.
 auto with sort arith.
Qed.

Theorem sorted_inv :
 forall (z:A) (l:list A), sorted_pol leb_pol (z :: l) -> sorted_pol leb_pol l.
Proof.
 intros z l H.
 inversion H; auto with sort.
Qed.

(*  Number of occurrences of z in l *)

Fixpoint nb_occ_pol (z:A) (l:list A) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') => 
      if eqb_pol z z' 
      then S (nb_occ_pol z l')
      else nb_occ_pol z l'
   end.


(* list l' is a permutation of list l *)

Definition equiv_pol (l l':list A) := 
    forall z:A, nb_occ_pol z l = nb_occ_pol z l'.

(* equiv is an equivalence ! *)
 
Lemma equiv_refl_pol: forall l:list A, equiv_pol l l.
Proof.
 unfold equiv_pol; trivial.
Qed.

Lemma equiv_sym_pol: forall l l':list A, equiv_pol l l' -> equiv_pol l' l.
Proof.
  unfold equiv_pol; auto.
Qed.
 
Lemma equiv_trans_pol:
 forall l l' l'':list A, equiv_pol l l' -> 
                         equiv_pol l' l'' -> 
                         equiv_pol l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.

Lemma equiv_cons_pol:
 forall (z:A) (l l':list A), equiv_pol l l' -> 
                             equiv_pol (z :: l) (z :: l').
Proof.
 intros z l l' H z'.
 simpl; case_eq  (eqb_pol z' z); auto. 
Qed.
 
Lemma equiv_perm_pol:
 forall (a b:A) (l l':list A),
   equiv_pol l l' -> 
   equiv_pol (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H z; simpl.
 case_eq (eqb_pol z a); case_eq (eqb_pol z b); 
  simpl; case (H z); auto.
Qed.

Hint Resolve equiv_cons_pol equiv_refl_pol equiv_perm_pol : sort.

Lemma insert_equiv_pol: forall (l:list A) (x:A), 
                  equiv_pol (x :: l) (insert_pol x l).
Proof.
 induction l as [|a l0 H]; simpl ; auto with sort.
 intros x; case_eq (leb_pol x a);
   simpl; auto with sort.
  intro; apply equiv_trans_pol  with (a :: x :: l0); 
   auto with sort.
Qed.
 
Lemma insert_sorted_pol:
 forall (l:list A) (x:A), sorted_pol leb_pol l -> sorted_pol leb_pol (insert_pol x l).
Proof.
  intros l x H; elim H; simpl; auto with sort.
  -  intro z; case_eq (leb_pol x z); simpl; intros; 
     auto with sort arith.
     
  -  intros z1 z2; case_eq (leb_pol x z2); simpl; intros; 
     case_eq (leb_pol x z1);intros; auto with sort arith.
Qed.

Lemma sort_equiv_pol : forall l, equiv_pol l (insertion_sort_pol l).
Proof.
 induction l;simpl;auto with sort.
apply equiv_trans_pol with (a:: insertion_sort_pol l).
 apply equiv_cons_pol;auto.
 apply insert_equiv_pol.
Qed.

Lemma sort_sorted_pol : forall l, sorted_pol leb_pol (insertion_sort_pol l).
induction l;simpl;auto with sort.
now apply insert_sorted_pol.
Qed.

End Poly.

(**Extraction "insert-sort_pol" insert_pol insertion_sort_pol.

Check sort_sorted_pol.**)


Definition sort_type:= forall (A:Type), (A->A->bool) -> list A -> list A.

Definition rel_total {A:Type} (comp_pol: A -> A -> bool) :=
forall a x :A, comp_pol x a = false -> comp_pol a x = true.

Definition pred_sort_pol (f: sort_type) :=forall (A:Type) (l:list A) (comp_pol: A -> A -> bool),
rel_total comp_pol -> equiv_pol A comp_pol l (f A comp_pol l) /\ sorted_pol comp_pol (f A comp_pol l).


Theorem pred_sort_inv : pred_sort_pol insertion_sort_pol.
Proof.
unfold pred_sort_pol.
intros.
split.
apply sort_equiv_pol.
apply sort_sorted_pol.
assumption.
Qed.

(**Exemple insertion d'entier naturel**)
Compute  insert_pol nat leb 4 (2 :: 3 :: 1 :: nil).

(**Exemple tri d'entier naturel**)
Compute insertion_sort_pol nat leb (2 :: 5 :: 1 :: nil).

(**Exemple nombre d'occurence (ici égal à 2) dans la liste**)
Compute nb_occ_pol nat beq_nat 2 (2 :: 5 :: 1 :: nil).

Require Import ZArith.
Open Scope Z_scope.
(**Exemple insertion d'entier relatif**)
Compute  insert_pol Z Z.leb 4 (2 :: 5 :: 1 :: nil).

(**Exemple tri d'entier relatif**)
Compute insertion_sort_pol Z Z.leb (2 :: 5 :: 1 :: nil).

(**Exemple nombre d'occurence (ici égal à 2) dans la liste**)
Compute nb_occ_pol Z Z.eqb 2 (2 :: 5 :: 1 :: nil).

Require Import String.
Open Scope string_scope.
(**Exemple insertion d'entier relatif**)
Search string.

Require Import Coq.Strings.Ascii.
Compute insert_pol string  "t"("c" :: "a" :: "z" :: nil).

(**Exemple tri d'entier relatif**)
Compute insertion_sort_pol Z Z.leb (2 :: 5 :: 1 :: nil).

(**Exemple nombre d'occurence (ici égal à 2) dans la liste**)
Compute nb_occ_pol Z Z.eqb 2 (2 :: 5 :: 1 :: nil).