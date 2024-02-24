Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.FinFun.
Require Import  Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Export ListNotations.
From Coq Require Import ssreflect ssrfun ssrbool.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
From Coq Require Import Lia.

Definition Finite A := {l : list A & Full l}.
Definition EqDec A := forall n m : A, {n = m} + {n <> m}.

Class Symbol (A : Set) := {
    finite : Finite A;
    eq_dec : EqDec A;
}.

Class Graph (A B : Set) := {
   symbol_A : Symbol A;
   symbol_B : Symbol B;
   incident : B -> A * A; 
}.

Definition get_graph_vertices {A B} (graph : Graph A B) : list A.
destruct (@finite _ (@symbol_A _ _ graph)).
exact x.
Defined.

Definition get_graph_edges {A B} (graph : Graph A B) : list B.
destruct (@finite _ (@symbol_B _ _ graph)).
exact x.
Defined.

Definition check_vertices {A} (eq_dec : EqDec A) (vertice a : A) : nat.
destruct (eq_dec vertice a).
exact 1.
exact 0.
Defined.

Definition degree {A B} 
   (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) (vertice : A) : nat.
induction ys.
exact 0.
exact (IHys + (check_vertices eq_dec vertice (incident a).1) + (check_vertices eq_dec vertice (incident a).2)).
Defined.

Definition sum_degree {A B}
       (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) : nat.
induction xs.
exact 0.
exact ((degree eq_dec (a :: xs) ys incident a) + IHxs).
Defined.

Theorem zero_edges A B (eq_dec : EqDec A) (xs : list A) (incident : B -> A * A) :
    sum_degree eq_dec xs [] incident = 0.
induction xs.
trivial.
simpl.
by rewrite IHxs.
Qed.

Theorem dump_count0 : forall A a (xs : list A) (eq_dec : EqDec A), 
    ~ In a xs -> count_occ eq_dec xs a = 0.
intros.
induction xs.
trivial.
have : ~ a = a0.
move => H'.
destruct H.
by left.
move => H2.
simpl.
remember (eq_dec0 a0 a).
destruct s.
by contradiction H2.
apply : IHxs.
move => H3.
destruct H.
by right.
Qed.

Theorem In_dif : forall A a b (xs : list A), In a xs -> ~ In b xs -> a <> b.
intros.
induction xs.
inversion H.
destruct H.
subst.
move => H.
destruct H0.
by left.
apply IHxs.
exact H.
move => H1.
destruct H0.
by right.
Qed.

Theorem no_dump_count : forall A a (xs : list A) (eq_dec : EqDec A),
    NoDup xs -> In a xs -> count_occ eq_dec xs a = 1.
intros.
induction xs.
inversion H0.
inversion H.
inversion H0.
destruct H0.
simpl in *.
rewrite H0.
remember (eq_dec0 a a).
destruct s.
rewrite dump_count0.
by rewrite <- H0.
trivial.
by contradiction n.
simpl.
rewrite H5.
remember (eq_dec0 a a).
destruct s.
rewrite dump_count0.
by subst.
trivial.
apply IHxs.
exact H4.
exact H0.
simpl.
subst.
set (In_dif _ _ _ _ H5 H3).
remember (eq_dec0 a0 a).
destruct s.
by contradiction n.
apply IHxs.
assumption.
assumption.
Qed.


Theorem degree_count_at_lest_1 A B b (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) 
      : degree eq_dec xs (b :: ys) incident (incident b).1 = degree eq_dec xs ys incident (incident b).1 + (check_vertices eq_dec (incident b).1 (incident b).2) + 1.
intros.
induction ys.
simpl.
unfold check_vertices.
remember (eq_dec (incident b).1 (incident b).1).
destruct s.
lia.
by contradiction n.
simpl in *.
unfold check_vertices.
remember (eq_dec (incident b).1 (incident b).1).
destruct s.
remember (eq_dec (incident b).1 (incident b).2).
destruct s.
trivial.
lia.
by contradiction n.
Qed.

Inductive IsEdgeConsistent {A B} (incident : B -> A * A)  : list A -> list B -> Prop :=
   | IsEdgeConsistent_nil : forall xs, IsEdgeConsistent incident xs []
   | NoDup_cons : forall xs ys y, In (incident y).1 xs -> In (incident y).2 xs
      -> IsEdgeConsistent incident xs ys -> IsEdgeConsistent incident xs (y::ys).

Theorem degree_diff_edge A B e (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) 
      :  (incident e).1 <> (incident e).2 ->
         degree eq_dec xs (e :: ys) incident (incident e).1 + degree eq_dec xs (e :: ys) incident (incident e).2 = degree eq_dec xs ys incident (incident e).1 + degree eq_dec xs ys incident (incident e).2 + 2.
intros.
rewrite degree_count_at_lest_1.
have : check_vertices eq_dec (incident e).1 (incident e).2 = 0.
unfold check_vertices.
remember (eq_dec (incident e).1 (incident e).2).
destruct s.
by contradiction H.
trivial.
move => H1.
simpl.
rewrite H1.
have : check_vertices eq_dec (incident e).2 (incident e).1 = 0.
unfold check_vertices.
remember (eq_dec (incident e).2 (incident e).1).
destruct s.
by contradiction H.
trivial.
move => H2.
rewrite H2.
have : check_vertices eq_dec (incident e).2 (incident e).2 = 1.
unfold check_vertices.
remember (eq_dec (incident e).2 (incident e).2).
destruct s.
trivial.
by contradiction n.
move => H3.
rewrite H3.
lia.
Qed.

Theorem degree_eq_edge A B e (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) 
      :  (incident e).1 = (incident e).2 ->
         degree eq_dec xs (e :: ys) incident (incident e).1 = degree eq_dec xs ys incident (incident e).1 + 2.
intros.
rewrite degree_count_at_lest_1.
rewrite H.
have : check_vertices eq_dec (incident e).2 (incident e).2 = 1.
unfold check_vertices.
remember (eq_dec (incident e).2 (incident e).2).
destruct s.
trivial.
by contradiction n.
intros.
rewrite H0.
lia.
Qed.

Theorem degree_connecitivy_plus_1 {A B} a v (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A):
    In (incident a).1 xs -> ~ In (incident a).2 xs -> In v xs ->
       degree eq_dec xs (a :: ys) incident v = degree eq_dec xs ys incident v + (check_vertices eq_dec v (incident a).1).
intros.
induction ys.
simpl.
unfold check_vertices.
remember (eq_dec v (incident a).2).
destruct s.
subst.
by contradiction H0.
auto.
simpl in *.
unfold check_vertices.
remember (eq_dec v (incident a).2).
destruct s.
contradiction H0.
rewrite <- e.
assumption.
remember (eq_dec v (incident a0).2).
remember (eq_dec v (incident a).1).
remember (eq_dec v (incident a0).1 ).
destruct s.
destruct s0.
destruct s1.
auto.
auto.
destruct s1.
auto.
auto.
destruct s1.
destruct s0.
auto.
auto.
auto.
Qed.

Theorem connecitivy_plus_1 {A B} a (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A):
    In (incident a).1 xs -> ~ In (incident a).2 xs -> 
       sum_degree eq_dec xs (a :: ys) incident = sum_degree eq_dec xs ys incident + 1.
intros.
induction xs.
inversion H.
simpl.
pose (@degree_connecitivy_plus_1 _ _ _ a0 eq_dec _ ys _ H H0).
simpl in *.
rewrite e.
by left.
clear e.
destruct H.
subst.
unfold check_vertices.
remember (eq_dec (incident a).1 (incident a).1).
destruct s.


induction xs.
inversion H.
simpl.
unfold check_vertices.
have : (incident a).2 <> a0.
move => H1.
contradiction H0.
by left.
move => H1.
remember (eq_dec a0 (incident a).1).
destruct s.
remember (eq_dec a0 (incident a).2).
destruct s.
subst.
by contradiction H1.
subst.

rewrite degree_count_at_lest_1.

rewrite IHxs.


have : (incident a).1 <> (incident a).2.
admit.
move => H1.
set (degree_diff_edge _ _ _ eq_dec (a0 :: xs) ys _ H1).
simpl in e.



Theorem hand_shake  {A B} (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A):
    NoDup xs -> NoDup ys -> IsEdgeConsistent incident xs ys -> sum_degree eq_dec xs ys incident = 2 * (length ys).
intros.
induction ys.
admit.
destruct xs.
admit.
simpl in *.
inversion H1.
subst.
destruct H4.
destruct H6.
subst.
set (degree_eq_edge _ _ _ eq_dec ((incident a).1 :: xs) ys _ H3).
simpl in *.
rewrite e.
inversion H.
subst.
admit.
inversion H.
subst.
have : (incident a).1 <> (incident a).2.
admit.
move => H9.
have : check_vertices eq_dec (incident a).1 (incident a).1 = 1.
admit.
move => H10.
rewrite H10; clear H10.
have : check_vertices eq_dec (incident a).1 (incident a).2 = 0.
admit.
move => H10.
rewrite H10; clear H10.
have :        degree eq_dec ((incident a).1 :: xs) ys incident (incident a).1 +
       sum_degree eq_dec xs ys incident = length ys + (length ys + 0).
apply IHys.
by inversion H0.
assumption.
move => H10.


set (degree_diff_edge _ _ _ eq_dec ((incident a).1 :: xs) ys _ H9).
simpl in *.


destruct xs.
admit.
simpl.


induction xs.
simpl in *.
inversion H1.
trivial.
inversion H2.
inversion H1.
simpl.
by rewrite zero_edges.
subst.
destruct H2.
destruct H3.
subst.
simpl.
set (degree_eq_edge _ _ _ eq_dec ((incident y).1 :: xs) ys0 _ H3).
simpl in e.
rewrite e.
inversion H0.
subst.
admit.
inversion H.
subst.
simpl.
have : (incident y).1 <> (incident y).2.
admit.
move => H9.
set (degree_diff_edge _ _ _ eq_dec ((incident y).1 :: xs) ys0 _ H9).
simpl.
simpl in e.



rewrite IHxs.
by inversion H.

rewrite degree_eq_edge.


unfold check_vertices.
destruct H3.
destruct H2.
subst.
remember (eq_dec (incident y).1 (incident y).1).


Theorem degree_count_eq
   A B b (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) 
      : NoDup ys -> NoDup xs -> In (incident b).1 xs /\ In (incident b).2 xs -> 
     degree eq_dec xs (b :: ys) incident (incident b).1 = degree eq_dec xs (b :: ys) incident (incident b).2.
intros.
simpl.
have : degree eq_dec xs ys incident (incident b).1 = degree eq_dec xs ys incident (incident b).2.
induction ys.
trivial.
simpl in *.
rewrite IHys.
by inversion H.
trivial.
intros.
by rewrite H2.
Qed.

Theorem degree_count_right A B b (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) 
      : NoDup ys -> NoDup xs -> In (incident b).1 xs /\ In (incident b).2 xs -> 
     degree eq_dec xs (b :: ys) incident (incident b).2 = degree eq_dec xs ys incident (incident b).2 + 2.
intros.
rewrite <- degree_count_eq.
rewrite degree_count_left.
auto. auto. auto.  auto. auto. auto. auto.
Qed.

Theorem dup_only_1 A B a (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) :
     In (incident a).1 xs /\ In (incident a).2 xs -> sum_degree eq_dec xs (a :: ys) incident = sum_degree eq_dec xs ys incident + (2 * count.
     
intros.
induction xs.
admit.
simpl.



Qed.


Theorem count_degree  A B b (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) :
   NoDup xs -> In (incident b).1 xs ->  In (incident b).2 xs -> 
   Nat.add (count_occ eq_dec xs (incident b).1) (count_occ eq_dec xs (incident b).2) = 2.
intros.
rewrite dup_only_1.
assumption.
assumption.
rewrite dup_only_1.
assumption.
assumption.
trivial.
Qed.


Theorem degree_edge A B b (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) :
   NoDup xs -> NoDup (b :: ys) -> 
   In (incident b).1 xs /\ In (incident b).2 xs ->
   sum_degree eq_dec xs (b :: ys) incident = sum_degree eq_dec xs ys incident + 2.
intros.
induction H.
inversion H1.
inversion H.
destruct H1.
simpl.
remember (incident b).
destruct p.


Theorem degree_edge A B (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) :
   NoDup xs -> NoDup ys -> 
   (forall b, In (incident b).1 xs /\ In (incident b).2 xs) ->
   sum_degree eq_dec xs (b :: ys) incident = (sum_degree eq_dec xs ys incident) + 2.
intros.
induction H0.
destruct xs.
destruct (H1 b).
inversion H0.


inversion H1.
simpl in *.
remember (incident b).
destruct H1.
destruct H2.


Theorem sum_degree_all A B (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A):
    NoDup xs -> NoDup ys -> (forall b, In (incident b).1 xs /\ In (incident b).2 xs) -> sum_degree eq_dec xs ys incident = 2 * length ys.
intros.
induction H0.
destruct xs.
trivial.
simpl.
admit.
simpl in *.
destruct H.

simpl in *.
by destruct H1.
simpl.
remember (incident x).
pose (H1 x).


rewrite count_degree.



inversion H1.
subst.


Definition make_edge_consistent {A} {B} (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) : 
     list B.
induction ys.
exact [].
destruct (incident a).
destruct (@count_occ _ eq_dec xs a0).
exact IHys.
destruct (@count_occ _ eq_dec xs a1).
exact IHys.
exact (a :: IHys).
Defined.

Theorem occurrences_edges {A} {B} a (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A) 
    : make_edge_consistent eq_dec xs (a :: ys) incident = make_edge_consistent eq_dec xs ys incident \/ (In (incident a).1 xs /\ In (incident a).2 xs).
induction ys.
simpl.
destruct (incident a).
remember (count_occ eq_dec xs a1).
remember (count_occ eq_dec xs a0).
destruct n.
destruct n0.
by left.
by left.
destruct n0.
by left.
right.
pose (count_occ_In eq_dec xs a0).
pose (count_occ_In eq_dec xs a1).
destruct i; destruct i0.
constructor.
apply : H0.
rewrite <- Heqn0.
auto with arith.
apply : H2.
rewrite <- Heqn.
auto with arith.
simpl in *.
destruct (incident a).
remember (count_occ eq_dec xs a1).
destruct (incident a0).
remember (count_occ eq_dec xs a3).
destruct n.
destruct n0.
by left.
remember (count_occ eq_dec xs a4).
destruct n.
by left.
by left.
remember (count_occ eq_dec xs a2).
remember (count_occ eq_dec xs a4).
destruct n0.
destruct n1.
by left.
destruct IHys.
by left.
by right.
destruct n1.
destruct n2.
by left.
by left.
destruct n2.
destruct IHys.
by left.
by right.
destruct IHys.
have : forall a ys, a :: ys = ys -> False.
intros.
induction ys0.
inversion H0.
injection H0.
move => H3 H4.
subst.
by apply : IHys0.
move => inj_false.
destruct (inj_false _ _ _ H).
by right.
Qed.


Theorem hand_shake_incident : forall {A B} a (ys : list B) (xs : list A) (eq_dec : EqDec A) (incident : B -> A * A),
   NoDup xs ->
   NoDup (a :: ys) ->
   In (incident a).1 xs /\ In (incident a).2 xs ->
   sum_degree eq_dec xs ys incident = 2 * (length ys) ->
   sum_degree eq_dec xs (a :: ys) incident = (2 * (length ys)) + 2.

intros.
remember (a :: ys).
dependent induction H0.
admit.
clear IHNoDup.
injection Heql.
move => inj inkj2; subst.
unfold sum_degree.
simpl.
remember (incident0 a).
destruct p.
destruct H2.


destruct H.
simpl in *.
destruct H2.
destruct H.
destruct H0.
simpl in *.
remember (incident0 a).
destruct p.

simpl in *.

clear IHNoDup.


simpl in *.
destruct (incident0 a).
simpl in H2.
destruct H3.
destruct H2.
destruct H2.



induction H0.
inversion H1.
inversion H.
simpl in *.


unfold sum_degree in H0.
simpl in *.
remember (incident0 a).
destruct p.


destruct (incident0 a).

destruct (incident0 a).
Admitted.


Theorem hand_shake  {A B} (eq_dec : EqDec A) (xs : list A) (ys : list B) (incident : B -> A * A):
    sum_degree eq_dec xs (make_edge_consistent eq_dec xs ys incident) incident = 2 * (length (make_edge_consistent eq_dec xs ys incident)).
intros.
generalize dependent xs.
induction ys.
intros.
simpl.
destruct xs.
trivial.
simpl.
by induction xs.
intros.
pose (IHys xs).
destruct (occurrences_edges a eq_dec xs ys incident).
rewrite <- H in e.
assumption.
simpl.
destruct (incident a).
remember (count_occ eq_dec xs a0).
remember (count_occ eq_dec xs a1).
destruct H.
destruct (count_occ_In eq_dec xs a0).
destruct (count_occ_In eq_dec xs a1).
destruct n.
auto with arith.
destruct n0.
auto with arith.
simpl.



unfold make_edge_consistent.


remember (get_graph_vertices graph).
remember (get_graph_edges graph).


simpl.

unfold sum_degree.
unfold get_graph_vertices.
unfold get_graph_edges.
do 2! destruct finite.
induction x.
destruct x0.
trivial.
destruct (@incident _ _ graph b).
destruct (f a).
simpl.



admit.
intros.

induction (get_graph_vertices graph).
simpl in *.


simpl in *.
remember (get_graph_edges graph).
destruct l.
unfold get_graph_edges in Heql.
destruct finite.


trivial.
simpl in *.
destruct (incident b).
unfold get_graph_vertices in Heql.
destruct finite.
unfold Full in f.
pose (f a).
rewrite <- Heql in i.
inversion i.



Fixpoint interval_fin {x y: nat} : y < x -> list (t x).
destruct y.
move => H.
exact [(of_nat_lt H)].
move => H.
exact ((of_nat_lt H) :: interval_fin x y (PeanoNat.Nat.lt_succ_l _ _ H)).
Defined.

Lemma Fin1Eq : forall (x y : t 1), x = y.
remember 1.
destruct x.
elim/@caseS'.
trivial.
intros.
assert (n = 0).
auto.
subst.
inversion p.
assert (n = 0).
auto.
subst.
inversion x.
Qed.

Theorem of_nat_irr : forall x (v : t x) p (H : p < x), exist _ p H = to_nat v -> v = of_nat_lt H.
intros.
rewrite <- to_nat_of_nat in H0.
rewrite <- of_nat_to_nat_inv.
rewrite H0.
by rewrite of_nat_to_nat_inv.
Qed.


Theorem FinitNatInd : 
   forall b x (v : t x) (H : b < x), proj1_sig (to_nat v) <= b -> In v (interval_fin H).
intros.
generalize dependent x.
induction b.
intros.
destruct x.
inversion H.
elim/@caseS : v H H0.
intros.
by left.
intros.
simpl in *.
destruct (to_nat p).
simpl in *.
inversion H0.
intros.
destruct v.
destruct b.
by right; left.
pose (IHb (S n) F1 (PeanoNat.Nat.lt_succ_l _ _ H) (PeanoNat.Nat.le_0_l _)).
by right.
simpl.
inversion H0.
simpl in *.
remember (to_nat v).
destruct s.
subst; simpl in *.
left.
inversion H2; subst.
apply (f_equal FS).
rewrite <- of_nat_to_nat_inv.
apply of_nat_irr.
rewrite <- to_nat_of_nat.
rewrite <- Heqs.
simpl.
by rewrite (@Peano_dec.le_unique (S b) n l (proj2 (PeanoNat.Nat.succ_lt_mono b n) H)).
right; subst.
exact (IHb (S n) (FS v) (PeanoNat.Nat.lt_succ_l _ _ H) H2).
Qed.


Lemma FiniteFin : forall x, Finite (t x).
move => x.
destruct x.
exists [].
move => t.
inversion t.
exists (@interval_fin _ x (le_n (S x))).
unfold Full.
move => a.
apply FinitNatInd.
elim/@rectS : a.
auto with arith.
intros.
simpl.
by destruct (to_nat p).
Qed.


Fixpoint nth_fin {A} (xs : list A) : t (length xs) -> A.
    refine(match xs as c return (t (length c)) -> A with
        |[] => fun i => match i with end
        |x :: xs' => _
    end).
Proof.
move => i.
remember (length (x :: xs')).
destruct i.
exact x.
injection Heqn.
move => inj; rewrite inj in i.
exact (nth_fin A xs' i).
Defined.


Section FinGraph.

Definition fin_list_to_incident_function {x} (xs : list ((t x) * (t x))) : 
    t (length xs) -> (t x) * (t x) := fun i => nth_fin xs i.

Instance SymbolFin (x : nat) : Symbol (t x) := {
    finite := (FiniteFin x);
    eq_dec := Coq.Vectors.Fin.eq_dec;
}. 


Instance GraphFin (x : nat) (edges : list ((t x) * (t x))) : Graph (t x) (t (length edges)) := {
    symbol_A := SymbolFin x;
    symbol_B := SymbolFin (length edges);
    incident := fin_list_to_incident_function edges;
}.
End FinGraph.





