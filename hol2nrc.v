
Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.

Axiom excluded_middle_informative : forall P:Prop, {P} + {~ P}.

Axiom proof_irrelevence : forall (P:Prop) (p1 p2: P), p1 = p2. 

Require Import Coq.Program.Equality.
(* adds Axiom JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y. *)

Close Scope nat_scope.

Require Import Coq.Sets.Image.
Require Import Coq.Sets.Powerset.

Implicit Arguments Im.
Implicit Arguments Singleton.
Implicit Arguments Union.
Implicit Arguments Power_set.
Implicit Arguments Intersection.
Implicit Arguments Full_set.

Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
Proof.
 apply functional_extensionality_dep.
Qed.

Lemma equal_f : forall {A B : Type} {f g : A -> B},
  f = g -> forall x, f x = g x.
Proof.
 intros; subst; auto.
Qed.

Lemma isect_def : forall a (f g : Ensemble a),
Intersection f g = fun x : a => f x /\ g x.
Proof.
 intros. apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. inversion H.
 subst. auto. intros. constructor. unfold In. destruct H. auto.
 auto. unfold In. destruct H. auto.
Qed.

Lemma union_def : forall a (f g : Ensemble a),
 Union f g = fun x : a => f x \/ g x.
Proof.
 intros. apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. inversion H.
 subst. auto. subst. auto. intros. destruct H. constructor.
 auto. constructor 2. auto.
Qed. 

 Lemma Im_Union s t {X Y: Ensemble s} {f: s -> t} 
 : Im (Union X Y) f = Union (Im X f) (Im Y f).
 Proof.
   intros. apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. inversion H.
 subst. unfold In in *. clear H. 
 inversion H0. subst. unfold In in *. constructor.
 unfold In. econstructor. unfold In. eauto. auto. subst.
  unfold In in *. constructor 2. unfold In. econstructor.
 unfold In. eauto. auto.

intros. destruct H. unfold In in *. inversion H. subst. clear H.
 unfold In in *. econstructor. unfold In. constructor. unfold In.
 eauto. auto. unfold In in *. inversion H. subst. clear H.
 unfold In in *. econstructor. unfold In. constructor 2. unfold In.
 eauto. auto.
Qed.

 Lemma Im_Singleton s t {x: s} {f: s -> t} 
 : Im (Singleton x) f = Singleton (f x).
Proof.
  intros. apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. inversion H.
 subst. unfold In in *. clear H. 
 inversion H0. subst. constructor. 

 intros. inversion H. subst. econstructor.
 unfold In. instantiate (1:=x). constructor. auto.
Qed.

Definition join {X} (I : Ensemble (Ensemble X)) : Ensemble X :=
 fun j => exists J, I J /\ J j.

Definition cartprod {X Y} (I: Ensemble X) (J: Ensemble Y) : Ensemble (X*Y) :=
 fun z : X*Y => I (fst z) /\ J (snd z). 

Definition disjunion {X Y} (I: Ensemble X) (J: Ensemble Y) : Ensemble (X+Y) :=
 fun z : X+Y => match z with 
                  | inl x => I x
                  | inr y => J y
                end. 

Definition mono {B C} (f: B -> C) := forall A (g h : A -> B), 
  ((fun x => f (g x)) = (fun x => f (h x)) -> (g = h)).

Inductive void : Set := .

Inductive ty : Set :=
 | one : ty
 | prop : ty
 | prod : ty -> ty -> ty
 | pow : ty -> ty
 | dom : ty
 | zero : ty
 | sum : ty -> ty -> ty.

Fixpoint inst (t: ty) : Set -> Type :=
 fun (D: Set) =>
 match t with
   | one => unit
   | prod t1 t2 => inst t1 D * inst t2 D
   | pow t' => inst t' D -> Prop
   | dom => D
   | prop => Prop
   | sum t1 t2 => inst t1 D + inst t2 D
   | zero => void 
 end. 

Fixpoint apply {D1 D2 : Set} (f: D1 -> D2) {t} : inst t D1 -> inst t D2 :=
 match t as t return inst t D1 -> inst t D2 with
     | one => fun I => I
     | prod t1 t2 => fun I =>  (apply f (fst I), apply f (snd I))
     | dom => f
     | pow t' => fun I => Im I (apply f)   
     | prop => fun I => I
     | zero => fun I => I
     | sum t1 t2 => fun I => match I with
                                 | inl I' => inl (apply f I')
                                 | inr I' => inr (apply f I')
                             end
 end.

Definition di {G t} (e: forall D, inst G D -> inst t D) 
 := forall (D1 D2: Set) (f: D1 -> D2) (pf: mono f) I, 
apply f (e D1 I) = e D2 (apply f I) .


Inductive exp : ty -> ty -> Set :=
 | equal : forall {t}, exp (prod t t) prop
 | inj1 : forall {t1 t2}, exp t1 (sum t1 t2)
 | inj2 : forall {t1 t2}, exp t2 (sum t1 t2)
 | case : forall {t1 t2 t3}, exp t1 t3 -> exp t2 t3 -> exp (sum t1 t2) t3   
 | id : forall {t}, exp t t
 | comp : forall {t1 t2 t3}, exp t1 t2 -> exp t2 t3 -> exp t1 t3
 | star : forall {t}, exp t one
 | pi1 : forall {t1 t2}, exp (prod t1 t2) t1
 | pi2 : forall {t1 t2}, exp (prod t1 t2) t2
 | pair : forall {t1 t2 t3}, exp t1 t2 -> exp t1 t3 -> exp t1 (prod t2 t3)
 | ev : forall {t}, exp (prod (pow t) t) prop 
 | curry : forall {t1 t2}, exp (prod t1 t2) prop -> exp t1 (pow t2)
 | contra : forall {t}, exp zero t
 | boolean1 : exp prop (sum one one)
 | boolean2 : exp (sum one one) prop
 | dist1 : forall {a b c}, exp (prod a (sum b c)) (sum (prod a b) (prod a c))
 | dist2 : forall {a b c}, exp (sum (prod a b) (prod a c)) (prod a (sum b c)).


Fixpoint denote {G t: ty} (e: exp G t) D : inst G D -> inst t D :=
    match e in exp G t return inst G D -> inst t D with
      | id t => fun I => I
      | comp t1 t2 t3 f g => fun I => denote g D (denote f D I)
      | star t => fun I => tt
      | pi1 t1 t2 => fun I => fst I
      | pi2 t1 t2 => fun I => snd I
      | pair t1 t2 t3 f g => fun I =>  (denote f D I, denote g D I)
      | ev t => fun I => (fst I) (snd I)
      | curry t1 t2 f => fun I => 
                 (fun J => denote f D (I, J)) 
      | equal t => fun I => fst I = snd I
      | inj1 t1 t2 => inl
      | inj2 t1 t2 => inr
      | case t1 t2 t3 f g => fun I => match I with
                                          | inl i => denote f D i
                                          | inr i => denote g D i
                                      end
      | contra t => fun I => match I with end
      | boolean1 => fun I => match excluded_middle_informative I with
                              | left _ => inl tt
                              | right _ => inr tt
                            end
      | boolean2 => fun I => match I with
                               | inl _ => True
                               | inr _ => False
                             end
      | dist1 a b c => fun I => match snd I with
                                  | inl l => inl (fst I, l)
                                  | inr r => inr (fst I, r)
                                end
      | dist2 a b c => fun I => match I with
                                     | inl l => (fst l, inl (snd l))
                                     | inr r => (fst r, inr (snd r))
                                end
    end.

Inductive expB : ty -> ty -> Type :=
 | equalB : forall {t}, expB (prod t t) prop
 | inj1B : forall {t1 t2}, expB t1 (sum t1 t2)
 | inj2B : forall {t1 t2}, expB t2 (sum t1 t2)
 | caseB : forall {t1 t2 t3}, expB t1 t3 -> expB t2 t3 -> expB (sum t1 t2) t3   
 | idB : forall {t}, expB t t
 | compB : forall {t1 t2 t3}, expB t1 t2 -> expB t2 t3 -> expB t1 t3
 | starB : forall {t}, expB t one
 | pi1B : forall {t1 t2}, expB (prod t1 t2) t1
 | pi2B : forall {t1 t2}, expB (prod t1 t2) t2
 | pairB : forall {t1 t2 t3}, expB t1 t2 -> expB t1 t3 -> expB t1 (prod t2 t3)
 | mzero : forall {t}, expB one (pow t)
 | mplus : forall {t}, expB (prod (pow t) (pow t)) (pow t) 
 | mjoin : forall {t}, expB (pow (pow t)) (pow t)
 | munit : forall {t}, expB t (pow t)
 | mpow : forall {t}, expB (pow t) (pow (pow t))
 | mmap : forall {t1 t2}, expB t1 t2 -> expB (pow t1) (pow t2)
 | boolean1B : expB prop (sum one one)
 | boolean2B : expB (sum one one) prop
 | str : forall {t1 t2}, expB (prod t1 (pow t2)) (pow (prod t1 t2))
 | contraB : forall {t}, expB zero t
 | dist1B : forall {a b c}, expB (prod a (sum b c)) (sum (prod a b) (prod a c))
 | dist2B : forall {a b c}, expB (sum (prod a b) (prod a c)) (prod a (sum b c)).

Fixpoint denoteB {G t: ty} (e: expB G t) D : inst G D -> inst t D :=
    match e in expB G t return inst G D -> inst t D with
      | idB t => fun I => I
      | compB t1 t2 t3 f g => fun I => denoteB g D (denoteB f D I)
      | starB t => fun I => tt
      | pi1B t1 t2 => fun I => fst I
      | pi2B t1 t2 => fun I => snd I
      | pairB t1 t2 t3 f g => fun I =>  (denoteB f D I, denoteB g D I)
      | equalB t => fun I => fst I = snd I
      | inj1B t1 t2 => inl
      | inj2B t1 t2 => inr
      | caseB t1 t2 t3 f g => fun I => match I with
                                          | inl i => denoteB f D i
                                          | inr i => denoteB g D i
                                      end
      | mzero t => fun I => Empty_set _
      | mplus t => fun I => Union (fst I) (snd I)
      | mjoin t => fun I => join I
      | munit t => fun I => Singleton I
      | mpow t => fun I => Power_set I
      | mmap t1 t2 f => fun I => Im I (denoteB f D)
      | boolean1B => fun I => match excluded_middle_informative I with
                              | left _ => inl tt
                              | right _ => inr tt
                            end
      | boolean2B => fun I => match I with
                               | inl _ => True
                               | inr _ => False
                             end
      | str t1 t2 => fun I => Im (snd I) (fun J => (fst I, J))
      | contraB t => fun I => match I with end 
      | dist1B a b c => fun I => match snd I with
                                  | inl l => inl (fst I, l)
                                  | inr r => inr (fst I, r)
                                end
      | dist2B a b c => fun I => match I with
                                     | inl l => (fst l, inl (snd l))
                                     | inr r => (fst r, inr (snd r))
                                end
    end.

Fixpoint atoms {t D} : inst t D -> inst (pow dom) D :=
 match t as t return inst t D -> inst (pow dom) D with
   | one => fun I => @Empty_set _
   | prod t1 t2 => fun I => Union  (atoms (fst I)) (atoms (snd I))
   | prop => fun I => @Empty_set _
   | dom => fun I => Singleton I
   | pow t' => fun I => join (Im I atoms ) 
   | zero => fun I => @Empty_set _
   | sum t1 t2 => fun I => match I with
                               | inl I1 => atoms I1
                               | inr I2 => atoms I2
                           end
 end.

Definition makeProd {s1 s2 t1 t2} (f : expB s1 t1) (g : expB s2 t2) 
 : expB (prod s1 s2) (prod t1 t2) :=
 pairB (compB pi1B f) (compB pi2B g).

Definition makeSum {s1 s2 t1 t2} (f : expB s1 t1) (g : expB s2 t2) 
 : expB (sum s1 s2) (sum t1 t2) :=
 caseB (compB f inj1B) (compB g inj2B).

Fixpoint atomsB {t} : expB t (pow dom)  :=
 match t as t return expB t (pow dom) with
   | one  => compB starB  mzero
   | prop => compB starB mzero
   | zero => compB starB mzero
   | dom => munit
   | pow t => compB (mmap atomsB) mjoin    
   | prod t1 t2 => compB (makeProd atomsB atomsB) mplus
   | sum t1 t2 => caseB atomsB atomsB
 end.

Theorem atomsSem : forall G D, denoteB (@atomsB G) D = atoms . 
Proof.
 induction G; try (simpl in *; auto).

 intros; rewrite IHG1; rewrite IHG2; auto.
 Focus 2. intros; rewrite IHG1; rewrite IHG2; auto.

 intros; rewrite IHG; auto.
Qed.

Fixpoint univ t {D} (I: inst (pow dom) D) : inst (pow t) D :=
 match t as t return inst (pow t) D with
   | one => Singleton tt 
   | prod t1 t2 =>  cartprod (univ _ I) (univ _ I) 
   | prop => Union (Singleton True) (Singleton False)
   | dom => I
   | pow t' => Power_set (univ _ I) 
   | zero => @Empty_set _
   | sum t1 t2 => disjunion (univ _ I) (univ _ I)
 end.


Definition trueB {G} : expB G prop := 
 compB starB (compB inj1B boolean2B).

Definition falseB {G} : expB G prop :=
 compB starB (compB inj2B boolean2B).

Definition trueE {G} : exp G prop := 
 comp star (comp inj1 boolean2).

Definition falseE {G} : exp G prop :=
 comp star (comp inj2 boolean2).

Definition singletonB {G X} (I: expB G X) : expB G (pow X) :=
  compB I munit.

Definition bindB {G s t} (f: expB (prod G t) (pow s))
 (X : expB G (pow t)) : expB G (pow s) :=
   compB (compB (compB (pairB idB X) str) (mmap f)) mjoin.

Definition cartprodB {G X Y} (I: expB G (pow X)) (J: expB G (pow Y)) 
 : expB G (pow (prod X Y)) := 
 bindB (bindB (compB (pairB (compB pi1B pi2B) pi2B) munit) (compB pi1B J)) I.

Theorem cartprodSem {G s t} : forall (x : expB G (pow s)) (y : expB G (pow t)),
 forall D I,
 denoteB (cartprodB x y) D I = cartprod (denoteB x D I) (denoteB y D I).
Proof.
 simpl. fold inst. intros. unfold join. apply functional_extensionality.
 intros. destruct x0. apply prop_extensionality. split.
 intros. destruct H. destruct H. inversion H. clear H.
 subst. destruct H0. destruct H. inversion H. clear H.
 subst. destruct x2. destruct p. destruct x1. simpl in *. unfold In in *.
 inversion H1. subst. clear H1. inversion H2. clear H2. subst.
 unfold In in *. assert (i4 = I). congruence. subst i4.
 assert (x0 = i5). congruence. subst x0. assert (i2 = I). congruence.
 subst. assert (i3 = i5). congruence. subst. assert (i1 = x1). congruence.
 subst. clear H3 H4. inversion H0. subst. clear H0.
 unfold cartprod. simpl. auto.

 intros. unfold cartprod in *. destruct H. simpl in *.

 eexists. split. econstructor. unfold In. econstructor.
 unfold In. eauto. eauto. split. simpl. 

 eexists. econstructor. econstructor. unfold In.
 econstructor. unfold In. eauto. eauto. eauto.
 simpl. constructor.
Qed.

Definition unionB {G X} (I J: expB G (pow X)) : expB G (pow X) :=
 compB (pairB I J) mplus.


Theorem unionSem {G s} : forall (x y : expB G (pow s)),
 forall D I,
 denoteB (unionB x y) D I = Union (denoteB x D I) (denoteB y D I).
Proof.
 intros. unfold unionB. simpl. auto.
Qed.


Definition disjunionB {G X Y} (I: expB G (pow X)) (J: expB G (pow Y)) 
 : expB G (pow (sum X Y)) :=   
 unionB (compB I (mmap inj1B)) (compB J (mmap inj2B)) .

Theorem disjunionSem {G X Y} : forall (x: expB G (pow X)) (y: expB G (pow Y)) ,
 forall D I,
 denoteB (disjunionB x y) D I = disjunion (denoteB x D I) (denoteB y D I).
Proof.
 intros. simpl. unfold disjunion. fold inst. apply functional_extensionality.
 intros. destruct x0. apply prop_extensionality. split. intros.
 inversion H. clear H. subst. unfold In in *. inversion H0. clear H0. subst.
 unfold In in *. assert (i = x0). congruence. subst. auto.
 subst. unfold In in *.  inversion H0. subst. unfold In in *.
 discriminate. intros. constructor. unfold In. econstructor. unfold In.
 eauto. auto. apply prop_extensionality. split. intros.
 inversion H. clear H. subst. unfold In in *. inversion H0.
 subst. clear H0. discriminate.
 subst. unfold In in H0. inversion H0. subst. assert (i = x0).
 congruence. clear H0. subst. unfold In in H1. auto.
 intros. constructor 2. unfold In. econstructor. unfold In. eauto. auto.
Qed.

Fixpoint univB t : expB (pow dom) (pow t) :=
 match t as t return expB (pow dom) (pow t) with
   | one => compB starB munit
   | zero => compB starB mzero
   | dom => idB
   | pow t' => compB (univB _) mpow
   | prod t1 t2 => cartprodB (univB _) (univB _)
   | sum t1 t2 => disjunionB (univB _) (univB _) 
   | prop => unionB (singletonB trueB) (singletonB falseB)
 end.

Theorem univSem {t} : forall D (I: inst (pow dom) D), 
 denoteB (univB t) D I = univ t I.
Proof.
 intros. induction t.

  simpl in *; auto.
  simpl in *; auto.
  Focus 3. simpl in *. auto.
  Focus 3. simpl in *. auto.

  unfold univ. fold univ. rewrite <- IHt1. rewrite <- IHt2.
  apply cartprodSem.

  unfold univ. fold univ. rewrite <- IHt.  clear IHt.
  unfold univB. fold univB. simpl. auto.

  unfold univ. fold univ. rewrite <- IHt1. rewrite <- IHt2.
  apply disjunionSem.
Qed.

Definition UB {G t} : expB G (pow t)  :=  
 compB atomsB (univB t).

Definition U {G t D} : inst G D -> inst (pow t) D  :=  
 fun I => univ t (atoms I).

Theorem uSem {t} : forall D (I: inst t D), denoteB UB D I = U (t:=t) I .
Proof. 
 intros. unfold UB. unfold U.
 simpl. rewrite univSem. rewrite atomsSem. auto.
Qed.

Theorem uSem2 { s t} : forall D (I: inst t D) (J: inst s D), denoteB UB D I J = U I J.
Proof. 
 intros. unfold UB. unfold U.
 simpl. rewrite univSem. rewrite atomsSem. auto.
Qed.

Lemma eq_push {A B} {f g : A -> B} :
f = g -> forall x, f x = g x.
Proof.
 intros. subst. reflexivity.
Qed.

Lemma mono_elim {A B} (f: A -> B) : mono f -> forall x y, f x = f y -> x = y.
Proof.
 intros. unfold mono in H. pose (H unit (fun _ => x) (fun _ => y)).
 simpl in *.
 cut ( (fun _ : unit => f x) = (fun _ : unit => f y) ).
 intros. pose (e H1). apply equal_f in e0. assumption. apply tt.
 rewrite H0. apply functional_extensionality. intros. reflexivity.
Qed.

Lemma im_mono {D1 D2} (f : D1 -> D2) :
 mono f -> mono (fun x => Im x f).
Proof.
 unfold mono.
 intros. apply functional_extensionality. intros.
 apply equal_f with x in H0. 
 cut (injective _ _ f). intros pf.
 pose (In_Image_elim D1 D2 (g x) f pf). unfold In in *. 
 rewrite H0 in i.
 pose (In_Image_elim D1 D2 (h x) f pf). unfold In in *. 
 apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. apply i0. 
 rewrite <- H0.
 econstructor. unfold In. eauto. auto.
 intros. apply i. econstructor. unfold In. eauto. auto.

 pose (@mono_elim _ _ _ H). auto.
Qed. 

 Lemma im_elim2 {A B} (g h : Ensemble A) (f : A -> B) 
 (pf : injective _ _ f) : Im g f  = Im h f -> g = h .
 Proof.
  intros. 
   pose (In_Image_elim _ _ g f pf). unfold In in i.
    pose (In_Image_elim _ _ h f pf). unfold In in i0.
   apply functional_extensionality. intros. 
  pose (i x). pose (i0 x). apply prop_extensionality. clearbody g0 h0. clear i i0.
  split. 
   intros. apply h0.
   rewrite <- H. econstructor. unfold In.
   eauto. reflexivity.
   intros. apply g0. rewrite H. econstructor. unfold In.
   eauto. reflexivity.
Qed.

 Lemma im_elim {A B} (g h : Ensemble A) (f : A -> B) 
 (pf : mono f) : Im g f  = Im h f -> g = h .
 Proof.
  pose (@mono_elim _ _ _ (im_mono _ pf)). apply e.
Qed.

Lemma monoToInj {A B} {f: A -> B} : mono f -> injective _ _ f. 
Proof.
 intros. pose (mono_elim _ H).
 unfold injective. assumption.
Qed.

Lemma inlMono {A B} : mono (@inl A B).
Proof.
  unfold mono. intros. apply functional_extensionality.
  intros. apply equal_f with x in H.
  congruence.
Qed.

Lemma inrMono {A B} : mono (@inr A B).
Proof.
  unfold mono. intros. apply functional_extensionality.
  intros. apply equal_f with x in H.
  congruence.
Qed.

Lemma apply_mono {D1 D2 : Set} {t} (f : D1 -> D2) :
 mono f -> mono (apply (t:=t) f).
Proof.
 induction t; (try unfold mono; auto). 

 simpl in *. intros. 
 pose (IHt1 H). pose (IHt2 H). clearbody m m0. clear IHt1 IHt2 H.
 apply functional_extensionality. intros.
 remember (g x). remember (h x). destruct (p). destruct (p0).
 pose (equal_f H0 x) as eqf. simpl in eqf. 
 rewrite <- Heqp in  eqf. rewrite <- Heqp0 in eqf. simpl in eqf.
 assert (apply f i =  apply f i1). congruence.
 assert (apply f i0 =  apply f i2). congruence.
 cut (i = i1 /\ i0 = i2). intros. destruct H2. congruence.
 pose (mono_elim _ m i i1 H).
 pose (mono_elim _ m0 i0 i2 H1). auto.

 unfold mono. intros. 
 apply functional_extensionality. intros.
 pose (equal_f H0 x) as eqf. simpl in eqf. clearbody eqf.

 apply im_elim2 with (apply f).
 apply monoToInj. apply IHt. assumption. assumption.

 simpl in *. intros. 
 pose (IHt1 H). pose (IHt2 H). clearbody m m0. clear IHt1 IHt2 H.
 apply functional_extensionality. intros.
 pose (equal_f H0 x) as eqf. simpl in eqf. clearbody eqf.
 remember (g x). remember (h x). destruct (s); destruct (s0). 
 pose (mono_elim _ (inlMono) _ _ eqf).
 clearbody e. clear eqf.
 pose (mono_elim _ m _ _ e). rewrite e0. reflexivity.
 discriminate. discriminate.
 pose (mono_elim _ (inrMono) _ _ eqf).
 clearbody e. clear eqf.
 pose (mono_elim _ m0 _ _ e). rewrite e0. reflexivity.
Qed.

Lemma pair_ind {t1 t2 t3} {e1: exp t1 t2} {e2: exp t1 t3} :
 di (denote (pair e1 e2))
-> (  di (denote e1) /\ di (denote e2) ).
Proof.
 unfold di in *; simpl in *; split; intros;  
 pose (H D1 D2 f pf I); congruence.
Qed.

 Lemma abs_ind {t1 t2} {e : exp (prod t1 t2) prop} :
 di (denote (curry e)) -> di (denote e).
 Proof.
  intros. simpl in H. fold inst in H. 
  unfold di in *. intros. simpl in *. destruct I. simpl in *.
  pose (H D1 D2 f pf i). clearbody e0. clear H.
  pose (eq_push e0). clearbody e1. clear e0. pose (e1 (apply f i0)).
  clearbody e0. clear e1. simpl in *. rewrite <- e0. clear e0.
  apply prop_extensionality. split. intros. 
  econstructor. unfold In. simpl. eauto. reflexivity.
  intros. inversion H. fold inst in *. subst. unfold In in *.
  cut (i0 = x). intros. subst. assumption.
  pose (@apply_mono _ _ t2 f pf).
  eapply mono_elim.
 eauto. assumption.
Qed.

 Lemma atomsFunctor t1 {D1 D2: Set} x0 (f: D1 -> D2) (I: inst t1 D1) :
   atoms I x0 ->
   atoms (apply f I) (f x0).
 Proof.
  induction t1; simpl.

  intros. inversion H.
  intros. inversion H.

  destruct I. simpl. intros. 
  pose (IHt1_1 i). pose (IHt1_2 i0). destruct H.
  unfold In in *. apply Union_introl. unfold In. apply a. assumption.
  apply Union_intror. apply a0. assumption.

  Focus 2. intros. inversion H. subst. constructor.

  intros. unfold join in *. destruct H. destruct H.
  inversion H. subst. fold inst in *. pose (IHt1 _ H0).
  unfold In in * . clearbody a. clear IHt1. clear H.
  exists ( (atoms (apply f x1))). split; try auto.
  econstructor.  unfold In. econstructor. unfold In. eauto. eauto. eauto.

  intros. elim H.

  intros. destruct I. pose (IHt1_1 i). clearbody a. pose (a H).
  clearbody a0. assumption.
 pose (IHt1_2 i). clearbody a. pose (a H).
  clearbody a0. assumption.
Qed.


 Lemma applyFunctor t1 t2 D1 D2 x0 f I :
 @U t1 t2 D1 I x0 -> @U t1 t2 D2 (apply f I) (apply f x0).
 Proof.
  induction t2; unfold U in *; simpl in *; try auto.
  fold inst in *.

  unfold cartprod. simpl. destruct x0. simpl.
  intros. destruct H.  split. apply IHt2_1.
   assumption. apply IHt2_2. assumption.

  fold inst in *. intros.
  constructor. unfold Included. intros. unfold In in *.
  inversion H0. subst. unfold In in *. 
  pose (IHt2 x1). clearbody u. clear IHt2.
  cut (univ _ (atoms I) x1). intros pf. pose (u pf).
  assumption.
  inversion H. subst. unfold Included in H2. unfold In in H2.
  apply H2. assumption.

  intros. apply atomsFunctor. assumption.

  fold inst in *. intros.
  unfold disjunion in *. destruct x0. apply IHt2_1. assumption.
  apply IHt2_2. assumption.
Qed.

 Lemma di_isect t1 t2 (p q : forall D, inst t1 D -> inst (pow t2) D) : 
    di p -> di q ->  @di t1 (pow t2) (fun D I => Intersection (p D I) (q D I)).
 Proof.
  intros pf1 pf2. unfold di in *. intros.
  apply functional_extensionality. fold inst. intros J.
  rewrite <- pf1; try assumption. 
  rewrite <- pf2; try assumption. 
  clear pf1 pf2.
  rewrite isect_def. rewrite isect_def.

  simpl. 
   apply prop_extensionality. split. intros.
   inversion H. fold inst in *. subst. clear H.
  unfold In in H0. destruct H0. constructor. econstructor. unfold In.
  eauto. reflexivity. econstructor. unfold In. eauto. reflexivity. 

  intros. destruct H. inversion H. inversion H0. subst.
  fold inst in *. clear H H0.
  cut (x = x0). intros sub. subst. clear H5.
  unfold In in *. econstructor. unfold In. eauto. reflexivity.
  apply mono_elim with (apply f). apply apply_mono. assumption. 
  assumption.
Qed.

Definition Im_def0 {t t0} (X : Ensemble t) (f : t -> t0) : Ensemble t0 
 := fun t0 => exists x : t, X x /\ (f x = t0).

Lemma Im_sem_0 : forall a b c d, (@Im_def0 a b c d = @Im a b c d).
Proof.
 intros.
 apply functional_extensionality. intros. apply prop_extensionality.
 split. intros. unfold Im_def0 in H. destruct H. destruct H.
 subst. econstructor. eauto. eauto.
 intros. inversion H. subst. clear H. unfold Im_def0.
 exists x0. eauto.
Qed.

Lemma Im_def0_eta : @Im_def0 = fun a b c d => @Im_def0  a b c d.
Proof.
 intros. auto.
Qed.

Lemma Im_eta : @Im = fun a b c d => @Im a b c d.
Proof.
 intros. auto.
Qed.

 Lemma uber_ext : 
 forall (f g : forall (a b: Type) (c: a -> Prop) (d: a -> b), b -> Prop), 
  (forall a b c d, f a b c d = g a b c d) -> f = g.
Proof.
 intros.
 pose (functional_extensionality_dep f g).
 apply e.
 intros.
 apply (functional_extensionality_dep (f x) (g x)).
 intros.
 apply (functional_extensionality_dep (f x x0) (g x x0)).
 intros. 
 apply (functional_extensionality_dep (f x x0 x1) (g x x0 x1)).
 intros. 
 apply H.
Qed.

Lemma Im_sem : @Im_def0 = @Im.
Proof.
 apply uber_ext.
 apply Im_sem_0.
Qed.

 Lemma foo {A B} (f : A -> B) I J  :
Im (Power_set I) (fun x => Im x f) J -> Power_set (Im I f) J .
Proof.
 intros H0.
 inversion H0. subst. clear H0. econstructor. unfold Included.
 unfold In in *. inversion H. subst. unfold Included in H0.
 unfold In in *. clear H. intros. inversion H. subst.
 clear H. unfold In in H1. econstructor. unfold In. eauto.
 auto.
Qed.

Definition ImInv {A B} (f: A -> B) (I: Ensemble B) : Ensemble A :=
 fun a:A => I (f a).

Lemma ImInv1 {X Y} {f: X -> Y} I : mono f -> ImInv f (Im I f) = I.
Proof.
 intros.  
 unfold ImInv. apply functional_extensionality. 
 intros. apply prop_extensionality. split. intros.
 inversion H0. subst. assert (x = x0). apply mono_elim with f. auto. auto.
 subst. auto. intros.  apply Im_def. auto.
Qed.

(*
Lemma ImInv2 {X Y} {f: X -> Y} I : mono f -> Im (ImInv f I) f = I.
Proof.
 intros.  
 unfold ImInv. apply functional_extensionality. 
 intros. apply prop_extensionality. split. intros.
 inversion H0. subst. clear H0. unfold In in *. auto.
 intros. econstructor. unfold In. Show Existentials. 


assert (x = x0). apply mono_elim with f. auto. auto.
 subst. auto. intros.  apply Im_def. auto.
Qed.
*)
 
Lemma bar {A B} (f : A -> B) I J (pf: mono f):
Power_set (Im I f) J -> Im (Power_set I) (fun x => Im x f) J.
Proof.
 intros. 
 inversion H. subst. clear H.

 unfold Included in H0. unfold In in H0. rewrite <- Im_sem.
 unfold Im_def0 at 1. 

 exists (fun a:A => I a /\ J (f a)). split. Focus 2.
 apply functional_extensionality. intros. apply prop_extensionality. split.
 intros. destruct H. destruct H. destruct H. subst. auto.
 intros.  rewrite Im_sem. 
  pose (H0 x H). clearbody i. clear H0. 
  inversion i. subst. clear i. unfold In in *.
  econstructor. unfold In. eauto. auto.


 econstructor. unfold Included.
 intros. unfold In in *.
 auto . destruct H. auto.
Qed.

 Lemma baz {A B} (f : A -> B) I  : mono f ->
Power_set (Im I f) = Im (Power_set I) (fun x => Im x f).
Proof.
 intros.
 apply functional_extensionality.
 intros. apply prop_extensionality.
 split. intros. apply bar. auto. auto.
 apply foo.
Qed.

 Lemma pow_di {t} : forall (D1 D2 : Set) (f : D1 -> D2),
   @mono D1 D2 f ->
   forall I : inst (pow t) D1,
   @eq (inst (pow (pow t)) D2)
     (@apply D1 D2 f (pow (pow t)) (@Power_set (inst t D1) I))
     (@Power_set (inst t D2) (@apply D1 D2 f (pow t) I)).
Proof.
intros.
 simpl. pose (@baz _ _ (apply (t:=t) f) I ). symmetry.
 apply e. apply apply_mono. auto.
Qed. 

(* NRC is DI  *******************************************************************)

Theorem nrc_is_di : forall G t (e: expB G t),
di (denoteB e).
Proof.
 intros G t; induction e; try (simpl in *; unfold di; auto). 

 Focus 4.
 unfold di; intros; simpl; intros. rewrite <- IHe1. 
 rewrite <- IHe2. reflexivity. assumption. assumption.

 Focus 3. 
 unfold di; simpl; intros; rewrite <- IHe1. 
 rewrite <- IHe2. reflexivity. assumption. assumption.

 intros.  destruct I. simpl. apply prop_extensionality.
 split. intros. subst. reflexivity. intros.
 pose (@apply_mono _ _ t f pf). 
 pose (@ mono_elim _ _ _ m i i0).
 apply e. assumption. 

 intros. destruct I. rewrite IHe1. simpl. reflexivity. assumption.
 rewrite IHe2. simpl. reflexivity. assumption.

 simpl in *. intros. fold inst. destruct I. 
 apply image_empty.

 simpl in *. intros. destruct I. simpl.
 apply Im_Union.

 Focus 2. simpl. intros. apply Im_Singleton.

 Focus 4. simpl. intros. fold inst.
 destruct ((if excluded_middle_informative I then inl tt else inr tt)); auto.

 simpl. intros. unfold join. fold inst. apply functional_extensionality.
 intros J. apply prop_extensionality. split. intros.
 inversion H. subst. clear H. unfold In in H0.
 destruct H0. destruct H.
 eexists. econstructor. econstructor. unfold In. eauto.
 eauto.  econstructor. unfold In. eauto. reflexivity.
 intros. destruct H. destruct H. inversion H. subst. clear H.
 inversion H0. subst. clear H0. unfold In in *. 
 econstructor. unfold In. eexists. eauto. reflexivity.

 Focus 3. simpl. intros. destruct I. auto. auto.

 Focus 3. intros. simpl in *. destruct I. simpl. fold inst.
 apply functional_extensionality. intros. destruct x.
 simpl. apply prop_extensionality. split. intros.
 inversion H. subst. simpl in *. destruct x. unfold In in *.
 simpl in *. clear H. inversion H0. subst. clear H0.
 econstructor. unfold In in *. econstructor. unfold In. eauto.
 eauto. congruence. intros. inversion H. clear H.
 subst. unfold In in *. inversion H0. subst.
 clear H0. unfold In in *. econstructor. unfold In.
 econstructor. unfold In. eauto. eauto. eauto.

 Focus 2. unfold di in *. simpl in *. 
 intros. apply functional_extensionality. intros.
 apply prop_extensionality. split. intros.
 inversion H. clear H. fold inst in *. subst. unfold In in *.
 inversion H0. subst. clear H0. unfold In in *. econstructor.
 unfold In. econstructor. unfold In. eauto. eauto. eauto.
 intros. inversion H. clear H. subst. fold inst in *.
 unfold In in *. inversion H0. clear H0. subst. unfold In in *.
 econstructor. unfold In. econstructor. unfold In. eauto. eauto.
 rewrite IHe. auto. auto.

 apply pow_di.
 
 intros. destruct I.

 intros. destruct I. simpl. destruct i0. simpl. auto.
 simpl. auto.

 intros. destruct I. simpl. destruct i. simpl. auto.
 simpl. auto.
Qed.


Definition full_hol t : exp one (pow t) :=
 curry (comp pi2 (comp (pair star star) equal)).

(* HOL not DI  *******************************************************************)


Theorem full_hol_not_di : ~ di (denote (full_hol dom)).
Proof.
  simpl in *.  unfold di. intuition.
  assert (mono (fun _ : unit => false)).
  unfold mono. intros. apply functional_extensionality. intros.
  destruct (h x). destruct (g x). auto.
  simpl in *.

  pose (H unit bool (fun x => false) H0 tt). clearbody e. clear H.
  rewrite <- Im_sem in e. unfold Im_def0 in e.
  pose (equal_f e). clearbody e0. clear e.
  pose (e0 true). clearbody e. clear e0.
  simpl in e.
  assert ((tt = tt) = True).
  apply prop_extensionality. split. auto. auto.
  rewrite H in e. clear H.
  assert ((exists _ : unit, True /\ false = true) = False).
  apply prop_extensionality. split. intros. destruct H. destruct H.
  discriminate. intros. elim H. rewrite e in H. 
  clear e.  clear H0. pose I. rewrite H in t. elim t.
Qed.

Definition andE {G} (f g: exp G prop) : exp G prop :=
 comp (pair (pair f g) (pair trueE trueE)) equal.

Lemma andSem {G} {f g: exp G prop} : 
 forall D I, denote (andE f g) D I = (denote f D I /\ denote g D I). 
Proof.
 intros. simpl. apply prop_extensionality. split. 
 intros. assert (denote f D I = True). congruence.
 rewrite H0. assert (denote g D I = True). congruence.
 rewrite H1. auto. 
 intros. destruct H. assert (denote f D I = True). 
 apply prop_extensionality. split; auto. rewrite H1.
 assert (denote g D I = True). apply prop_extensionality.
 split; auto. rewrite H2. auto.
Qed. 

Definition impliesE {G} (p q: exp G prop) : exp G prop :=
 comp (pair (andE p q) p) equal.

Lemma implesSem {G} {f g: exp G prop} : 
 forall D I, denote (impliesE f g) D I = (denote f D I -> denote g D I). 
Proof.
 intros. simpl. apply prop_extensionality. split. 
 intros.  assert (denote f D I = True). 
 apply prop_extensionality; auto. split; auto.
 rewrite H1 in *. assert (denote g D I \/ ~ denote g D I).
 apply classic. destruct H2. auto.
  assert (denote g D I = False). apply prop_extensionality; 
 split; auto. intros x; elim x. rewrite H3 in *.
 assert ( ((True, False) = (True, True))). rewrite H.
 auto. assert (True = False). congruence.
 rewrite <- H5. auto.
 intros. apply prop_extensionality. split.
 intros. assert (denote f D I = True). congruence.
 rewrite H1; auto. intros.
 pose (H H0). assert (denote f D I = True). apply prop_extensionality.
 split; auto. assert (denote g D I = True). apply prop_extensionality.
 split; auto. rewrite H1. rewrite H2. auto.
Qed.


Definition forallE {G t} (p: exp (prod G t) prop) : exp G prop :=
 comp (pair (curry p) (curry trueE)) equal.

Lemma forallSem {G t} {f: exp (prod G t) prop} : 
 forall D I, denote (forallE f) D I = forall x, denote f D (I, x). 
Proof.
 intros. simpl. fold inst. apply prop_extensionality. split. 
 intros. apply equal_f with x in H. rewrite H. auto.
 intros. apply functional_extensionality. 
 intros. apply prop_extensionality. split. auto.
 auto.
Qed.

Definition falseE0 {G} : exp G prop := @forallE G prop pi2.

Lemma falseSem {G} {f: exp G prop} : 
 forall D I, denote (@falseE0 G) D I = False.
Proof.
 intros. simpl. apply prop_extensionality.
 split. intros. apply equal_f with False in H.
 rewrite H. auto. intros. elim H.
Qed.

Definition neg {G} (e: exp G prop) : exp G prop := impliesE e falseE0.

Lemma negSem {G} (e: exp G prop) : 
 forall D I, denote (neg e) D I = ~ denote e D I.
Proof.
 intros. apply prop_extensionality. simpl. split; intros.
 rewrite <- H. intuition. clear H. assert (( (fun J : Prop => J) = (fun _ : Prop => True)) = True).  congruence. assert True; auto. rewrite <- H in H1.
 clear H H0. apply equal_f with False in H1. rewrite H1; auto.
 apply prop_extensionality. split; intros. assert (denote e D I = True).
 congruence. rewrite H1. auto. contradiction.
Qed.

Definition orE {G} (p q: exp G prop) : exp G prop :=
 neg (andE (neg p) (neg q)). 
(*
forallE (impliesE (impliesE (comp pi1 p) pi2) (impliesE (comp pi1 q) pi2)).
*)
Lemma prop_ext_inv : forall (P Q:Prop), (P = Q) = (P <-> Q).
Proof.
 intros. apply prop_extensionality. split.
 intros. subst. firstorder. intros. apply prop_extensionality. auto.
Qed.

Lemma deMorgan0 {p q}: (~(~p /\ ~q)) = (p \/ q).
Proof.
 rewrite prop_ext_inv. split. intros. assert (p \/ ~ p). apply classic.
 destruct H0. left. auto. assert (q \/ ~ q). apply classic.
 destruct H1. right. auto. assert False. apply H. auto.
 elim H2. intros. intuition.
Qed.

Lemma deMorgan {G} (p q: exp G prop) 
 : forall D I, (~ ((~ denote p D I) /\ (~ denote q D I) ) )
= (denote p D I \/ denote q D I).
Proof.
 intros. apply deMorgan0.
Qed.

Lemma orSem {G} {f g: exp G prop} : 
 forall D I, denote (orE f g) D I = (denote f D I \/ denote g D I). 
Proof.
 intros. unfold orE. rewrite negSem. rewrite andSem.
 rewrite negSem. rewrite negSem. rewrite deMorgan. auto.
Qed.

Definition existsE {G t} (p: exp (prod G t) prop) : exp G prop := 
  neg (forallE (neg p)).

Lemma inter {t p} : (exists x:t, p x) = (~ forall x:t, ~ p x).
Proof.
 apply prop_extensionality. split. intros. destruct H.
 intuition. apply H0 with x. auto. intros. 
 assert ((exists x : t, p x) \/ ~ exists x : t, p x). apply classic.
 destruct H0. auto. cut False. intros. elim H1.
 intuition. apply H. intros. apply H0. eauto.
Qed.

Lemma negpush {x y} : ((~ x) = (~ y)) = (x = y).
Proof.
 apply prop_extensionality. split. intros. 
 assert (x \/ ~ x). apply classic. destruct H0. 
 assert (x = True). apply prop_extensionality; split; auto.
 assert (y \/ ~ y). apply classic. destruct H2.
 assert (y = True). apply prop_extensionality; split; auto.
 subst. auto. subst. assert (y = False); apply prop_extensionality; split; auto.
 intros. elim H1.  intros. subst. rewrite prop_ext_inv in H. destruct H.
 assert ((~ False) = True). apply prop_extensionality; split; auto.
 rewrite H4 in H1. assert ((~ True) = False). apply prop_extensionality; split; auto.
 rewrite H5 in H1. apply H1.
 auto.
 assert (x = False). apply prop_extensionality; split; auto. intros. elim H1.
 assert (y \/ ~ y). apply classic. destruct H2.
 assert (y = True). apply prop_extensionality; split; auto.
 subst. rewrite prop_ext_inv in H. destruct H. apply prop_extensionality.
 split. auto. intros. assert ((~ True) = False). apply prop_extensionality.
 split; auto. rewrite <- H4. apply H. assumption.
 subst. assert (y = False); apply prop_extensionality; split; auto.
 intros. elim H1.  intros. subst. rewrite prop_ext_inv in H. destruct H. elim H3.
 intros. subst. auto.
Qed.


Lemma existsSem {G t} {f: exp (prod G t) prop} : 
 forall D I, denote (existsE f) D I = exists x, denote f D (I, x). 
Proof.
 intros. fold inst. unfold existsE.
 rewrite negSem. rewrite forallSem. fold inst.
 rewrite inter.  
 cut ((forall x : inst t D, denote (neg f) D (I, x) =  ~ denote f D (I, x))).
 intros pf. rewrite negpush. apply prop_extensionality.
 split. intros. pose (pf x). rewrite <- e. apply H. intros.
 rewrite negSem. apply H. intros. apply negSem.
Qed.

  


Fixpoint nrcToHol {G t: ty} (e: expB G t) : exp G t :=
    match e in expB G t return exp G t with
      | idB t => id
      | compB t1 t2 t3 f g => comp (nrcToHol f) (nrcToHol g)
      | starB t => star
      | pi1B t1 t2 => pi1
      | pi2B t1 t2 => pi2
      | pairB t1 t2 t3 f g => pair (nrcToHol f) (nrcToHol g)
      | equalB t => equal
      | inj1B t1 t2 => inj1
      | inj2B t1 t2 => inj2
      | caseB t1 t2 t3 f g => case (nrcToHol f) (nrcToHol g)
      | boolean1B => boolean1 
      | boolean2B => boolean2
      | contraB t => contra
      | mzero t => curry falseE 
      | munit t => curry equal
      | str t1 t2 => curry (andE (comp (pair (comp pi2 pi1) (comp pi1 pi1)) equal) 
                                 (comp (pair (comp pi1 pi2) (comp pi2 pi2)) ev))
      | mjoin t =>  curry (existsE (andE (comp (pair (comp pi1 pi1) pi2) ev) 
                                         (comp (pair pi2 (comp pi1 pi2)) ev)))
      | mpow t => curry (forallE (impliesE (comp (pair (comp pi1 pi2) pi2) ev) 
                                           (comp (pair (comp pi1 pi1) pi2) ev)))
      | mmap t1 t2 f => curry  (existsE (andE (comp (pair (comp pi1 pi1) pi2) ev) 
                                              (comp (pair (comp pi1 pi2) 
                                                          (comp pi2 (nrcToHol f)))
                                                    equal)))  
     | mplus t =>  curry (orE (comp (pair (comp pi1 pi1) pi2) ev)
                              (comp (pair (comp pi1 pi2) pi2) ev)) 
     | dist1B a b c => dist1
     | dist2B a b c => dist2
    end.

Lemma mjoin_ok {t} : denoteB mjoin = denote (nrcToHol (mjoin (t:=t))).
Proof.
 unfold nrcToHol. unfold denoteB. unfold denote. fold @denote. fold inst.
 apply functional_extensionality_dep. intros D. 
 apply functional_extensionality. intros I. unfold  join.
 apply functional_extensionality. intros J. fold inst in *.
 rewrite existsSem. fold inst. simpl. apply prop_extensionality.
 split; intros. destruct H. destruct H. exists x.
 assert (I x = True). apply prop_extensionality. split; auto. rewrite H1.
 assert (x J = True). apply prop_extensionality. split; auto. rewrite H2.
 auto.
 destruct H. exists x. inversion H. rewrite H2 in *. rewrite H1 in *.
 auto.
Qed.

Lemma mmap_ok {s t} (e: expB s t) : 
denoteB e = denote (nrcToHol e) ->
denoteB (mmap e) = denote (nrcToHol (mmap e)).
Proof.
 intros pf. unfold nrcToHol. fold @nrcToHol. unfold denote. fold @denote.
 fold inst. unfold denoteB. fold @denoteB. apply functional_extensionality_dep.
 intros D. apply functional_extensionality. intros I. rewrite <- Im_sem.
 unfold Im_def0. fold inst. apply functional_extensionality. fold inst.
 intros J. rewrite existsSem. fold inst. apply prop_extensionality.
 split. intros. destruct H. destruct H. subst J.  exists x. rewrite andSem.
 simpl.  split; auto. rewrite pf. auto.
 intros. destruct H. simpl in *. exists x. 
 inversion H. clear H. rewrite H1 in H2. rewrite H2.
 rewrite <- pf in H2. constructor; auto. symmetry. 
 fold inst in H2. rewrite H2.  auto.
Qed.

 Definition powDef {t} (X : Ensemble t) : Ensemble (Ensemble t) 
 := fun Y => forall z, Y z -> X z.

Lemma Power_set_eta : @Power_set = fun a b c => @Power_set  a b c.
Proof.
 intros. auto.
Qed.

 Lemma powSem : @powDef = @Power_set.
 Proof.
   rewrite Power_set_eta. unfold powDef.
   apply functional_extensionality_dep. intros D.
   apply functional_extensionality. intros I.
   apply functional_extensionality. intros J.
   apply prop_extensionality. split. intros.
   econstructor. unfold Included. unfold In. assumption.
   intros. inversion H. subst. unfold Included in H1. unfold In in *.
   apply H1. assumption.
 Qed.

Lemma mpow_ok {t} : denoteB mpow = denote (nrcToHol (mpow (t:=t))).
Proof.
 unfold nrcToHol. unfold denote. fold @denote. fold inst.
 unfold denoteB. apply functional_extensionality_dep. intros D.
 apply functional_extensionality. intros I. rewrite <- powSem.
 unfold powDef. fold inst. apply functional_extensionality. fold inst.
 intros J. rewrite forallSem. fold inst. apply prop_extensionality.
 split. intros pf H.  rewrite implesSem. intros. fold inst in *. 
 simpl in *. apply pf. assumption. intros. pose (H z). 
 simpl in *. clearbody d. clear H. rewrite <- d in H0. clear d.
 fold inst in *. assert (J z = True). congruence. assert (I z = True). 
 congruence. rewrite H1. auto.
Qed.

(* NRC to HOL Semantics Preserving *********************************************)

Theorem semPres_nrcToHol {G t} : forall (e: expB G t),
 denoteB e = denote (nrcToHol e).
Proof.
 induction e; intros; try auto.
 
 simpl; rewrite IHe1; rewrite IHe2; simpl; auto; fold inst in *.
 simpl; rewrite IHe1; rewrite IHe2; simpl; auto; fold inst in *.
 simpl; rewrite IHe1; rewrite IHe2; simpl; auto; fold inst in *.

 apply functional_extensionality_dep. intros. 
 apply functional_extensionality. intros. destruct x0. 
 apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. inversion H.
 intros. elim H.

 unfold nrcToHol. unfold denoteB. apply functional_extensionality_dep. intros.
 apply functional_extensionality. intros. 
 apply functional_extensionality. intros. fold inst in *. unfold denote.
 fold (@denote). rewrite orSem. rewrite union_def. unfold denote.
 simpl. auto.

 apply mjoin_ok.

 simpl.
 apply functional_extensionality_dep. intros. 
 apply functional_extensionality. intros. 
 apply functional_extensionality. intros.
 apply prop_extensionality. split. intros. inversion H. auto.
 intros. subst. constructor.

 apply mpow_ok.

 apply mmap_ok. assumption.

 simpl. fold inst.
 apply functional_extensionality_dep. intros. 
 apply functional_extensionality. intros. 
 apply functional_extensionality. intros.
 destruct x0. destruct x1. simpl.
 apply prop_extensionality. split. intros.
 inversion H. subst. unfold In in *. clear H.
 assert (i0 = i). congruence.  assert (i1 = x0). congruence.
 subst. assert ((i = i) = True). apply prop_extensionality.
 split; auto. rewrite H. assert (P x0 = True). apply prop_extensionality.
 split; auto. rewrite H2. auto.
 intros. assert (P i1 = True). congruence. assert ((i0 = i) = True).
 congruence. clear H. assert (P i1). rewrite H0; auto.
 assert (i0 = i). rewrite H1. auto. subst. clear H0 H1.
 econstructor. unfold In. eauto. eauto.
Qed.


Fixpoint hdi {G t: ty} (e: exp G t) : Prop :=
 di (denote e) /\
    match e in exp G t with
      | comp t1 t2 t3 f g => hdi f /\ hdi g
      | pair t1 t2 t3 f g => hdi f /\ hdi g
      | case t1 t2 t3 f g => hdi f /\ hdi g
      | curry t1 t2 f => hdi f
      | _ => True
    end.

Definition ifB {G t} (w: expB G prop) (e f: expB G t) : expB G t :=
 let x := compB w boolean1B in
  compB (pairB idB x) (compB dist1B (caseB (compB pi1B e) (compB pi1B f))).

Definition whereB {G s t} (w: expB (prod G s) prop) 
 (e: expB (prod G s) (pow t)) (b: expB G (pow s)) : expB G (pow t) :=
 bindB (ifB w e (compB starB mzero)) b.

Fixpoint holToNrc {G t: ty} (e: exp G t) : expB G t :=
    match e in exp G t return expB G t with
      | id t => idB
      | comp t1 t2 t3 f g => compB (holToNrc f) (holToNrc g)
      | star t => starB
      | pi1 t1 t2 => pi1B
      | pi2 t1 t2 => pi2B
      | pair t1 t2 t3 f g => pairB (holToNrc f) (holToNrc g)

      | ev t => 
        let rhs := compB starB munit in
        let xxx := whereB (compB (pairB pi2B (compB pi1B pi2B)) equalB) 
                          (compB starB munit) pi1B in
        compB (pairB xxx rhs) equalB  
      | curry t1 t2 f => whereB (holToNrc f) (compB pi2B munit) UB 
      | equal t => equalB
      | inj1 t1 t2 => inj1B
      | inj2 t1 t2 => inj2B
      | case t1 t2 t3 f g => caseB (holToNrc f) (holToNrc g)
      | contra t => contraB
      | boolean1 => boolean1B
      | boolean2 => boolean2B
      | dist1 a b c => dist1B
      | dist2 a b c => dist2B
    end.

Definition sing {t} (e: t) : Ensemble t := fun x:t => x = e.

Lemma singSem : 
 @Singleton = @sing.
Proof.
 unfold sing. 
 assert (Singleton = fun t (e x : t) => @Singleton t e x).
 auto. rewrite H. erewrite <- functional_extensionality_dep.
 eauto. intros. simpl. apply functional_extensionality.
 intros. apply functional_extensionality. intros. apply prop_extensionality.
 split; auto. intros. inversion H0. auto. intros. subst. constructor.
Qed.

 Lemma semPresEv : forall G (t: ty) (H: hdi (ev (t:=G))),
  denote ev = denoteB (holToNrc (ev (t:=G))).
Proof.
 intros. unfold holToNrc. unfold denote. unfold denoteB. fold @denoteB.
 apply functional_extensionality_dep. intros D. 
 apply functional_extensionality. intros I. destruct I. 
 rewrite singSem. unfold sing. simpl. fold inst. rewrite singSem.
 
 apply prop_extensionality. 
 split; intros. apply functional_extensionality.
 intros. destruct x. apply prop_extensionality. split. intros. auto.
 intros. exists (fun x:unit => x = tt). split; auto. econstructor.
 unfold In. econstructor. unfold In. eauto. eauto. eauto. 
 simpl. destruct (excluded_middle_informative (i0 = i0)).
 unfold sing. auto. elim n. auto.
  
 unfold join in *.
 apply equal_f with tt in H0. assert ((tt = tt) = True). 
 apply prop_extensionality. split; auto. rewrite H1 in H0.
 clear H1. assert True. auto. rewrite <- H0 in H1. clear H0.
 destruct H1. cut ( (x = fun y:unit => True) \/ (x = fun y:unit => False)).
 intros pf. destruct pf. subst. inversion H0. clear H0.
 inversion H1. subst. clear H1. destruct x. destruct p.
 unfold In in *. unfold sing in *. inversion H0. clear H0.
 subst. unfold In in *. apply equal_f with tt in H3. simpl in *.
 assert (i1 = i2 \/ ~ i1 = i2). apply classic.
 destruct H0. subst. assert (i2 = i0). congruence. subst.
 assert True. auto. rewrite H3 in H0. clear H3.
 destruct (excluded_middle_informative (i0 = i0)). subst.
 assert (i0 = x). congruence. subst. auto. elim H0. 
 destruct (excluded_middle_informative (i1 = i2)). contradiction. 
 assert True. auto. rewrite H3 in H5. elim H5.
 destruct H0. subst. elim H2. destruct H0. inversion H0.
 subst. clear H0. unfold In in *. inversion H2. subst.
 clear H2. unfold In in H0. 
 simpl in *. assert (x = i0 \/ ~ x = i0). apply classic.
 destruct H2. subst. destruct (excluded_middle_informative (i0=i0)).
 unfold sing in *. left. apply functional_extensionality. intros.
 destruct x. apply prop_extensionality. split; auto.
 elim H1. destruct (excluded_middle_informative (x = i0)).
 contradiction. inversion H1.
Qed.

Definition whereSem {G s t} (p : G*s -> Prop) (e: G*s -> Ensemble t)
 (I: G -> Ensemble s) := fun g t => exists s, I g s /\ p (g, s) /\ e (g, s) t.

 Lemma imx {G s t} (p : expB (prod G s) prop) (e: expB (prod G s) (pow t))
  (I: expB G (pow s)) : forall D ,
 (denoteB (whereB p e I) D ) = whereSem (denoteB p D) (denoteB e D) (denoteB I D) .
 Proof.
  unfold whereSem. fold inst. unfold whereB. unfold denoteB. 
  fold @denoteB. intros D. unfold bindB. unfold denoteB. fold @denoteB.
  unfold join. fold inst. apply functional_extensionality. intros T.
  fold inst in *. apply functional_extensionality. intros J. fold inst in *.
  apply prop_extensionality. split.

  intros. destruct H. destruct H. inversion H. subst. clear H. 
   unfold In in *. inversion H1. subst. clear H1.
   unfold In in *.
   unfold ifB in H0. unfold denoteB in H0. fold @denoteB in H0. fold inst in H0.
   simpl in H0. assert ((denoteB p D (T, x) \/ ~ (denoteB p D (T, x)))). 
   apply classic. destruct H1. 
   destruct (excluded_middle_informative (denoteB p D (T, x))). 
   simpl in *. eexists. eauto. elim H0. 
   destruct (excluded_middle_informative (denoteB p D (T, x))). 
   simpl in *. eexists. eauto. elim H0. 

intros. destruct H. destruct H. destruct H0. eexists.
 econstructor. econstructor. unfold In. econstructor.
 unfold In. simpl. eauto. eauto. eauto. simpl.
 fold inst. destruct (excluded_middle_informative (denoteB p D (T, x))).
  simpl. auto. contradiction.
Qed. 

Lemma mid1 : forall (p:Prop), (p = True) \/ (p = False).
Proof.
 intros. assert (p \/ ~ p). apply classic. destruct H.
 left. apply prop_extensionality. split; auto.
 right. apply prop_extensionality. split; intros.
 contradiction. elim H0.
Qed.


Definition semcomp {A B C} (f : A -> B)
 (g : B -> C) : A -> C :=
  fun a:A => g (f a).

Lemma mono_x : forall
  (D : Set)
  (G : ty)
  (t : ty)
  (I : unit -> inst G D)
  (J : inst t D -> Prop)
  (A : Type)
  (g : A -> inst t (sigT (atoms (I tt))))
  (h : A -> inst t (sigT (atoms (I tt))))
  (x : A),
   mono (fun x0 : sigT (atoms (I tt)) => projT1 x0).
Proof.
 intros. unfold mono. intros. apply functional_extensionality.
 intros. apply equal_f with x0 in H. unfold projT1 in H.
 destruct (g0 x0). destruct (h0 x0). subst. 
 assert (a = a0). apply proof_irrelevence. subst.
 auto.
Qed.

Lemma mono_apply_sig : forall
  (D : Set)
  (G : ty)
  (t : ty)
  (I : unit -> inst G D)
  (J : inst t D -> Prop),
   mono (apply (t:=t) (fun x : sigT (atoms (I tt)) => projT1 x)).
Proof.
 intros. unfold mono. intros. apply functional_extensionality.
 intros. apply equal_f with x in H.
 pose @apply_mono.
 cut (mono (fun x : sigT (atoms (I tt)) => projT1 x)).
 intros pf. eapply mono_elim. eauto. assumption.
 clear m.

 unfold mono. clear H. intros. apply functional_extensionality.
 intros. apply equal_f with x0 in H.
 apply mono_elim in H. assumption.

 eapply mono_x. eauto. eauto. eauto. eauto.
Qed.


Lemma U_SEM (D: Set) (G t: ty) (I: unit -> inst G D) :
  semcomp I (denoteB UB D) = 
  semcomp (denote (@curry one t trueE) (sigT (atoms (I tt))))
          (apply ((fun x => projT1 x))).
Proof.
 unfold semcomp. apply functional_extensionality. intros unt.
 destruct unt. simpl. fold inst. rewrite atomsSem. rewrite univSem.
 induction t.

  simpl. rewrite singSem.  unfold sing. rewrite <- Im_sem. unfold Im_def0.
  apply functional_extensionality. intros x. destruct x.
  apply prop_extensionality. split; auto. intros. exists tt. split.
  auto. auto.

  simpl. rewrite union_def. rewrite <- Im_sem. unfold Im_def0.
  apply functional_extensionality. intros P.
  apply prop_extensionality. split; intros. destruct H.
  inversion H. subst. exists True. auto. inversion H.
  subst. rewrite singSem in H. unfold sing in H. exists False.
  auto. destruct H. destruct H. subst. assert (P \/ ~ P).
  apply classic. destruct H0. left. rewrite singSem. unfold sing.
  apply prop_extensionality. split; auto. right. rewrite singSem.
  unfold sing. apply prop_extensionality; auto. split. intros.
  contradiction. intros. elim H1.

  simpl in *. rewrite IHt1. rewrite IHt2. clear IHt1 IHt2.
  unfold cartprod. fold inst. rewrite <- Im_sem. unfold Im_def0.
  apply functional_extensionality. intros J. destruct J.
  apply prop_extensionality. split. intros. 
  destruct H. destruct H. destruct H. destruct H0. destruct H0.
  clear H H0. simpl in *. exists (x, x0). split; auto.
  simpl. rewrite H1. rewrite H2. auto.
  intros. destruct H. destruct H. destruct x. simpl in *.
  clear H. split. exists i1. split; auto. 
  congruence. exists i2. split; auto. congruence.

  simpl in *. rewrite IHt. clear IHt. apply functional_extensionality.
  intros J. rewrite baz. rewrite <- powSem. rewrite <- Im_sem.
  unfold Im_def0. fold inst. unfold powDef. 
  apply prop_extensionality.  split; intros.
   destruct H. destruct H. eexists. split; auto. eassumption.
   destruct H. destruct H. eexists. split; auto. eassumption.
   apply mono_apply_sig. auto.

   simpl. rewrite <- Im_sem. unfold Im_def0.
   apply functional_extensionality. intros J.
   apply prop_extensionality. split; intros.
   exists ( (existT (atoms (I tt)) J) H). 
    split; auto. destruct H. destruct H. destruct x. 
    simpl in *. subst. assumption.

   simpl. apply functional_extensionality. intros. elim x.

   simpl in *. rewrite IHt1. rewrite IHt2. clear IHt1 IHt2.
   unfold disjunion. fold inst. apply functional_extensionality.
   intros J. destruct J. rewrite <- Im_sem. unfold Im_def0.
   apply prop_extensionality. split; intros. destruct H. destruct H.
   exists ( inl x). split; auto. rewrite H0. auto.
    destruct H. destruct H. destruct x.  exists (i0). split; auto.
    congruence. eexists. split; auto. discriminate.
   rewrite <- Im_sem. unfold Im_def0. apply prop_extensionality.
   split; intros. destruct H. destruct H. exists (inr x).
   split; auto. rewrite H0. auto.
    destruct H. destruct H. destruct x.  discriminate.
    exists i0. split; auto. congruence.
 Grab Existential Variables.
  discriminate.
Qed.


Lemma logic_helper_1 : forall (P Q: Prop), (P -> Q) -> exists R, (Q = (P \/ R)).
Proof.
 intros. eexists. apply prop_extensionality. split. intros. right. eauto.
 intros. destruct H0. apply H. auto. auto.
Qed.

Lemma logic_helper_2 : forall (D:Set) (P Q: D -> Prop), 
                         (forall (d: D), P d -> Q d) -> 
                         (exists R : D -> Prop, forall (d: D), (Q d = (P d \/ R d))).
Proof.
 intros. eexists. intros. apply prop_extensionality. split. intros. right. eauto.
 intros. destruct H0. apply H. auto. auto.
Qed.


Lemma mono_y : forall t D (I: inst t D),
 mono (fun x : sigT (atoms I) => projT1 x).
Proof.
 intros.
 unfold mono.
 intros.
 apply functional_extensionality.
 intros. apply equal_f with x in H.
 destruct (g x) . destruct (h x).
 simpl in *. subst. assert (a = a0).
 apply proof_irrelevence. subst. auto.
Qed.

Lemma setInc : forall x (I J: Ensemble x), 
                 (Included _ I J /\ Included _ J I) -> I = J.
Proof.
 intros. destruct H. unfold Included in *. apply functional_extensionality.
 intros. apply prop_extensionality. split; intros. apply H. assumption.
 apply H0. assumption.
Qed.

Conjecture paperOne: forall
  (t1 : ty)
  (t2 : ty)
  (e : exp (prod t1 t2) prop)
  (H0 : di (denote (curry e)))
  (H1 : hdi e)
  (D : Set)
  (I : inst t1 D),
  Included _ (fun J => denote e D (I, J)) (fun J => denoteB UB D I J).

 Lemma heart : forall
  (t1 : ty)
  (t2 : ty)
  (e : exp (prod t1 t2) prop)
  (H0 : di (denote (curry e)))
  (H1 : hdi e)
  (D : Set)
  (I : inst t1 D)
  (pf : denote e = denoteB (holToNrc e)),
  (fun J => denoteB (holToNrc e) D (I, J)) =
  (fun J => (exists s : inst t2 D,
      denoteB UB D I s /\
      denoteB (holToNrc e) D (I, s) /\ denoteB (compB pi2B munit) D (I, s) J)).
 Proof.
  intros. apply setInc. fold inst in *.
  split.

  Focus 2. unfold Included. intros. unfold In in *.
  destruct H. destruct H. destruct H2.
  simpl in *. fold inst in *. inversion H3. subst. clear H3. assumption.

  unfold Included.
  intros J. unfold In in *. exists J. split; try (split; auto).
  
  Focus 2.  simpl in *. constructor. 

  rewrite <- pf in H. clear pf.

  pose (paperOne t1 t2 e H0 H1 D I). fold inst in *. unfold Included in *.
  pose (i J). clearbody i0. clear i. unfold In in *. apply i0. assumption.
Qed.


Lemma semPresLam : forall
  (t1 : ty)
  (t2 : ty)
  (e : exp (prod t1 t2) prop)
  (IHe : hdi e -> denote e = denoteB (holToNrc e))
  (H : hdi (curry e)),
   denote (curry e) = denoteB (holToNrc (curry e)).
Proof.
 intros. unfold denote. fold @denote. fold inst. 
 unfold holToNrc. fold @holToNrc.
 inversion H. clear H.
 pose (IHe H1) as IH. clearbody IH. clear IHe. rewrite IH.
 assert (@denoteB = fun D I J x a => @denoteB D I J x a). auto.
 rewrite H. apply functional_extensionality_dep.
 intros D. apply functional_extensionality. intros I. 
 rewrite imx. unfold whereSem. fold inst. apply functional_extensionality.
 fold inst. intros J.  clear H.
 pose (heart t1 t2 e H0 H1 D I IH). fold inst in *.
 apply equal_f with J in e0. assumption. 
Qed.

Theorem semPres_holToNrc {G t} : forall (e: exp G t),
 hdi e -> denote e = denoteB (holToNrc e).
Proof.
 induction e; intros; try auto.
 
 unfold hdi in *. fold @hdi in *. destruct H. destruct H0. 
 pose (IHe1 H0). pose (IHe2 H1). unfold denote. fold @denote.
 rewrite e. rewrite e0. unfold holToNrc. fold @holToNrc. unfold denoteB.
 fold @denoteB. auto.

 unfold hdi in *. fold @hdi in *. destruct H. destruct H0. 
 pose (IHe1 H0). pose (IHe2 H1). unfold denote. fold @denote.
 rewrite e. rewrite e0. unfold holToNrc. fold @holToNrc. unfold denoteB.
 fold @denoteB. auto.

 unfold hdi in *. fold @hdi in *. destruct H. destruct H0. 
 pose (IHe1 H0). pose (IHe2 H1). unfold denote. fold @denote.
 rewrite e. rewrite e0. unfold holToNrc. fold @holToNrc. unfold denoteB.
 fold @denoteB. auto.

 apply semPresEv. auto. auto.

 apply semPresLam. auto. auto.
Qed.

(* Translated terms obey eta *****************************************)

Lemma u1_0_1 : forall A1 (D: Set) (i : inst A1 D) Y X,
   univ A1 Y i -> Included _ Y X -> univ A1 X i.
Proof.
 intros. induction A1. simpl; auto. simpl. rewrite union_def.
  simpl in *. destruct (excluded_middle_informative i). left. 
  assert (i = True). apply prop_extensionality. split; auto. rewrite H1. 
  constructor. right. assert (i = False). apply prop_extensionality.
   split; auto. intros. contradiction. rewrite H1. constructor.
  simpl in *. unfold cartprod in *. destruct H. split. apply IHA1_1.
  auto. apply IHA1_2. auto.
 simpl in *. rewrite <- powSem in *. unfold powDef in *. fold inst in *.
  intros. apply IHA1. apply H. auto.
 simpl in *. apply H0. auto.
 simpl in *. contradiction.
 simpl in *. unfold disjunion in *. destruct i. apply IHA1_1. auto.
 apply IHA1_2. auto.
Qed.

Lemma u1_0_0 : forall t (P Q: Ensemble t),
 Included t P (Union P Q).
Proof.
 intros. left. auto.
Qed.

Lemma u1_0_2 : forall t (P Q: Ensemble t),
 Included t P (Union Q P).
Proof.
 intros. right. auto.
Qed.

Lemma u1_2 : forall A D (J: inst A D) (P: Ensemble (inst A D)) (H: In _ P J), 
 Included _ (atoms J) (join (Im P atoms)).
Proof.
 unfold Included. unfold In. unfold Ensemble. unfold join. intros.
 unfold Ensemble. rewrite <- Im_sem. unfold Im_def0. exists (atoms J).
 split. exists J. auto. auto.
Qed.

Lemma u1_1 : forall A D (J: inst A D), In _ (univ A (atoms J)) J.
Proof.
 intros. fold inst in *. unfold In. induction A.
  simpl in *. destruct J. constructor. simpl. rewrite union_def.
  simpl in *. destruct (excluded_middle_informative J). left. 
  assert (J = True). apply prop_extensionality. split; auto. rewrite H. 
  constructor. right. assert (J = False). apply prop_extensionality.
   split; auto. intros. contradiction. rewrite H. constructor.

  simpl in *. destruct J. unfold cartprod. simpl. split. eapply u1_0_1.
  apply IHA1. apply u1_0_0. eapply u1_0_1. apply IHA2. apply u1_0_2.

 simpl in *. constructor. fold inst. unfold Included. fold inst.
  unfold In. intros I. intros pf. eapply u1_0_1. apply IHA. apply u1_2. auto.

 simpl in *. constructor. contradiction.

 simpl in *. unfold disjunion. destruct J. apply IHA1. apply IHA2.
Qed.

Lemma u1_3 : forall t A I (J: inst A I) (P: Ensemble (inst A I)) (H: In _ P J), 
 Included _ (univ t (atoms J)) (univ t (join (Im P atoms))).
Proof.
  unfold Included. unfold In. unfold Ensemble. fold inst. intros.
  induction t. simpl in *. auto. simpl in *. auto.
  simpl in *. destruct x. unfold cartprod in *. simpl in *.
  destruct H0. split. apply IHt1. auto. apply IHt2. auto.
  simpl in *. rewrite <- powSem in *. unfold powDef in *. fold inst in *.
  intros. pose (H0 z). clearbody u. clear H0. pose (IHt z). clearbody u0.
   clear IHt. pose (u H1). clearbody u1. clear u. pose (u0 u1). clearbody u.
   clear u1. clear u0. auto. pose (u1_2 _ _ J P H). clearbody i.
   unfold Included in i. unfold In in *. simpl in *. apply i. auto.
 simpl in *. auto.
 simpl in *. unfold disjunion in *. destruct x. apply IHt1. auto.
  apply IHt2. auto.
Qed.

Lemma u1_4 : forall t x P Q,
  In t P x -> Included t P Q -> In _ Q x.
Proof.
  intros. unfold In in *. unfold Included in *. apply H0. auto.
Qed.

Lemma u1 : forall A I (P : Ensemble (inst A I)) (J : inst A I ) (H : In _ P J),
   In _ (univ A (join (Im P atoms))) J.
Proof.
 intros. fold inst. pose (u1_1 A I J). fold inst in *. clearbody i.
 pose (u1_3 A A I J P H). fold inst in *. clearbody i0. pose (u1_4 _ _ _ _ i i0).
 clearbody i1. assumption.
Qed.

Theorem adom_eta : forall A, denoteB (holToNrc (curry (@ev A))) = denoteB idB.
Proof.
 intros. unfold holToNrc. apply functional_extensionality_dep.
 intros I. rewrite imx. unfold denoteB. fold @denoteB. 
           rewrite imx. unfold denoteB. fold @denoteB.
           simpl. unfold whereSem. fold inst.
           apply functional_extensionality. intros P.
           simpl. apply functional_extensionality. intros J.
           apply prop_extensionality. split.
 intros. destruct H. destruct H. destruct H0. inversion H1.
  subst. clear H1. apply equal_f with tt in H0. 
  assert (Singleton tt tt). constructor. rewrite <- H0 in H1.
  destruct H1. destruct H1. destruct H2. subst. auto.

 intros. exists J. split. rewrite univSem. rewrite atomsSem.

 Focus 2. split. apply functional_extensionality. intros. destruct x.
  apply prop_extensionality. split; intros. constructor. exists J.
  auto. constructor.

 apply u1. assumption.
Qed.

(* Translated terms obey weak beta **********************************)

Theorem t0 : forall (A B : ty) (D : Set) (f: expB A B) 
(I : inst A D), univ B (atoms I) (denoteB f D I).
Proof.
 intros. eapply u1_0_1 with (atoms (denoteB f D I)). apply u1_1.
 unfold Included. intros d. intros. unfold In in *.
 induction f; simpl in *; try auto. 
  simpl in *. contradiction.
  destruct I. apply IHf1. auto. apply IHf2. auto.
  contradiction. 
  left. auto. right. auto.
  destruct H. apply IHf1. auto. apply IHf2. auto.
  destruct H. rewrite <- Im_sem_0 in H. unfold Im_def0 in H.
   destruct H. destruct H. destruct H. contradiction.
  destruct I. simpl in *. unfold join in *. destruct H. destruct H.
  rewrite <- Im_sem_0 in *. unfold Im_def0 in *. destruct H. fold inst in *.
  destruct H. subst. destruct H; unfold In in *. left. unfold In. exists (atoms x).
  split. exists x. split; auto. auto. right. unfold In. exists (atoms x).
  split; auto. rewrite <- Im_sem_0. unfold Im_def0. exists x. split; auto.
 
  unfold join in *. fold inst in *. rewrite <- Im_sem_0 in *. unfold Im_def0 in *.
   destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
   subst. exists  (fun j : D => exists J : Ensemble D, Im x1 atoms J /\ J j).
   split. exists x1. split. auto. auto. exists (atoms x0). split.
   rewrite <- Im_sem_0. unfold Im_def0. exists x0. split. auto. auto. auto.

 unfold join in *. rewrite <- Im_sem_0 in *. rewrite singSem in *. 
  unfold Im_def0 in *. fold inst in *. unfold sing in *. destruct H.
  destruct H. destruct H. destruct H. subst. auto.

 unfold join in *. rewrite <- Im_sem_0 in *. unfold Im_def0 in *. fold inst in *.
  destruct H. destruct H. destruct H. destruct H. subst.
  destruct H0. destruct H0. rewrite <- Im_sem_0 in *. rewrite <- powSem in *.
  unfold powDef in *. unfold Im_def0 in *. destruct H0. destruct H0. subst.
  exists (atoms x1). split; auto. exists x1. split; auto.

 unfold join in *. rewrite <- Im_sem_0 in *. rewrite <- Im_sem_0 in *.
  unfold Im_def0 in *. fold inst in *. destruct H. destruct H. destruct H.
  destruct H. destruct H. destruct H. subst. eexists. split. eexists.
  split. eauto. eauto. eauto.

  destruct (excluded_middle_informative I). contradiction. contradiction.
  contradiction.

  destruct I. simpl in *. unfold join in *. rewrite <- Im_sem_0 in *.
  rewrite <- Im_sem_0 in *.  unfold Im_def0 in *. fold inst in *. 
  destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
  subst. simpl in *. destruct H0. left. auto. right. unfold In in *.
  eexists. split. eexists. split. eauto. eauto. eauto.

 contradiction.
 destruct I. destruct s. simpl in *. auto. simpl in *. auto.

 destruct I. destruct p. simpl in *. auto. destruct p. simpl in *. auto.
Qed.

Theorem t1 : forall A B (y : exp A B) D (I : inst A D),
   univ B (atoms I) (denoteB (holToNrc y) D I).
Proof.
 intros. apply t0. 
Qed.

Theorem adom_beta_2 : forall A B (f: exp (prod A B) prop) (y: exp A B) ,
 denoteB (holToNrc (comp (pair id y) f)) = 
 denoteB (holToNrc (comp (pair (curry f) y) ev)).
Proof.
 intros. unfold holToNrc. fold @holToNrc. unfold denoteB. fold @denoteB.
 apply functional_extensionality_dep. intros D.
 rewrite imx. unfold denoteB. fold @denoteB.
 apply functional_extensionality. intros I. unfold fst. unfold snd.
 rewrite singSem. unfold sing. rewrite imx. unfold denoteB. fold @denoteB.
 unfold whereSem. fold inst. simpl. rewrite univSem. rewrite atomsSem.
 rewrite singSem. unfold sing. 

 apply prop_extensionality. split; intros.

  apply functional_extensionality. intros J. destruct J. assert ((tt = tt) = True).
   apply prop_extensionality. split; auto. rewrite H0. apply prop_extensionality;
    split; auto. intros. clear H0 H1. exists (denoteB (holToNrc y) D I).
     split. exists (denoteB (holToNrc y) D I). split. fold inst in *.
      apply t1. split; try assumption. auto.
      split. reflexivity. auto.

  apply equal_f with tt in H. assert ((tt = tt) = True). apply prop_extensionality.
  split; auto. rewrite H0 in *. clear H0. assert True. auto. rewrite <- H in H0.
  clear H. destruct H0. destruct H. destruct H. destruct H. destruct H1.
  destruct H0. subst. subst x0. assumption.
Qed.

Theorem adom_beta : forall A B (f: exp (prod B A) prop)
 (pf : forall D i i0, denoteB (holToNrc f) D (i, i0) -> univ A (atoms i) i0),
 denoteB (holToNrc (comp (pair (comp pi1 (curry f)) (pi2 (t1:=B))) (@ev A))) = 
 denoteB (holToNrc f).
Proof.
 intros. unfold holToNrc. fold @holToNrc. unfold denoteB. fold @denoteB. 
 apply functional_extensionality_dep. intros D.
 rewrite imx. unfold denoteB. fold @denoteB.
 apply functional_extensionality. intros I. unfold fst. unfold snd.
 rewrite singSem. unfold sing. rewrite imx. unfold denoteB. fold @denoteB.
 unfold whereSem. fold inst. simpl. rewrite univSem. rewrite atomsSem.
 rewrite singSem. unfold sing. destruct I. 

 apply prop_extensionality. split; intros.  
 apply equal_f with tt in H. assert ((tt = tt) = True).
 apply prop_extensionality. split; intros. constructor. reflexivity.
  rewrite H0 in H. clear H0. assert ((exists s : inst A D,
         (exists s0 : inst A D,
            univ A (atoms i) s0 /\ denoteB (holToNrc f) D (i, s0) /\ s = s0) /\
         s = i0 /\ True)). rewrite H. auto. clear H. destruct H0.
  destruct H. destruct H0. clear H1. subst. destruct H. destruct H. destruct H0.
  subst. assumption.

 apply functional_extensionality. intros t. destruct t. apply prop_extensionality.
 split; intros. auto. exists i0. split; auto. exists i0.
 split; try auto. 
Qed.

(* Translated terms do not obey full beta ************************************)

Definition beta {A B} (f: exp (prod B A) prop) :=
  (comp (pair (comp pi1 (curry f)) (pi2 (t1:=B))) (@ev A)).

Definition tru : exp (prod one dom) prop := trueE.

Definition bad := beta tru.

Lemma bad_sem : (denoteB (holToNrc bad) = fun D:Set => fun x => False).
 Proof.
 unfold bad. unfold beta. unfold tru. unfold trueE. 
 unfold holToNrc. fold @holToNrc. unfold denoteB. fold @denoteB.
 apply functional_extensionality_dep. intros D. apply functional_extensionality.
 intros I. rewrite imx. rewrite singSem. unfold sing. unfold fst. unfold snd.
 rewrite imx. simpl. destruct I. unfold whereSem. simpl. rewrite singSem.
 apply prop_extensionality. split; intros; auto. apply equal_f with tt in H.
 assert ((tt = tt) = True). apply prop_extensionality; split; auto. rewrite H0 in H.
 clear H0. assert True. constructor. rewrite <- H in H0. clear H. 
  repeat destruct H0. repeat destruct H. contradiction.
Qed.

Lemma equal_f_dep0 : forall {A: Type} {B : Set -> Type} {f g : forall A, B A},
  f = g -> forall x, f x = g x.
Proof.
 intros; subst; auto.
Qed.

Lemma bad_true_same : denote bad = denote tru.
Proof.
 simpl. auto.
Qed.

Lemma bad_no_beta_1 (pf: denoteB (holToNrc bad) = denoteB (holToNrc tru)) : False. 
Proof.
 pose (@equal_f_dep0 Set (fun D : Set => inst (prod one dom) D -> inst prop D)
  (denoteB (holToNrc bad)) (denote bad) pf unit). clearbody e. clear pf.
  pose (equal_f e). clearbody e0. clear e. pose (e0 (tt,tt)). clearbody e.
  clear e0. simpl in *. destruct (excluded_middle_informative True).
   Focus 2. contradiction n. auto. clear t.
  repeat rewrite <- Im_sem_0 in *. unfold Im_def0 in *.
  unfold join in *. simpl in *. rewrite singSem in *. unfold sing in *.
  assert True. auto. rewrite <- e in H. clear e. apply equal_f with tt in H.
   simpl in *. assert ( (tt = tt) = True ). apply prop_extensionality. split; auto. 
  rewrite H0 in H. clear H0. assert True. auto. rewrite <- H in H0. clear H.
  destruct H0. destruct H. destruct H. destruct H. destruct H.
  destruct x1. destruct x0. destruct p. destruct u. destruct u0. destruct H.
  destruct H. destruct H. destruct H. destruct x1. destruct u. destruct u0.
  simpl in *. destruct ( excluded_middle_informative (tt = tt) ). 
  Focus 2. elim n. auto. clear e. subst x. clear H0. destruct H. destruct H.
  destruct H. elim H.
Qed.

Theorem adom_no_beta : exists A B (f: exp (prod A B) prop),
  (denoteB (holToNrc (beta f)) = denoteB (holToNrc f)) -> False.
Proof.
 exists one. exists dom. exists tru. apply bad_no_beta_1.
Qed.

(* Translatation HOL to NRC not semantics preserving for DI terms ***************)

Lemma bad_not_pres (pf: denoteB (holToNrc bad) = denote bad) : False. 
 pose (@equal_f_dep0 Set (fun D : Set => inst (prod one dom) D -> inst prop D)
  (denoteB (holToNrc bad)) (denote bad) pf unit). clearbody e. clear pf.
  pose (equal_f e). clearbody e0. clear e. pose (e0 (tt,tt)). clearbody e.
  clear e0. simpl in *. destruct (excluded_middle_informative True).
   Focus 2. contradiction n. auto. clear t.
  repeat rewrite <- Im_sem_0 in *. unfold Im_def0 in *.
  unfold join in *. simpl in *. rewrite singSem in *. unfold sing in *.
  assert True. auto. rewrite <- e in H. clear e. apply equal_f with tt in H.
   simpl in *. assert ( (tt = tt) = True ). apply prop_extensionality. split; auto. 
  rewrite H0 in H. clear H0. assert True. auto. rewrite <- H in H0. clear H.
  destruct H0. destruct H. destruct H. destruct H. destruct H.
  destruct x1. destruct x0. destruct p. destruct u. destruct u0. destruct H.
  destruct H. destruct H. destruct H. destruct x1. destruct u. destruct u0.
  simpl in *. destruct ( excluded_middle_informative (tt = tt) ). 
  Focus 2. elim n. auto. clear e. subst x. clear H0. destruct H. destruct H.
  destruct H. elim H.
Qed.

Lemma nrcToHol_notsem_di : 
 (forall A B (f: exp A B), di (denote f) -> 
  denote f = denoteB (holToNrc f)) -> False.
Proof.
 intros. assert (di (denote tru)). simpl. unfold di. unfold mono. simpl.
  intros. auto. assert (denote tru = denote bad). simpl. auto.
  assert (di (denote bad)). rewrite <- H1. auto. pose (H _ _ tru). pose (H _ _ bad).
  clearbody e e0. clear H. pose bad_not_pres. clearbody f. apply f. clear f.
  rewrite <- e0. auto. auto. 
Qed.

(* Note that the point-free forumulation of HOL, as defined in this file, 
  is more expressive than HOL as defined in my thesis.  See my thesis errata 
  for a proof that the translation HOL to NRC is not semantics preserving on
  DI terms for HOL + weakening.  Since the system in this file contains 
  HOL + weakening, we have that HOL as defined here is not semantics preserving
  for DI terms.  The question of whether the translation is semantics preserving
  for pure HOL (as defined in my thesis) on DI terms is still open as of April 2014.*) 




