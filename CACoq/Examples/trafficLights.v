
Require Import CaMain.
Import ListNotations.

Obligation Tactic := program_simpl; congruence.
 
Inductive modelPortsType := 
	a | y | b | x | i | j | l | k | m | n |  c. 
Program Instance modelPortsEqDec : EqDec modelPortsType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| a , a => in_left 
		| a , y => in_right
		| a , b => in_right
		| a , x => in_right
		| a , i => in_right
		| a , j => in_right
		| a , l => in_right
		| a , k => in_right
		| a , m => in_right
		| a , n => in_right
		| a , c => in_right
		| y , a => in_right
		| y , y => in_left 
		| y , b => in_right
		| y , x => in_right
		| y , i => in_right
		| y , j => in_right
		| y , l => in_right
		| y , k => in_right
		| y , m => in_right
		| y , n => in_right
		| y , c => in_right
		| b , a => in_right
		| b , y => in_right
		| b , b => in_left 
		| b , x => in_right
		| b , i => in_right
		| b , j => in_right
		| b , l => in_right
		| b , k => in_right
		| b , m => in_right
		| b , n => in_right
		| b , c => in_right
		| x , a => in_right
		| x , y => in_right
		| x , b => in_right
		| x , x => in_left 
		| x , i => in_right
		| x , j => in_right
		| x , l => in_right
		| x , k => in_right
		| x , m => in_right
		| x , n => in_right
		| x , c => in_right
		| i , a => in_right
		| i , y => in_right
		| i , b => in_right
		| i , x => in_right
		| i , i => in_left 
		| i , j => in_right
		| i , l => in_right
		| i , k => in_right
		| i , m => in_right
		| i , n => in_right
		| i , c => in_right
		| j , a => in_right
		| j , y => in_right
		| j , b => in_right
		| j , x => in_right
		| j , i => in_right
		| j , j => in_left 
		| j , l => in_right
		| j , k => in_right
		| j , m => in_right
		| j , n => in_right
		| j , c => in_right
		| l , a => in_right
		| l , y => in_right
		| l , b => in_right
		| l , x => in_right
		| l , i => in_right
		| l , j => in_right
		| l , l => in_left 
		| l , k => in_right
		| l , m => in_right
		| l , n => in_right
		| l , c => in_right
		| k , a => in_right
		| k , y => in_right
		| k , b => in_right
		| k , x => in_right
		| k , i => in_right
		| k , j => in_right
		| k , l => in_right
		| k , k => in_left 
		| k , m => in_right
		| k , n => in_right
		| k , c => in_right
		| m , a => in_right
		| m , y => in_right
		| m , b => in_right
		| m , x => in_right
		| m , i => in_right
		| m , j => in_right
		| m , l => in_right
		| m , k => in_right
		| m , m => in_left 
		| m , n => in_right
		| m , c => in_right
		| n , a => in_right
		| n , y => in_right
		| n , b => in_right
		| n , x => in_right
		| n , i => in_right
		| n , j => in_right
		| n , l => in_right
		| n , k => in_right
		| n , m => in_right
		| n , n => in_left 
		| n , c => in_right
		| c , a => in_right
		| c , y => in_right
		| c , b => in_right
		| c , x => in_right
		| c , i => in_right
		| c , j => in_right
		| c , l => in_right
		| c , k => in_right
		| c , m => in_right
		| c , n => in_right
		| c , c => in_left 
	end
	}.
Inductive merger1StatesType := 
	q0.
Program Instance merger1EqDec : EqDec merger1StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q0 , q0 => in_left 
	end
	}.
Inductive sync2StatesType := 
	q1.
Program Instance sync2EqDec : EqDec sync2StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q1 , q1 => in_left 
	end
	}.
Inductive sync3StatesType := 
	q2.
Program Instance sync3EqDec : EqDec sync3StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q2 , q2 => in_left 
	end
	}.
Inductive sync4StatesType := 
	q3.
Program Instance sync4EqDec : EqDec sync4StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q3 , q3 => in_left 
	end
	}.
Inductive transformer5StatesType := 
	q4.
Program Instance transformer5EqDec : EqDec transformer5StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q4 , q4 => in_left 
	end
	}.
Inductive sync6StatesType := 
	q5.
Program Instance sync6EqDec : EqDec sync6StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q5 , q5 => in_left 
	end
	}.
Inductive sync7StatesType := 
	q6.
Program Instance sync7EqDec : EqDec sync7StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q6 , q6 => in_left 
	end
	}.
Inductive fifo8StatesType := 
	 q7 | 	 p0 | 	p1.
Program Instance fifo8EqDec : EqDec fifo8StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q7 , q7 => in_left 
		| q7 , p0 => in_right 
		| q7 , p1 => in_right 
		| p0 , q7 => in_right 
		| p0 , p0 => in_left 
		| p0 , p1 => in_right 
		| p1 , q7 => in_right 
		| p1 , p0 => in_right 
		| p1 , p1 => in_left 
	end
	}.
Inductive merger9StatesType := 
	q8.
Program Instance merger9EqDec : EqDec merger9StatesType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| q8 , q8 => in_left 
	end
	}.
Definition merger1rel (s: merger1StatesType) :=
	match s with
		 | q0 => [([a;y], ConstraintAutomata.eqDc nat a y , q0);([b;y], ConstraintAutomata.eqDc nat b y , q0)] 
	end.
Definition merger1Automaton := {| 
	ConstraintAutomata.Q := [q0];
	ConstraintAutomata.N := [a;y;b];
	ConstraintAutomata.T := merger1rel;
	ConstraintAutomata.Q0 := [q0]
|}.
Definition sync2rel (s: sync2StatesType) :=
	match s with
		 | q1 => [([y;x], ConstraintAutomata.eqDc nat y x  , q1)] 
	end.
Definition sync2Automaton := {| 
	ConstraintAutomata.Q := [q1];
	ConstraintAutomata.N := [y;x];
	ConstraintAutomata.T := sync2rel;
	ConstraintAutomata.Q0 := [q1]
|}.
Definition sync3rel (s: sync3StatesType) :=
	match s with
		 | q2 => [([x;i], ConstraintAutomata.eqDc nat x i  , q2)] 
	end.
Definition sync3Automaton := {| 
	ConstraintAutomata.Q := [q2];
	ConstraintAutomata.N := [x;i];
	ConstraintAutomata.T := sync3rel;
	ConstraintAutomata.Q0 := [q2]
|}.
Definition sync4rel (s: sync4StatesType) :=
	match s with
		 | q3 => [([x;j], ConstraintAutomata.eqDc nat x j  , q3)] 
	end.
Definition sync4Automaton := {| 
	ConstraintAutomata.Q := [q3];
	ConstraintAutomata.N := [x;j];
	ConstraintAutomata.T := sync4rel;
	ConstraintAutomata.Q0 := [q3]
|}.

Close Scope Q_scope.
Definition swap01 (n:nat) :=
  match n with
  | 0 => 1
  | 1 => 0
  | S o => S o
  end.

Definition transformer5rel (s: transformer5StatesType) :=
	match s with
		 | q4 => [([j;l], ConstraintAutomata.trDc swap01 j l , q4)] 
	end.
Definition transformer5Automaton := {| 
	ConstraintAutomata.Q := [q4];
	ConstraintAutomata.N := [j;l];
	ConstraintAutomata.T := transformer5rel;
	ConstraintAutomata.Q0 := [q4]
|}.
Definition sync6rel (s: sync6StatesType) :=
	match s with
		 | q5 => [([i;k], ConstraintAutomata.eqDc nat i k  , q5)] 
	end.
Definition sync6Automaton := {| 
	ConstraintAutomata.Q := [q5];
	ConstraintAutomata.N := [i;k];
	ConstraintAutomata.T := sync6rel;
	ConstraintAutomata.Q0 := [q5]
|}.
Definition sync7rel (s: sync7StatesType) :=
	match s with
		 | q6 => [([l;m], ConstraintAutomata.eqDc nat l m  , q6)] 
	end.
Definition sync7Automaton := {| 
	ConstraintAutomata.Q := [q6];
	ConstraintAutomata.N := [l;m];
	ConstraintAutomata.T := sync7rel;
	ConstraintAutomata.Q0 := [q6]
|}.
Definition fifo8rel (s: fifo8StatesType) :=
	match s with
		 | q7 => [([k], ConstraintAutomata.dc k 0 , p0); ([k], ConstraintAutomata.dc k 1 , p1)] 
		 | p0 => [([n], ConstraintAutomata.dc n 0 , q7)]
		 | p1 => [([n], ConstraintAutomata.dc n 1 , q7)] 
	end.
Definition fifo8Automaton := {| 
	ConstraintAutomata.Q := [q7;p0;p1];
	ConstraintAutomata.N := [k;n];
	ConstraintAutomata.T := fifo8rel;
	ConstraintAutomata.Q0 := [q7]
|}.
Definition merger9rel (s: merger9StatesType) :=
	match s with
		 | q8 => [([m;c], ConstraintAutomata.eqDc nat m c , q8);([n;c], ConstraintAutomata.eqDc nat n c , q8)] 
	end.
Definition merger9Automaton := {| 
	ConstraintAutomata.Q := [q8];
	ConstraintAutomata.N := [m;c;n];
	ConstraintAutomata.T := merger9rel;
	ConstraintAutomata.Q0 := [q8]
|}.
Definition merger1sync2Product := ProductAutomata.buildPA merger1Automaton sync2Automaton.
Definition sync2sync3Product := ProductAutomata.buildPA merger1sync2Product sync3Automaton.
Definition sync3sync4Product := ProductAutomata.buildPA sync2sync3Product sync4Automaton.
Definition sync4transformer5Product := ProductAutomata.buildPA sync3sync4Product transformer5Automaton.
Definition transformer5sync6Product := ProductAutomata.buildPA sync4transformer5Product sync6Automaton.
Definition sync6sync7Product := ProductAutomata.buildPA transformer5sync6Product sync7Automaton.
Definition sync7fifo8Product := ProductAutomata.buildPA sync6sync7Product fifo8Automaton.
Definition fifo8merger9Product := ProductAutomata.buildPA sync7fifo8Product merger9Automaton.

(**** Readequar trecho de código abaixo para o exemplo acima ***)


(*We may state that from a initial state of the automaton (i.e., possible data gateway into *)
(* it is possible that a given traffic light may be open for an amount of time   *)
(* which may disturb pedestrians waiting to cross the road. *)
(* We may split this properties into two lemmas *)

(* The first one states that, from any initial state of te automaton, it is not possible  *)
(* to repeat the same state (i.e., the same signal) if data have left from a (the sensor) *)
(* to c (the receiver)                                                                    *)

Lemma possibleTrafficLightToBeOpenedNotTheSame : forall state,forall transition,
  In (state) (ConstraintAutomata.Q0 fifo8merger9Product) /\ 
  In (transition) (ConstraintAutomata.T fifo8merger9Product state) /\
  In (a) (fst(fst(transition))) /\ In (c) (fst(fst(transition))) -> 
  snd(transition) <> (q0,q1,q2,q3,q4,q5,q6,q7,q8).
Proof.
intros. destruct H.
simpl in H. destruct H. destruct H0.
- rewrite <- H in H0. vm_compute in H0. repeat (destruct H0). 
+ simpl; discriminate.
+ simpl; discriminate.
+ simpl; discriminate.
+ simpl; discriminate.
- inversion H.
Qed.

(* And now, we may state that, from any state reached from a initial state, they cannot reach a
scenario where one of the traffic light have dhe same data*)
Lemma possibleTrafficLightToBeOpenedNotTheSame2 : forall state,forall transition,
  In (state) (ConstraintAutomata.Q fifo8merger9Product) /\ 
  In (transition) (ConstraintAutomata.T fifo8merger9Product state) /\
  In (a) (fst(fst(transition))) /\ In (c) (fst(fst(transition))) -> 
  snd(transition) <> (state).
Proof.
intros. destruct H.
simpl in H. destruct H. destruct H0.
- rewrite <- H in H0. vm_compute in H0. repeat (destruct H0). 
+ rewrite <- H. simpl; discriminate.
+ rewrite <- H. simpl; discriminate.
+ rewrite <- H. simpl; discriminate.
+ rewrite <- H. simpl; discriminate.
- destruct H. destruct H0.
 rewrite <- H in H0. vm_compute in H0. repeat (destruct H0). 
+ rewrite <- H. simpl; discriminate.
+ destruct H. destruct H0 .
  rewrite <- H in H0. vm_compute in H0. repeat (destruct H0). 
  rewrite <- H. simpl; discriminate.
  inversion H.
Qed.




(*data flow*)
Definition dataAssignmentA (n:nat) := 
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end. 

  Definition dataAssignmentB (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentC (n:nat) :=
    match n with
    | 0 =>  0
    | 1 =>  (0)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentD (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentE (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentF (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentG (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentH (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentI (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentJ (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentK (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentL (n:nat) :=
    match n with
    | 0 =>  0
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentM (n:nat) :=
    match n with
    | 0 =>  0
    | 1 =>  (0)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentN (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentX (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

  Definition dataAssignmentY (n:nat) :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S p =>  0
    end.

   Definition timeStampSequencerA(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

  Definition timeStampSequencerB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 30#1
    | 1 => 70#1
    | 2 => 90#1
    | 3 => 120#1
    | 4 => 150#1
    | 5 => 180#1
    | S p =>  Z.of_nat(S p) + 190#1
    end.


  Definition timeStampSequencerC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 19#1
    end.

  Definition timeStampSequencerD (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

  Definition timeStampSequencerE (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

  Definition timeStampSequencerF (n:nat) : QArith_base.Q :=
    match n with (*filtro de cima*)
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.


  Definition timeStampSequencerG (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 30#1
    | 1 => 60#1
    | 2 => 80#1
    | 3 => 110#1
    | 4 => 140#1
    | 5 => 170#1
    | S p =>  Z.of_nat(S p) + 170#1
    end.

  Definition timeStampSequencerH (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

   Definition timeStampSequencerI(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.


   Definition timeStampSequencerJ(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

   Definition timeStampSequencerK(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

   Definition timeStampSequencerL(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

   Definition timeStampSequencerM(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

   Definition timeStampSequencerN (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 30#1 
    | 1 => 50#1
    | 2 => 80#1
    | 3 => 110#1
    | 4 => 140#1
    | 5 => 170#1
    | S p =>  Z.of_nat (S p) + 170#1 
    end.

   Definition timeStampSequencerX(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

  Definition timeStampSequencerY(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S p =>  Z.of_nat(S p) + 17#1
    end.

  Lemma timeStampSequencerAHolds : forall p, 
    Qlt (timeStampSequencerA p) (timeStampSequencerA (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerA. reflexivity.
  unfold timeStampSequencerA. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.
  
  Lemma timeStampSequencerBHolds : forall p, 
    Qlt (timeStampSequencerB p) (timeStampSequencerB (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerB. reflexivity.
  unfold timeStampSequencerB. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerCHolds : forall p, 
    Qlt (timeStampSequencerC p) (timeStampSequencerC (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerC. reflexivity.
  unfold timeStampSequencerC. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerDHolds : forall p, 
    Qlt (timeStampSequencerD p) (timeStampSequencerD (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerD. reflexivity.
  unfold timeStampSequencerD. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerEHolds : forall p, 
    Qlt (timeStampSequencerE p) (timeStampSequencerE (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerE. reflexivity.
  unfold timeStampSequencerE. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerFHolds : forall p, 
    Qlt (timeStampSequencerF p) (timeStampSequencerF (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerF. reflexivity.
  unfold timeStampSequencerF. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.


  Lemma timeStampSequencerGHolds : forall p, 
    Qlt (timeStampSequencerG p) (timeStampSequencerG (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerG. reflexivity.
  unfold timeStampSequencerG. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerHHolds : forall p, 
    Qlt (timeStampSequencerH p) (timeStampSequencerH (S p)). 
  Proof.
  intros. destruct p. unfold timeStampSequencerH. reflexivity.
  unfold timeStampSequencerH. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerIHolds : forall p, 
    Qlt (timeStampSequencerI p) (timeStampSequencerI (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerI. reflexivity.
  unfold timeStampSequencerI. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerJHolds : forall p, 
    Qlt (timeStampSequencerJ p) (timeStampSequencerJ (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerJ. reflexivity.
  unfold timeStampSequencerJ. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerKHolds : forall p, 
    Qlt (timeStampSequencerK p) (timeStampSequencerK (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerK. reflexivity.
  unfold timeStampSequencerK. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerLHolds : forall p, 
    Qlt (timeStampSequencerL p) (timeStampSequencerL (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerL. reflexivity.
  unfold timeStampSequencerL. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerMHolds : forall p, 
    Qlt (timeStampSequencerM p) (timeStampSequencerM (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerM. reflexivity.
  unfold timeStampSequencerM. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerNHolds : forall p, 
    Qlt (timeStampSequencerN p) (timeStampSequencerN (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerN. reflexivity.
  unfold timeStampSequencerN. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerXHolds : forall p, 
    Qlt (timeStampSequencerX p) (timeStampSequencerX (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerX. reflexivity.
  unfold timeStampSequencerX. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampSequencerYHolds : forall p, 
    Qlt (timeStampSequencerY p) (timeStampSequencerY (S p)).
  Proof.
  intros. destruct p. unfold timeStampSequencerY. reflexivity.
  unfold timeStampSequencerY. case (p). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.


  Definition portA := {|
        ConstraintAutomata.id := a;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampSequencerA;
        ConstraintAutomata.tdsCond := timeStampSequencerAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := b;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampSequencerB;
        ConstraintAutomata.tdsCond := timeStampSequencerBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portC := {|
        ConstraintAutomata.id := c;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampSequencerC;
        ConstraintAutomata.tdsCond := timeStampSequencerCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portI := {|
        ConstraintAutomata.id := i;
        ConstraintAutomata.dataAssignment := dataAssignmentI;
        ConstraintAutomata.timeStamp := timeStampSequencerI;
        ConstraintAutomata.tdsCond := timeStampSequencerIHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portJ := {|
        ConstraintAutomata.id := j;
        ConstraintAutomata.dataAssignment := dataAssignmentJ;
        ConstraintAutomata.timeStamp := timeStampSequencerJ;
        ConstraintAutomata.tdsCond := timeStampSequencerJHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portK := {|
        ConstraintAutomata.id := k;
        ConstraintAutomata.dataAssignment := dataAssignmentK;
        ConstraintAutomata.timeStamp := timeStampSequencerK;
        ConstraintAutomata.tdsCond := timeStampSequencerKHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portL := {|
        ConstraintAutomata.id := l;
        ConstraintAutomata.dataAssignment := dataAssignmentL;
        ConstraintAutomata.timeStamp := timeStampSequencerL;
        ConstraintAutomata.tdsCond := timeStampSequencerLHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portM := {|
        ConstraintAutomata.id := m;
        ConstraintAutomata.dataAssignment := dataAssignmentM;
        ConstraintAutomata.timeStamp := timeStampSequencerM;
        ConstraintAutomata.tdsCond := timeStampSequencerMHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portN := {|
        ConstraintAutomata.id := n;
        ConstraintAutomata.dataAssignment := dataAssignmentN;
        ConstraintAutomata.timeStamp := timeStampSequencerN;
        ConstraintAutomata.tdsCond := timeStampSequencerNHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portX := {|
        ConstraintAutomata.id := x;
        ConstraintAutomata.dataAssignment := dataAssignmentX;
        ConstraintAutomata.timeStamp := timeStampSequencerX;
        ConstraintAutomata.tdsCond := timeStampSequencerXHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portY := {|
        ConstraintAutomata.id := y;
        ConstraintAutomata.dataAssignment := dataAssignmentY;
        ConstraintAutomata.timeStamp := timeStampSequencerY;
        ConstraintAutomata.tdsCond := timeStampSequencerYHolds;
        ConstraintAutomata.index := 0 |}.

  Definition dataFlow := [portA;portB;portC;portI;
                        portJ;portK;portL;portM;portN;portX;portY].

  Eval vm_compute in ConstraintAutomata.run fifo8merger9Product dataFlow 2.

  Require Extraction.
  Extraction Language Haskell.
  Extraction "trafficLightsCertified" fifo8merger9Product.




