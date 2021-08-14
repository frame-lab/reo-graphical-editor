Require Import CaMain.
Require Import ReoCA.
Import ListNotations.

Obligation Tactic := program_simpl; congruence.

Inductive sequencerStates := s0 | q0a | p0a| p1a.
Inductive sequencerPorts := A | B | C | D | E | F | G | H | I | J.

Program Instance sequencerStatesEq : EqDec sequencerStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| s0,s0 => in_left 
		| q0a,q0a => in_left 
		| p0a,p0a => in_left 
		| p1a,p1a => in_left 
		| s0,q0a => in_right 
		| s0,p0a => in_right 
		| s0,p1a => in_right 
		| q0a,s0 => in_right 
		| q0a,p0a => in_right 
		| q0a,p1a => in_right 
		| p0a,s0 => in_right 
		| p0a,q0a => in_right 
		| p0a,p1a => in_right 
		| p1a,s0 => in_right 
		| p1a,q0a => in_right 
		| p1a,p0a => in_right 
		end 
	}.

Program Instance sequencerPortsEq : EqDec sequencerPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| C,C => in_left 
		| D,D => in_left 
		| E,E => in_left 
		| F,F => in_left 
		| G,G => in_left 
		| H,H => in_left 
		| I,I => in_left 
		| J,J => in_left 
		| A,B => in_right 
		| A,C => in_right 
		| A,D => in_right 
		| A,E => in_right 
		| A,F => in_right 
		| A,G => in_right 
		| A,H => in_right 
		| A,I => in_right 
		| A,J => in_right 
		| B,A => in_right 
		| B,C => in_right 
		| B,D => in_right 
		| B,E => in_right 
		| B,F => in_right 
		| B,G => in_right 
		| B,H => in_right 
		| B,I => in_right 
		| B,J => in_right 
		| C,A => in_right 
		| C,B => in_right 
		| C,D => in_right 
		| C,E => in_right 
		| C,F => in_right 
		| C,G => in_right 
		| C,H => in_right 
		| C,I => in_right 
		| C,J => in_right 
		| D,A => in_right 
		| D,B => in_right 
		| D,C => in_right 
		| D,E => in_right 
		| D,F => in_right 
		| D,G => in_right 
		| D,H => in_right 
		| D,I => in_right 
		| D,J => in_right 
		| E,A => in_right 
		| E,B => in_right 
		| E,C => in_right 
		| E,D => in_right 
		| E,F => in_right 
		| E,G => in_right 
		| E,H => in_right 
		| E,I => in_right 
		| E,J => in_right 
		| F,A => in_right 
		| F,B => in_right 
		| F,C => in_right 
		| F,D => in_right 
		| F,E => in_right 
		| F,G => in_right 
		| F,H => in_right 
		| F,I => in_right 
		| F,J => in_right 
		| G,A => in_right 
		| G,B => in_right 
		| G,C => in_right 
		| G,D => in_right 
		| G,E => in_right 
		| G,F => in_right 
		| G,H => in_right 
		| G,I => in_right 
		| G,J => in_right 
		| H,A => in_right 
		| H,B => in_right 
		| H,C => in_right 
		| H,D => in_right 
		| H,E => in_right 
		| H,F => in_right 
		| H,G => in_right 
		| H,I => in_right 
		| H,J => in_right 
		| I,A => in_right 
		| I,B => in_right 
		| I,C => in_right 
		| I,D => in_right 
		| I,E => in_right 
		| I,F => in_right 
		| I,G => in_right 
		| I,H => in_right 
		| I,J => in_right 
		| J,A => in_right 
		| J,B => in_right 
		| J,C => in_right 
		| J,D => in_right 
		| J,E => in_right 
		| J,F => in_right 
		| J,G => in_right 
		| J,H => in_right 
		| J,I => in_right 
		end 
	}.

  Definition dataAssignmentA n := 
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

  Definition dataAssignmentC n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

  Definition dataAssignmentD n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

  Definition dataAssignmentE n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  2
    | S n =>  2
    end.

  Definition dataAssignmentF n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  2
    | S n =>  2
    end.

  Definition dataAssignmentG n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

  Definition dataAssignmentH n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  2
    | S n =>  2
    end.

  Definition dataAssignmentI n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.


   Definition timeStampSequencerA(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 17#1
    end.

  Definition timeStampSequencerB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 18#1
    end.


  Definition timeStampSequencerC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 19#1
    end.

  Definition timeStampSequencerD (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1 
    end.

  Definition timeStampSequencerE (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 17#1
    end.

  Definition timeStampSequencerG (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 18#1
    end.

  Definition timeStampSequencerH (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 19#1
    end.

   Definition timeStampSequencerI(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1 
    end.

  Lemma timeStampSequencerAHolds : forall n, 
    Qlt (timeStampSequencerA n) (timeStampSequencerA (S n)).
  Proof.
  intros. destruct n. unfold timeStampSequencerA. reflexivity.
  unfold timeStampSequencerA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.
  
  Lemma timeStampSequencerBHolds : forall n, 
    Qlt (timeStampSequencerB n) (timeStampSequencerB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerB. reflexivity.
  unfold timeStampSequencerB. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerCHolds : forall n, 
    Qlt (timeStampSequencerC n) (timeStampSequencerC (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerC. reflexivity.
  unfold timeStampSequencerC. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerDHolds : forall n, 
    Qlt (timeStampSequencerD n) (timeStampSequencerD (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerD. reflexivity.
  unfold timeStampSequencerD. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerEHolds : forall n, 
    Qlt (timeStampSequencerE n) (timeStampSequencerE (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerE. reflexivity.
  unfold timeStampSequencerE. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerGHolds : forall n, 
    Qlt (timeStampSequencerG n) (timeStampSequencerG (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerG. reflexivity.
  unfold timeStampSequencerG. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerHHolds : forall n, 
    Qlt (timeStampSequencerH n) (timeStampSequencerH (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerH. reflexivity.
  unfold timeStampSequencerH. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerJHolds : forall n, 
    Qlt (timeStampSequencerA n) (timeStampSequencerA (S n)).
  Proof.
  intros. destruct n. unfold timeStampSequencerA. reflexivity.
  unfold timeStampSequencerA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampSequencerA;
        ConstraintAutomata.tdsCond := timeStampSequencerAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampSequencerB;
        ConstraintAutomata.tdsCond := timeStampSequencerBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portC := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampSequencerC;
        ConstraintAutomata.tdsCond := timeStampSequencerCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portD := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD;
        ConstraintAutomata.timeStamp := timeStampSequencerD;
        ConstraintAutomata.tdsCond := timeStampSequencerDHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portE := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE;
        ConstraintAutomata.timeStamp := timeStampSequencerE;
        ConstraintAutomata.tdsCond := timeStampSequencerEHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portG := {|
        ConstraintAutomata.id := G;
        ConstraintAutomata.dataAssignment := dataAssignmentG;
        ConstraintAutomata.timeStamp := timeStampSequencerG;
        ConstraintAutomata.tdsCond := timeStampSequencerGHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portH := {|
        ConstraintAutomata.id := H;
        ConstraintAutomata.dataAssignment := dataAssignmentH;
        ConstraintAutomata.timeStamp := timeStampSequencerH;
        ConstraintAutomata.tdsCond := timeStampSequencerHHolds;
        ConstraintAutomata.index := 0 |}.


  (*D FIFO E *)
  Definition dToEFIFOrel (s:sequencerStates) :=
    match s with
    | q0a => [([D], (ConstraintAutomata.dc D 0), p0a);
              ([D], (ConstraintAutomata.dc D 1), p1a)]
    | p0a => [([E], (ConstraintAutomata.dc E 0), q0a)]
    | p1a => [([E], (ConstraintAutomata.dc E 1), q0a)] 
    | s0 => []
    end.

  (* This FIFO starts with a data item; the value denoted by 0 is in it, as the initial state denotes *)
  Definition dToEFIFOCA:= ReoCa.ReoCABinaryChannel D E ([q0a;p0a;p1a]) ([q0a]) (dToEFIFOrel). 

  (* E Sync A *)
  Definition syncEACaBehavior (s: sequencerStates) :=
    match s with
    | s0 => [([E;A] , ConstraintAutomata.eqDc nat E A, s0)] 
    | _ => []
    end.

  Definition EAsyncCA := ReoCa.ReoCABinaryChannel E A ([s0]) ([s0]) syncEACaBehavior. 

  (*E FIFO G *)
  Definition eToGFIFOrel (s:sequencerStates) :=
    match s with
    | q0a => [([E], (ConstraintAutomata.dc E ( 0)), p0a) ;
              ([E], (ConstraintAutomata.dc E ( 1)), p1a)]
    | p0a => [([G], (ConstraintAutomata.dc G ( 0)), q0a)]
    | p1a => [([G], (ConstraintAutomata.dc G ( 1)), q0a)] 
    | s0 => []
    end.

  Definition eToGFIFOCA:= ReoCa.ReoCABinaryChannel E G ([q0a;p0a;p1a]) ([q0a]) eToGFIFOrel.

  (* G Sync B *)
  Definition syncGBCaBehavior (s: sequencerStates) :=
    match s with
    | s0 => [([G;B] , ConstraintAutomata.eqDc nat G B, s0)] 
    | _ => []
    end.

  Definition GBsyncCA := ReoCa.ReoCABinaryChannel G B ([s0]) ([s0]) syncGBCaBehavior.

  (*G FIFO H*)
  Definition gToHFIFOrel (s:sequencerStates):=
    match s with
    | q0a => [([G], (ConstraintAutomata.dc G ( 0)), p0a) ;
              ([G], (ConstraintAutomata.dc G ( 1)), p1a)]
    | p0a => [([H], (ConstraintAutomata.dc H ( 0)), q0a)]
    | p1a => [([H], (ConstraintAutomata.dc H ( 1)), q0a)] 
    | s0 => []
    end.

  Definition gToHFIFOCA:= ReoCa.ReoCABinaryChannel G H ([q0a;p0a;p1a]) ([q0a]) gToHFIFOrel.

  (* H Sync C *)
  Definition syncHCCaBehavior (s: sequencerStates) :=
    match s with
    | s0 => [([H;C] , ConstraintAutomata.eqDc nat H C, s0)] 
    | _ => []
    end.

  Definition HCsyncCA := ReoCa.ReoCABinaryChannel H C ([s0]) ([s0]) syncHCCaBehavior.

  (* We build the resulting product automaton *)
  Definition fifo1Product := ProductAutomata.buildPA dToEFIFOCA EAsyncCA.
  Definition fifo2Product := ProductAutomata.buildPA fifo1Product eToGFIFOCA.
  Definition fifo3Product := ProductAutomata.buildPA fifo2Product GBsyncCA.
  Definition fifo4Product := ProductAutomata.buildPA fifo3Product gToHFIFOCA.
  Definition resultingSequencerProduct := ProductAutomata.buildPA fifo4Product HCsyncCA.

  (*The automaton changes its initial configuration only if there are data in ports D*)
  (*Eval vm_compute in ConstraintAutomata.portsOfTransition resultingSequencerProduct 
    (q0a, s0, q0a, s0, q0a, s0).*)

  (*  If the automaton is in its starting state, D will be the only port 
      observing data *)
  Lemma firstPortToHavaDataIsD : forall state, 
    In (state) (ConstraintAutomata.Q0 resultingSequencerProduct) -> 
    In (state) (ConstraintAutomata.Q resultingSequencerProduct) /\
    In (D) (ConstraintAutomata.portsOfTransition resultingSequencerProduct state) /\
    ~ In (A) (ConstraintAutomata.portsOfTransition resultingSequencerProduct state) /\
    ~ In (B) (ConstraintAutomata.portsOfTransition resultingSequencerProduct state) /\
    ~ In (C) (ConstraintAutomata.portsOfTransition resultingSequencerProduct state).
  Proof.
  - intros. simpl in H0. destruct H0.
  + rewrite <- H0. vm_compute. split. left. reflexivity. split. 
    { left. reflexivity. }
  split. intros H. destruct H. inversion H1. exact H1. 
  split. intros H. destruct H. inversion H1. exact H1. 
  intros H. destruct H. inversion H1. exact H1. 
  + inversion H0.
  Qed.
 
  Definition singleExecInput := [portA;portB;portC;portD;portE;portG;portH].

  Definition run1 := Eval vm_compute in ConstraintAutomata.run resultingSequencerProduct singleExecInput 4.
  (*Print run1.*)

  Lemma acceptingRunAllPortsWData :  ~ In [] (run1) /\
                                       In [(p1a, s0, q0a, s0, q0a, s0)] (run1) /\
                                       In [(q0a, s0, p1a, s0, q0a, s0)] (run1) /\
                                       In [(q0a, s0, q0a, s0, p1a, s0)] (run1).
  Proof.
  unfold run1. split.
  unfold not. intros. simpl in H0. repeat (destruct H0; inversion H0).
  repeat (split; simpl;auto).
  Defined.

(* Ex 2 *)
 Definition timeStampSequencerA2(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerB2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.


  Definition timeStampSequencerC2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerD2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerE2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerG2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerH2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.


  Definition timeStampSequencerI2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Lemma timeStampSequencerA2Holds : forall n, 
    Qlt (timeStampSequencerA2 n) (timeStampSequencerA2 (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerA2. reflexivity.
  unfold timeStampSequencerA2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerB2Holds : forall n, 
    Qlt (timeStampSequencerB2 n) (timeStampSequencerB2 (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerB2. reflexivity.
  unfold timeStampSequencerB2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.
  Lemma timeStampSequencerC2Holds : forall n, 
    Qlt (timeStampSequencerC2 n) (timeStampSequencerC2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerC2. reflexivity.
  unfold timeStampSequencerC2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerD2Holds : forall n, 
    Qlt (timeStampSequencerD2 n) (timeStampSequencerD2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerD2. reflexivity.
  unfold timeStampSequencerD2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerE2Holds : forall n, 
    Qlt (timeStampSequencerE2 n) (timeStampSequencerB2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerE2. reflexivity.
  unfold timeStampSequencerE2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerG2Holds : forall n, 
    Qlt (timeStampSequencerG2 n) (timeStampSequencerG2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerG2. reflexivity.
  unfold timeStampSequencerG2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerH2Holds : forall n, 
    Qlt (timeStampSequencerH2 n) (timeStampSequencerH2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerH2. reflexivity.
  unfold timeStampSequencerH2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Definition portA2 := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampSequencerA2;
        ConstraintAutomata.tdsCond := timeStampSequencerA2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portB2 := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampSequencerB2;
        ConstraintAutomata.tdsCond := timeStampSequencerB2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portC2 := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampSequencerC2;
        ConstraintAutomata.tdsCond := timeStampSequencerC2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portD2 := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD;
        ConstraintAutomata.timeStamp := timeStampSequencerD2;
        ConstraintAutomata.tdsCond := timeStampSequencerD2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portE2 := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE;
        ConstraintAutomata.timeStamp := timeStampSequencerE2;
        ConstraintAutomata.tdsCond := timeStampSequencerE2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portG2 := {|
        ConstraintAutomata.id := G;
        ConstraintAutomata.dataAssignment := dataAssignmentG;
        ConstraintAutomata.timeStamp := timeStampSequencerG2;
        ConstraintAutomata.tdsCond := timeStampSequencerG2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portH2 := {|
        ConstraintAutomata.id := H;
        ConstraintAutomata.dataAssignment := dataAssignmentH;
        ConstraintAutomata.timeStamp := timeStampSequencerH2;
        ConstraintAutomata.tdsCond := timeStampSequencerH2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition secondExInput := [portA2;portB2;portC2;portD2;portE2;portG2;portH2].

  Definition run2 := Eval vm_compute in ConstraintAutomata.run resultingSequencerProduct secondExInput 7.
  (* Print run2. *)

  Lemma nonAcceptingRun : In [] (run2).
  Proof.
  simpl. auto. Defined.

  Lemma rejectingRun : ConstraintAutomata.rejecting resultingSequencerProduct secondExInput.
  Proof.
  unfold ConstraintAutomata.rejecting.
  exists 7. unfold ConstraintAutomata.lastReachedStates. vm_compute. reflexivity.
  Defined.


  Require Extraction.
  Extraction Language Haskell.
  Extraction "SequencerCertified" resultingSequencerProduct.
