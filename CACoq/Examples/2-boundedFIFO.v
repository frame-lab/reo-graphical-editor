Require Import CaMain.
Import ListNotations.

Obligation Tactic := program_simpl; congruence.

(* This example consists on using two FIFO channels of capacity one in order to build  *)
(* a single Reo channel which is a FIFO channel with capacity two. This is done by for-*)
(* malizing Constraint Automata of both channels with capacity one and then, by means  *)
(* of the product operation, the corresponding product automaton is built.             *)

Inductive fifoStates := q0a | p0a | p1a | q0b | p0b | p1b.
Inductive fifoPorts := A | B | C | D.

Program Instance fifoStatesEq : EqDec fifoStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| q0a,q0a => in_left 
		| p0a,p0a => in_left 
		| p1a,p1a => in_left 
		| q0b,q0b => in_left 
		| p0b,p0b => in_left 
		| p1b,p1b => in_left 
		| q0a,p0a => in_right 
		| q0a,p1a => in_right 
		| q0a,q0b => in_right 
		| q0a,p0b => in_right 
		| q0a,p1b => in_right 
		| p0a,q0a => in_right 
		| p0a,p1a => in_right 
		| p0a,q0b => in_right 
		| p0a,p0b => in_right 
		| p0a,p1b => in_right 
		| p1a,q0a => in_right 
		| p1a,p0a => in_right 
		| p1a,q0b => in_right 
		| p1a,p0b => in_right 
		| p1a,p1b => in_right 
		| q0b,q0a => in_right 
		| q0b,p0a => in_right 
		| q0b,p1a => in_right 
		| q0b,p0b => in_right 
		| q0b,p1b => in_right 
		| p0b,q0a => in_right 
		| p0b,p0a => in_right 
		| p0b,p1a => in_right 
		| p0b,q0b => in_right 
		| p0b,p1b => in_right 
		| p1b,q0a => in_right 
		| p1b,p0a => in_right 
		| p1b,p1a => in_right 
		| p1b,q0b => in_right 
		| p1b,p0b => in_right 
		end 
	}.

Program Instance fifoPortsEq : EqDec fifoPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| C,C => in_left 
		| D,D => in_left 
		| A,B => in_right 
		| A,C => in_right 
		| A,D => in_right 
		| B,A => in_right 
		| B,C => in_right 
		| B,D => in_right 
		| C,A => in_right 
		| C,B => in_right 
		| C,D => in_right 
		| D,A => in_right 
		| D,B => in_right 
		| D,C => in_right 
		end 
	}.

Close Scope Q_scope.

  Definition dataAssignmentA n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | S n => Some (0)
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    | S n => Some 1
    end.

  Definition timeStampFIFOA(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 =>  4#1
    | 2 =>  7#1
    | 3 =>  10#1
    | 4 =>  13#1
    | 5 =>  15#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 16#1 
    end.

  Definition timeStampFIFOB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1
    | 1 =>  5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 16#1
    end.

  Definition dataAssignmentC n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    | S n => Some 0
    end.

  Definition timeStampFIFOC(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  3#1
    | 1 =>  6#1
    | 2 =>  9#1
    | 3 =>  12#1
    | 4 =>  15#1
    | 5 =>  18#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 17#1 
    end.

  Lemma timeStampTestFIFOAHolds : forall n, 
    Qlt (timeStampFIFOA n) (timeStampFIFOA (S n)).
  Proof.
  intros. destruct n. unfold timeStampFIFOA. reflexivity.
  unfold timeStampFIFOA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat. Defined.

  Lemma timeStampTestFIFOBHolds : forall n, 
    Qlt (timeStampFIFOB n) (timeStampFIFOB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampFIFOB. reflexivity.
  unfold timeStampFIFOB. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qle. apply orderZofNat. Defined.

  Lemma timeStampTestFIFOCHolds : forall n, 
    Qlt (timeStampFIFOC n) (timeStampFIFOC (S n)). 
  Proof.
  intros. destruct n. unfold timeStampFIFOC. reflexivity.
  unfold timeStampFIFOC. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qle. apply orderZofNat. Defined.

  Definition portAF := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampFIFOA;
        ConstraintAutomata.tdsCond := timeStampTestFIFOAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBF := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampFIFOB;
        ConstraintAutomata.tdsCond := timeStampTestFIFOBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portCF := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampFIFOC;
        ConstraintAutomata.tdsCond := timeStampTestFIFOCHolds;
        ConstraintAutomata.index := 0 |}.

  (* realports is an input theta \in TDS^names given as input for constraint automata. *)
  (* Therefore, realports is an accepting data flow for runs that lasts 6 steps        *)
  Definition realports := [portAF;portBF;portCF].

  Definition oneBoundedFIFOrel (s:fifoStates) :
    set (set fifoPorts * ConstraintAutomata.DC fifoPorts (option nat) *
          fifoStates) :=
    match s with
    | q0a => [([A], (ConstraintAutomata.dc A (Some 0)), p0a) ;
              ([A], (ConstraintAutomata.dc A (Some 1)), p1a)]
    | p0a => [([B], (ConstraintAutomata.dc B (Some 0)), q0a)]
    | p1a => [([B], (ConstraintAutomata.dc B (Some 1)), q0a)] 
    | q0b | p0b | p1b => []
    end.

Check oneBoundedFIFOrel.

  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0a;p0a;p1a];
    ConstraintAutomata.N := [A;B];
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0a]
  |}.

  (*Second FIFO CA *)

  Definition oneBoundedFIFOrel2 (s:fifoStates) :=
    match s with
    | q0b => [([B], (ConstraintAutomata.dc B (Some 0)), p0b) ;
              ([B], (ConstraintAutomata.dc B (Some 1)), p1b)]
    | p0b => [([C], (ConstraintAutomata.dc C (Some 0)), q0b)]
    | p1b => [([C], (ConstraintAutomata.dc C (Some 1)), q0b)] 
    | q0a | p0a | p1a => []
    end.

  Definition oneBoundedFIFOCA2 := {|
    ConstraintAutomata.Q := [q0b;p0b;p1b];
    ConstraintAutomata.N := [B;C];
    ConstraintAutomata.T := oneBoundedFIFOrel2;
    ConstraintAutomata.Q0 := [q0b]
  |}.

  Definition twoBoundedFifo := ProductAutomata.buildPA oneBoundedFIFOCA oneBoundedFIFOCA2.

  (* Ex 1 *)

  (* ru6 is a lemma which asserts that the data flow denoted by the TDS denoted by realports *)
  (* is an accepting run with six steps                                                      *)
  Definition ru6 := Eval compute in ConstraintAutomata.run twoBoundedFifo realports 6.

  Lemma ru6Accept : ~ (In ([]) (ru6)).
  Proof.
  intros. unfold not. unfold ru6. simpl. intros. repeat (destruct H ; inversion H). Defined.

  (* Second example: a non-accepting run on another theta \in TDS^names as input. *)

  (* Second data flow *)

    Definition dataAssignmentA2 n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | S n => Some (0)
    end.

  Definition dataAssignmentB2 n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    | S n => Some 1
    end.

  Definition timeStampFIFOA2(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 =>  3#1
    | 2 =>  7#1
    | 3 =>  10#1
    | 4 =>  13#1
    | 5 =>  15#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 20#1 
    end.

  Definition timeStampFIFOB2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1
    | 1 =>  5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 14#1
    end.

  Definition dataAssignmentC2 n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    | S n => Some 0
    end.

  Definition timeStampFIFOC2(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  4#1
    | 1 =>  6#1
    | 2 =>  9#1
    | 3 =>  12#1
    | 4 =>  15#1
    | 5 =>  18#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 15#1 
    end.

  Lemma timeStampTestFIFOA2Holds : forall n, 
    Qlt (timeStampFIFOA2 n) (timeStampFIFOA2 (S n)).
  Proof.
  intros. destruct n. unfold timeStampFIFOA2. reflexivity.
  unfold timeStampFIFOA2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampTestFIFOB2Holds : forall n, 
    Qlt (timeStampFIFOB2 n) (timeStampFIFOB2 (S n)). 
  Proof.
  intros. destruct n. unfold timeStampFIFOB2. reflexivity.
  unfold timeStampFIFOB2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qle. apply orderZofNat. Defined.

  Lemma timeStampTestFIFOC2Holds : forall n, 
    Qlt (timeStampFIFOC2 n) (timeStampFIFOC2 (S n)). 
  Proof.
  intros. destruct n. unfold timeStampFIFOC2. reflexivity.
  unfold timeStampFIFOC2. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qle. apply orderZofNat. Defined.

  Definition portA2 := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA2;
        ConstraintAutomata.timeStamp := timeStampFIFOA2;
        ConstraintAutomata.tdsCond := timeStampTestFIFOA2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portB2 := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB2;
        ConstraintAutomata.timeStamp := timeStampFIFOB2;
        ConstraintAutomata.tdsCond := timeStampTestFIFOB2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portC2 := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC2;
        ConstraintAutomata.timeStamp := timeStampFIFOC2;
        ConstraintAutomata.tdsCond := timeStampTestFIFOC2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition ru62 := Eval compute in ConstraintAutomata.run twoBoundedFifo [portA2;portB2;portC2] 8.

  (* ru62 describes a nonaccepting run *)
  Lemma ru62Accept : ~ (In ([]) (ru62)).
  Proof.
  intros. unfold not. unfold ru62. simpl. intros. repeat (destruct H ; inversion H). Defined.

  (* In this very run, there is a moment in which the buffer becomes full with two zeroes *)
  (* This is denoted by fullFifoWith0*)
  Lemma fullFifoWith0 : In [(p0a,p0b)] ru62.
  Proof. simpl; auto. Defined.

  (* The following model is the 2 bounded FIFO declared as a whole connector, not employing Product:*) 

  Definition twoBoundedFIFOrel (s:(fifoStates * fifoStates)) :
    set (set fifoPorts * ConstraintAutomata.DC fifoPorts (option nat) *
          (fifoStates * fifoStates)) :=
    match s with
    | (q0a, q0a) => [([A], (ConstraintAutomata.dc A (Some 0)), (p0a,p0a));
                     ([A], (ConstraintAutomata.dc A (Some 1)), (p1a,p1a))]
    | (p0a,p0a) => [([B], (ConstraintAutomata.dc B (Some 0)), (q0b,q0b))]
    | (p1a,p1a) => [([B], (ConstraintAutomata.dc B (Some 1)), (q0b,q0b))] 
    | (q0b,q0b) => [([B], (ConstraintAutomata.dc B (Some 0)), (p0b,p0b));
                    ([B], (ConstraintAutomata.dc B (Some 1)), (p1b,p1b))]
    | (p0b,p0b) => [([C], (ConstraintAutomata.dc C (Some 0)), (q0b,q0b))]
    | (p1b,p1b) => [([C], (ConstraintAutomata.dc C (Some 1)), (q0b,q0b))] 
    | _ => []
    end.

  Definition twoBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [(q0a,q0a);(p0a,p0a);(p1a,p1a);(q0b,q0b);(p0b,p0b);(p1b,p1b)];
    ConstraintAutomata.N := [A;B;C];
    ConstraintAutomata.T := twoBoundedFIFOrel;
    ConstraintAutomata.Q0 := [(q0a,q0a)]
  |}.

 (* We may verify that the 2-fifo built from the product of two 1-bounded FIFO yields
    the same result as the 2-bounded-fifo-connector. *)
  Eval compute in ConstraintAutomata.areBisimilar twoBoundedFifo twoBoundedFIFOCA.




