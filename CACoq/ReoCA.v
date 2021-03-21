Require Import CaMain.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module ReoCa.
  Section ReoCa.

  (* Parametric construction of constraint automata of Reo channels *) 

  Variable name state data: Set. 
  Definition ReoCABinaryChannel (a b: name) (states: set state) (initialStates : set state) 
  (transitionRelation : state -> set (set name * ConstraintAutomata.DC name data * state)):=
      {|
      ConstraintAutomata.Q := states;
      ConstraintAutomata.N := [a;b];
      ConstraintAutomata.T := transitionRelation;
      ConstraintAutomata.Q0 := initialStates
      |}.


  (* Definition to build CA for Replicator and Merger channels *)
  Definition ReoCATernaryChannel (a b c: name) (states: set state) (initialStates : set state) 
  (transitionRelation: state -> set (set name * ConstraintAutomata.DC name data * state)) :=
       {|
      ConstraintAutomata.Q := states;
      ConstraintAutomata.N := [a;b;c];
      ConstraintAutomata.T := transitionRelation;
      ConstraintAutomata.Q0 := initialStates
      |}.

  End ReoCa.
End ReoCa.

(* Implementation Examples of canonical Constraint Automata as presented by Baier et al.'s paper *)
(* Sync channel CA *)
  Inductive syncState := q0s.
  Inductive syncPorts := E | F.

  Instance syncStateEq: EqDec syncState eq :=
    {equiv_dec x y := 
      match x,y with
      | q0s,q0s => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  455
    | S n =>  (1)
    end.

 Definition timeStampTestSync (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 2#1 (* an example of a time stamp function, by injecting N to Z *)
    end.

  Lemma timeStampTestHoldsSync : forall n, 
    Qlt (timeStampTestSync n) (timeStampTestSync (S n)). 
  Proof.
  intros. destruct n. unfold timeStampTestSync. simpl. reflexivity. 
  unfold timeStampTestSync.
  apply orderZofNat. Defined.

  Instance syncPortsEq: EqDec syncPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | E,E | F,F => in_left
      | E,F | F,E => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portE := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentBoth;
        ConstraintAutomata.timeStamp := timeStampTestSync;
        ConstraintAutomata.tdsCond := timeStampTestHoldsSync;
        ConstraintAutomata.index := 0 |}.

  Definition portF:= {|
        ConstraintAutomata.id := F;
        ConstraintAutomata.dataAssignment := dataAssignmentBoth;
        ConstraintAutomata.timeStamp := timeStampTestSync;
        ConstraintAutomata.tdsCond := timeStampTestHoldsSync;
        ConstraintAutomata.index := 0 |}.

  Definition syncCaBehavior (s: syncState) : 
  set (set syncPorts * ConstraintAutomata.DC syncPorts nat * syncState) :=
    match s with
    | q0s => [([E;F] , ConstraintAutomata.eqDc nat E F, q0s)] 
    end.

  Definition syncCA :=  {|
    ConstraintAutomata.Q := [q0s];
    ConstraintAutomata.N := [E;F];
    ConstraintAutomata.T := syncCaBehavior;
    ConstraintAutomata.Q0 := [q0s]
  |}.

  Definition paramSync := ReoCa.ReoCABinaryChannel E F [q0s] [q0s] syncCaBehavior.

  Eval compute in ConstraintAutomata.run syncCA [portE;portF] 200.

  (* LossySync CA *)
  Inductive lossySyncStates := q0.

  Inductive lossySyncPorts := A | B.

  Instance lossySyncStateEq: EqDec lossySyncStates eq :=
    {equiv_dec x y := 
      match x,y with
      | q0, q0 => in_left
      end }.
   Proof.
   reflexivity.
   Defined.

   Instance LossySyncPortsEq: EqDec lossySyncPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | A,A | B,B => in_left
      | A,B | B,A => in_right
      end }.
   Proof.
   all: congruence.
   Defined.

   Definition dataAssignmentLossySyncBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  1
    | S n =>  (1)
    end.

  Definition timeStampLossyA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 69#1
    end.

  Definition timeStampLossyB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 3#1
    end.

  Lemma timeStampTestHoldsLossyA: forall n, 
    Qlt (timeStampLossyA n) (timeStampLossyA (S n)). 
  Proof.
  intros. destruct n. unfold timeStampLossyA. reflexivity. 
  unfold timeStampLossyA.
  apply orderZofNat. Defined.

  Lemma timeStampTestHoldsLossyB: forall n, 
    Qlt (timeStampLossyB n) (timeStampLossyB (S n)).
  Proof.
  intros. destruct n. unfold timeStampLossyB. reflexivity. 
  unfold timeStampLossyB.
  apply orderZofNat. Defined.

  Definition lossySyncCaBehavior (s: lossySyncStates) :
  set (set lossySyncPorts * ConstraintAutomata.DC lossySyncPorts nat * lossySyncStates):=
    match s with
    | q0 => [([A;B] , ConstraintAutomata.eqDc nat A B, q0);
             ([A], (ConstraintAutomata.tDc lossySyncPorts nat), q0)] 
    end.

  Definition lossySyncCA := {|
    ConstraintAutomata.Q := [q0];
    ConstraintAutomata.N := [A;B];
    ConstraintAutomata.T := lossySyncCaBehavior;
    ConstraintAutomata.Q0 := [q0]
  |}.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
        ConstraintAutomata.timeStamp := timeStampLossyA;
        ConstraintAutomata.tdsCond := timeStampTestHoldsLossyA;
        ConstraintAutomata.index := 0 |}.

  Definition portB:= {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
        ConstraintAutomata.timeStamp := timeStampLossyB;
        ConstraintAutomata.tdsCond := timeStampTestHoldsLossyB;
        ConstraintAutomata.index := 0 |}.

  Eval compute in ConstraintAutomata.run lossySyncCA [portA;portB] 10. (*does not accept the TDS composed by portA and portB because
                                                                         only B has data in theta.time(2), which is not comprised by the automaton's transitions *)
  Definition paramLossySync := ReoCa.ReoCABinaryChannel A B [q0] [q0] lossySyncCaBehavior.
  (* FIFO CA *)

  Inductive FIFOStates : Type := q0F | p0F | p1F.
  Inductive FIFOports : Type := AF | BF.
  Instance portsEq : EqDec FIFOports eq :=
    {equiv_dec x y := 
      match x,y with
      | AF,AF | BF,BF => in_left
      | AF,BF | BF,AF => in_right
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentA n := 
    match n with
    | 0 =>  0
    | 1 =>  0
    | 2 =>  1 
    | S n =>  (1)
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 =>  0
    | 1 =>  (0)
    | 2 =>  1
    | S n =>  1
    end.

  Definition timeStampFIFOA(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 =>  3#1
    | 2 =>  5#1
    | 3 =>  7#1
    | 4 =>  9#1
    | 5 =>  11#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1 
    end.

  Definition timeStampFIFOB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1 
    | 1 =>  4#1
    | 2 => 6#1
    | 3 => 8#1
    | 4 => 10#1
    | 5 => 12#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 10#1
    end.

  Lemma timeStampTestFIFOAHolds : forall n, Qlt (timeStampFIFOA n) (timeStampFIFOA (S n)).
  Proof.
  intros. destruct n. unfold timeStampFIFOA. reflexivity.
  unfold timeStampFIFOA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampTestFIFOBHolds : forall n, 
    Qlt (timeStampFIFOB n) (timeStampFIFOB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampFIFOB. reflexivity.
  unfold timeStampFIFOB. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Definition portAF := {|
        ConstraintAutomata.id := AF;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampFIFOA;
        ConstraintAutomata.tdsCond := timeStampTestFIFOAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBF := {|
        ConstraintAutomata.id := BF;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampFIFOB;
        ConstraintAutomata.tdsCond := timeStampTestFIFOBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition realports := [portAF;portBF].

  Definition oneBoundedFIFOrel (s:FIFOStates) :
  set (set FIFOports * ConstraintAutomata.DC FIFOports nat * FIFOStates) :=
    match s with
    | q0F => [([AF], (ConstraintAutomata.dc AF 0), p0F);
              ([AF], (ConstraintAutomata.dc AF 1), p1F)]
    | p0F => [([BF], (ConstraintAutomata.dc BF 0), q0F)]
    | p1F => [([BF], (ConstraintAutomata.dc BF 1), q0F)] 
    end.

  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0F;p0F;p1F];
    ConstraintAutomata.N := [AF;BF];
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0F]
  |}.

  Definition paramFIFO1 := ReoCa.ReoCABinaryChannel AF BF [q0F;p0F;p1F] [q0F] oneBoundedFIFOrel.

  Lemma dataInAF: forall s, In AF (ConstraintAutomata.retrievePortsFromRespTransitions (ConstraintAutomata.T oneBoundedFIFOCA s)) <->
    s = q0F.
  Proof.
  split. 
  - intros. destruct s. 
    + reflexivity.
    + simpl in H. inversion H. discriminate. inversion H0.
    + simpl in H. inversion H. discriminate. inversion H0.
  - intros. rewrite H. simpl. left. reflexivity.
  Defined.

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA realports 8.

  (* SyncDrain CA *)

  Inductive syncDrainState := q1D.
  Inductive syncDrainPorts :=  AD | BD.

  Instance syncDrainStateEq: EqDec syncDrainState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1D, q1D => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentSyncDrainBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  69
    | S n =>  (1)
    end.

 Definition timeStampSyncDrain (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Lemma timeStampSyncDrainHolds : forall n, 
    Qlt (timeStampSyncDrain n) (timeStampSyncDrain (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSyncDrain. reflexivity.
  unfold timeStampSyncDrain. case (n). reflexivity.
  intros n0. unfold timeStampSyncDrain. apply orderZofNat.  Defined.

  Instance syncDrainPortsEq: EqDec syncDrainPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AD,AD | BD,BD => in_left
      | AD,BD | BD,AD => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAD := {|
        ConstraintAutomata.id := AD;
        ConstraintAutomata.dataAssignment := dataAssignmentSyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampSyncDrain;
        ConstraintAutomata.tdsCond := timeStampSyncDrainHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBD:= {|
        ConstraintAutomata.id := BD;
        ConstraintAutomata.dataAssignment := dataAssignmentSyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampSyncDrain;
        ConstraintAutomata.tdsCond := timeStampSyncDrainHolds;
        ConstraintAutomata.index := 0 |}.

  Definition syncDrainCaBehavior (s: syncDrainState) : set
  (set syncDrainPorts * ConstraintAutomata.DC syncDrainPorts nat * syncDrainState) :=
    match s with
    | q1D => [([AD;BD] , ConstraintAutomata.tDc syncDrainPorts nat, q1D)] 
    end.

  Definition SyncDrainCA := {|
    ConstraintAutomata.Q := [q1D];
    ConstraintAutomata.N := [AD;BD];
    ConstraintAutomata.T := syncDrainCaBehavior;
    ConstraintAutomata.Q0 := [q1D]
  |}.

  Eval compute in ConstraintAutomata.run SyncDrainCA [portAD;portBD] 15.

  Definition paramSyncDrain := ReoCa.ReoCABinaryChannel AD BD [q1D] [q1D] syncDrainCaBehavior.

  Check paramSyncDrain.

  (* AsyncDrain *)
  Inductive aSyncDrainState := q1A.
  Inductive aSyncDrainPorts :=  AA | BA.

  Instance aSyncDrainStateEq: EqDec aSyncDrainState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1A, q1A => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentASyncDrainBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  0
    | S n =>  (1)
    end.

 Definition timeStampASyncDrainA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 7#1
    end.

   Definition timeStampASyncDrainB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStampASyncDrainHolds : forall n, 
    Qlt (timeStampASyncDrainA n) (timeStampASyncDrainA (S n)). 
  Proof.
  intros. destruct n. unfold timeStampASyncDrainA. reflexivity.
  unfold timeStampASyncDrainA. case (n). reflexivity.
  intros n0. unfold timeStampASyncDrainA. apply orderZofNat.  Defined.


  Lemma timeStampASyncDrainBHolds : forall n, 
    Qlt (timeStampASyncDrainB n) (timeStampASyncDrainB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampASyncDrainB. reflexivity.
  unfold timeStampASyncDrainB. case (n). reflexivity.
  intros n0. unfold timeStampASyncDrainB. apply orderZofNat. Defined.

  Instance aSyncDrainPortsEq: EqDec aSyncDrainPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AA,AA | BA,BA => in_left
      | AA,BA | BA,AA => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAA := {|
        ConstraintAutomata.id := AA;
        ConstraintAutomata.dataAssignment := dataAssignmentASyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampASyncDrainA;
        ConstraintAutomata.tdsCond := timeStampASyncDrainHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBA:= {|
        ConstraintAutomata.id := BA;
        ConstraintAutomata.dataAssignment := dataAssignmentASyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampASyncDrainB;
        ConstraintAutomata.tdsCond := timeStampASyncDrainBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition aSyncDrainCaBehavior (s: aSyncDrainState): set
  (set aSyncDrainPorts * ConstraintAutomata.DC aSyncDrainPorts nat * aSyncDrainState) :=
    match s with
    | q1A => [([AA] , ConstraintAutomata.tDc aSyncDrainPorts nat, q1A);
              ([BA] , ConstraintAutomata.tDc aSyncDrainPorts nat, q1A)] 
    end.

  Definition aSyncDrainCA := {|
    ConstraintAutomata.Q := [q1A];
    ConstraintAutomata.N := [AA;BA];
    ConstraintAutomata.T := aSyncDrainCaBehavior;
    ConstraintAutomata.Q0 := [q1A]
  |}.

  Eval compute in ConstraintAutomata.run aSyncDrainCA  [portAA;portBA] 10.

  Definition paramAsyncDrain := ReoCa.ReoCABinaryChannel AA BA [q1A] [q1A] aSyncDrainCaBehavior.

  (* Filter CA *)
  Inductive filterState := q1F.
  Inductive filterPorts :=  C | D.

  Instance filterStateEq: EqDec filterState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1F, q1F => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentfilterBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  0
    | S n =>  (1)
    end.

 Definition timeStampfilterA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 7#1
    end.

   Definition timeStampfilterB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 20#1
    end.

  Lemma timeStampfilterHolds : forall n, 
    Qlt (timeStampfilterA n) (timeStampfilterA (S n)).   
  Proof.
  intros. destruct n. unfold timeStampfilterA. reflexivity.
  unfold timeStampfilterA. case (n). reflexivity.
  intros n0. unfold timeStampfilterA. apply orderZofNat. Defined.

  Lemma timeStampfilterBHolds : forall n, 
    Qlt (timeStampfilterB n) (timeStampfilterB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampfilterB. reflexivity.
  unfold timeStampfilterB. apply orderZofNat. Defined.

  Instance filterPortsEq: EqDec filterPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | C,C | D,D => in_left
      | C,D | D,C => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portC := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentfilterBoth;
        ConstraintAutomata.timeStamp := timeStampfilterA;
        ConstraintAutomata.tdsCond := timeStampfilterHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portD:= {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentfilterBoth;
        ConstraintAutomata.timeStamp := timeStampfilterB;
        ConstraintAutomata.tdsCond := timeStampfilterBHolds;
        ConstraintAutomata.index := 0 |}.

  (*As an example, the filter condition over the data item in port A is the data should be 3 *)
  Definition filterCaBehavior (s: filterState) : set
  (set filterPorts * ConstraintAutomata.DC filterPorts nat * filterState) :=
    match s with
    | q1F => [([C;D] , ConstraintAutomata.andDc (ConstraintAutomata.dc C (3)) 
                                                 (ConstraintAutomata.eqDc nat C D), q1F);
              ([C] , ConstraintAutomata.negDc (ConstraintAutomata.dc C (3)), q1F)]
    end.

  (* The CA itself is formalized as *)
  Definition filterCA := {|
    ConstraintAutomata.Q := [q1F];
    ConstraintAutomata.N := [C;D];
    ConstraintAutomata.T := filterCaBehavior;
    ConstraintAutomata.Q0 := [q1F]
  |}.

  Eval compute in ConstraintAutomata.run filterCA [portC;portD] 3.

  Definition paramFilter := ReoCa.ReoCABinaryChannel C D [q1F] [q1F] filterCaBehavior.


  (* Transform CA *)

  Definition trasformFunction (n: nat) := n + 3.

  Inductive transformState := q1T.
  Inductive transformPorts :=  AT | BT.

  Instance transformStateEq: EqDec transformState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1T, q1T => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmenttransformAF n := 
    match n with
    | 0 =>  0
    | 1 =>  0
    | 2 =>  0
    | 3 =>  0
    | S n =>  (1)
    end.

  Definition dataAssignmenttransformBF n := 
    match n with
    | 0 =>  3
    | 1 =>  3
    | 2 =>  3
    | 3 =>  3
    | S n =>  (4)
    end.

 Definition timeStamptransformA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

   Definition timeStamptransformB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStamptransformHolds : forall n, 
    Qlt (timeStamptransformA n) (timeStamptransformA (S n)). 
  Proof.   
  intros. destruct n. unfold timeStamptransformA. reflexivity.
  unfold timeStamptransformA. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStamptransformBHolds : forall n, 
    Qlt (timeStamptransformB n) (timeStamptransformB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStamptransformB. reflexivity.
  unfold timeStamptransformB. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Instance transformPortsEq: EqDec transformPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AT,AT | BT,BT => in_left
      | AT,BT | BT,AT => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAT := {|
        ConstraintAutomata.id := AT;
        ConstraintAutomata.dataAssignment := dataAssignmenttransformAF;
        ConstraintAutomata.timeStamp := timeStamptransformA;
        ConstraintAutomata.tdsCond := timeStamptransformHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBT:= {|
        ConstraintAutomata.id := BT;
        ConstraintAutomata.dataAssignment := dataAssignmenttransformBF;
        ConstraintAutomata.timeStamp := timeStamptransformB;
        ConstraintAutomata.tdsCond := timeStamptransformBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition transformCaBehavior (s: transformState) : set
  (set transformPorts * ConstraintAutomata.DC transformPorts nat * transformState) :=
    match s with
    | q1T => [([AT;BT] , ConstraintAutomata.trDc trasformFunction AT BT, q1T)]
    end.

  Definition transformCA := {|
    ConstraintAutomata.Q := [q1T];
    ConstraintAutomata.N := [AT;BT];
    ConstraintAutomata.T := transformCaBehavior;
    ConstraintAutomata.Q0 := [q1T]
  |}.

  Eval compute in ConstraintAutomata.run transformCA [portAT;portBT] 10.

 Definition paramTransform := ReoCa.ReoCABinaryChannel AT BT [q1T] [q1T] transformCaBehavior.


  (* Merger CA*)
  Inductive mergerState := q1M.
  Inductive mergerPorts :=  AM | BM | CM.

  Instance mergerStateEq: EqDec mergerState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1M, q1M => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentmergerBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  555
    | 3 =>  69
    | S n =>  (1)
    end.

 Definition timeStampmergerA (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

   Definition timeStampmergerB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Definition timeStampmergerC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStampmergerHolds : forall n, 
    Qlt (timeStampmergerA n) (timeStampmergerA (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampmergerA. reflexivity.
  unfold timeStampmergerA. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampmergerBHolds : forall n, 
    Qlt (timeStampmergerB n) (timeStampmergerB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampmergerB. reflexivity.
  unfold timeStampmergerB. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampmergerCHolds : forall n, 
    Qlt (timeStampmergerC n) (timeStampmergerC (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampmergerC. reflexivity.
  unfold timeStampmergerC. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Instance mergerPortsEq: EqDec mergerPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AM,AM | BM,BM  | CM, CM => in_left
      | AM,BM | AM,CM | BM,AM | BM,CM | CM, AM | CM, BM => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAM := {|
        ConstraintAutomata.id := AM;
        ConstraintAutomata.dataAssignment := dataAssignmentmergerBoth;
        ConstraintAutomata.timeStamp := timeStampmergerA;
        ConstraintAutomata.tdsCond := timeStampmergerHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBM:= {|
        ConstraintAutomata.id := BM;
        ConstraintAutomata.dataAssignment := dataAssignmentmergerBoth;
        ConstraintAutomata.timeStamp := timeStampmergerB;
        ConstraintAutomata.tdsCond := timeStampmergerBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portCM:= {|
        ConstraintAutomata.id := CM;
        ConstraintAutomata.dataAssignment := dataAssignmentmergerBoth;
        ConstraintAutomata.timeStamp := timeStampmergerC;
        ConstraintAutomata.tdsCond := timeStampmergerCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition mergerCaBehavior (s: mergerState) : set
  (set mergerPorts * ConstraintAutomata.DC mergerPorts nat * mergerState) :=
    match s with
    | q1M => [([AM;CM] , ConstraintAutomata.eqDc nat AM CM, q1M);
              ([BM;CM] , ConstraintAutomata.eqDc nat BM CM, q1M)] 
    end. 

  Definition mergerCA := {|
    ConstraintAutomata.Q := [q1M];
    ConstraintAutomata.N := [AM;BM;CM];
    ConstraintAutomata.T := mergerCaBehavior;
    ConstraintAutomata.Q0 := [q1M]
  |}.

  Eval compute in ConstraintAutomata.run mergerCA [portAM;portBM;portCM] 10.

  Definition paramMerger := ReoCa.ReoCATernaryChannel AM BM CM [q1M] [q1M] mergerCaBehavior.

  (* Replicator CA *)
  Inductive replicatorState := q1R.
  Inductive replicatorPorts :=  AR | BR | CR.

  Instance replicatorStateEq: EqDec replicatorState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1R, q1R => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentreplicatorBoth n := 
    match n with
    | 0 =>  0
    | 1 =>  1
    | 3 =>  2
    | S n =>  (1 + S n)
    end.

 Definition timeStampreplicatorA (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

   Definition timeStampreplicatorB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Definition timeStampreplicatorC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStampreplicatorHolds : forall n, 
    Qlt (timeStampreplicatorA n) (timeStampreplicatorA (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampreplicatorA. reflexivity.
  unfold timeStampreplicatorA. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampreplicatorBHolds : forall n, 
    Qlt (timeStampreplicatorB n) (timeStampreplicatorB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampreplicatorB. reflexivity.
  unfold timeStampreplicatorB. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampreplicatorCHolds : forall n, 
    Qlt (timeStampreplicatorC n) (timeStampreplicatorC (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampreplicatorC. reflexivity.
  unfold timeStampreplicatorC. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Instance replicatorPortsEq: EqDec replicatorPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AR,AR | BR,BR  | CR, CR => in_left
      | AR,BR | AR,CR | BR,AR | BR,CR | CR, AR | CR, BR => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAR := {|
        ConstraintAutomata.id := AR;
        ConstraintAutomata.dataAssignment := dataAssignmentreplicatorBoth;
        ConstraintAutomata.timeStamp := timeStampreplicatorA;
        ConstraintAutomata.tdsCond := timeStampreplicatorHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBR:= {|
        ConstraintAutomata.id := BR;
        ConstraintAutomata.dataAssignment := dataAssignmentreplicatorBoth;
        ConstraintAutomata.timeStamp := timeStampreplicatorB;
        ConstraintAutomata.tdsCond := timeStampreplicatorBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portCR:= {|
        ConstraintAutomata.id := CR;
        ConstraintAutomata.dataAssignment := dataAssignmentreplicatorBoth;
        ConstraintAutomata.timeStamp := timeStampreplicatorC;
        ConstraintAutomata.tdsCond := timeStampreplicatorCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition replicatorCaBehavior (s: replicatorState) : set
  (set replicatorPorts * ConstraintAutomata.DC replicatorPorts nat * replicatorState) :=
    match s with
    | q1R => [([AR;BR;CR] , ConstraintAutomata.andDc (ConstraintAutomata.eqDc nat AR BR) 
                                                     (ConstraintAutomata.eqDc nat AR CR), q1R)] 
    end.

  Definition replicatorCA := {|
    ConstraintAutomata.Q := [q1R];
    ConstraintAutomata.N := [AR;BR;CR];
    ConstraintAutomata.T := replicatorCaBehavior;
    ConstraintAutomata.Q0 := [q1R]
  |}.

  Eval compute in ConstraintAutomata.run replicatorCA [portAR;portBR;portCR] 11.

  Definition paramReplicator := ReoCa.ReoCATernaryChannel AR BR CR [q1R] [q1R] replicatorCaBehavior.
