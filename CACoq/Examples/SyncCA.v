Require Import CaMain.
Require Import ReoCA.
Require Import Coq.micromega.Lia.
Import ListNotations.

Obligation Tactic := program_simpl; congruence.

(* An unary FIFO as a simple example *)
Inductive automatonStates := q0.
Inductive automatonPorts := A | B.

Program Instance automatonStatesEq : EqDec automatonStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| q0,q0 => in_left
		end 
	}.

Program Instance automatonPortsEq : EqDec automatonPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| A,B => in_right 
		| B,A => in_right 
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

   Definition timeStampAutomatonA(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 19#1 
    end.

  Definition timeStampAutomatonB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 19#1 
    end.

(*   Lemma aux'' : forall n: nat, 
                forall q : QArith_base.Q, Z.of_nat (S n) + (q) = Z.of_nat (S n) + (q).
  Proof. *)


  Lemma timeStampAutomatonAHolds : forall n, 
    Qlt (timeStampAutomatonA n) (timeStampAutomatonA (S n)).
  Proof.
  intros. destruct n. unfold timeStampAutomatonA. reflexivity.
  unfold timeStampAutomatonA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.
  
  Lemma timeStampAutomatonBHolds : forall n, 
    Qlt (timeStampAutomatonB n) (timeStampAutomatonB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampAutomatonB. reflexivity.
  unfold timeStampAutomatonB. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampAutomatonA;
        ConstraintAutomata.tdsCond := timeStampAutomatonAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampAutomatonB;
        ConstraintAutomata.tdsCond := timeStampAutomatonBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition automatonTransition (s:automatonStates):=
    match s with
    | q0 => [([A;B], (ConstraintAutomata.eqDc nat A B), q0)]
    end.

  Definition theta := [portA;portB].

  Definition reoSync := ReoCa.ReoCABinaryChannel A B [q0] [q0] automatonTransition.

  Lemma aux': forall k, ConstraintAutomata.thetaN
       [ConstraintAutomata.calcIndex (k) portA;
       ConstraintAutomata.calcIndex (k) portB] = [A;B].
  Proof.
  induction k.
  - auto.
  - unfold ConstraintAutomata.thetaN. simpl.
    unfold ConstraintAutomata.timeStampEqThetaTime. 
    unfold ConstraintAutomata.nextTime. simpl.
    case k. auto.
    intros. case n. auto.
    intros. case n0. auto.
    intros. case n1. auto.
    intros. case n2. auto.
    intros. case n3. auto.
    intros.
    unfold ConstraintAutomata.minimum.
    simpl.  
    case_eq (Qle_bool (Z.pos
               (Pos.succ
                  (Pos.succ
                     (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat n4)))))) +
                19) # 1) (Z.pos
               (Pos.succ
                  (Pos.succ
                     (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat n4)))))) +
                19) # 1)).
    case_eq ( Qeq_bool
    (Z.pos
       (Pos.succ
          (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat n4)))))) +
        19) # 1)
        (Z.pos
         (Pos.succ
            (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat n4)))))) +
          19) # 1)).
    intros. simpl. rewrite H. reflexivity.
    intros. rewrite Qeq_eq_bool in H. inversion H.
    congruence. 
    intros. unfold Qle_bool in H. simpl in H. unfold Qeq_bool. unfold negb. 
    unfold Zeq_bool. simpl.
    Search Q. Search "_ <=? _".
    Admitted.


  Theorem acceptingRun : ConstraintAutomata.accepting' reoSync theta.
  Proof.
  unfold ConstraintAutomata.accepting'.
  intros. destruct q. induction k.
  - unfold ConstraintAutomata.stepAux. simpl. congruence.
  - unfold ConstraintAutomata.stepAux. simpl. rewrite aux'. 
    simpl. unfold ConstraintAutomata.eqDataPorts. 
    unfold ConstraintAutomata.retrievePortFromInput. simpl. 
    destruct k. auto. destruct k. auto. simpl. discriminate.
  Defined.

  Eval compute in ConstraintAutomata.run reoSync [portA;portB] 11.
