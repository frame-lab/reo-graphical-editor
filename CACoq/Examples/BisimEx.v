Require Import CaMain.
Require Import ReoCA.
Import ListNotations.

Obligation Tactic := program_simpl ; congruence.

(*Two bisimilar automata from Baier et al.'s 2006 paper introducing Constraint Automata *)

Inductive automatonStates := q1 | p1 | r1 | q2 | p2 | r2 | p2' | q3 | u3.
Inductive automatonPorts := A | B | C.

Program Instance automatonStatesEq : EqDec automatonStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| q1,q1 => in_left 
		| p1,p1 => in_left
 		| r1,r1 => in_left 
		| q2,q2 => in_left
    | p2,p2 => in_left 
		| r2,r2 => in_left
    | p2',p2' => in_left
    | q3, q3 => in_left
    | u3, u3 => in_left
    | q1,p1 | q1, r1 | q1,q2 | q1,p2 | q1, r2 | q1,p2' | q1,q3 | q1,u3 => in_right
    | p1,q1 | p1, r1 | p1,q2 | p1,p2 | p1, r2 | p1,p2' | p1,q3 | p1,u3 => in_right
    | r1,q1 | r1,p1  | r1,q2 | r1,p2 | r1, r2 | r1,p2' | r1,q3 | r1,u3 => in_right
    | q2,q1 | q2, p1 | q2,r1 | q2,p2 | q2, r2 | q2,p2' | q2,q3 | q2,u3 => in_right
    | p2,q1 | p2, p1 | p2,r1 | p2,q2 | p2, r2 | p2,p2' | p2,q3 | p2,u3 => in_right
    | r2,q1 | r2, p1 | r2,q2 | r2,p2 | r2, r1 | r2,p2' | r2,q3 | r2,u3 => in_right
    | p2',q1 | p2', p1 | p2',q2 | p2',p2 | p2', r1 | p2',r2 | p2',q3 | p2',u3 => in_right
    | q3,q1 | q3,p1 | q3, r1 | q3,q2 | q3,p2 | q3, r2 | q3,p2' | q3,u3 => in_right
    | u3,q1 | u3,p1 | u3, r1 | u3,q2 | u3,p2 | u3, r2 | u3,p2' | u3,q3 => in_right
		end 
	}.

Program Instance automatonPortsEq : EqDec automatonPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
    | C,C => in_left
		| A,B => in_right 
		| B,A => in_right 
    | A,C => in_right
    | B,C => in_right
    | C,A => in_right
    | C,B => in_right
		end 
	}.

Close Scope Q_scope.

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
    | S n =>  Z.of_nat (S n) + 16#1 
    end.

  Definition timeStampAutomatonB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 9#1
    | 3 => 12#1
    | 4 => 15#1
    | 5 => 18#1
    | S n =>  Z.of_nat(S n) + 170#1
    end.


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

  Definition automaton1Transition (s:automatonStates):=
    match s with
    | q1 => [([A], (ConstraintAutomata.tDc automatonPorts nat), p1);
             ([A], (ConstraintAutomata.tDc automatonPorts nat), r1)]
    | p1 => [([B], (ConstraintAutomata.tDc automatonPorts nat), q1)]
    | r1 => [([C], (ConstraintAutomata.tDc automatonPorts nat), q1)]
    | _ => []
    end.

  (*Automaton 1*)
  Definition firstAutomaton := ConstraintAutomata.CA ([q1;p1;r1]) ([A;B;C]) (automaton1Transition) 
  ([q1]). 

  (* We parametrize the data item as in the example *)
  Definition automaton2Transition (n:nat) (s:automatonStates) :
  set (set automatonPorts * ConstraintAutomata.DC automatonPorts nat * automatonStates) :=
    match s with
    | q2  => [([A], (ConstraintAutomata.dc A n), p2);
              ([A], ((ConstraintAutomata.negDc (ConstraintAutomata.dc A n))), p2');
              ([A], (ConstraintAutomata.tDc automatonPorts nat), r2)]
    | r2  => [([C], (ConstraintAutomata.tDc automatonPorts nat), q2)]
    | p2  => [([B], (ConstraintAutomata.tDc automatonPorts nat), q2)]
    | p2' => [([B], (ConstraintAutomata.tDc automatonPorts nat), q2)]
    | _ => []
    end.

  Definition secondAutomaton := ConstraintAutomata.CA ([q2;p2;p2';r2]) ([A;B;C]) (automaton2Transition 0) 
  ([q2]). 

  (* firstAutomaton and secondAutomaton are bisimilar *)
  Eval compute in ConstraintAutomata.bisimulation firstAutomaton secondAutomaton.

  (* Therefore, they are language equivalent *)
  Eval compute in ConstraintAutomata.areBisimilar firstAutomaton secondAutomaton.

  (* We also implement the non bisimilar automaton provided in the aforementioned example *)

  Definition automaton3Transition (n:nat) (s:automatonStates) :
  set (set automatonPorts * ConstraintAutomata.DC automatonPorts nat * automatonStates) :=
    match s with
    | q3  => [([A], (ConstraintAutomata.tDc automatonPorts nat), u3)]
    | u3  => [([B], (ConstraintAutomata.tDc automatonPorts nat), q3);
              ([C], (ConstraintAutomata.tDc automatonPorts nat), q3)]
    | _ => []
    end.

  Definition thirdAutomaton := ConstraintAutomata.CA ([q3;u3]) ([A;B;C]) (automaton3Transition 0) 
  ([q3]). 

  (* And we may verify that they are not bisimilar *)
  Eval compute in ConstraintAutomata.bisimulation firstAutomaton thirdAutomaton.

  Eval compute in ConstraintAutomata.areBisimilar firstAutomaton thirdAutomaton.
    


  






