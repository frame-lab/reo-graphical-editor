Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

(* The following lemma was formalized thanks to anonymous reviewers' contribution *)
Lemma orderZofNat : forall n, forall a, (Z.of_nat (S n) + a) # 1 < Z.of_nat (S (S n)) + a # 1.
Proof.
intros.
assert (forall z, z # 1 < (z + 1) # 1).
+ intros. assert (inject_Z z < inject_Z (z + 1)). rewrite <- Zlt_Qlt. 
  lia. unfold inject_Z in H. exact H.
+ assert (forall b, forall a, (b + a) # 1 < ((b + 1) + a) # 1).
  intros. rewrite <- Z.add_assoc. rewrite (Z.add_comm 1).
  rewrite Z.add_assoc. apply H.
  assert (forall n, Z.of_nat (S n) = ((Z.of_nat n) + 1)%Z).
  intro. simpl. lia. rewrite (H1 ((S n))). apply H0. Defined.

Close Scope Q_scope.

Obligation Tactic := program_simpl; congruence.


Set Implicit Arguments.
Set Maximal Implicit Insertion.


Import ListNotations.
(* ---------------------------------------- Utils ---------------------------------------------------------------- *)

Program Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.

Program Instance pair_eqdec A B `(EqDec A eq) `(EqDec B eq) : EqDec (A * B) eq :=
{
  equiv_dec x y:=
    match x, y with
      | (a, b), (c,d) => if a == c then
                            if b == d then in_left else in_right
                         else in_right
    end
}.

Program Fixpoint s1_in_s2 {A} `{EqDec A eq} (s1 s2 : set A) :=
  match s1 with
    | [] => true
    | a::t => set_mem equiv_dec a s2 && s1_in_s2 t s2
  end.

Fixpoint set_eq {A} `{EqDec A eq} (s1 s2 : set A) :=
  if (length s1 == length s2) then
      if (s1_in_s2 s1 s2) then
          if (s1_in_s2 s2 s1) then true else false
      else false
  else false.

Lemma set_eq_sound {A} `{EqDec A eq} : forall s1 : set A, forall s2 : set A,
   set_eq s1 s2 = true <-> ((length s1 = length s2))
   /\ s1_in_s2 s1 s2 = true /\ s1_in_s2 s2 s1 = true.
  Proof.
  split.
  - intros. destruct s1. destruct s2.
  + split. reflexivity. split. assumption. assumption.
  + inversion H0.
  + unfold set_eq in H0. destruct equiv_dec in H0.
    case_eq (s1_in_s2 (a :: s1) s2). case_eq (s1_in_s2 s2 (a :: s1)). intros. rewrite H1 in H0. rewrite H2 in H0. inversion e.
    split. reflexivity. auto. intros. rewrite H2 in H0. rewrite H1 in H0. inversion H0. intros. 
    rewrite H1 in H0. inversion H0. congruence. 
  - intros. destruct s1. destruct s2.
  + reflexivity.
  + destruct H0. inversion H0.
  + simpl. destruct H0. destruct H1. simpl in H0. rewrite H0.
    simpl s1_in_s2 in H1. rewrite H1. rewrite H2. repeat simpl. destruct equiv_dec. reflexivity. congruence.
  Defined.


(* --------------------------------------------------------------------------------------------------------------- *)

Module ConstraintAutomata.
  Section ConstraintAutomata.

    Variable state name data: Set. 

    Context `{EqDec name eq} `{EqDec state eq} `{EqDec (data) eq}.

    Notation " a <? b " := (negb (Qle_bool b a)).
    Notation "a =? b" := (Qeq_bool a b).

    Record tds := mktds {
      id : name;
      dataAssignment : nat -> data; 
      timeStamp : nat -> QArith_base.Q;
      tdsCond : forall n:nat, Qlt (timeStamp n) (timeStamp (S n));
      index : nat

    }.

    Inductive DC name data:= 
    | tDc : DC name data
    | dc : name -> data -> DC name data
    | eqDc : name -> name -> DC name data
    | andDc : DC name data -> DC name data -> DC name data
    | orDc  : DC name data -> DC name data -> DC name data
    | trDc  : (data -> data) -> name -> name -> DC name data
    | negDc : DC name data -> DC name data.

    Notation "a @ b" := (andDc a b)(no associativity, at level 69).
    Notation "a $ b" := (orDc a b) (no associativity, at level 69).

    Definition evalDC (po: option tds) (d : data) : bool :=
       match po with
       | Some p => if (dataAssignment p(index p) == d) then true else false
       | None => false
       end.

    Lemma evalDCSound : forall po, forall d, evalDC po d = true <-> exists x, po = Some x /\ 
      dataAssignment x(index x) = d.
    Proof.
    split.
    - intros. destruct po. simpl in H2. destruct equiv_dec in H2.
    + exists t. inversion e. auto.
    + inversion H2.
    + inversion H2.
    - intros. destruct H2. destruct H2. rewrite H2. unfold evalDC. rewrite H3. destruct equiv_dec.
      reflexivity. congruence.
    Defined.


    (* The following definition searches for a tds in a set of tds, returning it if it exists and None otherwise *)
    Fixpoint retrievePortFromInput (tds:set tds) (n: name) :=
      match tds with
      | [] => None
      | a::t => if (n == id a) then Some a else retrievePortFromInput t n
      end.
    Lemma retrievePortFromInputSound : forall tds:set tds, forall n: name,forall a, retrievePortFromInput tds n = Some a
    -> In a tds /\ n = id a.
    Proof.
    - intros. 
    + induction tds0. inversion H2.
    simpl in H2. destruct equiv_dec in H2. inversion e. split. inversion H2. simpl. auto. inversion H2. reflexivity.
    apply IHtds0 in H2. split. simpl. destruct H2. right. exact H2. destruct H2. exact H3. Defined.

    Definition eqDataPorts (n1: name) (n2: name) (theta: set tds) :=
      match (retrievePortFromInput theta n1) with
      | Some a => match (retrievePortFromInput theta n2) with
                  | Some b => if (dataAssignment a(index a)) == (dataAssignment b(index b)) then true else false
                  | None => false
                  end
      | None => false
      end.

    Lemma eqDataPortsSound : forall n1, forall n2, forall tds , eqDataPorts n1 n2 tds = true <-> 
      exists a, retrievePortFromInput tds n1 = Some a /\ exists b, retrievePortFromInput tds n2 = Some b 
      /\ (dataAssignment a(index a)) = (dataAssignment b(index b)).
    Proof.
    split.
    - intros. unfold eqDataPorts in H2. case_eq (retrievePortFromInput tds0 n1). 
      case_eq (retrievePortFromInput tds0 n2).
    + intros. rewrite H3 in H2.  rewrite H4 in H2. destruct equiv_dec in H2. inversion e.
      exists t0. split. reflexivity. exists t. split. reflexivity. assumption.
      inversion H2.
    + intros. rewrite H4 in H2. rewrite H3 in H2. inversion H2.
    + intros. rewrite H3 in H2. inversion H2.
    - intros. destruct H2. destruct H2. destruct H3. destruct H3. 
      unfold eqDataPorts. rewrite H2. rewrite H3. rewrite H4. destruct equiv_dec. reflexivity. congruence.
  Defined.

    Definition transformDC (transform: data -> data) (n1: name) (n2: name) (tds:set tds) :=
      match (retrievePortFromInput tds n1) with
      | Some a => match (retrievePortFromInput tds n2) with
                  | Some b => if transform((dataAssignment a(index a))) == (dataAssignment b(index b)) then true else false
                  | None => false
                  end
      | None => false
      end.

    Lemma transformDCsound : forall transform, forall n1, forall n2, forall tds, transformDC transform n1 n2 tds = true <->
      exists a, retrievePortFromInput tds n1 = Some a /\ exists b, retrievePortFromInput tds n2 = Some b 
      /\ transform((dataAssignment a(index a))) = (dataAssignment b(index b)).
    Proof.
    split.
    - intros. unfold transformDC in H2. case_eq (retrievePortFromInput tds0 n1). 
      case_eq (retrievePortFromInput tds0 n2).
    + intros. rewrite H3 in H2.  rewrite H4 in H2. destruct equiv_dec in H2. inversion e.
      exists t0. split. reflexivity. exists t. split. reflexivity. assumption.
      inversion H2.
    + intros. rewrite H4 in H2. rewrite H3 in H2. inversion H2.
    + intros. rewrite H3 in H2. inversion H2.
    - intros. destruct H2. destruct H2. destruct H3. destruct H3. 
      unfold transformDC. rewrite H2. rewrite H3. rewrite H4. destruct equiv_dec. reflexivity. congruence.
    Defined.

    Fixpoint evalCompositeDc (tds:set tds) (dc: DC name data) : bool :=
      match dc with
      | tDc _ _ => true
      | dc a b => evalDC (retrievePortFromInput tds a) (b)
      | eqDc _ a b => eqDataPorts a b tds
      | andDc a b => evalCompositeDc tds a && evalCompositeDc tds b
      | orDc a b => evalCompositeDc tds a || evalCompositeDc tds b
      | trDc transform a b  => transformDC transform a b tds
      | negDc a => negb (evalCompositeDc tds a)
      end.  

      Lemma evalCompositeDcSound : forall tds, forall dca: DC name data, evalCompositeDc tds dca = true <-> 
      dca = tDc _ _ \/ 
      (exists a, exists b, dca = dc a b /\ (evalDC (retrievePortFromInput tds a) b) = true ) \/
      (exists a, exists b, dca = eqDc _ a b /\ eqDataPorts a b tds = true) \/
      (exists a, exists b, dca = andDc a b /\ evalCompositeDc tds a && evalCompositeDc tds b = true) \/
      (exists a,exists b, dca = orDc a b /\ evalCompositeDc tds a || evalCompositeDc tds b = true) \/
      (exists a, exists b, exists tr, dca = trDc tr a b /\ transformDC tr a b tds = true) \/
      (exists a, dca = negDc a /\ negb (evalCompositeDc tds a) = true).
      Proof.  
      split.
      - intros. destruct dca.
      + left. reflexivity.
      + simpl in H2. right. left. exists n. exists d. auto.
      + simpl in H2. right. right. left. exists n. exists n0. auto.
      + simpl in H2. right. right. right. left.  exists dca1. exists dca2. auto.
      + simpl in H2. right. right. right. right. left. exists dca1. exists dca2. auto.
      + simpl in H2. right. right. right. right. right. left. exists n. exists n0. exists d. auto.
      + simpl in H2. repeat right. exists dca.  auto.
      - intros. destruct H2.
      + rewrite H2. reflexivity.
      + destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. rewrite H2. simpl. exact H3.
      Defined. 

    Record constraintAutomata : Type := CA {
      Q : set state;
      N : set name;
      T : state -> set (set (name) * DC name data * state);
      Q0 : set state;
    }.

    Fixpoint returnSmallerNumber (m:QArith_base.Q) (l:set QArith_base.Q) :=
      match l with
      | [] => m
      | a::t => if ((a <? m)) then 
                   returnSmallerNumber a t else returnSmallerNumber m t
      end.
    Open Scope Q_scope.

    Theorem returnSmallerNumber_sound : forall m, forall l, returnSmallerNumber m l <> m 
    -> l <> [] /\ exists a, In a l /\ a <? m = true.
    Proof.
    - intros.
    induction l.
    unfold returnSmallerNumber in H2. congruence.
    simpl in H2. split.
    discriminate.
    case_eq (a <? m). intros. rewrite H3 in H2. exists a. simpl. auto.
    intros. rewrite H3 in H2. apply IHl in H2. destruct H2. repeat (destruct H4).
    exists x. split. simpl. right. exact H4. exact H5.
    Defined.

    Notation "x |> f" := (f x) (at level 69, only parsing).

    Close Scope Q_scope.

    Definition getThetaTimeCandidate (p:tds) :=
      [timeStamp p(index(p))].

    Fixpoint getAllThetaTimes (theta: set tds) :=
      match theta with
      | [] => []
      | a::t => getThetaTimeCandidate a++getAllThetaTimes t
      end.
    Lemma getAllThetaTimesSound : forall s: set tds, getAllThetaTimes s <> [] <-> exists a, In a s.
    Proof.
    split.
    - intros. destruct s. simpl in H2. congruence. exists t. simpl. auto.
    - intros. destruct s. inversion H2. inversion H3. simpl. discriminate.
    Defined.

    Definition minimum (l: set QArith_base.Q) :=
       returnSmallerNumber (hd (Qmake 0 1) l) (tl l).

    Definition nextTime (theta:set tds) :=
      minimum(getAllThetaTimes theta).

    Definition timeStampEqThetaTime (theta:set tds) (a:tds) :=
      (timeStamp a(index a) =? nextTime (theta)).

    Lemma timeStampEqThetaTimeSound : forall s, forall a, timeStampEqThetaTime s a = true <-> 
      ((timeStamp a(index a) =? nextTime (s)) = true).
    Proof.
    split.
    - intros. unfold timeStampEqThetaTime in H2. exact H2.
    - intros. unfold timeStampEqThetaTime. rewrite H2. reflexivity.
    Defined.

    Fixpoint nextNames (theta: set tds) (theta2:set tds) : set name := 
      match theta2 with
      | a::t => if (timeStampEqThetaTime theta a ) then
                    id a :: nextNames theta t
                else nextNames theta t
      | []   => []
      end.

    Lemma nextNamesSound : forall theta, forall theta2, nextNames theta theta2 <> [] <-> 
    (exists a, In a theta2 /\ timeStampEqThetaTime theta a = true).
    Proof.
    split.
    - intros. induction theta2.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (timeStampEqThetaTime theta a).
    { intros. exists a. split. simpl;auto. exact H3. }
    { intros. rewrite H3 in H2. apply IHtheta2 in H2. destruct H2. destruct H2.
      exists x. split. simpl;auto. exact H4. }
    -  intros. induction theta2. 
    + destruct H2.  destruct H2. inversion H2.
    + simpl. case_eq (timeStampEqThetaTime theta a). intros. discriminate.
      intros. apply IHtheta2. destruct H2. destruct H2. simpl in H2. destruct H2.  rewrite <- H2 in H4. 
      congruence. exists x. split. exact H2. exact H4.
    Defined. 
    
    Definition thetaN (theta: set tds) :=
      nextNames (theta) (theta).

    Fixpoint nextData (theta: set tds) (theta2:set tds) : set((name * data)) := 
      match theta2 with
      | a::t => if (timeStampEqThetaTime theta a) then
                   ((id a) , (dataAssignment a(index(a)))) :: nextData theta t
                else nextData theta t
      | []   => []
      end.

    Lemma nextDataSound : forall theta, forall theta2, nextData theta theta2 <> [] <-> 
    (exists a, In a theta2 /\ timeStampEqThetaTime theta a = true).
    Proof.
    split.
    - intros. induction theta2.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (timeStampEqThetaTime theta a).
    { intros. exists a. split. simpl;auto. exact H3. }
    { intros. rewrite H3 in H2. apply IHtheta2 in H2. destruct H2. destruct H2.
      exists x. split. simpl;auto. exact H4. }
    -  intros. induction theta2. 
    + destruct H2.  destruct H2. inversion H2.
    + simpl. case_eq (timeStampEqThetaTime theta a). intros. discriminate.
      intros. apply IHtheta2. destruct H2. destruct H2. simpl in H2. destruct H2.  rewrite <- H2 in H4. 
      congruence. exists x. split. exact H2. exact H4.
    Defined. 

    Close Scope Q_scope.

    Definition derivative (p: tds) := mktds (id p) (dataAssignment p) (timeStamp p)
        (tdsCond p) (S (index p)).

    Lemma derivative_sound : forall p, derivative p = mktds (id p) (dataAssignment p) (timeStamp p)
        (tdsCond p) ( S(index p)).
    Proof.
    reflexivity.
    Defined.

    Fixpoint derivativePortInvolved (s:set name) (a: tds)  :=
      match s with
      | [] => [a] 
      | x::t => if x == id a then [derivative(a)]
                else derivativePortInvolved t a
      end.

    Definition allDerivativesFromPortsInvolved (names: set name) (theta:set tds) : set tds :=
      flat_map (derivativePortInvolved names) theta.

    Definition portsDerivative (names: set name) (theta: set tds) := 
      allDerivativesFromPortsInvolved names theta. 

    Fixpoint portsOutsideTransition (p: tds) (portNames : set name) :=
      match portNames with
       | [] => true
       | a::t => if (id p <> a) then portsOutsideTransition p t else false
      end.

    Lemma portsOutsideTransitionSound : forall p, forall portNames, portsOutsideTransition p portNames = false <->
      (exists b, In b portNames /\ (id p = b)).
    Proof.
    split.
    - intros. induction portNames.
    + simpl in H2. inversion H2.
    + simpl in H2. destruct nequiv_dec in H2. apply IHportNames in H2.
      repeat destruct H2. exists x. split.
      simpl;auto.
      exact H3.
      inversion e. exists a.
      split. simpl;auto.
      exact H3.
    - intros. induction portNames.
    + repeat destruct H2.
    + simpl. destruct nequiv_dec. apply IHportNames. repeat destruct H2. congruence. exists x. split; assumption.
      reflexivity. 
    Defined.
  
    Fixpoint step' (theta : set tds) (portNames: set name)
     (transitions: set(set name * DC name data * state)) : set state :=
     match transitions with
     | [] => []
     | a::t => if (set_eq (portNames)((fst(fst(a))))) 
                   && (evalCompositeDc (theta) (snd(fst(a)))) then snd(a)::step' theta portNames t
                   else step' theta portNames t
     end.

    Lemma step'_sound : forall theta, forall portNames, forall transitions, step' theta portNames transitions <> [] -> exists a,
    In a transitions /\ (set_eq (portNames)((fst(fst(a)))))
                   && (evalCompositeDc (theta) (snd(fst(a)))) = true.
    Proof. 
    - intros. induction transitions. simpl in H2. congruence. simpl in H2. 
    case_eq (set_eq (portNames)((fst(fst(a))))). 
    case_eq (evalCompositeDc theta (snd (fst a))). intros.
    + exists a. split. simpl;auto. rewrite H3. rewrite H4. reflexivity.
    + intros. rewrite H3 in H2. rewrite H4 in H2. apply IHtransitions in H2.
      destruct H2. destruct H2. exists x. split. simpl;auto. exact H5.
    + intros. rewrite H3 in H2. apply IHtransitions in H2.
      destruct H2. destruct H2. exists x. split. simpl;auto. exact H4.
    Defined.

    Definition stepAux (ca:constraintAutomata) (theta:set tds) (portNames:set name) (s: state) 
    : set state :=
      step' theta portNames (T ca s).

    (* We apply the step to every state in the given configuration:                     *)
    Definition stepa (ca:constraintAutomata) (s: set state) (theta:set tds) (portNames: set name) 
    : set name * set state :=
     (portNames, flat_map (stepAux ca theta portNames) s).

    Definition step (ca:constraintAutomata) (s: set state) (theta:set tds) : set name * set state :=
      stepa ca s theta (thetaN theta).

    Definition run' (ca:constraintAutomata)  : 
      set tds -> nat -> set state -> set (set state) -> set (set state) :=
      fix rec theta k initialStates trace := 
        match k with 
          | 0 => trace
          | S m => trace ++ [snd (step ca initialStates theta)]
                    |> rec
                      (flat_map(derivativePortInvolved(fst((step ca initialStates theta)))) theta) m (snd (step ca initialStates theta))
        end.

    Definition run (ca:constraintAutomata) (theta: set tds) (k : nat) :=
      run' ca theta k (Q0 ca) [Q0 ca].

  (* We define a function that returns the input theta post processed by the automaton. Intuitively, *)
  (* it is similar to run but instead of accumulating states, it returns theta's k-th derivative     *)

    Definition tdsDerivate (ca:constraintAutomata)  : 
      set tds -> nat -> set state -> set tds :=
      fix rec theta k initialStates := 
        match k with 
          | 0 => theta
          | S m => rec (flat_map (derivativePortInvolved(fst((step ca initialStates theta)))) theta) m (snd(step ca initialStates theta)) 
        end.

  (* And a version of a run which returns only the last state reached *)
    Definition lastReachedStates (ca:constraintAutomata) (theta: set tds) (k : nat) : set state :=
      last (run ca theta k) (ConstraintAutomata.Q0 ca).

  (* We define some functions to retrieve data from transitions, in order to prove *)
  (* properties about behavior of automata                                         *)

    Fixpoint retrievePortsFromRespTransitions (s : set (set (name) * DC name data * state)) :=
    match s with
    | [] => []
    | a::t => set_union equiv_dec (fst (fst a) ) (retrievePortsFromRespTransitions t)
    end.

    Definition portsOfTransition (ca: constraintAutomata) (s : state) :=
      retrievePortsFromRespTransitions (ConstraintAutomata.T ca s).

  (* We define acceptance for infinite runs as Baier et al. propose *)

  Definition rejecting (ca: constraintAutomata) (theta: set tds) : Prop :=
    exists k, (lastReachedStates ca theta k) = [].

  Definition calcIndex (k: nat) (p : tds) := mktds (id p) (dataAssignment p) (timeStamp p)
        (tdsCond p) (k).

  Definition accepting' (ca: constraintAutomata) (theta: set tds) :=
    forall q,forall k, stepAux ca (map(calcIndex k) (theta)) (thetaN (map(calcIndex k) (theta))) q <> [].

  (* Bisimulation as boolean verification *)


  (* We filter the transition to be compared with a transition that contains the same name set *)
  Fixpoint getTransition (portNames: set name) (t2 : set (set(name) * DC name data * state)) :=
    match t2 with
    | [] => [] 
    | a::t => if (set_eq portNames (fst(fst(a)))) then a::getTransition portNames t else getTransition portNames t
    end. 


  (* We need to evalate whether the next reached states are also equivalent. Then, we need to store *)
  (* pairs of states to be evaluated *)
  Fixpoint getReachedStatesFromPair (t1 : (set(name) * DC name data * state)) (setT2 : set (set(name) * DC name data * state)) :=
    match setT2 with
    | [] => []
    | a::nextT2 =>  set_add equiv_dec (snd(t1),snd(a)) (getReachedStatesFromPair t1 nextT2)
    end.

  (* Check whether exists a transition with port names equal to the port name of a single transition of A1 *)
  Fixpoint iterateTransitionsQ1A1 (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state) (q2: state) 
    (setT1 : set (set(name) * DC name data * state)) (setT2: set (set(name) * DC name data * state)) 
    (acc: set (state * state)) :=
    match setT1 with
    | [] => (q1,q2)::acc 
    | a::t => if set_eq ((getReachedStatesFromPair (a) (getTransition (fst(fst(a))) (setT2)))) ([]) then [] else 
              ((getReachedStatesFromPair (a) (getTransition (fst(fst(a))) (setT2))))++ iterateTransitionsQ1A1 ca1 ca2 q1 q2 t setT2 acc
    end.
 
  (* Expanding the reached states *)
  Definition iterateOverNextStates (ca1: constraintAutomata) (ca2: constraintAutomata) (acc : set (state * state))
  (states : set (state * state)) :=
    match states with
    | [] => []
    | a::t => iterateTransitionsQ1A1 ca1 ca2 (fst(a)) (snd(a)) (ConstraintAutomata.T ca1 (fst(a))) 
              (ConstraintAutomata.T ca2 (snd(a))) acc 
    end.

  Fixpoint bisimilarStatesCa1ToCa2 (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state) (q2: state) 
    (setT1 : set (set(name) * DC name data * state)) (setT2: set (set(name) * DC name data * state)) 
    (acc: set (state * state)) :=
    match setT1 with
    | [] => (q1,q2)::acc
    | a::t => if set_eq ((getReachedStatesFromPair (a) (getTransition (fst(fst(a))) (setT2)))) ([]) then [] else
              bisimilarStatesCa1ToCa2 ca1 ca2 q1 q2 t setT2 acc
    end.

  (* Retrieving only the bisimilar states after each round. *)
  Fixpoint retrieveCleanStates (ca1: constraintAutomata) (ca2: constraintAutomata)
  (acc: set (state * state)) (states: set (state * state)) :=
    match states with
    | [] => []
    | a::t => set_union equiv_dec (bisimilarStatesCa1ToCa2 ca1 ca2 (fst(a)) (snd(a)) (ConstraintAutomata.T ca1 (fst(a))) (ConstraintAutomata.T ca2 (snd(a))) acc)
              (retrieveCleanStates ca1 ca2 acc t)
    end. 
  
  (* Auxiliary definition that iterates over the set of (possible) bisimilar states, recursively verifying whether they indeed are bisimilar *)
  Definition evaluateObtainedStates (ca1: constraintAutomata) (ca2: constraintAutomata) : nat -> set (state * state) -> 
  set (state * state) -> set (state * state) :=
    fix rec steps acc nextPairStates :=
    match steps with
    | 0 =>  acc
    | S n =>
            set_union equiv_dec (rec n acc (iterateOverNextStates ca1 ca2 acc nextPairStates)) 
            (retrieveCleanStates ca1 ca2 acc ((iterateOverNextStates ca1 ca2 acc nextPairStates)))
    end.

  Fixpoint iterateOverA2States (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state) (q2: set (state)) 
    (acc: set (state * state)) :=
    match q2 with
    | [] => acc
    | a::t => evaluateObtainedStates ca1 ca2 (length(ConstraintAutomata.Q(ca1))) acc [(q1,a)]  
              ++ iterateOverA2States ca1 ca2 q1 t acc
    end.  

  Fixpoint iterateOverA1States (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: set (state)) (q2: set (state)) 
  (acc: set (state * state)) : set (state * state) :=
    match q1 with
    | [] => acc
    | a::t => iterateOverA2States ca1 ca2 a q2 acc ++ iterateOverA1States ca1 ca2 t q2 acc
    end.

  Fixpoint containsSymmetric (setPairs : set (state * state)) (setPairsFull: set (state * state)):=
    match setPairs with
    | [] => []
    | a::t => match a with
              | (q1,q2) => if existsb (fun x : (state * state) => match x with
                                       |(a,b) => (equiv_decb a q2) && (equiv_decb b q1)  end) (setPairsFull) then (q1,q2)::containsSymmetric t setPairsFull
                           else containsSymmetric t setPairsFull
              end
    end.

  Definition bisimulationAux (ca1: constraintAutomata) (ca2: constraintAutomata) :=
    (iterateOverA1States ca1 ca2 (ConstraintAutomata.Q0 ca1) (ConstraintAutomata.Q0 ca2) []) ++ 
    (iterateOverA1States ca2 ca1 (ConstraintAutomata.Q0 ca2) (ConstraintAutomata.Q0 ca1) []).

  (* bisimulation is commutative *)
  Lemma bisimulationAuxCommutative : forall ca1, forall ca2, forall a, 
   (In a (bisimulationAux ca1 ca2)) <-> (In a (bisimulationAux ca2 ca1)).
  Proof.
  intros.
  split.
  - intros. unfold bisimulationAux. unfold bisimulationAux in H2. apply in_or_app.
    apply in_app_or in H2. destruct H2. right. exact H2. left. exact H2.
  - intros. unfold bisimulationAux. unfold bisimulationAux in H2. apply in_or_app.
    apply in_app_or in H2. destruct H2. right. exact H2. left. exact H2.
  Defined.

  (* We compute if the relation is symmetric *)
  Fixpoint isSymmetricAux (setPairs : set (state * state)) (setPairsFull: set (state * state)) :=
    set_eq (setPairs) (containsSymmetric (setPairs) setPairsFull).

  Definition isSymmetric (setPairs : set (state * state)) :=
    if isSymmetricAux (setPairs) (setPairs) then setPairs else [].


  (* We retrieve possible pair of states that can be transitive within R *)
 (* Fixpoint retrieveCandidatesTransitivity (setPairs : set (state * state)) (setPairsFull: set (state * state)) :=
    match setPairs with
    | [] => []
    | pairStates::t => match pairStates with
                       | (a, b) => set_union equiv_dec (flat_map (fun x : (state * state) => match x with 
                                    |(a',b') => if (equiv_decb b a') then [(a,b')]
                                                else [] end) setPairsFull) (retrieveCandidatesTransitivity t setPairsFull)
              end
    end.

  Check retrieveCandidatesTransitivity.

  (* We check the transitivity of the obtained relation by computing pairs to which the transitivity holds.*)
  Fixpoint computeTransitivity (ca1: constraintAutomata) (ca2: constraintAutomata) 
  (setPairs : set (state * state)) (setPairsFull: set (state * state)) :=
  match setPairs with
  | [] => setPairsFull
  | pairStates::t => match pairStates with
                     | (a,b) => if (match ConstraintAutomata.T ca2 b with
                                    | [] => true
                                    | _ => false
                                    end) 
                                then set_union equiv_dec (bisimilarStatesCa1ToCa2 ca1 ca2 a b 
                                  (ConstraintAutomata.T ca2 b) (ConstraintAutomata.T ca1 a) [])
                                     (computeTransitivity ca1 ca2 t setPairsFull)
                                else set_union equiv_dec (bisimilarStatesCa1ToCa2 ca1 ca2 a b (ConstraintAutomata.T ca1 a) (ConstraintAutomata.T ca2 b) [])
                                     (computeTransitivity ca1 ca2 t setPairsFull)
                      end
  end.*)

   Definition isBisim (setPairs : set (state * state)) :=
    isSymmetric setPairs.

  Definition bisimulation (ca1: constraintAutomata) (ca2: constraintAutomata) :=
    isBisim (bisimulationAux ca1 ca2).


  (* We calculate the partition Q / R *)
  Fixpoint mountSubsetFromPairs (pairStates : state) (setPairs : set (state * state)) :=
    match setPairs with
    | [] => [pairStates]
    | a::t => if (fst(a) == pairStates) then set_add equiv_dec (snd(a)) (mountSubsetFromPairs pairStates t)
              else mountSubsetFromPairs pairStates t
    end.

  Fixpoint getQrelR (setRel : set (state * state)) :=
    match setRel with
    | [] => []
    | a::t =>  set_add equiv_dec (mountSubsetFromPairs (fst(a)) (setRel)) (getQrelR t)
    end.


  (* We define the Notation 3.8, DC_A(q,N,P) as Baier et al. define for bisimulation as dcsOfState *)

  Fixpoint getReachedDcs (t: set (set name * DC name data * state)) (setStates: set state) :=
    match t with
    | [] => []
    | a::t => if set_mem equiv_dec (snd(a)) (setStates)
              then (snd(fst(a)))::(getReachedDcs t setStates)
              else (getReachedDcs t setStates)
    end.

  Fixpoint orDcs (dc : DC name data) :=
    match dc with
    | andDc a b => ConstraintAutomata.orDc (ConstraintAutomata.negDc (orDcs a)) (ConstraintAutomata.negDc(orDcs b))
    | _ => dc
    end.

  (* Then we build the disjunction of all dcs of a single transition that reaches a state in P *)
  Fixpoint disjunctionOfDcs (setDcs : set(DC name data))  :=
    match setDcs with
    | [] => ConstraintAutomata.negDc(ConstraintAutomata.tDc name data)
    | a::t => match a with
              | andDc x y => (ConstraintAutomata.orDc (orDcs a) (disjunctionOfDcs t)) 
              | _ => (ConstraintAutomata.orDc (a) (disjunctionOfDcs t))
              end
    end.

   Definition dcsOfState (ca: constraintAutomata) (q: state) (portNames : set name) (P: set state) :=
    disjunctionOfDcs((getReachedDcs (getTransition (portNames) (ConstraintAutomata.T ca q))) (P)).

  (* Equivalence for DCs. Requires that an equality relation to be defined for functions data -> data *)
  Context `{EqDec (data -> data) eq}.
  
Program Instance dc_eqDec `(EqDec name eq) `(EqDec data eq)  : EqDec (DC name data) eq :=
    { equiv_dec := fix rec dc1 dc2 :=
      match dc1,dc2 with
       | tDc _ _, tDc _ _ => in_left
       | dc a b, dc c d => if a == c then if b == d then in_left else in_right else in_right
       | eqDc _ a b, eqDc _ c d => if a == c then if b == d then in_left else in_right else in_right
       | andDc a b, andDc c d => if rec a c then if rec b d then in_left else in_right else in_right
       | orDc a b, orDc c d => if rec a c then if rec b d then in_left else in_right else in_right
       | negDc a, negDc b => if rec a b then in_left else in_right
       | trDc f a b, trDc g c d => if f == g then if a == c then if b == d then in_left else in_right else in_right else in_right
       | tDc _ _ , dc a b => in_right
       | tDc _ _ , eqDc _ a b => in_right
       | tDc _ _ , andDc a b | tDc _ _ , orDc a b => in_right
       | tDc _ _ , negDc a => in_right
       | tDc _ _ , trDc f a b => in_right

       | dc a b  , tDc _ _ => in_right
       | dc a b  , eqDc _ c d => in_right
       | dc a b  , andDc c d => in_right
       | dc a b  , orDc c d => in_right
       | dc a b  , negDc c => in_right
       | dc a b  , trDc f c d => in_right

       | eqDc _ a b  , tDc _ _ => in_right
       | eqDc _ a b  , dc c d => in_right
       | eqDc _ a b  , andDc c d => in_right
       | eqDc _ a b  , orDc c d => in_right
       | eqDc _ a b  , negDc c => in_right
       | eqDc _ a b  , trDc f c d => in_right

       | andDc a b  , tDc _ _ => in_right
       | andDc a b  , dc c d => in_right
       | andDc a b  , eqDc _ c d => in_right
       | andDc a b  , orDc c d => in_right
       | andDc a b  , negDc c => in_right
       | andDc a b  , trDc f c d => in_right

       | orDc a b  , tDc _ _ => in_right
       | orDc a b  , dc c d => in_right
       | orDc a b  , eqDc _ c d => in_right
       | orDc a b  , andDc c d => in_right
       | orDc a b  , negDc c => in_right
       | orDc a b  , trDc f c d => in_right

       | negDc a  , tDc _ _ => in_right
       | negDc a  , dc c d => in_right
       | negDc a  , eqDc _ c d => in_right
       | negDc a  , andDc c d => in_right
       | negDc a  , orDc b c => in_right
       | negDc a  , trDc f c d => in_right

       | trDc f a b , tDc _ _ => in_right
       | trDc f a b , dc c d => in_right
       | trDc f a b , eqDc _ c d => in_right
       | trDc f a b , andDc c d => in_right
       | trDc f a b , orDc c d => in_right
       | trDc f a b , negDc c => in_right
      end
    }.

  (* After reconstructing a DC as Notation 3.8 from a set of possible data constraints of transitions q -> P *)
  (* We need to evaluate whether they are equivalent or not                                                  *)
  Fixpoint dismantleDc (dc: DC name data) :=
    match dc with
    | tDc _ _ => [tDc _ _]
    | eqDc _ a b => [eqDc _ a b]
    | dc a b => [dc]
    | negDc a => [negDc a]
    | trDc f a b => [trDc f a b]
    | orDc a b | andDc a b => set_union equiv_dec (dismantleDc a) (dismantleDc b)
    end.

  (* We search for conditions !A \/ A or \top in a single DC, which makes it always true *)

  Fixpoint existsComplementOrTrue (setDc : set (DC name data)) :=
    match setDc with
    | [] => false
    | a::t => match a with
              | tDc _ _ => true
              | _ => if (set_mem equiv_dec (negDc(a)) (setDc)) then true else (existsComplementOrTrue t)
              end
    end.

  Lemma existsComplementOrTrueSound  : forall setDc,
    existsComplementOrTrue setDc = true -> In (tDc _ _) setDc \/ (exists a, In (a) (setDc) /\ In (negDc(a)) (setDc)).
  Proof.
  - intros. induction setDc. inversion H3. simpl in H3. destruct a. left. simpl;auto.
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (dc n d). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (eqDc data n n0). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (a1 @ a2). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (a1 $ a2) . split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (trDc d n n0). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e.
    right. exists (negDc a). split. simpl;auto. simpl. left. reflexivity. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (negDc a). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
    Qed.
    

  Definition areEquivalentAux (dc1 : set (DC name data)) (dc2: set (DC name data)) :=
    set_eq ((dc1)) ((dc2)) || 
      ((existsComplementOrTrue dc1) && (existsComplementOrTrue dc2)).

  (* We define equivalence of DCs as defined by Notation 3.8 (aforementioned) *)
  Fixpoint areEquivalent (dc1 : DC name data) (dc2: DC name data) :=
    areEquivalentAux (dismantleDc dc1) (dismantleDc dc2).

  (*We define the powerset's construction, in order to verify all possible port names' labels for transitions *)
  Fixpoint powerset (s: set name) :=
    match s with 
    | [] => []
    | a::t => concat (map (fun f => [a::f;f]) (powerset t))
    end.

  (* The comparison of dcsOfState for all port names of both automata *)
  Fixpoint compareDcBisimPortName (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state)
  (q2: state) (P: set state) (setNames: set (set name)) :=
    match setNames with
    | [] => true
    | a::t => areEquivalent((dcsOfState (ca1) (q1) a P)) ((dcsOfState (ca2) (q2) a P)) && 
              (compareDcBisimPortName ca1 ca2 q1 q2 P t)
    end.

  (* Now we want to know if compareDcBisimPortName holds for every P \in Q / R as elements of the bisimulation relation *)
  Fixpoint compareDcBisimPartition (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state)
  (q2: state) (setNames: set (set name)) (qMinusR : set (set state)):=
    match qMinusR with
    | [] => true
    | a::t => (compareDcBisimPortName ca1 ca2 q1 q2 a setNames) && (compareDcBisimPartition ca1 ca2 q1 q2 setNames t)
    end.

  (* We need to check if the above condition holds for every pair of states (q1,q2) \in R as the bisim. relation *)
  Fixpoint compareDcBisimStates (ca1: constraintAutomata) (ca2: constraintAutomata) 
  (setNames: set (set name)) (qMinusR : set (set state)) (pairStates : set (state * state)) :=
    match pairStates with
    | [] => true
    | a::t =>  (compareDcBisimPartition ca1 ca2 (fst(a)) (snd(a)) setNames qMinusR) &&
               (compareDcBisimStates ca1 ca2 setNames qMinusR t)
    end.

  (* We have to ensure that all states of both CA have been comprehended by the obtained bisimulation relation *)

  Fixpoint statesA1InSetPairStates (setPairStates: set (state * state)) : set state:=
    match setPairStates with
    | [] => []
    | a::t => set_add equiv_dec (fst(a)) (statesA1InSetPairStates t)
    end.

  Fixpoint statesA2InSetPairStates (setPairStates: set (state * state)) : set state:=
    match setPairStates with
    | [] => []
    | a::t => set_add equiv_dec (snd(a)) (statesA2InSetPairStates t)
    end.

  Definition containsAllStatesOfBothCa (setQ1 : set state) (setQ2 : set state) (setBisim : set (state * state)) :=
    (s1_in_s2 (setQ1) (statesA1InSetPairStates setBisim)) && (s1_in_s2 (setQ2) (statesA2InSetPairStates setBisim)).
  
  Definition checkBisimilarity (ca1: constraintAutomata) (ca2: constraintAutomata) (bisimRelation : set (state * state)) :=
    if (set_eq (ConstraintAutomata.N ca1) (ConstraintAutomata.N ca2)) && (negb(equiv_decb (bisimRelation) ([]))) then  
    compareDcBisimStates ca1 ca2 (powerset (ConstraintAutomata.N ca1)) (getQrelR (bisimRelation)) (bisimRelation)  &&
    containsAllStatesOfBothCa (ConstraintAutomata.Q0 ca1) (ConstraintAutomata.Q0 ca2) (bisimRelation)(*(containsSymmetric (bisimRelation) (bisimRelation))*)
    else false.
    
  Definition areBisimilar (ca1: constraintAutomata) (ca2: constraintAutomata) :=
    checkBisimilarity ca1 ca2 (bisimulation ca1 ca2).
 
  End ConstraintAutomata.
End ConstraintAutomata. 

Module ProductAutomata.
  Section ProductAutomata.
    Variable state name data state2: Set.
    Context `{EqDec name eq} `{EqDec state eq} `{EqDec state2 eq} `{EqDec (data) eq}.

    Definition constraintAutomata  := ConstraintAutomata.constraintAutomata state name data.
    Definition constraintAutomata2 := ConstraintAutomata.constraintAutomata state2 name data.
    Definition DC := ConstraintAutomata.DC name data.

    Definition statesSet (a1:ConstraintAutomata.constraintAutomata state name data) (a2:ConstraintAutomata.constraintAutomata state2 name data) :=
      list_prod (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2).

    Lemma statesSetSound :forall a1,forall a2, forall a, forall b,
      In (a,b) (statesSet a1 a2) <-> In a (ConstraintAutomata.Q a1) /\ In b (ConstraintAutomata.Q a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    Definition nameSet (a1:ConstraintAutomata.constraintAutomata state name data) (a2:ConstraintAutomata.constraintAutomata state2 name data) :=
      set_union equiv_dec (ConstraintAutomata.N a1) (ConstraintAutomata.N a2).
    
    Lemma nameSetSound : forall a1, forall a2, forall a,
      In a (nameSet a1 a2) <-> In a (ConstraintAutomata.N a1) \/ In a (ConstraintAutomata.N a2).
    Proof.
    intros. apply set_union_iff.
    Defined.

    Definition initialStates (a1: constraintAutomata) (a2: constraintAutomata2) :=
      list_prod (ConstraintAutomata.Q0 a1) (ConstraintAutomata.Q0 a2).

    Lemma initialStatesSound : forall a1, forall a2, forall a, forall b,
      In (a,b) (initialStates a1 a2) <-> In a (ConstraintAutomata.Q0 a1) /\ In b (ConstraintAutomata.Q0 a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

  
    Definition condR1 (t1 : ( set(name) * DC * state)) (t2 : (set(name) * DC * state2))
      (names1 : set name) (names2: set name) :=
      set_eq (set_inter equiv_dec (names2) (fst(fst(t1)))) (set_inter equiv_dec (names1) (fst(fst(t2)))).

    Lemma condR1Sound : forall t1, forall t2, forall names1, forall names2,
    condR1 t1 t2 names1 names2 = true <-> 
    set_eq (set_inter equiv_dec (names2) (fst(fst(t1)))) (set_inter equiv_dec (names1) (fst(fst(t2)))) = true.
    Proof. 
    split. 
    - intros. unfold condR1 in H2. case_eq (set_eq (set_inter equiv_dec names2 (fst (fst t1)))
         (set_inter equiv_dec names1 (fst (fst t2)))).
    + intros. reflexivity.
    + intros. unfold condR1 in H3. rewrite H4 in H3. discriminate.
    - intros. unfold condR1. rewrite H3. reflexivity.
    Defined.

    Definition singleTransitionR1 (Q1: state) (Q2: state2)
      (transition1: (set (name) * DC * (state))) 
      (transition2: (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :  (set (state * state2 * ((set name * DC) * (state * state2)))) :=
        if (condR1 (transition1) (transition2) (names1) (names2)) then
                  [((Q1,Q2),(((set_union equiv_dec (fst(fst(transition1))) (fst(fst(transition2)))),ConstraintAutomata.andDc (snd(fst(transition1))) 
                            (snd(fst(transition2)))),(snd(transition1) , (snd(transition2)))))]
        else [].

    Lemma singleTransitionR1Sound : forall Q1, forall Q2, forall transition1, 
    forall transition2, forall names1, forall names2, singleTransitionR1 Q1 Q2 transition1 transition2
    names1 names2 <> [] <-> (condR1 (transition1) (transition2) (names1) (names2)) = true.
    Proof.
    split.
    - intros. unfold singleTransitionR1 in H3. 
      case_eq (condR1 (transition1) (transition2) (names1) (names2)). reflexivity. 
      intros. rewrite H4 in H3. congruence.
    - intros. unfold singleTransitionR1. rewrite H3. discriminate.
    Defined.

    Fixpoint moreTransitionsR1 (Q1: state) (Q2: state2)
      (transition1: (set (name) * DC * (state))) 
      (transition2: set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match transition2 with
      | [] => []
      | a::t => (singleTransitionR1 Q1 Q2 transition1 a names1 names2)++
                (moreTransitionsR1 Q1 Q2 transition1 t names1 names2)
      end.

    Fixpoint transitionsForOneStateR1 (Q1: state) (Q2: state2)
      (transition1: set (set (name) * DC * (state))) 
      (transition2: set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match transition1 with
      | [] => []
      | a::t => (moreTransitionsR1 Q1 Q2 a transition2 names1 names2)++
                (transitionsForOneStateR1 Q1 Q2 t transition2 names1 names2)
      end.

    Fixpoint iterateOverA2R1 (Q1: state) (Q2: set state2)
      (transition1: state -> set (set (name) * DC * (state))) 
      (transition2: state2 -> set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match Q2 with
      | [] => []
      | a::t => (transitionsForOneStateR1 Q1 a (transition1 Q1) (transition2 a) names1 names2)++
                (iterateOverA2R1 Q1 t transition1 transition2 names1 names2)
      end.

    Fixpoint allTransitionsR1 (Q1: set state) (Q2: set state2)
      (transition1: state -> set (set (name) * DC * (state))) 
      (transition2: state2 -> set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match Q1 with
      | [] => []
      | a::t => (iterateOverA2R1 a Q2 transition1 transition2 names1 names2)++
                (allTransitionsR1 t Q2 transition1 transition2 names1 names2)
    end. 


    Definition transitionsRule1 (a1: constraintAutomata) (a2: constraintAutomata2) := 
      allTransitionsR1 (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2) 
                       (ConstraintAutomata.T a1) (ConstraintAutomata.T a2) 
                       (ConstraintAutomata.N a1) (ConstraintAutomata.N a2).

    Definition condR2 (tr: set (name) * DC * state) (names2: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names2) == nil then true else false.

    Lemma condR2Sound : forall tr, forall names2, condR2 tr names2 = true <->
      set_inter equiv_dec (fst(fst(tr))) names2 = nil.
    Proof.
    split.
    - intros. unfold condR2 in H3. destruct equiv_dec in H3. inversion e. reflexivity.
      inversion H3.
    - intros. unfold condR2. rewrite H3. reflexivity.
    Defined.

    Fixpoint singleTransitionR2 (q1:state) (transition : (set (name) * DC * (state))) (a2States : set state2) (a2Names: set name)   
    : set (state * state2 * ((set name * DC) * (state * state2))) :=
    match a2States with
    | [] => []
    | q2::t => if (condR2 (transition) (a2Names)) then 
                 ((q1,q2),((fst(transition)), ((snd(transition)), (q2))))::singleTransitionR2 q1 transition t a2Names
                else singleTransitionR2 q1 transition t a2Names
    end.

    Lemma singleTransitionR2Sound : forall q1, forall transition, forall a2States, forall a2Names, 
      singleTransitionR2 q1 transition a2States a2Names <> [] <-> condR2 (transition) (a2Names) = true /\ a2States <> [].
    Proof.
    split.
    - intros. induction a2States. unfold singleTransitionR2 in H3. congruence.
      simpl in H3. case_eq (condR2 transition a2Names). intros. split. reflexivity. congruence.
      intros. rewrite H4 in H3. simpl in H3. apply IHa2States in H3. destruct H3. congruence.
    - intros. induction a2States. unfold singleTransitionR2. destruct H3. congruence.
      simpl. case_eq (condR2 transition a2Names). discriminate. intros. destruct H3. congruence.
    Defined.
     
    Definition transitionR2 (q1:state) : set (set (name) * DC * (state)) -> 
      set state2 -> set name 
      -> set (state * state2 * ((set name * DC) * (state * state2))) :=
      fix rec transitions q2 names2 :=
        match transitions with
        | [] => [] 
        | a::t =>  (singleTransitionR2 q1 a q2 names2)++(rec t q2 names2)
        end.

    Fixpoint allTransitionsR2 (Q1: set state) (transitions: state -> set (set (name) * DC * (state))) 
      (names2: set name) (a2States : set state2) := 
      match Q1 with
      | [] => []
      | a::t => (transitionR2 a (transitions(a)) a2States names2)++(allTransitionsR2 t transitions names2 a2States)
      end.

    Definition transitionsRule2 (a1: constraintAutomata) (a2 : constraintAutomata2)  :=
      (allTransitionsR2 (ConstraintAutomata.Q a1) (ConstraintAutomata.T a1) 
                                      (ConstraintAutomata.N a2) (ConstraintAutomata.Q a2)).

    Definition condR3 (tr: set (name) * DC * state2) (names1: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names1) == nil then true else false.

    Lemma condR3Sound : forall tr, forall names1, condR3 tr names1 = true <->
      set_inter equiv_dec (fst(fst(tr))) names1 = nil.
    Proof.
    split.
    - intros. unfold condR3 in H3. destruct equiv_dec in H3. inversion e. reflexivity.
      inversion H3.
    - intros. unfold condR3. rewrite H3. reflexivity.
    Defined.

    Fixpoint singleTransitionR3 (q2:state2) (transition : (set (name) * DC * (state2))) (a2States : set state) (a1Names: set name)   
    : set (state * state2 * ((set name * DC) * (state * state2))) :=
    match a2States with
    | [] => []
    | q1::t => if (condR3 (transition) (a1Names)) then 
                 ((q1,q2),((fst(transition)), ((q1) , (snd(transition)))))::singleTransitionR3 q2 transition t a1Names
                else singleTransitionR3 q2 transition t a1Names
    end.

    Lemma singleTransitionR3Sound : forall q2, forall transition, forall a1States, forall a1Names,
    singleTransitionR3 q2 transition a1States a1Names <> [] <-> 
    condR3 (transition) (a1Names) = true /\ a1States <> [].
    Proof.
    split. 
    - intros. induction a1States. simpl in H3. congruence.
    simpl in H3. case_eq (condR3 (transition) (a1Names)). split. reflexivity. discriminate.
    intros. rewrite H4 in H3. apply IHa1States in H3. destruct H3. congruence.
    - intros. induction a1States. destruct H3. congruence.
    simpl. case_eq (condR3 (transition) (a1Names)). discriminate.
    destruct H3. congruence.
    Defined.
  
    Definition transitionR3 (q2:state2) : set (set (name) * DC * (state2)) -> 
      set state -> set name  
      -> set (state * state2 * ((set name * DC) * (state * state2))) :=
      fix rec transitions q1 names1 :=
        match transitions with
        | [] => [] 
        | a::t =>  (singleTransitionR3 q2 a q1 names1)++(rec t q1 names1)
        end.

    Fixpoint allTransitionsR3 (Q2: set state2) (transitions: state2 -> set (set (name) * DC * (state2))) 
      (names1: set name) (a1States : set state) := 
      match Q2 with
      | [] => []
      | a::t => (transitionR3 a (transitions(a)) a1States names1)++(allTransitionsR3 t transitions names1 a1States)
      end.

    Definition transitionsRule3 (a1: constraintAutomata) (a2 : constraintAutomata2)  :=
      (allTransitionsR3 (ConstraintAutomata.Q a2) (ConstraintAutomata.T a2) 
                       (ConstraintAutomata.N a1) (ConstraintAutomata.Q a1)).

    Definition buildTransitionRuleProductAutomaton (a1: constraintAutomata) (a2: constraintAutomata2) :=
      (transitionsRule1 a1 a2)++(transitionsRule2 a1 a2)++(transitionsRule3 a1 a2).

    Fixpoint recoverResultingStatesPA (st: (state * state2)) 
      (t:set (state * state2 * ((set name * DC) * (state * state2)))) :=
      match t with
      | [] => []
      | a::tx => if st == fst((a)) then (snd((a))::recoverResultingStatesPA st tx)
                 else recoverResultingStatesPA st tx
      end.

    Lemma recoverResultingStatesPASound : forall st, forall t, recoverResultingStatesPA st t <> [] <->
      exists a, In a t /\ st = fst(a).
    Proof.
    split.
    - intros. induction t. simpl in H3. congruence.
      simpl in H3. destruct equiv_dec in H3. inversion e. exists a. split. simpl; auto. reflexivity.
      apply IHt in H3. destruct H3. exists x. destruct H3. split. simpl. auto. exact H4. 
    - intros. induction t. destruct H3. destruct H3. inversion H3. 
      simpl. destruct equiv_dec.  discriminate. apply IHt. destruct H3. destruct H3. simpl in H3. destruct H3. 
      rewrite <- H3 in H4. congruence. exists x. split. exact H3. exact H4.
    Defined.

    Definition transitionPA (a1: constraintAutomata) (a2: constraintAutomata2) (s: (state * state2)) :=
      recoverResultingStatesPA s (buildTransitionRuleProductAutomaton a1 a2). 

    Definition buildPA (a1: constraintAutomata) (a2:constraintAutomata2) := 
      ConstraintAutomata.CA (statesSet a1 a2) (nameSet a1 a2) (transitionPA a1 a2) (initialStates a1 a2).

  End ProductAutomata.
End ProductAutomata.


Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
Require Export Coq.Numbers.BinNums.