{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module TrafficLightsCertified where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n0 =
  case n0 of {
   O -> f;
   S n1 -> f0 n1 (nat_rect f f0 n1)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Sumbool =
   Left
 | Right

eq_dec :: Nat -> Nat -> Sumbool
eq_dec n0 =
  nat_rec (\m -> case m of {
                  O -> Left;
                  S _ -> Right}) (\_ iHn m ->
    case m of {
     O -> Right;
     S m0 -> iHn m0}) n0

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t0 -> Cons (f a) (map f t0)}

list_prod :: (List a1) -> (List a2) -> List (Prod a1 a2)
list_prod l l' =
  case l of {
   Nil -> Nil;
   Cons x t0 -> app (map (\y -> Pair x y) l') (list_prod t0 l')}

type Set a = List a

set_add :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of {
   Nil -> Cons a Nil;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> Cons a1 x1;
     Right -> Cons a1 (set_add aeq_dec a x1)}}

set_mem :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Bool
set_mem aeq_dec a x =
  case x of {
   Nil -> False;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> True;
     Right -> set_mem aeq_dec a x1}}

set_inter :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_inter aeq_dec x y =
  case x of {
   Nil -> Nil;
   Cons a1 x1 ->
    case set_mem aeq_dec a1 y of {
     True -> Cons a1 (set_inter aeq_dec x1 y);
     False -> set_inter aeq_dec x1 y}}

set_union :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of {
   Nil -> x;
   Cons a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)}

type EqDec a = a -> a -> Sumbool

equiv_dec :: (EqDec a1) -> a1 -> a1 -> Sumbool
equiv_dec eqDec =
  eqDec

nat_eq_eqdec :: EqDec Nat
nat_eq_eqdec =
  eq_dec

list_eqdec :: (EqDec a1) -> EqDec (List a1)
list_eqdec eqa x y =
  case x of {
   Nil -> case y of {
           Nil -> Left;
           Cons _ _ -> Right};
   Cons hd tl ->
    case y of {
     Nil -> Right;
     Cons hd' tl' ->
      case equiv_dec eqa hd hd' of {
       Left -> list_eqdec eqa tl tl';
       Right -> Right}}}

pair_eqdec :: (EqDec a1) -> (EqDec a2) -> EqDec (Prod a1 a2)
pair_eqdec h h0 x y =
  case x of {
   Pair a b ->
    case y of {
     Pair c d ->
      case equiv_dec h a c of {
       Left -> equiv_dec h0 b d;
       Right -> Right}}}

s1_in_s2 :: (EqDec a1) -> (Set a1) -> (Set a1) -> Bool
s1_in_s2 h s1 s2 =
  case s1 of {
   Nil -> True;
   Cons a t0 -> andb (set_mem (equiv_dec h) a s2) (s1_in_s2 h t0 s2)}

set_eq :: (EqDec a1) -> (Set a1) -> (Set a1) -> Bool
set_eq h s1 s2 =
  case equiv_dec nat_eq_eqdec (length s1) (length s2) of {
   Left ->
    case s1_in_s2 h s1 s2 of {
     True -> s1_in_s2 h s2 s1;
     False -> False};
   Right -> False}

data DC name data0 =
   TDc
 | Dc name data0
 | EqDc name name
 | AndDc (DC name data0) (DC name data0)
 | OrDc (DC name data0) (DC name data0)
 | TrDc (data0 -> data0) name name
 | NegDc (DC name data0)

data ConstraintAutomata state name data0 =
   CA (Set state) (Set name) (state -> Set
                             (Prod (Prod (Set name) (DC name data0)) state)) 
 (Set state)

q :: (ConstraintAutomata a1 a2 a3) -> Set a1
q c =
  case c of {
   CA q1 _ _ _ -> q1}

n :: (ConstraintAutomata a1 a2 a3) -> Set a2
n c =
  case c of {
   CA _ n0 _ _ -> n0}

t :: (ConstraintAutomata a1 a2 a3) -> a1 -> Set
     (Prod (Prod (Set a2) (DC a2 a3)) a1)
t c =
  case c of {
   CA _ _ t0 _ -> t0}

q0 :: (ConstraintAutomata a1 a2 a3) -> Set a1
q0 c =
  case c of {
   CA _ _ _ q1 -> q1}

type ConstraintAutomata0 state name data0 =
  ConstraintAutomata state name data0

type ConstraintAutomata2 name data0 state2 =
  ConstraintAutomata state2 name data0

type DC0 name data0 = DC name data0

statesSet :: (ConstraintAutomata a1 a2 a3) -> (ConstraintAutomata a4 
             a2 a3) -> List (Prod a1 a4)
statesSet a1 a2 =
  list_prod (q a1) (q a2)

nameSet :: (EqDec a2) -> (ConstraintAutomata a1 a2 a3) -> (ConstraintAutomata
           a4 a2 a3) -> Set a2
nameSet h a1 a2 =
  set_union (equiv_dec h) (n a1) (n a2)

initialStates :: (ConstraintAutomata0 a1 a2 a3) -> (ConstraintAutomata2 
                 a2 a3 a4) -> List (Prod a1 a4)
initialStates a1 a2 =
  list_prod (q0 a1) (q0 a2)

condR1 :: (EqDec a2) -> (Prod (Prod (Set a2) (DC0 a2 a3)) a1) -> (Prod
          (Prod (Set a2) (DC0 a2 a3)) a4) -> (Set a2) -> (Set a2) -> Bool
condR1 h t1 t2 names1 names2 =
  set_eq h (set_inter (equiv_dec h) names2 (fst (fst t1)))
    (set_inter (equiv_dec h) names1 (fst (fst t2)))

singleTransitionR1 :: (EqDec a2) -> a1 -> a4 -> (Prod
                      (Prod (Set a2) (DC0 a2 a3)) a1) -> (Prod
                      (Prod (Set a2) (DC0 a2 a3)) a4) -> (Set a2) -> (Set 
                      a2) -> Set
                      (Prod (Prod a1 a4)
                      (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
singleTransitionR1 h q1 q2 transition1 transition2 names1 names2 =
  case condR1 h transition1 transition2 names1 names2 of {
   True -> Cons (Pair (Pair q1 q2) (Pair (Pair
    (set_union (equiv_dec h) (fst (fst transition1)) (fst (fst transition2)))
    (AndDc (snd (fst transition1)) (snd (fst transition2)))) (Pair
    (snd transition1) (snd transition2)))) Nil;
   False -> Nil}

moreTransitionsR1 :: (EqDec a2) -> a1 -> a4 -> (Prod
                     (Prod (Set a2) (DC0 a2 a3)) a1) -> (Set
                     (Prod (Prod (Set a2) (DC0 a2 a3)) a4)) -> (Set a2) ->
                     (Set a2) -> List
                     (Prod (Prod a1 a4)
                     (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
moreTransitionsR1 h q1 q2 transition1 transition2 names1 names2 =
  case transition2 of {
   Nil -> Nil;
   Cons a t0 ->
    app (singleTransitionR1 h q1 q2 transition1 a names1 names2)
      (moreTransitionsR1 h q1 q2 transition1 t0 names1 names2)}

transitionsForOneStateR1 :: (EqDec a2) -> a1 -> a4 -> (Set
                            (Prod (Prod (Set a2) (DC0 a2 a3)) a1)) -> (Set
                            (Prod (Prod (Set a2) (DC0 a2 a3)) a4)) -> (Set
                            a2) -> (Set a2) -> List
                            (Prod (Prod a1 a4)
                            (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
transitionsForOneStateR1 h q1 q2 transition1 transition2 names1 names2 =
  case transition1 of {
   Nil -> Nil;
   Cons a t0 ->
    app (moreTransitionsR1 h q1 q2 a transition2 names1 names2)
      (transitionsForOneStateR1 h q1 q2 t0 transition2 names1 names2)}

iterateOverA2R1 :: (EqDec a2) -> a1 -> (Set a4) -> (a1 -> Set
                   (Prod (Prod (Set a2) (DC0 a2 a3)) a1)) -> (a4 -> Set
                   (Prod (Prod (Set a2) (DC0 a2 a3)) a4)) -> (Set a2) -> (Set
                   a2) -> List
                   (Prod (Prod a1 a4)
                   (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
iterateOverA2R1 h q1 q2 transition1 transition2 names1 names2 =
  case q2 of {
   Nil -> Nil;
   Cons a t0 ->
    app
      (transitionsForOneStateR1 h q1 a (transition1 q1) (transition2 a)
        names1 names2)
      (iterateOverA2R1 h q1 t0 transition1 transition2 names1 names2)}

allTransitionsR1 :: (EqDec a2) -> (Set a1) -> (Set a4) -> (a1 -> Set
                    (Prod (Prod (Set a2) (DC0 a2 a3)) a1)) -> (a4 -> Set
                    (Prod (Prod (Set a2) (DC0 a2 a3)) a4)) -> (Set a2) ->
                    (Set a2) -> List
                    (Prod (Prod a1 a4)
                    (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
allTransitionsR1 h q1 q2 transition1 transition2 names1 names2 =
  case q1 of {
   Nil -> Nil;
   Cons a t0 ->
    app (iterateOverA2R1 h a q2 transition1 transition2 names1 names2)
      (allTransitionsR1 h t0 q2 transition1 transition2 names1 names2)}

transitionsRule1 :: (EqDec a2) -> (ConstraintAutomata0 a1 a2 a3) ->
                    (ConstraintAutomata2 a2 a3 a4) -> List
                    (Prod (Prod a1 a4)
                    (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
transitionsRule1 h a1 a2 =
  allTransitionsR1 h (q a1) (q a2) (t a1) (t a2) (n a1) (n a2)

condR2 :: (EqDec a2) -> (Prod (Prod (Set a2) (DC0 a2 a3)) a1) -> (Set 
          a2) -> Bool
condR2 h tr names2 =
  case equiv_dec (list_eqdec h)
         (set_inter (equiv_dec h) (fst (fst tr)) names2) Nil of {
   Left -> True;
   Right -> False}

singleTransitionR2 :: (EqDec a2) -> a1 -> (Prod (Prod (Set a2) (DC0 a2 a3))
                      a1) -> (Set a4) -> (Set a2) -> Set
                      (Prod (Prod a1 a4)
                      (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
singleTransitionR2 h q1 transition a2States a2Names =
  case a2States of {
   Nil -> Nil;
   Cons q2 t0 ->
    case condR2 h transition a2Names of {
     True -> Cons (Pair (Pair q1 q2) (Pair (fst transition) (Pair
      (snd transition) q2))) (singleTransitionR2 h q1 transition t0 a2Names);
     False -> singleTransitionR2 h q1 transition t0 a2Names}}

transitionR2 :: (EqDec a2) -> a1 -> (Set
                (Prod (Prod (Set a2) (DC0 a2 a3)) a1)) -> (Set a4) -> (Set
                a2) -> Set
                (Prod (Prod a1 a4)
                (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
transitionR2 h q1 transitions q2 names2 =
  case transitions of {
   Nil -> Nil;
   Cons a t0 ->
    app (singleTransitionR2 h q1 a q2 names2)
      (transitionR2 h q1 t0 q2 names2)}

allTransitionsR2 :: (EqDec a2) -> (Set a1) -> (a1 -> Set
                    (Prod (Prod (Set a2) (DC0 a2 a3)) a1)) -> (Set a2) ->
                    (Set a4) -> List
                    (Prod (Prod a1 a4)
                    (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
allTransitionsR2 h q1 transitions names2 a2States =
  case q1 of {
   Nil -> Nil;
   Cons a t0 ->
    app (transitionR2 h a (transitions a) a2States names2)
      (allTransitionsR2 h t0 transitions names2 a2States)}

transitionsRule2 :: (EqDec a2) -> (ConstraintAutomata0 a1 a2 a3) ->
                    (ConstraintAutomata2 a2 a3 a4) -> List
                    (Prod (Prod a1 a4)
                    (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
transitionsRule2 h a1 a2 =
  allTransitionsR2 h (q a1) (t a1) (n a2) (q a2)

condR3 :: (EqDec a1) -> (Prod (Prod (Set a1) (DC0 a1 a2)) a3) -> (Set 
          a1) -> Bool
condR3 h tr names1 =
  case equiv_dec (list_eqdec h)
         (set_inter (equiv_dec h) (fst (fst tr)) names1) Nil of {
   Left -> True;
   Right -> False}

singleTransitionR3 :: (EqDec a2) -> a4 -> (Prod (Prod (Set a2) (DC0 a2 a3))
                      a4) -> (Set a1) -> (Set a2) -> Set
                      (Prod (Prod a1 a4)
                      (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
singleTransitionR3 h q2 transition a2States a1Names =
  case a2States of {
   Nil -> Nil;
   Cons q1 t0 ->
    case condR3 h transition a1Names of {
     True -> Cons (Pair (Pair q1 q2) (Pair (fst transition) (Pair q1
      (snd transition)))) (singleTransitionR3 h q2 transition t0 a1Names);
     False -> singleTransitionR3 h q2 transition t0 a1Names}}

transitionR3 :: (EqDec a2) -> a4 -> (Set
                (Prod (Prod (Set a2) (DC0 a2 a3)) a4)) -> (Set a1) -> (Set
                a2) -> Set
                (Prod (Prod a1 a4)
                (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
transitionR3 h q2 transitions q1 names1 =
  case transitions of {
   Nil -> Nil;
   Cons a t0 ->
    app (singleTransitionR3 h q2 a q1 names1)
      (transitionR3 h q2 t0 q1 names1)}

allTransitionsR3 :: (EqDec a2) -> (Set a4) -> (a4 -> Set
                    (Prod (Prod (Set a2) (DC0 a2 a3)) a4)) -> (Set a2) ->
                    (Set a1) -> List
                    (Prod (Prod a1 a4)
                    (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
allTransitionsR3 h q2 transitions names1 a1States =
  case q2 of {
   Nil -> Nil;
   Cons a t0 ->
    app (transitionR3 h a (transitions a) a1States names1)
      (allTransitionsR3 h t0 transitions names1 a1States)}

transitionsRule3 :: (EqDec a2) -> (ConstraintAutomata0 a1 a2 a3) ->
                    (ConstraintAutomata2 a2 a3 a4) -> List
                    (Prod (Prod a1 a4)
                    (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4)))
transitionsRule3 h a1 a2 =
  allTransitionsR3 h (q a2) (t a2) (n a1) (q a1)

buildTransitionRuleProductAutomaton :: (EqDec a2) -> (ConstraintAutomata0 
                                       a1 a2 a3) -> (ConstraintAutomata2 
                                       a2 a3 a4) -> List
                                       (Prod (Prod a1 a4)
                                       (Prod (Prod (Set a2) (DC0 a2 a3))
                                       (Prod a1 a4)))
buildTransitionRuleProductAutomaton h a1 a2 =
  app (transitionsRule1 h a1 a2)
    (app (transitionsRule2 h a1 a2) (transitionsRule3 h a1 a2))

recoverResultingStatesPA :: (EqDec a1) -> (EqDec a4) -> (Prod a1 a4) -> (Set
                            (Prod (Prod a1 a4)
                            (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4))))
                            -> List
                            (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4))
recoverResultingStatesPA h0 h1 st t0 =
  case t0 of {
   Nil -> Nil;
   Cons a tx ->
    case equiv_dec (pair_eqdec h0 h1) st (fst a) of {
     Left -> Cons (snd a) (recoverResultingStatesPA h0 h1 st tx);
     Right -> recoverResultingStatesPA h0 h1 st tx}}

transitionPA :: (EqDec a2) -> (EqDec a1) -> (EqDec a4) ->
                (ConstraintAutomata0 a1 a2 a3) -> (ConstraintAutomata2 
                a2 a3 a4) -> (Prod a1 a4) -> List
                (Prod (Prod (Set a2) (DC0 a2 a3)) (Prod a1 a4))
transitionPA h h0 h1 a1 a2 s =
  recoverResultingStatesPA h0 h1 s
    (buildTransitionRuleProductAutomaton h a1 a2)

buildPA :: (EqDec a2) -> (EqDec a1) -> (EqDec a4) -> (ConstraintAutomata0 
           a1 a2 a3) -> (ConstraintAutomata2 a2 a3 a4) -> ConstraintAutomata
           (Prod a1 a4) a2 a3
buildPA h h0 h1 a1 a2 =
  CA (statesSet a1 a2) (nameSet h a1 a2) (transitionPA h h0 h1 a1 a2)
    (initialStates a1 a2)

data ModelPortsType =
   A
 | Y
 | B
 | X
 | I
 | J
 | L
 | K
 | M
 | N
 | C

modelPortsEqDec :: EqDec ModelPortsType
modelPortsEqDec x y =
  case x of {
   A -> case y of {
         A -> Left;
         _ -> Right};
   Y -> case y of {
         Y -> Left;
         _ -> Right};
   B -> case y of {
         B -> Left;
         _ -> Right};
   X -> case y of {
         X -> Left;
         _ -> Right};
   I -> case y of {
         I -> Left;
         _ -> Right};
   J -> case y of {
         J -> Left;
         _ -> Right};
   L -> case y of {
         L -> Left;
         _ -> Right};
   K -> case y of {
         K -> Left;
         _ -> Right};
   M -> case y of {
         M -> Left;
         _ -> Right};
   N -> case y of {
         N -> Left;
         _ -> Right};
   C -> case y of {
         C -> Left;
         _ -> Right}}

merger1EqDec :: Sumbool
merger1EqDec =
  Left

sync2EqDec :: Sumbool
sync2EqDec =
  Left

sync3EqDec :: Sumbool
sync3EqDec =
  Left

sync4EqDec :: Sumbool
sync4EqDec =
  Left

transformer5EqDec :: Sumbool
transformer5EqDec =
  Left

sync6EqDec :: Sumbool
sync6EqDec =
  Left

sync7EqDec :: Sumbool
sync7EqDec =
  Left

data Fifo8StatesType =
   Q7
 | P0
 | P1

fifo8EqDec :: EqDec Fifo8StatesType
fifo8EqDec x y =
  case x of {
   Q7 -> case y of {
          Q7 -> Left;
          _ -> Right};
   P0 -> case y of {
          P0 -> Left;
          _ -> Right};
   P1 -> case y of {
          P1 -> Left;
          _ -> Right}}

merger9EqDec :: Sumbool
merger9EqDec =
  Left

merger1rel :: List
              (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
merger1rel =
  Cons (Pair (Pair (Cons A (Cons Y Nil)) (EqDc A Y)) __) (Cons (Pair (Pair
    (Cons B (Cons Y Nil)) (EqDc B Y)) __) Nil)

merger1Automaton :: ConstraintAutomata () ModelPortsType Nat
merger1Automaton =
  CA (Cons __ Nil) (Cons A (Cons Y (Cons B Nil))) (\_ -> merger1rel) (Cons __
    Nil)

sync2rel :: List
            (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
sync2rel =
  Cons (Pair (Pair (Cons Y (Cons X Nil)) (EqDc Y X)) __) Nil

sync2Automaton :: ConstraintAutomata () ModelPortsType Nat
sync2Automaton =
  CA (Cons __ Nil) (Cons Y (Cons X Nil)) (\_ -> sync2rel) (Cons __ Nil)

sync3rel :: List
            (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
sync3rel =
  Cons (Pair (Pair (Cons X (Cons I Nil)) (EqDc X I)) __) Nil

sync3Automaton :: ConstraintAutomata () ModelPortsType Nat
sync3Automaton =
  CA (Cons __ Nil) (Cons X (Cons I Nil)) (\_ -> sync3rel) (Cons __ Nil)

sync4rel :: List
            (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
sync4rel =
  Cons (Pair (Pair (Cons X (Cons J Nil)) (EqDc X J)) __) Nil

sync4Automaton :: ConstraintAutomata () ModelPortsType Nat
sync4Automaton =
  CA (Cons __ Nil) (Cons X (Cons J Nil)) (\_ -> sync4rel) (Cons __ Nil)

swap01 :: Nat -> Nat
swap01 n0 =
  case n0 of {
   O -> S O;
   S o -> case o of {
           O -> O;
           S _ -> S o}}

transformer5rel :: List
                   (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat))
                   ())
transformer5rel =
  Cons (Pair (Pair (Cons J (Cons L Nil)) (TrDc swap01 J L)) __) Nil

transformer5Automaton :: ConstraintAutomata () ModelPortsType Nat
transformer5Automaton =
  CA (Cons __ Nil) (Cons J (Cons L Nil)) (\_ -> transformer5rel) (Cons __
    Nil)

sync6rel :: List
            (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
sync6rel =
  Cons (Pair (Pair (Cons I (Cons K Nil)) (EqDc I K)) __) Nil

sync6Automaton :: ConstraintAutomata () ModelPortsType Nat
sync6Automaton =
  CA (Cons __ Nil) (Cons I (Cons K Nil)) (\_ -> sync6rel) (Cons __ Nil)

sync7rel :: List
            (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
sync7rel =
  Cons (Pair (Pair (Cons L (Cons M Nil)) (EqDc L M)) __) Nil

sync7Automaton :: ConstraintAutomata () ModelPortsType Nat
sync7Automaton =
  CA (Cons __ Nil) (Cons L (Cons M Nil)) (\_ -> sync7rel) (Cons __ Nil)

fifo8rel :: Fifo8StatesType -> List
            (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat))
            Fifo8StatesType)
fifo8rel s =
  case s of {
   Q7 -> Cons (Pair (Pair (Cons K Nil) (Dc K O)) P0) (Cons (Pair (Pair (Cons
    K Nil) (Dc K (S O))) P1) Nil);
   P0 -> Cons (Pair (Pair (Cons N Nil) (Dc N O)) Q7) Nil;
   P1 -> Cons (Pair (Pair (Cons N Nil) (Dc N (S O))) Q7) Nil}

fifo8Automaton :: ConstraintAutomata Fifo8StatesType ModelPortsType Nat
fifo8Automaton =
  CA (Cons Q7 (Cons P0 (Cons P1 Nil))) (Cons K (Cons N Nil)) fifo8rel (Cons
    Q7 Nil)

merger9rel :: List
              (Prod (Prod (List ModelPortsType) (DC ModelPortsType Nat)) ())
merger9rel =
  Cons (Pair (Pair (Cons M (Cons C Nil)) (EqDc M C)) __) (Cons (Pair (Pair
    (Cons N (Cons C Nil)) (EqDc N C)) __) Nil)

merger9Automaton :: ConstraintAutomata () ModelPortsType Nat
merger9Automaton =
  CA (Cons __ Nil) (Cons M (Cons C (Cons N Nil))) (\_ -> merger9rel) (Cons __
    Nil)

merger1sync2Product :: ConstraintAutomata () ModelPortsType Nat
merger1sync2Product =
  unsafeCoerce buildPA modelPortsEqDec (\_ _ -> merger1EqDec) (\_ _ ->
    sync2EqDec) merger1Automaton sync2Automaton

sync2sync3Product :: ConstraintAutomata () ModelPortsType Nat
sync2sync3Product =
  unsafeCoerce buildPA modelPortsEqDec
    (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec)) (\_ _ ->
    sync3EqDec) merger1sync2Product sync3Automaton

sync3sync4Product :: ConstraintAutomata () ModelPortsType Nat
sync3sync4Product =
  unsafeCoerce buildPA modelPortsEqDec
    (pair_eqdec (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec))
      (\_ _ -> sync3EqDec)) (\_ _ -> sync4EqDec) sync2sync3Product
    sync4Automaton

sync4transformer5Product :: ConstraintAutomata () ModelPortsType Nat
sync4transformer5Product =
  unsafeCoerce buildPA modelPortsEqDec
    (pair_eqdec
      (pair_eqdec (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec))
        (\_ _ -> sync3EqDec)) (\_ _ -> sync4EqDec)) (\_ _ ->
    transformer5EqDec) sync3sync4Product transformer5Automaton

transformer5sync6Product :: ConstraintAutomata () ModelPortsType Nat
transformer5sync6Product =
  unsafeCoerce buildPA modelPortsEqDec
    (pair_eqdec
      (pair_eqdec
        (pair_eqdec (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec))
          (\_ _ -> sync3EqDec)) (\_ _ -> sync4EqDec)) (\_ _ ->
      transformer5EqDec)) (\_ _ -> sync6EqDec) sync4transformer5Product
    sync6Automaton

sync6sync7Product :: ConstraintAutomata () ModelPortsType Nat
sync6sync7Product =
  unsafeCoerce buildPA modelPortsEqDec
    (pair_eqdec
      (pair_eqdec
        (pair_eqdec
          (pair_eqdec
            (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec)) (\_ _ ->
            sync3EqDec)) (\_ _ -> sync4EqDec)) (\_ _ -> transformer5EqDec))
      (\_ _ -> sync6EqDec)) (\_ _ -> sync7EqDec) transformer5sync6Product
    sync7Automaton

sync7fifo8Product :: ConstraintAutomata (Prod () Fifo8StatesType)
                     ModelPortsType Nat
sync7fifo8Product =
  buildPA modelPortsEqDec
    (unsafeCoerce pair_eqdec
      (pair_eqdec
        (pair_eqdec
          (pair_eqdec
            (pair_eqdec
              (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec))
              (\_ _ -> sync3EqDec)) (\_ _ -> sync4EqDec)) (\_ _ ->
          transformer5EqDec)) (\_ _ -> sync6EqDec)) (\_ _ -> sync7EqDec))
    fifo8EqDec sync6sync7Product fifo8Automaton

fifo8merger9Product :: ConstraintAutomata (Prod (Prod () Fifo8StatesType) ())
                       ModelPortsType Nat
fifo8merger9Product =
  buildPA modelPortsEqDec
    (pair_eqdec
      (unsafeCoerce pair_eqdec
        (pair_eqdec
          (pair_eqdec
            (pair_eqdec
              (pair_eqdec
                (pair_eqdec (\_ _ -> merger1EqDec) (\_ _ -> sync2EqDec))
                (\_ _ -> sync3EqDec)) (\_ _ -> sync4EqDec)) (\_ _ ->
            transformer5EqDec)) (\_ _ -> sync6EqDec)) (\_ _ -> sync7EqDec))
      fifo8EqDec) (\_ _ -> merger9EqDec) sync7fifo8Product merger9Automaton

