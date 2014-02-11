-- | Simultaneous move games. This representation supports continuous domains
--   of moves. For discrete domains, see 'Game.Normal'.
module Game.Simult

import Game.Class
import Game.Payoff
import Game.Profile
import Game.Tree

%default total


-- | A general simultaneous move game. Maps a strategy profile to a payoff.
data Simult : MoveTypes np -> Type where
  MkSimult : {mvs : MoveTypes np} -> (Profile mvs -> Maybe (Payoff np)) -> Simult mvs

-- | Get the payoff function for a simultaneous game.
payoffFun : {mvs : MoveTypes np} -> Simult mvs -> Profile mvs -> Maybe (Payoff np)
payoffFun (MkSimult f) = f

-- | Convert a simultaneous move game into a game tree.
fromSimult : {mvs : MoveTypes np} -> Simult mvs -> GameTree Continuous () mvs
fromSimult (MkSimult f) = fromMaybe (Leaf () tie) (node last [] f)
  where 
    %assert_total
    node : {np  : Nat} -> {mvs : MoveTypes np}
        -> {lev : Nat} -> {ts  : Vect lev Type}
        -> (i   : Fin (S np))
        -> HVect ts    -- ts = drop i (toVect mvs)
        -> (Profile mvs -> Maybe (Payoff np))
        -> Maybe (GameTree Continuous () mvs)
    node fZ     ms pay = map (Leaf ()) (pay (profile (believe_me ms)))
    node (fS k) ms pay = Just (Node () (MkPlayerID k)
                         (ContinuousEdges (\m => node (weaken k) (m :: ms) pay)))

instance Game (Simult {np} mvs) where
  numPlayers _ = np
  edgeType   _ = Continuous
  stateType  _ = ()
  moveTypes  _ = mvs
  toGameTree   = fromSimult
  

--
-- * Static unit tests
--

namespace Test

  t_sum : GameTree Continuous () [Float,Float]
  t_sum = fromSimult (MkSimult (\(MkHVectBy [a,b]) => Just (payoff [a+b,a+b])))

  {- Totality checker prevents this test from passing.
  test_fromSimult :
    so (outcome (execMoveC (execMoveC t_sum 3) 4) == payoff [7,7])
  test_fromSimult = oh
  -}
