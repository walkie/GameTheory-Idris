--   Functions for executing game trees.
module Game.Exec

import Game.Class
import Game.Tree

%default total

{-
go : Edge e => Current e s mvs -> Either (Complete mvs) (Current e s mvs)
go (MkCurrent (Node s i es) t) = ...
go (MkCurrent (Leaf s p)    t) = Left (MkComplete t (summarize t) p)
-}
