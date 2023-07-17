{-# OPTIONS -v impossible:10 #-}
-- Andreas, 2021-05-12, issue #5379
module ImpossibleVerboseReduceM where

-- Note: keep ReduceM as first word after IMPOSSIBLE!
{-# IMPOSSIBLE ReduceM SHOULD ALSO PRINT THIS DEBUG MESSAGE. LET'S MAKE IT VERY LONG SO IT CANNOT BE OVERLOOKED!!!!!!!!!!!!!!!!!!! #-}

-- Should print the text after IMPOSSIBLE and then raise an internal error.
