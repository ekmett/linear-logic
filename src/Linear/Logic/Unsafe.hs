{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE Unsafe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Linear.Logic.Unsafe
( toLinear
, unsafePar
) where
 
import Linear.Logic
import Unsafe.Linear (toLinear)

-- | When developing proofs it is often handy to lie about multiplicity,
-- while you are still filling in holes. This enables that workflow.
-- When you are done, you can convert from 'unsafePar' back to 'par'
--
-- 'toLinear' can also come in handy temporarily during this
-- process.
unsafePar :: (forall c. Y (Not b -> a) (Not a -> b) c -> c) %1 -> a ⅋ b
unsafePar f = par \case
  L -> toLinear (f L)
  R -> toLinear (f R)
