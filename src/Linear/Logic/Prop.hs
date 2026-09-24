{-# language LinearTypes #-}
{-# language NoImplicitPrelude #-}
{-# language RankNTypes #-}
{-# language Safe #-}
{-# language TypeFamilyDependencies #-}

-- | Propositions and their refutation types. Kept separate from the
-- connectives so their definitions can use the typechecker plugin.
module Linear.Logic.Prop (Prop(..)) where

-- | Propositions with a specified refutation type.
--
-- With @-fplugin Linear.Logic.Plugin@, a given @Prop a@ also supplies
-- @Prop (Not a)@ by exchanging the two refutation methods. This is a plugin
-- rule rather than a recursive superclass.
class Prop a where
  -- | \(a^\bot\). The type of refutations of \(a\)
  --
  -- \(a^{\bot^\bot} \) = \(a\)
  type Not a = c | c -> a
  -- | \(a\) and \(a^\bot\) together yield a contradiction.
  --
  -- @
  -- ('!=') :: a %1 -> 'Not' a %1 -> r
  -- @
  (!=) :: a %1 -> Not a %1 -> r
  a != na = na =! a

  -- | Refute with the arguments exchanged. Keeping both methods in the
  -- dictionary lets the plugin dualize by swapping fields, without building
  -- another flip closure at each step.
  (=!) :: Not a %1 -> a %1 -> r
  na =! a = a != na

  {-# minimal (!=) | (=!) #-}
