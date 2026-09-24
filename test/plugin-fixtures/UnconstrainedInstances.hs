{-# LANGUAGE ConstraintKinds, FlexibleContexts, GADTs, TypeFamilies, TypeOperators #-}
module UnconstrainedInstances where

import Linear.Logic

data Dict c where
  Dict :: c => Dict c

-- This module is compiled without the plugin. These instances must no
-- longer ask their callers for double-negation evidence.
ur :: Dict (Prop (Ur a))
ur = Dict

whyNot :: Dict (Prop (WhyNot a))
whyNot = Dict

tensor :: Prop a => Dict (Prop (a, b))
tensor = Dict

par :: Prop a => Dict (Prop (a ⅋ b))
par = Dict

lol :: Prop b => Dict (Prop (a ⊸ b))
lol = Dict

apart :: Prop b => Dict (Prop (b <#- a))
apart = Dict
