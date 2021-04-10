{-# language CPP #-}
{-# language BlockArguments #-}
{-# language DefaultSignatures #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language ImportQualifiedPost #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language LinearTypes #-}
{-# language NoImplicitPrelude #-}
{-# language NoStarIsType #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language StandaloneKindSignatures #-}
{-# language StrictData #-}
{-# language TupleSections #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeFamilyDependencies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language ImportQualifiedPost #-}
{-# language Trustworthy #-}
{-# options_ghc -fplugin Linear.Logic.Plugin #-}

-- {-# options_ghc -Wno-unused-imports #-}

module Linear.Logic.James where

import Linear.Logic.Functor
import Linear.Logic
import Prelude.Linear ((&))

james :: (Prop' b, Lol l, Lol l') => l (Ur (a ⊸ b)) (l' (Ur a) b)
james = lol \case
  R -> \(Ur a2b) -> lol \case
    R -> \(Ur a) -> fun' a2b a
    L -> \nb -> whyNot \a -> fun' a2b a != nb
  L -> \nf -> apartR nf & \(Ur a :-#> nb) -> whyNot \a2b -> fun' a2b a != nb

