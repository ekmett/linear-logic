linear-logic
============

[![Hackage](https://img.shields.io/hackage/v/linear-logic.svg)](https://hackage.haskell.org/package/linear-logic) [![Build Status](https://github.com/ekmett/linear-logic/workflows/Haskell-CI/badge.svg)](https://github.com/ekmett/linear-logic/actions?query=workflow%3AHaskell-CI)

This package encodes a version of intuitionistic linear logic on top of linear Haskell, using a variation of the 
technique described by Michael Shulman in [Linear Logic for Constructive Mathematics](https://arxiv.org/abs/1805.07518). Embedding a larger linear logic into the simple linear logic available to us in Linear Haskell means we are able to
recover the full suite of linear unitors, not just two of them, meaning we model linear logic, rather than affine logic.

The central idea is to track for each type not just its type of proofs, but also its type of refutations.

Building
--------

The library and its test suites build with GHC 9.14.1 and cabal-install 3.16:

```sh
cabal build all --enable-tests
cabal test all -fcore-lint --test-show-details=direct
cabal exec -- runghc -package=HUnit test/PluginRejections.hs
```

The plugin uses GHC's type-family rewriter API, available from GHC 9.4.

Plugin
------

Enable the plugin in modules that use the involution and dual-dictionary laws:

```haskell
{-# LANGUAGE LinearTypes, ScopedTypeVariables, TypeApplications, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Linear.Logic.Plugin #-}

import Linear.Logic

doubleNegation :: Not (Not a) %1 -> a
doubleNegation a = a

refuteDual :: forall a r. Prop a => Not a %1 -> a %1 -> r
refuteDual = (!=) @(Not a)
```

`Prop` is now the class previously named `Prop'`; the old two-dictionary
constraint synonym is gone. A single `Prop a` supplies dual evidence through
the plugin, without a recursive `Prop (Not a)` superclass or
`UndecidableSuperClasses`. `Prep` has been removed, including the equality
superclass of `Prop`. Enable the plugin wherever double-negation evidence is
needed; it is no longer carried in proposition dictionaries.

The class is defined in `Linear.Logic.Prop` and reexported through
`Linear.Logic.Internal` and `Linear.Logic`. Keeping the declaration separate
lets the core connectives and instances also use the plugin during compilation.

The dictionary stores `(!=)` and `(=!)`, with the law `a =! b = b != a`.
Dualization swaps these method fields and applies erased type coercions; it
does not introduce another runtime flip wrapper. An existing dual dictionary
in scope takes precedence. Instances may implement either method; the other
has a flipped default.

The plugin treats `Not (Not a) ~ a` as an axiom of the embedding and rewrites
it inside larger types. `Not` instances must respect that law. Dictionary
synthesis uses actual given evidence, including for compound propositions;
it does not invent dictionaries without a source. The indexed `IProp'`/`IProp`
API is unchanged.

The `core-lint` development flag checks the plugin and the generated evidence
in its tests. The tests exercise both method slots,
repeated dualization, and dictionary selection. The separate HUnit compiler
tests check rejection of false equalities, missing or unrelated dictionaries,
an unrelated family also called `Not`, and cyclic inference.

Full-library Core Lint also reports pre-existing failures in `contra''`,
`contraIso''`, `parL`, `parR`, and `dupUr`; these reproduce on the version
before the plugin replacement. The development flag therefore targets the
plugin and its evidence tests.

Contact Information
-------------------

Contributions and bug reports are welcome!

Please feel free to contact me through github or on the #haskell IRC channel on irc.libera.chat.

-Edward Kmett
