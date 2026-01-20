linear-logic
============

[![Hackage](https://img.shields.io/hackage/v/linear-logic.svg)](https://hackage.haskell.org/package/linear-logic) [![Build Status](https://github.com/ekmett/linear-logic/workflows/Haskell-CI/badge.svg)](https://github.com/ekmett/linear-logic/actions?query=workflow%3AHaskell-CI)

This package encodes a version of intuitionistic linear logic on top of linear Haskell, using a variation of the 
technique described by Michael Shulman in [Linear Logic for Constructive Mathematics](https://arxiv.org/abs/1805.07518). Embedding a larger linear logic into the simple linear logic available to us in Linear Haskell means we are able to
recover the full suite of linear unitors, not just two of them, meaning we model linear logic, rather than affine logic.

The central idea is to track for each type not just its type of proofs, but also its type of refutations.

Contact Information
-------------------

Contributions and bug reports are welcome!

Please feel free to contact me through github or on the #haskell IRC channel on irc.libera.chat.

-Edward Kmett
