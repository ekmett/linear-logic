# Changelog

## Unreleased

- Support GHC 9.14.1 and linear-base 0.8, including updated plugin APIs and
  explicit multiplicities in the linear-function Profunctor instance.
- Remove the ghc-tcplugins-extra dependency in favor of the GHC API directly.
- Test linear-function dimap and make HUnit failures fail the test executable.
- Fix the self-recursive weakDist default to delegate to dist.
- Fix plugin solver signature and guard legacy imports to avoid warnings.
- Add a logic-properties test suite (HUnit-based) covering basic With/Par laws.
- Document contributor conventions in AGENTS.md.

## 0.0.1

- Add version bounds and expand tested GHC versions.
- Add a plugin canary test module.
- Ignore Cabal and GHC build artifacts in .gitignore.
