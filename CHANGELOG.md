# Changelog

## Unreleased

- Remove Prep and the equality superclass of Prop. Separate the class into
  Linear.Logic.Prop so the core instances can also use the plugin, and drop
  their double-negation constraints.
- Replace the experimental plugin with involution rewriting, scoped dual
  dictionary synthesis, and evidence-backed inverse type inference.
- Rename the Prop' class to Prop and remove the two-dictionary Prop synonym.
  Add the (=!) method so dualization swaps existing dictionary slots.
- Build the plugin in an internal sublibrary and use it in the library's
  higher-level modules; remove their explicit Prep requirements and remove
  UndecidableSuperClasses. The rewriter requires GHC 9.4 or later.
- Exercise plugin evidence with Core Lint, HUnit runtime tests, and compiler
  acceptance/rejection tests.
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
