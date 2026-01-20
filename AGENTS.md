# Agent Rules

- Prefer `import Foo qualified as Bar` over `import qualified Foo as Bar` for visual consistency (enable `ImportQualifiedPost` as needed).
- Leave macOS `ld` duplicate `-lm` warnings alone (they are benign and come from toolchain flags).
- Use HUnit for tests
