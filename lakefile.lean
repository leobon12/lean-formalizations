import Lake
open Lake DSL
package «lean-formalizations» where
  version := v!"0.1.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "a4c8ef0a69f52ec80525d5086bb3542f4660faaf"
lean_lib BouRabeeGwynne
lean_lib ReflectedWalk
lean_lib ReflectedGMS
lean_lib LQGDimension
lean_lib QuantumZipper
@[default_target]
lean_lib Certificate
