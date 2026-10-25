import Lake
open Lake DSL
package «lean-formalizations» where
  version := v!"0.1.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "a4c8ef0a69f52ec80525d5086bb3542f4660faaf"
lean_lib MeshOnly
lean_lib BouRabeeGwynne
lean_lib ReflectedWalk
lean_lib ReflectedGMS
lean_lib LQGDimension
lean_lib QuantumZipper
lean_lib LQGMetric
lean_lib MeshRates
lean_lib GaussianLQG
lean_lib HigherDimLFPP
lean_lib SmallGammaGeodesics
lean_lib HigherDimLQGMetric
lean_lib HigherDimLQGContinuity
@[default_target]
lean_lib Certificate

lean_lib SupercriticalLQGUniqueness
lean_lib SLUSupport
lean_lib SLUMetricAPI
lean_lib SLUMetricAPI2
lean_lib SLUFieldSupport
lean_lib BR1Bridges
lean_lib NV1Evidence
