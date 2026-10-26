# Public extract of the probe of the hypothesis ξ > ξ_crit

A Lean metaprogram followed the compiled proof of the sealed Theorem 1.1, from the frozen root through the values of all project constants, and reported every place where the hypothesis `hξ : xiCrit < ξ` or any fact about `xiCrit` is used (ruling A23). Its verdict line is `XI: UNUSED`. On this evidence the supporting theorem `Root.conformal_covariance_all_xi` states Theorem 1.1 without the hypothesis; the released `Check.lean` checks that it implies the frozen theorem and that the two types differ exactly by that binder. The probe files and their full outputs (`XITrace.out` and the copy without the hypothesis) are kept in the development record. Source: development audit file, SHA-256 `e8fd8e708868a826ffe3455d90d8aae5b8fd019093ff28dea99fab2bd1c69bd9`.

## Decision

The sealed root's `hξ : xiCrit < (ξ : ℝ)` has no substantive use. In the compiled proof, it is forwarded through seven root/provider binders, then passed to four input slots in `Root.conformal_covariance_of_inputs`. The proof terms supplying all four slots ignore that binder. `P43Final.prop43_input_slot` also ignores it. No result about `xiCrit`, including its `sInf` definition, is invoked to derive a mathematical fact.

A copy of the root assembly and provider statement with the threshold hypothesis deleted kernel-checks for every `ξ : Set.Ioi (0 : ℝ)` using the same proved inputs. The exact frozen `by exact ...conformal_covariance_impl` cannot itself prove that stronger type, since the compiled provider still requires `hξ`; a new generalized declaration can use the existing input theorems and the copied assembly without any new mathematical lemma. The frozen statement was not changed.

## Proof-term flow

The metaprogram starts at the frozen root, recursively follows values of project constants (including opaque theorem values), and reports every type containing `xiCrit`. There are 1,599 project constants in this value closure and nine `xiCrit`-typed constants; eight are in the provider subclosure. The threshold flow is:

```text
Frozen.conformal_covariance #2
  -> Implementation.conformal_covariance_impl #2
  -> Root.conformal_covariance_of_prop43 #3
  -> Root.conformal_covariance_of_two_inputs #4
  -> Root.conformal_covariance_of_three_inputs #5
  -> Root.conformal_covariance_of_four_inputs #6
  -> Root.conformal_covariance_closed #7
  -> Root.conformal_covariance_of_inputs #7
       -> hTight arg#2 -> adapter in of_two_inputs: DROP
       -> hGEL   arg#2 -> adapter in of_three_inputs: DROP
       -> hP43   arg#2 -> P43Final.prop43_input_slot: DROP
       -> hL51   arg#2 -> adapter in of_prop43: DROP
```

The threshold binder of `P43Final.prop43_input_slot` itself is `DROP`. The other `xiCrit` occurrences in compiled values are lambda/forall type annotations: `XI-VALUE-POSITIONS` reports `term=0` in each of the seven values containing the constant. Thus there is no use of an `xiCrit` fact or a lemma about `sInf` along the proof path. The `xiCrit` definition is `sInf {x : ℝ | ∃ hx : 0 < x, IsLFPPExponent ⟨x, hx⟩ 2}`; it is present as the type of the discarded assumption, and its value is never unfolded in this proof.

| Constant whose type mentions `xiCrit` | Module | Threshold binder |
| --- | --- | --- |
| `SupercriticalConformalCovariance.conformal_covariance` | `SupercriticalConformalCovariance.Frozen.ConformalCovariance` | #2, forwards to provider |
| `SupercriticalConformalCovariance.Implementation.conformal_covariance_impl` | `SupercriticalConformalCovariance.Implementation.ConformalCovariance` | #2, forwards to `of_prop43` |
| `SupercriticalConformalCovariance.P43Final.prop43_input_slot` | `SupercriticalConformalCovariance.P43Final.Closed` | #2, dropped |
| `SupercriticalConformalCovariance.Root.conformal_covariance_of_prop43` | `SupercriticalConformalCovariance.Root.LocalDischarge` | #3, forwards to `of_two_inputs` |
| `SupercriticalConformalCovariance.Root.conformal_covariance_of_two_inputs` | `SupercriticalConformalCovariance.Root.LocalDischarge` | #4, forwards to `of_three_inputs` |
| `SupercriticalConformalCovariance.Root.conformal_covariance_of_three_inputs` | `SupercriticalConformalCovariance.Root.LocalDischarge` | #5, forwards to `of_four_inputs` |
| `SupercriticalConformalCovariance.Root.conformal_covariance_of_four_inputs` | `SupercriticalConformalCovariance.Root.GPullDischarge` | #6, forwards to `conformal_covariance_closed` |
| `SupercriticalConformalCovariance.Root.conformal_covariance_closed` | `SupercriticalConformalCovariance.Root.Assembly` | #7, forwards to `of_inputs` |
| `SupercriticalConformalCovariance.Root.conformal_covariance_of_inputs` | `SupercriticalConformalCovariance.Root.Assembly` | #7, four slot applications only |

Each `Root` wrapper also binds one or more higher-order input slots whose types mention `xiCrit`; `XITrace.out` lists the slot binders and their forwarding edges. The nested `INNER-XI-LAMBDA: DROP` lines identify the slot adapters. `of_inputs` reports its own `INNER-XI-LAMBDA hξ: USED` because it passes the proof to those four slots; that is forwarding, not a terminal mathematical use.
