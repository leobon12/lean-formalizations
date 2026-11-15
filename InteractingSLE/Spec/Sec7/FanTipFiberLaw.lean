/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FanTipFiber
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal
import Mathlib.Probability.Process.Stopping

/-!
# Aux. lemma 135: a singleton active tip fibre at an original stopping time

Packet PROVE-SEC7-E (specification §7.5, `source/spec/p433-480.md` L121–L151, pp. 439–441).

**Aux. lemma 135.** Let `κ' > 4` and let `η'` be a continuous chordal Loewner trace driven, in
half-plane capacity time, by `dW_t = √κ' dB_t + b_t dt`. Assume that after every positive deterministic
time `a` the driver law up to each finite stopping time under consideration is locally mutually
absolutely continuous with respect to `√κ'` times Brownian motion started at `W_a`. Let `T ≥ 0` be a
finite stopping time. Then almost surely on `{T > 0, η'(T) ∈ ℍ}`, `f_T⁻¹({η'(T)}) = {W_T}` (TS1).

## Formal statement

`ae_isSingletonTipFiber_of_isLocallyBrownianAfter`: for a filtration `𝓕`, an `𝓕`-stopping time `T`
(finite, `T : Ω → ℝ≥0`), a driver `W` with almost surely continuous paths, `W_0 = 0`, generating almost
surely the continuous Loewner trace `η`, and the local Brownian hypothesis
`IsLocallyBrownianAfter κ' 𝓕 P W a T` at every positive rational `a`, almost surely
`0 < T → η(T) ∈ ℍ → IsSingletonTipFiber W T`.

* **The local absolute-continuity hypothesis** (`IsLocallyBrownianAfter`) is stated in the form in which
  the proof uses it ("Girsanov's theorem gives a strictly positive Radon–Nikodym derivative in both
  directions between this stopped driver law and the ordinary Brownian driver law"): there are
  localizing `𝓕_{a+·}`-stopping times `σ_n` exhausting `{T > a}` up to `T − a` and probability measures
  `Q_n` with `P ≪ Q_n` such that, `P`-almost surely, `W_{a+t} − W_a = √κ' β^n_t` for `t ≤ σ_n`, `β^n` an
  `𝓕_{a+·}`-Brownian motion. Only `P ≪ Q_n` is used (the source assumes mutual absolute continuity).
  The source's sufficient condition (progressive drift of finite energy, with bounded-energy
  localizations) produces exactly this by Girsanov's theorem (`InteractingSLE.Girsanov`); that
  derivation is not part of this file.
* **The external input** `ZhanStoppingTipFiberStatement κ'` is [Zha10, Theorem 6.1, proof of
  (iii)–(iv)] as the specification uses it ("This proves (TS1) for ordinary `SLE_κ'` at any
  original-filtration stopping time"), in the filtration form needed by the conditioning step ("condition
  on the original history up to `a` … The first part then applies at the stopped time `T − a`"): for a
  Brownian motion `β` of a filtration `𝓖` and a `𝓖`-stopping time `τ`, almost surely on `{0 < τ < ∞}`
  with an interior tip, the chain driven by `√κ' β` has a singleton tip fibre at `τ`. It is not
  formalized in this project (EXT-INV `EXT-Zha10-Thm6.1`) and is a hypothesis of the theorem.
* The source's first reduction ("apply the positive-time statement at `T ∨ (1/j)`") is not needed: the
  composition argument below is eventwise on `{T > 0}`.

## Proof

Fix a positive rational `a`. On `{T > a}` the future driver `W(a + ·) − W(a)` agrees with `√κ' β^n` up
to `T − a` on `{T − a ≤ σ_n}`; the fibre at time `T − a` only depends on the driver on `[0, T − a]`
(`isSingletonTipFiber_congr`), the input applies to the `𝓖`-stopping time `(T − a) ∧ σ_n` under `Q_n`,
and `P ≪ Q_n` transfers the null set (`ae_shift_isSingletonTipFiber`). The deterministic composition
`f_T = f_a ∘ f^{(a)}_{T−a}` at a rational `a` before the first visit of the interior tip
(`IsLoewnerTrace.isSingletonTipFiber_of_forall_rat`, `FanTipFiber.lean`) concludes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H drive)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Sec7

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The real-time path `s ↦ W_{s⁺}(ω)` of a process indexed by `ℝ≥0` (the Loewner driver as a function
on `ℝ`, as in `IsGeneratingTrace`). -/
def realPath (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun s => W s.toNNReal ω

theorem continuous_realPath {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : Continuous fun t : ℝ≥0 => W t ω) :
    Continuous (realPath W ω) :=
  h.comp continuous_real_toNNReal

theorem realPath_zero {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : W 0 ω = 0) : realPath W ω 0 = 0 := by
  simp [realPath, h]

/-- The shifted filtration `t ↦ 𝓕_{a+t}`. -/
def shiftFiltration (𝓕 : Filtration ℝ≥0 mΩ) (a : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (a + t)
  mono' _ _ hst := 𝓕.mono (add_le_add_right hst a)
  le' t := 𝓕.le (a + t)

/-- `T − a` (truncated) is a stopping time of the shifted filtration. -/
theorem isStoppingTime_tsub {𝓕 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (a : ℝ≥0) :
    IsStoppingTime (shiftFiltration 𝓕 a) fun ω => ((T ω - a : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  have h := hT (a + t)
  have heq : {ω | ((T ω - a : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {ω | (T ω : WithTop ℝ≥0) ≤ ((a + t : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, tsub_le_iff_right, add_comm t a]
  rw [heq]
  exact h

/-! ### The named external input -/

/-- **[Zha10, Theorem 6.1, proof of (iii)–(iv)]** for ordinary chordal `SLE_κ'` (named external input,
EXT-INV `EXT-Zha10-Thm6.1`; not formalized). For every Brownian motion `β` of a filtration `𝓖` and every
`𝓖`-stopping time `τ`, almost surely, if `0 < τ < ∞` and the tip of the chain driven by `√κ' β` is
interior at time `τ`, then that chain has a singleton tip fibre at `τ` ((TS1) for ordinary `SLE_κ'`).
The specification uses it for `κ' > 4` (for `κ' ≤ 4` the trace is simple). -/
def ZhanStoppingTipFiberStatement (κ' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0),
    IsFilteredBrownianReal 𝓖 β Q → IsStoppingTime 𝓖 τ →
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, τ ω = t → 0 < t → loewnerTip (drive κ' β ω) t ∈ H →
      IsSingletonTipFiber (drive κ' β ω) t

/-! ### The local absolute-continuity hypothesis of Aux. lemma 135 -/

/-- **Aux. 135's hypothesis after the positive time `a`, for the stopping time `T`**, in the
change-of-measure form produced by Girsanov's theorem: there are probability measures `Q n` with
`P ≪ Q n`, `𝓕_{a+·}`-Brownian motions `β n` under `Q n` and `𝓕_{a+·}`-stopping times `σ n` such that
`P`-almost surely `W_{a+t} − W_a = √κ' β^n_t` for `t ≤ σ_n`, and almost surely on `{T > a}` some
`σ_n` reaches `T − a`
("the driver law up to each finite stopping time under consideration is locally mutually absolutely
continuous with respect to `√κ'` times Brownian motion started at `W_a`"). -/
def IsLocallyBrownianAfter (κ' : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (a : ℝ≥0) (T : Ω → ℝ≥0) : Prop :=
  ∃ (Q : ℕ → Measure Ω) (β : ℕ → ℝ≥0 → Ω → ℝ) (σ : ℕ → Ω → WithTop ℝ≥0),
    (∀ n, IsProbabilityMeasure (Q n)) ∧ (∀ n, P ≪ Q n) ∧
    (∀ n, IsFilteredBrownianReal (shiftFiltration 𝓕 a) (β n) (Q n)) ∧
    (∀ n, IsStoppingTime (shiftFiltration 𝓕 a) (σ n)) ∧
    (∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ σ n ω →
      W (a + t) ω - W a ω = Real.sqrt κ' * β n t ω) ∧
    (∀ᵐ ω ∂P, a < T ω → ∃ n, ((T ω - a : ℝ≥0) : WithTop ℝ≥0) ≤ σ n ω)

/-! ### The future chain after a positive time `a` -/

/-- On `[0, u]` with `u ≤ σ_n`, the future driver `W(a + ·) − W(a)` is `√κ' β^n`. -/
theorem shiftDrive_realPath_eqOn {κ' : ℝ} {W : ℝ≥0 → Ω → ℝ} {β : ℝ≥0 → Ω → ℝ}
    {σ : Ω → WithTop ℝ≥0} {a : ℝ≥0} {ω : Ω}
    (hagree : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ σ ω → W (a + t) ω - W a ω = Real.sqrt κ' * β t ω)
    {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ σ ω) :
    EqOn (shiftDrive (realPath W ω) a) (drive κ' β ω) (Icc 0 u) := by
  intro r hr
  have hrle : r.toNNReal ≤ u := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have h := hagree r.toNNReal ((WithTop.coe_le_coe.2 hrle).trans hu)
  simp only [shiftDrive, realPath, drive]
  rw [Real.toNNReal_add a.coe_nonneg hr.1, Real.toNNReal_coe]
  exact h

/-- **Aux. 135, the conditional step** (p. 440: "On `{T > a}`, the mapped future curve in `D_a`,
translated so that its seed is zero, is driven by `W_{a+t} − W_a` … Increasing the localizations
transfers the singleton-fiber conclusion to the mapped future on the event that its tip is
interior"). Under the local Brownian hypothesis after `a`, almost surely on `{T > a}`, if the future
chain has an interior tip at time `T − a`, it has a singleton tip fibre there. -/
theorem ae_shift_isSingletonTipFiber {κ' : ℝ} (hZ : ZhanStoppingTipFiberStatement.{u} κ')
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}
    (hWc : ∀ᵐ ω ∂P, Continuous fun t : ℝ≥0 => W t ω)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {a : ℝ≥0}
    (hloc : IsLocallyBrownianAfter κ' 𝓕 P W a T) :
    ∀ᵐ ω ∂P, a < T ω →
      loewnerTip (shiftDrive (realPath W ω) a) ((T ω : ℝ) - a) ∈ H →
      IsSingletonTipFiber (shiftDrive (realPath W ω) a) ((T ω : ℝ) - a) := by
  obtain ⟨Q, β, σ, hQ, hPQ, hβ, hσ, hagree, hcover⟩ := hloc
  have hZn : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      min ((T ω - a : ℝ≥0) : WithTop ℝ≥0) (σ n ω) = t → 0 < t →
      loewnerTip (drive κ' (β n) ω) t ∈ H → IsSingletonTipFiber (drive κ' (β n) ω) t := fun n =>
    (hPQ n).ae_le (@hZ Ω mΩ (Q n) (hQ n) (shiftFiltration 𝓕 a) (β n) _ (hβ n)
      ((isStoppingTime_tsub hT a).min (hσ n)))
  have hβc : ∀ n, ∀ᵐ ω ∂P, Continuous fun t : ℝ≥0 => β n t ω := fun n =>
    (hPQ n).ae_le (hβ n).1.cont
  filter_upwards [hcover, hWc, ae_all_iff.2 hZn, ae_all_iff.2 hβc, ae_all_iff.2 hagree]
    with ω hcov hc hZω hβω hagω haT htip
  obtain ⟨n, hn⟩ := hcov haT
  set v : ℝ≥0 := T ω - a with hv
  have hTa : (T ω : ℝ) - a = (v : ℝ) := by rw [hv, NNReal.coe_sub haT.le]
  rw [hTa] at htip ⊢
  have hEq := shiftDrive_realPath_eqOn (hagω n) hn
  have hV := QuantumZipper.RS.continuous_shiftDrive (continuous_realPath hc) (a : ℝ)
  have hV0 : shiftDrive (realPath W ω) a 0 = 0 := shiftDrive_zero _ _
  have hD := QuantumZipper.drive_continuous (κ := κ') (hβω n)
  have hD0 : drive κ' (β n) ω 0 = 0 := by
    rw [← hEq ⟨le_rfl, v.coe_nonneg⟩, hV0]
  rw [isSingletonTipFiber_congr hV hV0 hD hD0 v.coe_nonneg hEq]
  rw [loewnerTip_congr hV hV0 hD hD0 v.coe_nonneg hEq] at htip
  exact hZω n v (min_eq_left hn) (tsub_pos_of_lt haT) htip

/-! ### Aux. lemma 135 -/

/-- **Aux. lemma 135** (a singleton active tip fibre at an original stopping time). Let `η` be almost
surely a continuous Loewner trace of the driver `W` (paths almost surely continuous, `W_0 = 0`), `T` a
finite `𝓕`-stopping time, and assume the local Brownian hypothesis of Aux. 135 after every positive
rational time. Then, given the external input [Zha10, Theorem 6.1 (iii)–(iv)], almost surely on
`{T > 0, η(T) ∈ ℍ}` the chain has a singleton tip fibre at `T`: `f_T⁻¹({η(T)}) = {W_T}` (TS1). The
tip may have been visited earlier. -/
theorem ae_isSingletonTipFiber_of_isLocallyBrownianAfter {κ' : ℝ}
    (hZ : ZhanStoppingTipFiberStatement.{u} κ') {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ} {T : Ω → ℝ≥0}
    (hWc : ∀ᵐ ω ∂P, Continuous fun t : ℝ≥0 => W t ω) (hW0 : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hη : ∀ᵐ ω ∂P, IsLoewnerTrace (realPath W ω) (η ω))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hloc : ∀ a : ℚ, 0 < a → IsLocallyBrownianAfter κ' 𝓕 P W (a : ℝ).toNNReal T) :
    ∀ᵐ ω ∂P, 0 < T ω → η ω (T ω) ∈ H → IsSingletonTipFiber (realPath W ω) (T ω) := by
  have hshift : ∀ a : ℚ, ∀ᵐ ω ∂P, 0 < a → (a : ℝ).toNNReal < T ω →
      loewnerTip (shiftDrive (realPath W ω) (a : ℝ).toNNReal) ((T ω : ℝ) - (a : ℝ).toNNReal) ∈ H →
      IsSingletonTipFiber (shiftDrive (realPath W ω) (a : ℝ).toNNReal)
        ((T ω : ℝ) - (a : ℝ).toNNReal) := by
    intro a
    by_cases ha : 0 < a
    · filter_upwards [ae_shift_isSingletonTipFiber hZ hWc hT (hloc a ha)] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h ha
  filter_upwards [hη, hWc, hW0, ae_all_iff.2 hshift] with ω hηω hc h0 hsh hT0 hpH
  have hT0' : (0 : ℝ) < T ω := by exact_mod_cast hT0
  refine hηω.isSingletonTipFiber_of_forall_rat (continuous_realPath hc) (realPath_zero h0) hT0' hpH
    fun a ha0 haT hpa => ?_
  have haa : (((a : ℝ).toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal _ ha0.le
  have haT' : (a : ℝ).toNNReal < T ω := by
    rw [← NNReal.coe_lt_coe, haa]; exact haT
  have hsum : (a : ℝ) + ((T ω : ℝ) - a) = T ω := by ring
  obtain ⟨hξ, -⟩ := hηω.shift_tip_mem_H (continuous_realPath hc) (realPath_zero h0) ha0.le
    (sub_nonneg.2 haT.le) (by rw [hsum]; exact hpH) (by rw [hsum]; exact hpa)
  have h := hsh a (by exact_mod_cast ha0) haT' (by rw [haa]; exact hξ)
  rwa [haa] at h

end Sec7

end InteractingSLE
