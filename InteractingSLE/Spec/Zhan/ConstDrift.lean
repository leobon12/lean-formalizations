/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftUpper
import InteractingSLE.Spec.Zhan.StripEndpointFinal

/-!
# Constant strip drift `|σ| < 1`: the reduction of `ConstDriftEndpointStatement`

Packet PROVE-ZHAN-A5. Astra, *Formalization proofs and dependency audit* (ruling R35), "Constant drift with
`|σ| < 1`: from the diffusion to the actual trace" (`source/external/AstraIG1/ig1_formalization_proofs.txt`
L1420–L1499). PROVE-ZHAN-A4's named input `ConstDriftEndpointStatement κ` (`StripDrift.lean`) is reduced here to
three named statements, each one step of the source proof:

* `ConstDriftTraceStatement κ` — the strip path of a constant-drift strip driver has a continuous generating trace on
  its strip life (the source's "noncircular source of the simple continuous strip prefixes", L1336–L1347: bounded-drift
  Girsanov on finite strip-time intervals);
* `UpperGapStatement κ` — the upper-point diffusion (3.15) `dX = −√κ dB + (tanh(X/2) − σ) dt` started at any rational
  point satisfies `∫₀^∞ sech²(X/2) < ∞`, i.e. the derivative (3.23) `A = ψ'(x + iπ)` stays bounded (the source's
  "earlier scale calculation", L1441–L1450: `s(X)` is a bounded martingale, `X → ±∞`, then `X_t/t → ±1 − σ`);
* `ConstDriftHeightStatement κ` — the strip height `arg(1 + η)` of the trace tends to `π` (the source's elimination of
  the interior terminal cluster points, L1471–L1499, the resampling argument with the extremal-length bounds).

Everything else is proved: the bounded hull (`ConstDriftHull.lean`), Koebe at the upper points and the derivative
identity (3.23) in integrated form (`ConstDriftKoebe.lean`, `ConstDriftUpper.lean`), and the topological endpoint
argument (`ConstDriftCluster.lean`).

## Main results

* `abs_stripDriver_le_of_sublinear`: Brownian sublinearity gives `|ξ_t| ≤ C + at` with `|σ| < a < 1`;
* `constDriftEndpointStatement_of_trace_upper_height` (**conditional helper**):
  `ConstDriftTraceStatement κ → UpperGapStatement κ → ConstDriftHeightStatement κ →
  ConstDriftEndpointStatement κ`;
* `stripEndpointStatement_of_trace_upper_height`: with PROVE-ZHAN-A4's whole-tail Girsanov step, the strip endpoint
  theorem `StripEndpointStatement κ` from the same three statements.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

universe u

namespace InteractingSLE

namespace Zhan

open Strip

/-! ### The three named statements -/

/-- **Named statement (trace).** For `|σ| < 1` and every filtered Brownian motion `β`, almost surely every strip path
whose strip driver is `√κ β_t + σ t` has a continuous generating chordal trace on its strip life (Astra L1336–L1347:
"Bounded-drift Girsanov on each finite interval removes its upper drift and inserts any prescribed constant drift.
The resulting constant-drift strip prefixes are continuous and simple"). -/
def ConstDriftTraceStatement (κ : ℝ) : Prop :=
  ∀ σ : ℝ, |σ| < 1 → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ)
    (β : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 β P →
      ∀ᵐ ω ∂P, ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞),
        HasStripDriver w v ζ (fun t => Real.sqrt κ * β t ω + σ * t) →
          ∃ η : ℝ≥0 → ℂ, ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η

/-- **Named statement (upper-point derivative bound).** For `|σ| < 1` and every filtered Brownian motion `β`, almost
surely, for every rational `q`, the solutions of the upper-gap equation (3.15)
`X_t = q − ξ_t + ∫₀ᵗ tanh(X_u/2) du`, `ξ_t = √κ β_t + σ t`, have a uniformly bounded integral
`∫₀ᵀ 1/(1 + cosh X) = ½∫₀ᵀ sech²(X/2)` on every horizon `T`: the derivative `A_t = exp(½∫₀ᵗ sech²(X/2))` of (3.23)
stays bounded. (Astra L1441–L1450: the scale function makes `X → ±∞`, and then `X_t/t → ±1 − σ`; the scale density
is `scaleDensity`, `UpperPoint.lean`.) -/
def UpperGapStatement (κ : ℝ) : Prop :=
  ∀ σ : ℝ, |σ| < 1 → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ)
    (β : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 β P →
      ∀ᵐ ω ∂P, ∀ q : ℚ, ∃ K : ℝ,
        ∀ T : ℝ, 0 ≤ T → ∀ X : ℝ → ℝ, ContinuousOn X (Icc 0 T) →
          (∀ t ∈ Icc 0 T, X t = q - (Real.sqrt κ * β t.toNNReal ω + σ * t) +
            ∫ r in (0 : ℝ)..t, Real.tanh (X r / 2)) →
          ∫ r in (0 : ℝ)..T, 1 / (1 + Real.cosh (X r)) ≤ K

/-- **Named statement (height).** For `|σ| < 1` and every filtered Brownian motion `β`, almost surely, for every strip
path whose strip driver is `√κ β_t + σ t` and every generating trace `η` on its strip life, the strip height
`arg(1 + η)` tends to `π` along the strip life: the terminal cluster set lies on the upper line (Astra L1471–L1499,
"Eliminate all other terminal cluster points"). -/
def ConstDriftHeightStatement (κ : ℝ) : Prop :=
  ∀ σ : ℝ, |σ| < 1 → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ)
    (β : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 β P →
      ∀ᵐ ω ∂P, ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (η : ℝ≥0 → ℂ),
        HasStripDriver w v ζ (fun t => Real.sqrt κ * β t ω + σ * t) →
          (∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) →
            ∀ ε > 0, EvLife w v ζ fun s => Real.pi - ε < arg (1 + η s)

/-! ### Sublinearity of the strip driver -/

/-- `b ≤ (e^R − 1)/(e^R + 1)` for `R = log((1 + b)/(1 − b)) > 0`, `0 < b < 1`. -/
theorem le_tanh_half_log (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    0 < Real.log ((1 + b) / (1 - b)) ∧
      b ≤ (Real.exp (Real.log ((1 + b) / (1 - b))) - 1) / (Real.exp (Real.log ((1 + b) / (1 - b))) + 1) := by
  have h1 : 0 < 1 - b := by linarith
  have hq : 1 ≤ (1 + b) / (1 - b) := by rw [le_div_iff₀ h1]; linarith
  refine ⟨Real.log_pos (by rw [lt_div_iff₀ h1]; linarith), ?_⟩
  · rw [Real.exp_log (by linarith)]
    rw [le_div_iff₀ (by linarith)]
    field_simp
    nlinarith

/-- **Brownian sublinearity of the strip driver.** If `β` has continuous paths and `β_t/t → 0`, then for
`|σ| < a` there is `C` with `|√κ β_t + σ t| ≤ C + a t` for all `t ≥ 0`. -/
theorem abs_driver_le_of_sublinear {κ σ a : ℝ} (hσa : |σ| < a) {f : ℝ≥0 → ℝ} (hc : Continuous f)
    (hf : Tendsto (fun t : ℝ≥0 => f t / (t : ℝ)) atTop (𝓝 0)) :
    ∃ C, ∀ t : ℝ≥0, |Real.sqrt κ * f t + σ * t| ≤ C + a * t := by
  obtain ⟨C, hC⟩ := sublinear_of_tendsto hc hf (Real.sqrt κ) (a - |σ|) (by linarith)
  refine ⟨C, fun t => ?_⟩
  have h1 := hC t t.2
  rw [Real.toNNReal_coe] at h1
  calc |Real.sqrt κ * f t + σ * t| ≤ |Real.sqrt κ * f t| + |σ * t| := abs_add_le _ _
    _ ≤ (C + (a - |σ|) * t) + |σ| * t := by
        have e : |σ * (t : ℝ)| = |σ| * t := by rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg t)]
        linarith
    _ = C + a * t := by ring

variable {κ : ℝ}

/-- **The constant-drift endpoint theorem from the three named statements** (conditional helper). -/
theorem constDriftEndpointStatement_of_trace_upper_height
    (hT : ConstDriftTraceStatement.{u} κ) (hU : UpperGapStatement.{u} κ)
    (hH : ConstDriftHeightStatement.{u} κ) : ConstDriftEndpointStatement.{u} κ := by
  intro σ hσ Ω mΩ P 𝓗 β hβ
  filter_upwards [hT σ hσ P 𝓗 β hβ, hU σ hσ P 𝓗 β hβ, hH σ hσ P 𝓗 β hβ, hβ.1.cont,
    hβ.1.tendsto_div_id_atTop] with ω htr hup hht hc hlaw
  intro w v ζ hd
  have h := hd.1
  have hξ := hd.2
  -- sublinearity and the bounded hull
  set a := (|σ| + 1) / 2 with ha
  have hσa : |σ| < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  set b := (a + 1) / 2 with hb
  have hb0 : 0 < b := by rw [hb]; linarith [abs_nonneg σ]
  have hb1 : b < 1 := by rw [hb]; linarith
  have hab : a ≤ b := by rw [hb]; linarith
  obtain ⟨hR, hbR⟩ := le_tanh_half_log b hb0 hb1
  set R := Real.log ((1 + b) / (1 - b)) with hRdef
  obtain ⟨C, hC⟩ := abs_driver_le_of_sublinear (κ := κ) hσa hc hlaw
  have hξC : ∀ t : ℝ≥0, |stripDriver (extPath w) (extPath v) t| ≤ C + a * t := fun t => by
    rw [hξ t]; exact hC t
  refine hasStripEndpoint_of_stripConv h (htr w v ζ hd) fun η hη => ?_
  refine h.stripConv_of_height hη (M := C + R) (fun s hs => ?_) (hht w v ζ η hd hη) fun q => ?_
  · have := h.norm_one_add_trace_mem_Icc hR hbR hab hξC hη hs
    simpa using this
  -- the rational upper points
  have hy : -1 - Real.exp q < -1 := by linarith [Real.exp_pos (q : ℝ)]
  have hlog : Real.log (-1 - (-1 - Real.exp q)) = q := by
    rw [show -1 - (-1 - Real.exp (q : ℝ)) = Real.exp q by ring, Real.log_exp]
  obtain ⟨K, hK⟩ := hup q
  refine h.exists_pos_le_norm_trace_sub_sech hη hy (K := K) fun s' s'' hs's'' hs'' uy huy => ?_
  rw [h.integral_sech_eq_upperGap hy hs's'' hs'' huy]
  refine hK _ (((h.2.1 s' (hs''.mono hs's''.le))).stripClock_nonneg ⟨NNReal.coe_nonneg s', le_rfl⟩)
    _ (h.continuousOn_upperGapOf hy hs's'' hs'' huy) fun t ht => ?_
  rw [h.upperGapOf_ode hy hs's'' hs'' huy ht, hlog]
  congr 2
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have := hξ t.toNNReal
  simp only at this
  rw [Real.coe_toNNReal _ ht0] at this
  exact this

/-- **The strip endpoint theorem from the three named statements** (with PROVE-ZHAN-A4's whole-tail Girsanov
reduction `stripEndpointStatement_of_constDrift`). -/
theorem stripEndpointStatement_of_trace_upper_height (hκ : 0 < κ)
    (hT : ConstDriftTraceStatement.{u} κ) (hU : UpperGapStatement.{u} κ)
    (hH : ConstDriftHeightStatement.{u} κ) : StripEndpointStatement.{u} κ :=
  stripEndpointStatement_of_constDrift hκ (constDriftEndpointStatement_of_trace_upper_height hT hU hH)

end Zhan

end InteractingSLE
