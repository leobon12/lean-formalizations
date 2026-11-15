import InteractingSLE.Spec.Sec2.GirsanovSLE
import InteractingSLE.Spec.Dimension.Transfer

/-!
# Localized Girsanov comparison after a deterministic time (input (O1) of Aux. lemma 15)

Packet PROVE-T11-DU2. Specification, proof of Aux. lemma 15 (`source/spec/p049-096.md`, L868, p. 89): "For
every deterministic rational `a > 0` … condition on the driving history through `a` … Stop the future after
elapsed time `n` … or when a force gap becomes at most `1/n` … The additional driving drift is bounded by
`n ∑_j |ρ_j|`. Stopped Girsanov comparison therefore gives mutual absolute continuity with ordinary `SLE_κ` …
Complete the reference Brownian path independently after its cutoff."

Here the comparison is made through PROVE-SEC2-GIR's Girsanov theorem for a drift cut at a stopping time
(`Girsanov.girsanov_cutDrift`). With the cut reciprocal `r_δ` (`Girsanov.recipCut`, `= 1/x` for `|x| ≥ δ`) and
`θ = κ^{-1/2} ∑_j ρ_j r_δ(W − V_j)` cut at `τ = ζ ∧ (a + T)`, the process `B̂ = B + ∫ θ` is a Brownian motion
under an equivalent probability `Q`. Its increments after `a`, `X_t = B̂_{a+t} − B̂_a`, form a Brownian motion
under `Q` for all times (this is the "independent completion" of the reference path), so the law of `X` under
`P` is absolutely continuous with respect to a Brownian law. Whenever all gaps stay `≥ δ` on `[a, a + t]`
(`t ≤ T`, `a + t < ζ`), the drift of `W` on `[a, a + t]` is exactly `√κ θ`, hence `W_{a+t} − W_a = √κ X_t`.

No measurability of the gap event is needed: the identity holds pathwise on an almost sure event, and the
transfer of almost sure properties through `≪` (`ae_trace_good_of_absolutelyContinuous`) needs none either.

## Main results

* `sub_eq_sqrt_mul_sub_of_cut` (deterministic algebra);
* `exists_brownian_localization`: the localized comparison (O1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper QuantumZipper.RS InteractingSLE.Girsanov

/-- All force gaps at one time are at least `δ`. -/
def GapsGE {nL nR : ℕ} (δ w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : Prop :=
  (∀ i, δ ≤ |w - vL i|) ∧ ∀ i, δ ≤ |w - vR i|

/-- **Pathwise algebra of the localized comparison.** If `w = √κ b + ∫ ∑_k σ_k/(w − u_k)` at the times `a`
and `a + t`, `b̂ = b + ∫ κ^{-1/2} ∑_k σ_k r_δ(w − u_k)` at the same times, and all gaps are `≥ δ` on
`[a, a + t]`, then `w_{a+t} − w_a = √κ (b̂_{a+t} − b̂_a)`. -/
theorem sub_eq_sqrt_mul_sub_of_cut {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {m : ℕ} (σ : Fin m → ℝ)
    {w b bh : ℝ≥0 → ℝ} {u : Fin m → ℝ≥0 → ℝ} {a t : ℝ≥0}
    (hint : ∀ k, IntervalIntegrable (fun s : ℝ => σ k / (w s.toNNReal - u k s.toNNReal)) volume 0
      ((a + t : ℝ≥0) : ℝ))
    (hfint : IntervalIntegrable (fun s : ℝ => (Real.sqrt κ)⁻¹ *
      addedDriftCut σ δ (w s.toNNReal) (fun k => u k s.toNNReal)) volume 0 ((a + t : ℝ≥0) : ℝ))
    (hw1 : w (a + t) = Real.sqrt κ * b (a + t) + ∑ k, ∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ),
      σ k / (w s.toNNReal - u k s.toNNReal))
    (hw2 : w a = Real.sqrt κ * b a + ∑ k, ∫ s in (0 : ℝ)..(a : ℝ),
      σ k / (w s.toNNReal - u k s.toNNReal))
    (hb1 : bh (a + t) = b (a + t) + ∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), (Real.sqrt κ)⁻¹ *
      addedDriftCut σ δ (w s.toNNReal) (fun k => u k s.toNNReal))
    (hb2 : bh a = b a + ∫ s in (0 : ℝ)..(a : ℝ), (Real.sqrt κ)⁻¹ *
      addedDriftCut σ δ (w s.toNNReal) (fun k => u k s.toNNReal))
    (hgap : ∀ s : ℝ≥0, a ≤ s → s ≤ a + t → ∀ k, δ ≤ |w s - u k s|) :
    w (a + t) - w a = Real.sqrt κ * (bh (a + t) - bh a) := by
  have hsκ : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have haat : ((a : ℝ≥0) : ℝ) ≤ ((a + t : ℝ≥0) : ℝ) := by
    exact_mod_cast le_self_add
  have hsub : Set.uIcc (0 : ℝ) (a : ℝ) ⊆ Set.uIcc 0 ((a + t : ℝ≥0) : ℝ) := by
    rw [Set.uIcc_of_le (NNReal.coe_nonneg a), Set.uIcc_of_le (NNReal.coe_nonneg _)]
    exact Set.Icc_subset_Icc_right haat
  -- the cut drift is the true drift on `[a, a + t]`
  have hcongr : ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), (Real.sqrt κ)⁻¹ *
        addedDriftCut σ δ (w s.toNNReal) (fun k => u k s.toNNReal)
      = (Real.sqrt κ)⁻¹ * ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ),
          σ k / (w s.toNNReal - u k s.toNNReal) := by
    rw [← intervalIntegral.integral_finsetSum fun k _ =>
      (hint k).mono_set (by
        rw [Set.uIcc_of_le haat, Set.uIcc_of_le (NNReal.coe_nonneg _)]
        exact Set.Icc_subset_Icc_left (NNReal.coe_nonneg a)),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le haat] at hs
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg a).trans hs.1
    have h1 : a ≤ s.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.1
    have h2 : s.toNNReal ≤ a + t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.2
    simp only [addedDriftCut]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [recipCut_of_le hδ (hgap _ h1 h2 k), div_eq_mul_inv]
  have hD : ∀ k, (∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      - (∫ s in (0 : ℝ)..(a : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      = ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal) := fun k =>
    intervalIntegral.integral_interval_sub_left (hint k) ((hint k).mono_set hsub)
  have hF := intervalIntegral.integral_interval_sub_left hfint (hfint.mono_set hsub)
  rw [hw1, hw2, hb1, hb2]
  have hsum : (∑ k, ∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      - (∑ k, ∫ s in (0 : ℝ)..(a : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      = ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hD k
  have key : Real.sqrt κ * ((∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), (Real.sqrt κ)⁻¹ *
        addedDriftCut σ δ (w s.toNNReal) (fun k => u k s.toNNReal))
      - ∫ s in (0 : ℝ)..(a : ℝ), (Real.sqrt κ)⁻¹ *
        addedDriftCut σ δ (w s.toNNReal) (fun k => u k s.toNNReal))
      = ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal) := by
    rw [hF, hcongr, ← mul_assoc, mul_inv_cancel₀ hsκ, one_mul]
  linear_combination hsum - key

/-- **(O1): localized Girsanov comparison after a deterministic time.** For an integrated `SLE_κ(ρ)`
evolution, a deterministic time `a`, a horizon `T` and a gap size `δ > 0`, there is a random continuous
path `X` (measurable into `CPath`) whose law is absolutely continuous with respect to a Brownian law, such
that almost surely: for every `t ≤ T` with `a + t < ζ` at which all force gaps have stayed `≥ δ` on
`[a, a + t]`, `W_{a+t} − W_a = √κ X_t`. -/
theorem exists_brownian_localization {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (a T : ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ X : Ω → CPath, Measurable X ∧ ∃ μ : Measure CPath, IsProbabilityMeasure μ ∧
      IsBrownianReal canonBM μ ∧ P.map X ≪ μ ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ((a + t : ℝ≥0) : ℝ≥0∞) < ζ ω →
        (∀ s : ℝ≥0, a ≤ s → s ≤ a + t →
          GapsGE δ (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
        W (a + t) ω - W a ω = Real.sqrt κ * (X ω).1 t := by
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  set U : Fin (nL + nR) → ℝ≥0 → Ω → ℝ := allMarks VL VR with hUdef
  set σ : Fin (nL + nR) → ℝ := Fin.addCases (motive := fun _ => ℝ) ρL ρR with hσ
  set F : ℝ → (Fin (nL + nR) → ℝ) → ℝ := fun w u => (Real.sqrt κ)⁻¹ * addedDriftCut σ δ w u
    with hFdef
  have hFc : Continuous fun p : ℝ × (Fin (nL + nR) → ℝ) => F p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ hδ)
  have hFb : ∀ w u, |F w u| ≤ (Real.sqrt κ)⁻¹ * ((∑ j, |σ j|) * δ⁻¹) := fun w u => by
    rw [hFdef, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg κ))]
    exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ hδ w u)
      (inv_nonneg.2 (Real.sqrt_nonneg κ))
  set τ : Ω → ℝ≥0∞ := fun ω => min (ζ ω) ((a + T : ℝ≥0) : ℝ≥0∞) with hτdef
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s} := by
    intro s
    have h1 : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)} :=
      hW s univ MeasurableSet.univ
    have h2 : {ω | τ ω ≤ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)}ᶜ ∪
        {_ω : Ω | ((a + T : ℝ≥0) : ℝ≥0∞) ≤ s} := by
      ext ω
      simp [hτdef, min_le_iff, not_lt]
    rw [h2]
    exact h1.compl.union (MeasurableSet.const _)
  have hτζ : ∀ ω, τ ω ≤ ζ ω := fun ω => min_le_left _ _
  have hτT : ∀ ω, τ ω ≤ ((a + T : ℝ≥0) : ℝ≥0∞) := fun ω => min_le_right _ _
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (U k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hVL i
    | right i => simpa [hUdef, allMarks] using hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => U k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [hUdef, allMarks] using hp.2.2.2.2.2.1 i
  obtain ⟨hequiv, hBM, hident⟩ := girsanov_cutDrift hBF hFc hFb hW hU hτ hτζ hτT hcont
  set θ := cutDrift τ ζ F W U with hθ
  set Q := girsanovMeasure P 𝓕 B θ (a + T + 1) with hQ
  set Bh := girsanovProcess B θ with hBh
  have : IsProbabilityMeasure Q := hequiv.isProb
  have hshift : IsBrownianReal (fun t ω => Bh (a + t) ω - Bh a ω) Q := hBM.1.shift a
  obtain ⟨G, hGm, hGc, -, hGbr, hGeq⟩ := exists_good_version0 hshift
  have hXm := measurable_toCPath hGm hGc
  refine ⟨toCPath G hGc, hXm, Q.map (toCPath G hGc), inferInstance,
    isBrownianReal_canonBM hGbr.toIsPreBrownianReal hGm hGc, hequiv.ac'.map hXm, ?_⟩
  filter_upwards [hident, hpath, hequiv.ac'.ae_le hGeq, hcont] with ω hid hp hG hc t htT htζ hgap
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgapL, hgapR, hweq, -⟩ := hp
  have hX : (toCPath G hGc ω).1 t = Bh (a + t) ω - Bh a ω := hG t
  rw [hX]
  have hale : a ≤ a + t := le_self_add
  have haζ : (a : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hale) htζ
  have ht' : ((a + t : ℝ≥0) : ℝ≥0∞) ≤ τ ω :=
    le_min htζ.le (ENNReal.coe_le_coe.2 (add_le_add_right htT a))
  have ha' : (a : ℝ≥0∞) ≤ τ ω :=
    le_min haζ.le (ENNReal.coe_le_coe.2 le_self_add)
  have hsplit : ∀ r : ℝ≥0, (∑ k, ∫ s in (0 : ℝ)..(r : ℝ), σ k / (W s.toNNReal ω - U k s.toNNReal ω))
      = (∑ i, ∫ s in (0 : ℝ)..(r : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
        + (∑ i, ∫ s in (0 : ℝ)..(r : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
    intro r
    rw [Fin.sum_univ_add]
    simp only [hσ, hUdef, allMarks, Fin.addCases_left, Fin.addCases_right]
  have hint : ∀ k, IntervalIntegrable (fun s : ℝ => σ k / (W s.toNNReal ω - U k s.toNNReal ω))
      volume 0 ((a + t : ℝ≥0) : ℝ) := fun k => by
    cases k using Fin.addCases with
    | left i =>
      simp only [hσ, hUdef, allMarks, Fin.addCases_left, div_eq_mul_inv]
      exact (hgapL (a + t) htζ i).const_mul (ρL i)
    | right i =>
      simp only [hσ, hUdef, allMarks, Fin.addCases_right, div_eq_mul_inv]
      exact (hgapR (a + t) htζ i).const_mul (ρR i)
  have hfint := intervalIntegrable_comp_of_le hFc hFb hW hU hτ (hτζ ω) hc.1 hc.2 ht'
  refine sub_eq_sqrt_mul_sub_of_cut (u := fun k s => U k s ω) (w := fun s => W s ω)
    (b := fun s => B s ω) (bh := fun s => Bh s ω) hκ hδ σ hint hfint ?_ ?_ (hid _ ht') (hid _ ha') ?_
  · have h1 := hweq (a + t) htζ
    beta_reduce at h1
    rw [hsplit]; linarith
  · have h1 := hweq a haζ
    beta_reduce at h1
    rw [hsplit]; linarith
  · intro s h1 h2 k
    cases k using Fin.addCases with
    | left i =>
      simp only [hUdef, allMarks, Fin.addCases_left]
      exact (hgap s h1 h2).1 i
    | right i =>
      simp only [hUdef, allMarks, Fin.addCases_right]
      exact (hgap s h1 h2).2 i

end InteractingSLE.Dimension
