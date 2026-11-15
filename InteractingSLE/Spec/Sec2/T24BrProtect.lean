import InteractingSLE.Spec.Sec2.T24BrMean
import InteractingSLE.Spec.Sec2.T24BrAnnounce
import InteractingSLE.Spec.Coupling.MartMeansLife
import InteractingSLE.Spec.Sec7.PhaseSelFullLevy

/-!
# Protected stopping times chosen on the curve space

Intersect the landed safe Loewner stop with the landed coordinate exit stop.
The first protects the marked interior point and the lifetime; the second bounds
all force coordinates and the reconstructed Brownian part.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge

open Coupling Coupling.MartMeans Sec7.PhaseSelFull MartChar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0} {z : ℂ} {K : ℕ}

/-- A finite safe stop with an additional bound on the driver and force coordinates. -/
def protectedCurveTime (z : ℂ) (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ)
    (T : ℕ → Ω → ℝ≥0) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (K n : ℕ) (ω : Ω) : ℝ≥0 :=
  min (if ω ∈ G then locTimeL z n (T n ω) (ζ ω) (W · ω) else 0)
    (lifeLocN W V (fun _ => ⊤) (n + K) ω)

/-- Both stops in the intersection are stopping times of the coordinate filtration. -/
theorem isStoppingTime_protectedCurveTime [𝓖.IsRightContinuous]
    (hWa : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : ∀ t, MeasurableSet[𝓖 t] G)
    (hWc : ∀ ω, Continuous (W · ω)) (hVc : ∀ i ω, Continuous (V i · ω))
    (hWad : StronglyAdapted 𝓖 W) (hVad : ∀ i, StronglyAdapted 𝓖 (V i))
    (hT : ∀ n, IsStoppingTime 𝓖 fun ω => (T n ω : WithTop ℝ≥0))
    (hz : 0 < z.im) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => (protectedCurveTime z W V T ζ G K n ω : WithTop ℝ≥0) := by
  have h1 := isStoppingTime_locStopL hWa hGc hG (hT n) hz
  have h2 := isStoppingTime_lifeLoc hWc hVc hWad hVad (isStoppingTime_top' (𝓖 := 𝓖)) (n + K)
  convert h1.min h2 using 1
  funext ω
  simp only [protectedCurveTime, WithTop.coe_min, locStopL, coe_lifeLocN]

/-- The safe condition is preserved by the additional coordinate stop. -/
theorem isSafeAt_protectedCurveTime
    {ω : Ω} (hω : ω ∈ G) (hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hw0 : W 0 ω = 0) (hz : 0 < z.im) {n : ℕ} (hTζ : (T n ω : ℝ≥0∞) < ζ ω) :
    IsSafeAt (Metric.closedBall z (locRad z n)) (locLevel z n) n (T n ω) (ζ ω) (W · ω)
      (protectedCurveTime z W V T ζ G K n ω) := by
  apply (isSafeAt_locTimeL hw hw0 hz n hTζ).anti hw (closedBall_locRad_subset hz n)
  simp only [protectedCurveTime, hω, ↓reduceIte]
  exact min_le_left _ _

/-- Uniform coordinate bounds up to the protected time. -/
theorem abs_le_of_le_protectedCurveTime
    (hWc : ∀ ω, Continuous (W · ω)) (hVc : ∀ i ω, Continuous (V i · ω))
    {ω : Ω} (hinit : absSum W V 0 ω < K) {n : ℕ} {s : ℝ≥0}
    (hs : s ≤ protectedCurveTime z W V T ζ G K n ω) :
    |W s ω| ≤ ((n + K : ℕ) : ℝ) ∧ ∀ i, |V i s ω| ≤ ((n + K : ℕ) : ℝ) := by
  have hmem : ω ∈ initEvent W V (n + K) := by
    exact hinit.trans_le (by exact_mod_cast Nat.le_add_left K n)
  apply abs_le_of_le_lifeLoc hWc hVc hmem
  rw [← coe_lifeLocN]
  exact WithTop.coe_le_coe.2 (hs.trans (min_le_right _ _))

/-- The protected times exhaust every time before swallowing and before the lifetime. -/
theorem eventually_lt_protectedCurveTime
    (hWc : ∀ ω, Continuous (W · ω)) (hVc : ∀ i ω, Continuous (V i · ω))
    {ω : Ω} (hω : ω ∈ G) (hTm : Monotone fun n => T n ω)
    (hTex : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω)
    (hz : 0 < z.im) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < QuantumZipper.swallowTime (Ito.rpath (W · ω)) z)
    (hrζ : (r : ℝ≥0∞) < ζ ω) :
    ∀ᶠ n in atTop, r < protectedCurveTime z W V T ζ G K n ω := by
  have hsafe := eventually_lt_locTimeL (hWc ω).continuousOn hz hTm hTex hr hrζ
  have hcoord := eventually_le_lifeLoc (T := fun _ : Ω => ⊤) hWc hVc
    (ω := ω) (u := r + 1) le_top
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcoord
  filter_upwards [hsafe, eventually_ge_atTop N] with n hn hnN
  simp only [protectedCurveTime, hω, ↓reduceIte, lt_min_iff]
  refine ⟨hn, ?_⟩
  have hc := hN (n + K) (hnN.trans (by omega))
  rw [← coe_lifeLocN, WithTop.coe_le_coe] at hc
  exact (lt_add_one r).trans_le hc

/-- The integrated driving equation reconstructs the Brownian path before its lifetime. -/
theorem brownian_eq_martValue_before {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    b t = martValue (jointρ ρL ρR) (w 0) (jointV (fun i => vL i 0) (fun i => vR i 0))
      (w t) (jointV (fun i => vL i t) (fun i => vR i t)) / Real.sqrt κ := by
  have hN1 := h.isForcePath.w_eq_N1 h.driverEq ht
  have hM : martValue (jointρ ρL ρR) (w 0) (jointV (fun i => vL i 0) (fun i => vR i 0))
      (w t) (jointV (fun i => vL i t) (fun i => vR i t)) = Real.sqrt κ * b t := by
    simp only [martValue, jointρ, jointV, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      h.1, h.2.1, h.2.2.1, sub_zero]
    linarith
  apply (eq_div_iff (Real.sqrt_pos.2 hκ).ne').2
  rw [hM]
  ring

/-- The coordinate exit stop also bounds the reconstructed Brownian part. -/
theorem abs_normalized_martProc_le_of_le_protectedCurveTime
    {κ : ℝ} (hκ : 0 < κ) {ρ : ι → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hVc : ∀ i ω, Continuous (V i · ω))
    {ω : Ω} {n : ℕ} {s : ℝ≥0}
    (hs : s ≤ protectedCurveTime z W V T ζ G K n ω) :
    |martProc ρ W V s ω / Real.sqrt κ| ≤
      (2 * ((n + K : ℕ) : ℝ) + (∑ i, |ρ i|) * ((n + K : ℕ) : ℝ)) / Real.sqrt κ := by
  have hle : s ≤ lifeLocN W V (fun _ => ⊤) (n + K) ω := hs.trans (min_le_right _ _)
  have hb := abs_martProc_lifeLocN_le (ρ := ρ) (T := fun _ : Ω => ⊤) hWc hVc (n + K) s ω
  rw [min_eq_left hle] at hb
  rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hκ)]
  exact div_le_div_of_nonneg_right hb (Real.sqrt_pos.2 hκ).le

end InteractingSLE.Sec2.T24Bridge
