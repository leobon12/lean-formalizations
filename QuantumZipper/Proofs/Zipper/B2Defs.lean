import QuantumZipper.Proofs.Zipper.RegCont
import QuantumZipper.Proofs.Loewner.RealLine

/-!
# B2 (definitions and pathwise identities): the finite-horizon picture `Γᵀ`

`blueprint/E_BRANCH_BLUEPRINT.md` §2 (standing setup) and §4, node B2. Paper: Sheffield,
*Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.2 (p. 14) and §5.2
(pp. 57–59: the stationary configuration is obtained by "starting at stationarity for some large
`T` and unzipping"); this file only contains the deterministic part.

## Definitions (blueprint §2)

For a driver `W` and a horizon `T`:
* `vrev W T s = W (T − min (max s 0) T) − W T` (the blueprint's `V`: `W(T−s) − W T` on `[0,T]`,
  `0` for `s ≤ 0`, constant `−W T` after `T`);
* `wfut W T s = W (T + max s 0) − W T` (the blueprint's `W⁰`).

For a Brownian motion `B` and a field `X`: `cfg κ B X ω = (ofFun (h0rev κ) + X ω, drive κ B ω)`
(the `Γ⁰` sample `𝒵`), `zipped κ T t = zipCapDown √κ (T − t) ∘ cfg` (the blueprint's `𝒞_t`),
`Yf κ T t = (zipped κ T t).1 = unzippedField √κ 𝒵 (T − t)` (`Y_t`), `h0f κ T = Yf κ T 0`
(`h⁰`), `hitT κ T B ω x = realHitTime (V ω) x` (`τ_x`), `collided κ T B X ω x = 𝒞_{τ_x}`
(`C_x`, meaningful on `{τ_x ≤ T}`), and `qt κ V t ϖ = Q ∫ log‖(revMap V t)'‖ dϖ` (`q_t`).

## Results

* `zipped_snd_of_le`, `zipped_snd_of_ge`: the driver of `𝒞_t` is `s ↦ V(t−s) − V t` on
  `[0,t]` and `s ↦ W⁰(s−t) − V t` after `t` (A1(c)).
* `fwdMapInv_eq_revMap_vrev`, `revMap_vrev_eq_comp`: on `ℍ`, `fwdMapInv W T = revMap V T =
  revMap V₁ (T−t) ∘ revMap V t` with `V₁ r = W(T−t−r) − W(T−t)`.
* `coordChange_comp_of_eqOn` (own elementary proof: chain rule): raw values of iterated coordinate
  changes compose exactly, `coordChange x (G ∘ F) Q μ = coordChange x G Q (F_* μ) + Q ∫ log|F'| dμ`,
  given integrability of the two log-derivatives.
* **`coordChange_fwdMapInv_split`** (B2(b), raw form): for every measure `μ` carried by `ℍ` with
  the two log-derivative integrabilities,
  `unzippedField γ c T μ = unzippedField γ c (T − t) (μ.map F) + Qc γ ∫ log‖F'‖ dμ`,
  `F = revMap (vrev W T) t`. Corollaries: `h0f_fc_split` (dyadic folded circles, all `ω` with a
  continuous driver vanishing at `0`) and `h0f_compact_split` (`h⁰ ϖ = Y_t ϖ_t + q_t` for any
  finite `ϖ` carried by a compact subset of `ℍ`, e.g. the arc normalizer).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B2

open TwoPoint UnzipInvariance

/-! ## 1. Definitions -/

/-- The time-reversed driver `V s = W(T − s) − W T` on `[0,T]` (clamped outside). -/
def vrev (W : ℝ → ℝ) (T : ℝ) : ℝ → ℝ := fun s => W (T - min (max s 0) T) - W T

/-- The future driver `W⁰ s = W(T + s) − W T` (clamped for `s ≤ 0`). -/
def wfut (W : ℝ → ℝ) (T : ℝ) : ℝ → ℝ := fun s => W (T + max s 0) - W T

variable {Ω : Type*}

/-- The `Γ⁰` sample `𝒵 = (𝔥₀ + X, √κ B)`. -/
def cfg (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample × (ℝ → ℝ) :=
  (ofFun (h0rev κ) + X ω, drive κ B ω)

/-- The blueprint's `V`. -/
def Vr (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := vrev (drive κ B ω) T

/-- The blueprint's `W⁰`. -/
def W0 (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := wfut (drive κ B ω) T

/-- The zipped configurations `𝒞_t = zipCapDown γ (T − t) 𝒵`. -/
def zipped (κ T t : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    FieldSample × (ℝ → ℝ) :=
  zipCapDown (Real.sqrt κ) (T - t) (cfg κ B X ω)

/-- The zipped fields `Y_t = 𝒞_t.1`. -/
def Yf (κ T t : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  (zipped κ T t B X ω).1

/-- The fully zipped field `h⁰ = Y_0`. -/
def h0f (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  Yf κ T 0 B X ω

/-- `τ_x = realHitTime V x`. -/
def hitT (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (x : ℝ) : ℝ≥0∞ := realHitTime (Vr κ T B ω) x

/-- The collided configuration `C_x = 𝒞_{τ_x}` (meaningful on `{τ_x ≤ T}`). -/
def collided (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (x : ℝ) :
    FieldSample × (ℝ → ℝ) :=
  zipped κ T (hitT κ T B ω x).toReal B X ω

/-- `q_t = Q ∫ log‖(revMap V t)'‖ dϖ`, `Q = Qc √κ`. -/
def qt (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) : ℝ :=
  Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap V t) z‖ ∂ϖ

theorem Yf_eq_unzippedField (κ T t : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    Yf κ T t B X ω = unzippedField (Real.sqrt κ) (cfg κ B X ω) (T - t) := rfl

theorem h0f_eq_unzippedField (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    h0f κ T B X ω = unzippedField (Real.sqrt κ) (cfg κ B X ω) T := by
  simp only [h0f, Yf_eq_unzippedField, sub_zero]

/-! ## 2. Drivers -/

variable {W : ℝ → ℝ} {T t : ℝ}

theorem vrev_of_mem {s : ℝ} (hs : s ∈ Icc 0 T) : vrev W T s = W (T - s) - W T := by
  simp only [vrev, max_eq_left hs.1, min_eq_left hs.2]

theorem continuous_vrev (hW : Continuous W) (T : ℝ) : Continuous (vrev W T) := by
  unfold vrev; fun_prop

theorem vrev_zero (hT : 0 ≤ T) : vrev W T 0 = 0 := by
  simp [vrev_of_mem (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)]

/-! ## 3. Flow identities on `ℍ` -/

theorem revMap_vrev_eq (z : ℂ) :
    revMap (fun s => W (T - s) - W T) T z = revMap (vrev W T) T z :=
  ReverseFlow.revMap_congr_drive z fun _ hs => (vrev_of_mem hs).symm

theorem fwdMapInv_eq_revMap_vrev (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) : fwdMapInv W T z = revMap (vrev W T) T z := by
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hT hz, revMap_vrev_eq]

/-- `revMap V T = revMap V₁ (T − t) ∘ revMap V t` on `ℍ`, `V₁ r = W(T−t−r) − W(T−t)`. -/
theorem revMap_vrev_eq_comp (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) (htT : t ≤ T)
    {z : ℂ} (hz : z ∈ H) :
    revMap (vrev W T) T z =
      revMap (fun r => W (T - t - r) - W (T - t)) (T - t) (revMap (vrev W T) t z) := by
  have hT : 0 ≤ T := ht.trans htT
  have hs : 0 ≤ T - t := sub_nonneg.2 htT
  rw [← fwdMapInv_eq_revMap_vrev hW hW0 hT hz]
  have key := RegCont.fwdMapInv_add hW hW0 hs ht hz
  rw [show T - t + t = T by ring] at key
  have hin : revMap (fun r => W (T - r) - W T) t z = revMap (vrev W T) t z :=
    ReverseFlow.revMap_congr_drive z fun r hr => (vrev_of_mem ⟨hr.1, hr.2.trans htT⟩).symm
  rw [key, hin, fwdMapInv_eq_revMap_timeRev W hW hW0 hs
    (im_revMap_pos (continuous_vrev hW T) hz ht)]

/-! ## 4. Composition of coordinate changes (raw values) -/

/-- **Composition of coordinate changes.** If `Φ = G ∘ F` on `ℍ`, `F` maps `ℍ` into `ℍ`, both are
holomorphic with non-vanishing derivative on `ℍ`, `μ` is carried by `ℍ`, and `log|Φ'|`,
`log|F'|` are `μ`-integrable, then
`coordChange x Φ Q μ = coordChange x G Q (F_* μ) + Q ∫ log|F'| dμ`. Own elementary proof
(chain rule and `Measure.map_map`). -/
theorem coordChange_comp_of_eqOn (x : FieldSample) (Q : ℝ) {Φ G F : ℂ → ℂ} {μ : Measure ℂ}
    (hΦ : EqOn Φ (G ∘ F) H) (hμ : μ Hᶜ = 0) (hFH : MapsTo F H H)
    (hFd : DifferentiableOn ℂ F H) (hGd : DifferentiableOn ℂ G H)
    (hG0 : ∀ z ∈ H, deriv G z ≠ 0) (hF0 : ∀ z ∈ H, deriv F z ≠ 0)
    (hFm : Measurable F) (hGm : Measurable G)
    (hi1 : Integrable (fun z => Real.log ‖deriv Φ z‖) μ)
    (hi2 : Integrable (fun z => Real.log ‖deriv F z‖) μ) :
    coordChange x Φ Q μ =
      coordChange x G Q (μ.map F) + Q * ∫ z, Real.log ‖deriv F z‖ ∂μ := by
  have hae : ∀ᵐ z ∂μ, z ∈ H := ae_iff.2 hμ
  have hpt : ∀ z ∈ H, Real.log ‖deriv Φ z‖ =
      Real.log ‖deriv G (F z)‖ + Real.log ‖deriv F z‖ := by
    intro z hz
    have hev : Φ =ᶠ[𝓝 z] G ∘ F :=
      Filter.eventually_of_mem (isOpen_H.mem_nhds hz) fun w hw => hΦ hw
    have hFz : F z ∈ H := hFH hz
    rw [hev.deriv_eq, deriv_comp z ((hGd _ hFz).differentiableAt (isOpen_H.mem_nhds hFz))
      ((hFd _ hz).differentiableAt (isOpen_H.mem_nhds hz)), norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (hG0 _ hFz)) (norm_ne_zero_iff.2 (hF0 _ hz))]
  have hi3 : Integrable (fun z => Real.log ‖deriv G (F z)‖) μ := by
    refine (hi1.sub hi2).congr ?_
    filter_upwards [hae] with z hz
    simp only [Pi.sub_apply, hpt z hz, add_sub_cancel_right]
  have hmapΦ : μ.map Φ = (μ.map F).map G := by
    rw [Measure.map_map hGm hFm]
    exact Measure.map_congr (hae.mono fun z hz => hΦ hz)
  have hint : ∫ w, Real.log ‖deriv G w‖ ∂(μ.map F) = ∫ z, Real.log ‖deriv G (F z)‖ ∂μ :=
    integral_map hFm.aemeasurable
      (Real.measurable_log.comp (measurable_deriv G).norm).aestronglyMeasurable
  have hsplit : ∫ z, Real.log ‖deriv Φ z‖ ∂μ =
      ∫ z, Real.log ‖deriv G (F z)‖ ∂μ + ∫ z, Real.log ‖deriv F z‖ ∂μ := by
    rw [← integral_add hi3 hi2]
    exact integral_congr_ae (hae.mono fun z hz => hpt z hz)
  unfold coordChange
  rw [hmapΦ, hsplit, hint]
  ring

/-! ## 5. B2(b), raw form: `h⁰ = Y_t` zipped by `V` on `[0,t]` -/

/-- **B2(b), raw form.** For a continuous driver with `W 0 = 0`, `0 ≤ t ≤ T`, and `μ` carried by
`ℍ` with `log|(revMap V T)'|`, `log|(revMap V t)'|` integrable:
`c.1` unzipped by `T` at `μ` equals `c.1` unzipped by `T − t` at `F_* μ` plus
`Qc γ ∫ log|F'| dμ`, `F = revMap V t`, `V = vrev W T`. -/
theorem coordChange_fwdMapInv_split (x : FieldSample) (Q : ℝ) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) (htT : t ≤ T) {μ : Measure ℂ} (hμ : μ Hᶜ = 0)
    (hi1 : Integrable (fun z => Real.log ‖deriv (revMap (vrev W T) T) z‖) μ)
    (hi2 : Integrable (fun z => Real.log ‖deriv (revMap (vrev W T) t) z‖) μ) :
    coordChange x (fwdMapInv W T) Q μ =
      coordChange x (fwdMapInv W (T - t)) Q (μ.map (revMap (vrev W T) t)) +
        Q * ∫ z, Real.log ‖deriv (revMap (vrev W T) t) z‖ ∂μ := by
  have hT : 0 ≤ T := ht.trans htT
  have hs : 0 ≤ T - t := sub_nonneg.2 htT
  have hVc := continuous_vrev hW T
  set V₁ : ℝ → ℝ := fun r => W (T - t - r) - W (T - t) with hV₁
  have hV₁c : Continuous V₁ := by rw [hV₁]; fun_prop
  have hFm : Measurable (revMap (vrev W T) t) := measurable_revMap hVc ht
  have hFH : MapsTo (revMap (vrev W T) t) H H := fun z hz => im_revMap_pos hVc hz ht
  rw [coordChange_congr_of_eqOn (fun z hz => fwdMapInv_eq_revMap_vrev hW hW0 hT hz) hμ,
    coordChange_comp_of_eqOn x Q (G := revMap V₁ (T - t)) (F := revMap (vrev W T) t)
      (fun z hz => revMap_vrev_eq_comp hW hW0 ht htT hz) hμ hFH
      (differentiableOn_revMap _ hVc ht) (differentiableOn_revMap _ hV₁c hs)
      (fun z hz => deriv_revMap_ne_zero _ hV₁c hs hz)
      (fun z hz => deriv_revMap_ne_zero _ hVc ht hz) hFm (measurable_revMap hV₁c hs) hi1 hi2]
  congr 1
  have hμF : (μ.map (revMap (vrev W T) t)) Hᶜ = 0 := by
    rw [Measure.map_apply hFm isOpen_H.measurableSet.compl]
    exact measure_mono_null (fun z hz hzH => hz (hFH hzH)) hμ
  exact (coordChange_congr_of_eqOn
    (fun z hz => fwdMapInv_eq_revMap_timeRev W hW hW0 hs hz) hμF x Q).symm

/-- The raw split for dyadic (indeed all) folded circles of positive radius. -/
theorem coordChange_fwdMapInv_split_fc (x : FieldSample) (Q : ℝ) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) (htT : t ≤ T) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    coordChange x (fwdMapInv W T) Q (foldedCircle w r) =
      coordChange x (fwdMapInv W (T - t)) Q ((foldedCircle w r).map (revMap (vrev W T) t)) +
        Q * ∫ z, Real.log ‖deriv (revMap (vrev W T) t) z‖ ∂(foldedCircle w r) :=
  coordChange_fwdMapInv_split x Q hW hW0 ht htT (ae_iff.1 (foldedCircle_ae_mem_H w hr))
    (integrable_log_norm_deriv_revMap_foldedCircle (continuous_vrev hW T) (ht.trans htT) w hr)
    (integrable_log_norm_deriv_revMap_foldedCircle (continuous_vrev hW T) ht w hr)

/-- `log|(revMap V t)'|` is integrable against any finite measure carried by a compact subset
of `ℍ` (continuity of the derivative of a holomorphic map, which does not vanish). -/
theorem integrable_log_norm_deriv_revMap_of_compact {V : ℝ → ℝ} (hV : Continuous V)
    (ht : 0 ≤ t) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {ϖ : Measure ℂ}
    [IsFiniteMeasure ϖ] (hϖ : ϖ Kᶜ = 0) :
    Integrable (fun z => Real.log ‖deriv (revMap V t) z‖) ϖ := by
  have hd : ContinuousOn (deriv (revMap V t)) H :=
    ((differentiableOn_revMap V hV ht).analyticOnNhd isOpen_H).deriv.continuousOn
  have hc : ContinuousOn (fun z => Real.log ‖deriv (revMap V t) z‖) K :=
    (hd.mono hKH).norm.log fun z hz => norm_ne_zero_iff.2 (deriv_revMap_ne_zero V hV ht (hKH hz))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine (integrable_const C).mono'
    (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable ?_
  filter_upwards [ae_iff.2 hϖ] with z hz
  exact hC z hz

/-- The raw split for a finite measure carried by a compact subset of `ℍ` (the normalizer `ϖ`). -/
theorem coordChange_fwdMapInv_split_compact (x : FieldSample) (Q : ℝ) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) (htT : t ≤ T) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] (hϖ : ϖ Kᶜ = 0) :
    coordChange x (fwdMapInv W T) Q ϖ =
      coordChange x (fwdMapInv W (T - t)) Q (ϖ.map (revMap (vrev W T) t)) +
        Q * ∫ z, Real.log ‖deriv (revMap (vrev W T) t) z‖ ∂ϖ :=
  coordChange_fwdMapInv_split x Q hW hW0 ht htT
    (measure_mono_null (compl_subset_compl.2 hKH) hϖ)
    (integrable_log_norm_deriv_revMap_of_compact (continuous_vrev hW T) (ht.trans htT) hK hKH hϖ)
    (integrable_log_norm_deriv_revMap_of_compact (continuous_vrev hW T) ht hK hKH hϖ)

/-! ## 6. The same identities for `h⁰` and `Y_t` -/

variable {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ω : Ω}

/-- **B2(b), raw form, folded circles.** `h⁰ μ = Y_t (F_* μ) + Q ∫ log|F'| dμ` for every folded
circle `μ` of positive radius, at every `ω` whose Brownian path is continuous and starts at `0`.
-/
theorem h0f_fc_split (hc : Continuous fun s => B s ω) (h0 : B 0 ω = 0) (ht : 0 ≤ t)
    (htT : t ≤ T) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    h0f κ T B X ω (foldedCircle w r) =
      Yf κ T t B X ω ((foldedCircle w r).map (revMap (Vr κ T B ω) t)) +
        qt κ (Vr κ T B ω) t (foldedCircle w r) := by
  rw [h0f_eq_unzippedField, Yf_eq_unzippedField]
  exact coordChange_fwdMapInv_split_fc _ _ (drive_continuous hc) (drive_zero h0) ht htT w hr

/-- **B2(b), `h⁰ ϖ = Y_t ϖ_t + q_t`**, for every finite `ϖ` carried by a compact subset of `ℍ`
(`ϖ_t = ϖ.map (revMap V t)`). -/
theorem h0f_compact_split (hc : Continuous fun s => B s ω) (h0 : B 0 ω = 0) (ht : 0 ≤ t)
    (htT : t ≤ T) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {ϖ : Measure ℂ}
    [IsFiniteMeasure ϖ] (hϖ : ϖ Kᶜ = 0) :
    h0f κ T B X ω ϖ = Yf κ T t B X ω (ϖ.map (revMap (Vr κ T B ω) t)) + qt κ (Vr κ T B ω) t ϖ := by
  rw [h0f_eq_unzippedField, Yf_eq_unzippedField]
  exact coordChange_fwdMapInv_split_compact _ _ (drive_continuous hc) (drive_zero h0) ht htT hK
    hKH hϖ

end B2
end QuantumZipper
