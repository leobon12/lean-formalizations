import QuantumZipper.Proofs.Section5.Prop16D4WInSc0

/-!
# D4⁺ʷ inputs (part 5): transfer of half-ball areas through TV-local convergence

Tools for clauses `hgrow` and `htight` of `Prop16D4WInputsStmt`:

* `tv_event_bound`: `Q B ≤ Q A + ν S + tvDist (Q.map F) ν` when a.s. `B ⊆ A ∪ F⁻¹ S`;
* `map_antitone_tendsto`: the pushforward of decreasing measurable sets whose intersection is
  a.s. avoided has measure `→ 0` (also for a non-a.e.-measurable map, where the pushforward is
  the junk measure `0`);
* `rbump s₁ s₂`: a continuous radial cut-off, `1` on `B̄_{s₁}`, `0` off `B_{s₂}`, which squeezes
  `μ(B_{s₁} ∩ ℍ) ≤ ∫ rbump dμ ≤ μ(B_{s₂} ∩ ℍ)` (`lintegral_rbump_ge`, `lintegral_rbump_le`);
* `phiN γ R g`: the measurable function of `locField (R+1)` computing `liApprox γ R g`
  (`liApprox_eq_phiN`, via `locRecon`), which is `∫ g dμ` whenever the local area limit exists
  on a domain containing `B_R ∩ ℍ` (`Prop16Area.liApprox_eq_lintegral`);
* `canon_facts`: for a locally good sample at a positive scale `a`, the canonical field's area
  pairing is computed by `liApprox`, and `μ_{canon}(B_s ∩ ℍ) = μ_x(B_{sa} ∩ ℍ)`.

Own elementary arguments (squeezing a measurable functional between continuous bumps).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G TV

theorem tv_event_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {Q : Measure α}
    {ν : Measure β} {F : α → β} (hF : AEMeasurable F Q) {S : Set β} (hS : MeasurableSet S)
    {A B : Set α} (h : ∀ᵐ p ∂Q, p ∈ B → p ∈ A ∨ F p ∈ S) :
    Q B ≤ Q A + (ν S + tvDist (Q.map F) ν) := by
  have h1 : Q B ≤ Q (A ∪ F ⁻¹' S) := measure_mono_ae (h.mono fun p hp hpB => hp hpB)
  have h2 : Q (F ⁻¹' S) ≤ ν S + tvDist (Q.map F) ν := by
    rw [← Measure.map_apply_of_aemeasurable hF hS]
    exact tsub_le_iff_left.1 (le_tvDist hS)
  exact h1.trans ((measure_union_le _ _).trans (add_le_add le_rfl h2))

theorem map_antitone_tendsto {Ω' β : Type*} [MeasurableSpace Ω'] [MeasurableSpace β]
    {P' : Measure Ω'} [IsFiniteMeasure P'] {G : Ω' → β} (hG : AEMeasurable G P') {S : ℕ → Set β}
    (hS : ∀ n, MeasurableSet (S n)) (hanti : Antitone S) (h : ∀ᵐ ω ∂P', G ω ∉ ⋂ n, S n) :
    Tendsto (fun n => (P'.map G) (S n)) atTop (𝓝 0) := by
  have hlim := tendsto_measure_iInter_atTop (μ := P'.map G) (fun n => (hS n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have h0 : P' (G ⁻¹' ⋂ n, S n) = 0 :=
    measure_mono_null (fun ω hω => not_not.2 hω) (ae_iff.1 h)
  rw [Measure.map_apply_of_aemeasurable hG (MeasurableSet.iInter hS), h0] at hlim
  exact hlim

/-! ## Radial cut-offs -/

/-- The radial cut-off `min 1 (max 0 ((s₂ − ‖z‖)/(s₂ − s₁)))`. -/
def rbump (s1 s2 : ℝ) (z : ℂ) : ℝ := min 1 (max 0 ((s2 - ‖z‖) / (s2 - s1)))

theorem continuous_rbump (s1 s2 : ℝ) : Continuous (rbump s1 s2) := by
  unfold rbump; fun_prop

theorem rbump_nonneg (s1 s2 : ℝ) (z : ℂ) : 0 ≤ rbump s1 s2 z :=
  le_min zero_le_one (le_max_left _ _)

theorem rbump_le_one (s1 s2 : ℝ) (z : ℂ) : rbump s1 s2 z ≤ 1 := min_le_left _ _

theorem rbump_eq_one {s1 s2 : ℝ} (h12 : s1 < s2) {z : ℂ} (hz : ‖z‖ ≤ s1) :
    rbump s1 s2 z = 1 := by
  unfold rbump
  refine min_eq_left (le_max_of_le_right ?_)
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem norm_lt_of_rbump_ne_zero {s1 s2 : ℝ} (h12 : s1 < s2) {z : ℂ} (hz : rbump s1 s2 z ≠ 0) :
    ‖z‖ < s2 := by
  by_contra h
  push Not at h
  apply hz
  unfold rbump
  have : (s2 - ‖z‖) / (s2 - s1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [max_eq_left this, min_eq_right zero_le_one]

theorem hasCompactSupport_rbump {s1 s2 : ℝ} (h12 : s1 < s2) : HasCompactSupport (rbump s1 s2) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) s2) fun z hz => by
    by_contra h
    exact hz (mem_closedBall_zero_iff.2 (norm_lt_of_rbump_ne_zero h12 h).le)

theorem lintegral_rbump_ge {s1 s2 : ℝ} (h12 : s1 < s2) (μ : Measure ℂ) :
    μ (ball 0 s1 ∩ H) ≤ ∫⁻ z, ENNReal.ofReal (rbump s1 s2 z) ∂μ := by
  rw [← lintegral_indicator_one ((isOpen_ball.inter isOpen_H).measurableSet)]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ ball (0 : ℂ) s1 ∩ H
  · rw [indicator_of_mem hz, Pi.one_apply, rbump_eq_one h12 (mem_ball_zero_iff.1 hz.1).le,
      ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]; exact zero_le

theorem lintegral_rbump_le {s1 s2 : ℝ} (h12 : s1 < s2) {μ : Measure ℂ} (hμ : μ Hᶜ = 0) :
    ∫⁻ z, ENNReal.ofReal (rbump s1 s2 z) ∂μ ≤ μ (ball 0 s2 ∩ H) := by
  have h1 : ∫⁻ z, ENNReal.ofReal (rbump s1 s2 z) ∂μ ≤ μ (ball 0 s2) := by
    rw [← lintegral_indicator_one isOpen_ball.measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hz : rbump s1 s2 z = 0
    · rw [hz, ENNReal.ofReal_zero]; exact zero_le
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (norm_lt_of_rbump_ne_zero h12 hz)),
        Pi.one_apply, ENNReal.ofReal_le_one]
      exact rbump_le_one _ _ _
  refine h1.trans (measure_mono_ae ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with z hz hzb
  exact ⟨hzb, not_not.1 hz⟩

/-! ## `liApprox` as a measurable function of the local field -/

/-- `liApprox γ R g` read off `locField (R+1)`. -/
def phiN (γ : ℝ) (R : ℕ) (g : ℂ → ℝ) : (ℕ → ℝ) → ℝ≥0∞ := fun v =>
  liApprox γ R g (locRecon (R + 1) v)

theorem measurable_phiN (γ : ℝ) (R : ℕ) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable (phiN γ R g) :=
  (measurable_liApprox γ R hg).comp (measurable_locRecon _)

theorem liApprox_eq_phiN (γ : ℝ) (R : ℕ) (g : ℂ → ℝ) (x : FieldSample) :
    liApprox γ R g x = phiN γ R g (locField (R + 1) x) :=
  liApprox_congr (by push_cast; exact le_rfl) (locField_locRecon (R + 1) x).symm g

/-! ## The canonical field of a locally good sample -/

/-- **Deterministic facts on the canonical field** of a locally good sample at a positive scale:
its local area measure charges only `ℍ`, its half-ball areas are those of `x` at scale `a`, and
its area pairings with cut-offs inside `B_R` are computed by `liApprox`. -/
theorem canon_facts {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    (ha : 0 < scaleParamOn γ x U) :
    qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U) Hᶜ = 0 ∧
    (∀ s : ℝ, qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U) (ball 0 s ∩ H) =
      qAreaMeasureOn γ x U (ball 0 (s * scaleParamOn γ x U) ∩ H)) ∧
    ∀ R : ℕ, hball R ⊆ canonicalDomainOn γ x U → ∀ g : ℂ → ℝ, Continuous g →
      (∀ z, 0 ≤ g z) → HasCompactSupport g → (∀ z, g z ≠ 0 → z ∈ ball (0 : ℂ) R) →
      liApprox γ R g (canonicalOn γ x U) =
        ∫⁻ z, ENNReal.ofReal (g z) ∂(qAreaMeasureOn γ (canonicalOn γ x U)
          (canonicalDomainOn γ x U)) := by
  have hVH : canonicalDomainOn γ x U ⊆ H := preimage_mul_subset_H hUH ha
  refine ⟨measure_mono_null (compl_subset_compl.2 hVH) (qAreaMeasureOn_compl _ _ _),
    fun s => ?_, fun R hR g hg hg0 hgc hgR => ?_⟩
  · rw [qAreaMeasureOn_canonicalOn_of_locallyGood hγ hx hU hUH hUV ha,
      Measure.map_apply (by fun_prop : Measurable fun z : ℂ => z / (scaleParamOn γ x U : ℂ))
        (isOpen_ball.inter isOpen_H).measurableSet,
      GoodTransforms.preimage_div_ball_inter_H ha]
  · have hμ := isVagueLimitOn_qAreaMeasureOn
      (exists_vague_rescale_of_locallyGood hγ hx hU hUH hUV ha)
    exact liApprox_eq_lintegral hVH hR hμ hg hg0 hgc hgR

end Prop16Asm

end QuantumZipper
