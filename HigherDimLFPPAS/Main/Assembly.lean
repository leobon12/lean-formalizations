import HigherDimLFPPAS.Main.AsConclusion
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLFPPAS.Glue.Seed
import HigherDimLFPPAS.Glue.Normalizer
import HigherDimLFPPAS.Scaling.UnitSpeedAdmissible
import HigherDimLFPPAS.Scaling.AffineInternalScaling
import HigherDimLFPPAS.Scaling.CoordScaling
import HigherDimLFPPAS.Scaling.LocFieldScaling
import HigherDimLFPPAS.Iterate.Prop41
import HigherDimLFPPAS.Covering.Interface
import HigherDimLFPPAS.Sharp.Prop51
import HigherDimLFPPAS.Field.PathwiseLemma23i
import HigherDimLFPPAS.Field.Transfer
import HigherDimLFPPAS.Gauss.Lemma23ii
import HigherDimLFPPAS.Gauss.Lemma23iii
import HigherDimLFPPAS.Annulus.Meas
import HigherDimLFPPAS.Localize.Confine
import HigherDimLFPPAS.Coarse.Lemma27
import HigherDimLFPPAS.Bridge.Internal
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Main.Cor104
import HigherDimLQGContinuity.Median.MedianOneStrong
import HigherDimLQGContinuity.Frozen.Theorem11Xi
import HigherDimLFPP.Field.Exists
import HigherDimLFPPAS.Signed.Kernel

/-!
# Early assembly of the almost sure convergence theorem

This module converts Assumption 1.1 into the shared setting and records the composition while
the four probability/endpoint producers are still in progress. The producer interfaces are
passed to the composition as ordinary hypotheses; the final assembly will replace those
hypotheses with the producer theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS

open HigherDimLQGMetric HigherDimLFPPAS.Core
open HigherDimLQGContinuity
open HigherDimLFPP (Rd)

private theorem assembly_close_of_l23i {d : ℕ} {κ : Rd d → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    {ω : Ω} {R : ℝ} (hR : 0 < R)
    (hω : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun ε x => locField κ ε (h ω) x - convMollify κ ε (h ω) x) (fun _ => 0)
      (𝓝[>] (0 : ℝ)) (closedBall (0 : Rd d) R))
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ x ∈ closedBall (0 : Rd d) R,
        |locField κ ε (h ω) x - convMollify κ ε (h ω) x| ≤ η := by
  have hev := (Metric.tendstoUniformlyOn_iff.1 (hω R hR)) η hη
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεbound x hx
  have hlt := hsub ⟨hε, hεbound⟩ x hx
  simpa only [Real.dist_eq, zero_sub, abs_neg] using hlt.le

private theorem assembly_transfer_oscillation {d : ℕ} {κ : Rd d → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    {ω : Ω} {R a η : ℝ} (_hR : 0 < R) (ha : 0 < a) (hη : 0 < η)
    (hclose : ∀ η' : ℝ, 0 < η' → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x ∈ closedBall (0 : Rd d) R,
        |locField κ ε (h ω) x - convMollify κ ε (h ω) x| ≤ η')
    (hraw : ∀ η' : ℝ, 0 < η' → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ η') :
    ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ η ∧
          |locField κ ε (h ω) x - locField κ δ (h ω) x| ≤ η := by
  obtain ⟨εc, hεc, hclosec⟩ := hclose (η / 3) (by linarith)
  have hrawc := hraw (η / 3) (by linarith)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-a) < εc :=
    hpow.eventually (Iio_mem_nhds hεc)
  obtain ⟨Np, hNp⟩ := eventually_atTop.1 hev
  obtain ⟨Nraw, hNraw⟩ := eventually_atTop.1 hrawc
  let N := max Np Nraw
  have hN : ∀ n, N ≤ n → ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ η ∧
          |locField κ ε (h ω) x - locField κ δ (h ω) x| ≤ η := by
    intro n hn ε hε δ hδ x hx
    by_cases hn0 : n = 0
    · subst n
      have hbad : (1 : ℝ) ≤ 0 := by
        have hz : (0 : ℝ) ^ (-a) = 0 := Real.zero_rpow (neg_ne_zero.mpr ha.ne')
        calc
          1 = (((0 : ℝ) + 1) ^ (-a)) := by simp
          _ ≤ ε := by simpa using hε.1
          _ ≤ (0 : ℝ) ^ (-a) := by simpa using hε.2
          _ = 0 := hz
      linarith
    have hnpos : 0 < n := by omega
    have hupper : (n : ℝ) ^ (-a) < εc := hNp n (by dsimp [N] at hn; omega)
    have hraw' := hNraw n (by dsimp [N] at hn; omega)
    have hlowerPos : 0 < ((n : ℝ) + 1) ^ (-a) := Real.rpow_pos_of_pos (by positivity) _
    have hεpos : 0 < ε := hlowerPos.trans_le hε.1
    have hδpos : 0 < δ := hlowerPos.trans_le hδ.1
    have hεsmall : ε < εc := hε.2.trans_lt hupper
    have hδsmall : δ < εc := hδ.2.trans_lt hupper
    have he₁ := hclosec ε hεpos hεsmall x hx
    have he₂ := hclosec δ hδpos hδsmall x hx
    have hosc := hraw' ε hε δ hδ x hx
    have he₂' : |convMollify κ δ (h ω) x - locField κ δ (h ω) x| ≤ η / 3 := by
      simpa only [abs_sub_comm] using he₂
    constructor
    · exact hosc.trans (by linarith)
    · calc
      |locField κ ε (h ω) x - locField κ δ (h ω) x|
          ≤ |locField κ ε (h ω) x - convMollify κ ε (h ω) x| +
              |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| +
              |convMollify κ δ (h ω) x - locField κ δ (h ω) x| := by
            calc
              _ = |(locField κ ε (h ω) x - convMollify κ ε (h ω) x) +
                  (convMollify κ ε (h ω) x - convMollify κ δ (h ω) x) +
                  (convMollify κ δ (h ω) x - locField κ δ (h ω) x)| := by congr 1; ring
              _ ≤ _ := by
                calc
                  _ ≤ |(locField κ ε (h ω) x - convMollify κ ε (h ω) x) +
                      (convMollify κ ε (h ω) x - convMollify κ δ (h ω) x)| +
                      |convMollify κ δ (h ω) x - locField κ δ (h ω) x| := abs_add_le _ _
                  _ ≤ _ := by gcongr; exact abs_add_le _ _
        _ ≤ η := by linarith
  exact eventually_atTop.2 ⟨N, hN⟩

/-- F1b already has exactly the `Core.Lemma23i` interface. -/
theorem lemma23i_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.Lemma23i κ P h :=
  Field.lemma23i_of_setting_F1b hS

/-- F2b and the F1b localization estimate give the logarithmic bound for both fields. -/
theorem lemma23ii_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h23i : Core.Lemma23i κ P h) :
    Core.Lemma23ii κ P h := by
  have hraw := Gauss.lemma23_ii_all_F2b (by have := hS.dim; omega) hS.admissible hS.field
  filter_upwards [hraw, h23i] with ω hωraw hωloc
  intro R η hR hη
  have hclose := fun η' hη' => assembly_close_of_l23i (d := d) (κ := κ) (P := P)
    (h := h) (ω := ω) (R := R) hR hωloc (η := η') hη'
  obtain ⟨εr, hεr, hrawbound⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (hωraw R (η / 2) (by linarith))
  obtain ⟨εc, hεc, hclosebound⟩ := hclose (η / 2) (by linarith)
  let ε₀ := min εr (min εc (Real.exp (-1)))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; exact lt_min hεr (lt_min hεc (Real.exp_pos _))
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  intro x hx
  have hεr' : ε < εr := (hε.2.trans_le (min_le_left _ _))
  have hεc' : ε < εc := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hexp : ε ≤ Real.exp (-1) := (hε.2.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))).le
  have hlogε : Real.log ε ≤ -1 := by
    calc Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log hε.1 hexp
      _ = -1 := by rw [Real.log_exp]
  have hlog : 1 ≤ Real.log ε⁻¹ := by rw [Real.log_inv]; linarith
  have hraw' := hrawbound ⟨hε.1, hεr'⟩ x hx
  have hclose' := hclosebound ε hε.1 hεc' x hx
  constructor
  · exact hraw'.trans (by
      have hnonneg : 0 ≤ Real.log ε⁻¹ := le_trans (by norm_num) hlog
      nlinarith [Real.sqrt_nonneg (2 * (d : ℝ)), hnonneg])
  · have htri : |locField κ ε (h ω) x| ≤
        |convMollify κ ε (h ω) x| +
          |locField κ ε (h ω) x - convMollify κ ε (h ω) x| := by
      calc
        |locField κ ε (h ω) x| =
            |convMollify κ ε (h ω) x +
              (locField κ ε (h ω) x - convMollify κ ε (h ω) x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    calc
      |locField κ ε (h ω) x| ≤ _ := htri
      _ ≤ (Real.sqrt (2 * (d : ℝ)) + η / 2) * Real.log ε⁻¹ + η / 2 := add_le_add hraw' hclose'
      _ ≤ (Real.sqrt (2 * (d : ℝ)) + η) * Real.log ε⁻¹ := by
        nlinarith [Real.sqrt_nonneg (2 * (d : ℝ)), mul_nonneg (by linarith : 0 ≤ η / 2)
          (by linarith : 0 ≤ Real.log ε⁻¹ - 1)]

/-- Transfer the F2b oscillation bound from the convolution field to the localized field. -/
theorem lemma23iii_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h23i : Core.Lemma23i κ P h) :
    Core.Lemma23iii κ P h := by
  intro a ha
  have hraw := Gauss.lemma23_iii_F2b (by have := hS.dim; omega) hS.admissible hS.field ha
  have hmag := Gauss.lemma23_ii_all_F2b (by have := hS.dim; omega) hS.admissible hS.field
  filter_upwards [hraw, hmag, h23i] with ω hωraw hωmag hωloc
  intro R η hR hη
  have hclose := fun η' hη' => assembly_close_of_l23i (d := d) (κ := κ) (P := P)
    (h := h) (ω := ω) (R := R) hR hωloc (η := η') hη'
  exact assembly_transfer_oscillation (d := d) (κ := κ) (P := P) (h := h) (ω := ω)
    (R := R) (a := a) (η := η) hR ha hη hclose
    (fun η' hη' => hωraw R η' hη')

/-- The landed L32m theorem already states the Core interface verbatim. -/
theorem lemma32Meas_adapter {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.Lemma32Meas κ ξ Q D P h :=
  Annulus.lemma32Meas_holds hS

/-- C27's open-set, C¹-path statement specializes to the Core open-ball internal metric form. -/
theorem lemma27_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.Lemma27Stmt κ ξ D P h := by
  intro q hq
  obtain ⟨C, hC, εbase, hεbase, H⟩ := Coarse.c27_lemma27
    (by have := hS.dim; omega) hS.xi_pos hS.admissible hS.strong hS.field hS.conv
    hq.1 hq.2 (β := 1) one_pos
  refine ⟨C, 1, hC, one_pos, ?_⟩
  intro ρ hρ
  let ε₀ := min εbase 1
  refine ⟨(2 * ρ + 7) ^ d, ε₀, lt_min hεbase one_pos, ?_⟩
  intro ε hε
  have hεbase' : ε ∈ Ioo (0 : ℝ) εbase :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hεone : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have Hρ := H ρ hρ.le (ball (0 : Rd d) ρ) isOpen_ball
    (by
      intro x hx
      exact ball_subset_closedBall hx) P h hS.field ε hεbase'
  have hsubset :
      {ω | ¬ ∀ x ∈ ball (0 : Rd d) ρ, ∀ y ∈ ball (0 : Rd d) ρ,
        setDistIn (Core.Meps κ ξ ε (h ω)) (thickening (ε ^ q) (ball 0 ρ))
            (ball x (ε ^ q)) (ball y (ε ^ q)) ≤ ENNReal.ofReal C * (D (h ω)).internal (ball 0 ρ) x y ∧
        setDistIn (D (h ω)) (thickening (ε ^ q) (ball 0 ρ))
            (ball x (ε ^ q)) (ball y (ε ^ q)) ≤ ENNReal.ofReal C *
              (Core.Meps κ ξ ε (h ω)).internal (ball 0 ρ) x y} ⊆
      {ω | ¬ ∀ φ : C(Rd d, ℝ), ⇑φ = locField κ ε (h ω) →
        ∀ ha : 0 < (aEps κ ξ ε)⁻¹, ∀ x ∈ ball (0 : Rd d) ρ, ∀ y ∈ ball (0 : Rd d) ρ,
          setDistIn ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha)
              (thickening (ε ^ q) (ball 0 ρ)) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * (D (h ω)).internal (ball 0 ρ) x y ∧
          setDistIn (D (h ω)) (thickening (ε ^ q) (ball 0 ρ)) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha).internal (ball 0 ρ) x y} := by
    intro ω hcore hgood
    apply hcore
    intro x hx y hy
    let φ : C(Rd d, ℝ) := Core.locFieldC κ ε (h ω)
    have hφ : ⇑φ = locField κ ε (h ω) :=
      Localize.locFieldC_coe
        (continuous_locField hS.seed.kernelSmooth
          (Localize.locRad_pos_of_mem_Ioo hεone) (h ω))
    have hεpos : 0 < ε := hε.1
    have ha0 : 0 < aEps κ ξ ε := hS.seed.aEps_pos ξ ε hεpos
    have ha : 0 < (aEps κ ξ ε)⁻¹ := inv_pos.2 ha0
    have hMeps : Core.Meps κ ξ ε (h ω) =
        (fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha := by
      dsimp [φ]
      exact Localize.meps_eq_smul (h ω) ha0
    have hC27 := hgood φ hφ ha x hx y hy
    constructor
    · simpa only [hMeps] using hC27.1
    · simpa only [hMeps] using hC27.2
  calc
    P {ω | ¬ ∀ x ∈ ball (0 : Rd d) ρ, ∀ y ∈ ball (0 : Rd d) ρ,
      setDistIn (Core.Meps κ ξ ε (h ω)) (thickening (ε ^ q) (ball 0 ρ))
          (ball x (ε ^ q)) (ball y (ε ^ q)) ≤ ENNReal.ofReal C * (D (h ω)).internal (ball 0 ρ) x y ∧
      setDistIn (D (h ω)) (thickening (ε ^ q) (ball 0 ρ))
          (ball x (ε ^ q)) (ball y (ε ^ q)) ≤ ENNReal.ofReal C *
            (Core.Meps κ ξ ε (h ω)).internal (ball 0 ρ) x y}
        ≤ P {ω | ¬ ∀ φ : C(Rd d, ℝ), ⇑φ = locField κ ε (h ω) →
          ∀ ha : 0 < (aEps κ ξ ε)⁻¹, ∀ x ∈ ball (0 : Rd d) ρ, ∀ y ∈ ball (0 : Rd d) ρ,
            setDistIn ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha)
                (thickening (ε ^ q) (ball 0 ρ)) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * (D (h ω)).internal (ball 0 ρ) x y ∧
            setDistIn (D (h ω)) (thickening (ε ^ q) (ball 0 ρ)) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha).internal (ball 0 ρ) x y} :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal ((2 * ρ + 7) ^ d * ε ^ (1 : ℝ)) := Hρ

/-- The frozen Assumption 1.1 supplies the corresponding `Core.Setting` at `Q = distExp d ξ`. -/
theorem setting_of_assumption11 {d : ℕ} {ξ : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hκ : IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) (hA : Assumption11 d ξ κ D P h) :
    Core.Setting d ξ (distExp d ξ) κ D P h := by
  exact ⟨hd, hξ, hA.subcritical, hκ,
    Glue.seedFacts_of_admissible hd hκ, hA.strong, hh, hA.conv⟩

/-! The four producer inputs are polymorphic interface theorems, so the proof can specialize them
to the setting supplied by Assumption 1.1. L32p's input includes its two rescaling interfaces;
they are grouped with its marginal estimate because those three outputs travel together through
that packet's handoff. -/

theorem asConvergence_of_remaining
    (h24 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma23i κ P h →
      Core.Lemma24Conv κ ξ D P h ∧ Core.Lemma24Confine κ ξ P h)
    (h32p : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h →
      Core.PairLaw κ ξ D P h ∧ Core.RescaledConv κ ξ D P h ∧
        (Core.LocFieldScaling κ → Core.CoordScaling ξ Q D P h →
          Core.AffineInternalScaling d → Core.PairLaw κ ξ D P h →
          Core.RescaledConv κ ξ D P h → Core.Lemma32Marginal κ ξ Q D P h))
    (h61 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma27Stmt κ ξ D P h →
      Core.Lemma23ii κ P h → Core.Lemma25Exponent κ ξ Q → Core.Lemma61Stmt κ ξ D P h)
    (h62 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma61Stmt κ ξ D P h →
      Core.Lemma27Stmt κ ξ D P h → Core.Lemma23i κ P h → Core.Lemma23iii κ P h →
      Core.Lemma25Window κ ξ → Core.Lemma62Stmt κ ξ P h) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ →
      ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ D : DistRd d → ContMetric d,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → Assumption11 d ξ κ D P h →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) := by
  intro d ξ hd hξ κ hκ D Ω _ P _ h hh hA
  let hS := setting_of_assumption11 hd hξ hκ hh hA
  let h23i := lemma23i_holds hS
  let h23ii := lemma23ii_holds hS h23i
  let h23iii := lemma23iii_holds hS h23i
  let h25 := Glue.lemma25_holds hS
  let h24' := h24 hS h23i
  have hsc := Scaling.locFieldScaling_holds (by have := hS.dim; omega) hS.seed.kernelSmooth
  have hcs := Scaling.coordScaling_holds hS
  have hai := Scaling.affineInternalScaling_holds d
  obtain ⟨hpl, hrc, h32producer⟩ := h32p hS
  have h32m := h32producer hsc hcs hai hpl hrc
  have h32me := lemma32Meas_adapter hS
  have h33 := Covering.lemma33_holds hS h32m h32me
  have h27 := lemma27_holds hS
  have hus := Scaling.unitSpeedAdmissible_holds d
  have h41 := Iterate.prop41_holds d
  have h51 := SharpComp.prop51_holds hS h41 hus h33 h27 h24'.1 h24'.2
  have h61' := h61 hS h27 h23ii h25.2.2
  have h62' := h62 hS h61' h27 h23i h23iii h25.2.1
  exact Main.asConclusion_of_parts hS hus h51 h61' h62' h23i h23iii h25.2.1

/-- The unconditional convergence corollary from the four remaining producer interfaces. -/
theorem asConvergence_nonneg_of_remaining
    (h24 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma23i κ P h →
      Core.Lemma24Conv κ ξ D P h ∧ Core.Lemma24Confine κ ξ P h)
    (h32p : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h →
      Core.PairLaw κ ξ D P h ∧ Core.RescaledConv κ ξ D P h ∧
        (Core.LocFieldScaling κ → Core.CoordScaling ξ Q D P h →
          Core.AffineInternalScaling d → Core.PairLaw κ ξ D P h →
          Core.RescaledConv κ ξ D P h → Core.Lemma32Marginal κ ξ Q D P h))
    (h61 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma27Stmt κ ξ D P h →
      Core.Lemma23ii κ P h → Core.Lemma25Exponent κ ξ Q → Core.Lemma61Stmt κ ξ D P h)
    (h62 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma61Stmt κ ξ D P h →
      Core.Lemma27Stmt κ ξ D P h → Core.Lemma23i κ P h → Core.Lemma23iii κ P h →
      Core.Lemma25Window κ ξ → Core.Lemma62Stmt κ ξ P h) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧
      HigherDimLQGContinuity.IsMedianOne d D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) := by
  intro d ξ hd hξ hsub
  obtain ⟨⟨D, hD, hconv⟩, -⟩ := HigherDimLQGMetric.theorem12 d ξ hd hξ hsub
  obtain ⟨κ₀, hκ₀⟩ := HigherDimLFPP.exists_isLFPPKernel d
  refine ⟨D, hD, (HigherDimLQGContinuity.isMedianOne_iff_isMedian hD.measurable).2 ?_, ?_⟩
  · exact HigherDimLQGMetric.l10a_subseq_limit_median_one (by omega) hκ₀ ξ
      (fun n : ℕ => 1 / ((n : ℝ) + 2))
      (fun n => (one_div_pos.2 (by positivity) : (0 : ℝ) < 1 / ((n : ℝ) + 2)))
      (fun P _ h hh R hR δ hδ =>
        (hconv κ₀ hκ₀ P h hh R hR δ hδ).comp
          HigherDimLQGContinuity.par_tendsto_inv_nat_add_two)
  · intro κ hκ Ω _ P _ h hh
    exact asConvergence_of_remaining h24 h32p h61 h62 d ξ hd hξ κ
      (HigherDimLFPP.IsLFPPKernel.toAdmissibleSeed hκ) D P h hh
      ⟨hsub, hD, hconv κ hκ P h hh.1.isLGFPlusBddCont⟩

/-- The almost-sure limit is every median-one strong metric, using the unconditional corollary. -/
theorem asConvergence_medianOne_of_remaining
    (h24 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma23i κ P h →
      Core.Lemma24Conv κ ξ D P h ∧ Core.Lemma24Confine κ ξ P h)
    (h32p : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h →
      Core.PairLaw κ ξ D P h ∧ Core.RescaledConv κ ξ D P h ∧
        (Core.LocFieldScaling κ → Core.CoordScaling ξ Q D P h →
          Core.AffineInternalScaling d → Core.PairLaw κ ξ D P h →
          Core.RescaledConv κ ξ D P h → Core.Lemma32Marginal κ ξ Q D P h))
    (h61 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma27Stmt κ ξ D P h →
      Core.Lemma23ii κ P h → Core.Lemma25Exponent κ ξ Q → Core.Lemma61Stmt κ ξ D P h)
    (h62 : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma61Stmt κ ξ D P h →
      Core.Lemma27Stmt κ ξ D P h → Core.Lemma23i κ P h → Core.Lemma23iii κ P h →
      Core.Lemma25Window κ ξ → Core.Lemma62Stmt κ ξ P h) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
      HigherDimLQGContinuity.IsMedianOne d D →
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) := by
  intro d ξ hd hξ hsub D hD hD1 κ hκ Ω _ P _ h hh
  obtain ⟨D₀, hD₀, hD₀1, hconv⟩ :=
    asConvergence_nonneg_of_remaining h24 h32p h61 h62 d ξ hd hξ hsub
  obtain ⟨V, -, -, hV, -⟩ := HigherDimLQGContinuity.theorem11Xi d hd
  filter_upwards [hconv κ hκ P h hh, hV ξ hξ hsub D hD hD1 P h hh,
    hV ξ hξ hsub D₀ hD₀ hD₀1 P h hh] with ω h1 h2 h3 F hF
  rw [← h2, h3]
  exact h1 F hF

end HigherDimLFPPAS
