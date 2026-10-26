import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Localize.Conv

/-!
# Rescaled convergence on the pinned field (`Core.RescaledConv`)

Packet RZC (route 2 of packet RZ) for Lemma 3.2 and Lemma 4.3′ of
`source/higher-dimensional-lfpp-almost-sure.pdf`; planning audits MA1 Details A10.3 (second half), A6.1, A4 and
MA3 P9(b). The proof is the one of Lemma 2.4 (i) (packet L24, `Localize.lemma24Conv_of_setting`) with `M_ε` replaced by
the rescaled localized metric `𝔐_{ε,ε/r} = 𝔞_{ε/r}⁻¹ D^{ĝ_{ε/r,ε}}` (`Core.MepsR`) and the convergence (1.6) of
Assumption 1.1 taken along `δ_j = ε_j / r_j → 0⁺`.

* `rzc_continuous_locFieldR`, `rzc_locFieldRC_coe`: for a smooth kernel and `locRad ε / r > 0`, the field
  `ĝ_{ε/r,ε} = Core.locFieldR κ ε r g` is continuous for every distribution `g`, so the bundled field is not junk.
* `rzc_mepsR_eq_smul`, `rzc_mepsR_apply`, `rzc_mepsR_eq_weylMetric`: for `𝔞_{ε/r} > 0`,
  `𝔐_{ε,ε/r} = e^{ξ(ĝ_{ε/r,ε} − g ∗ K_{ε/r})} · N_{ε/r}` (Weyl scaling of the length metric `N_{ε/r} = Core.Neps`).
* `rzc_measurable_mepsR`: `ω ↦ 𝔐_{ε,ε/r}(h ω)` is measurable (smooth kernel, `locRad ε / r > 0`, `𝔞_{ε/r} > 0`).
* `rzc_tendsto_mepsR_of_tendsto_neps` (deterministic, MA1 A6.1 in Weyl form): if `N_{δ_n}(g) → G` locally uniformly
  with `G` a proper length metric and `ĝ_{δ_n,ε_n} − g ∗ K_{δ_n} → 0` uniformly on centred balls, then
  `𝔐_{ε_n,δ_n}(g) → G` locally uniformly (packet D1's `Det.eventually_weyl_metric_local_comparison`).
* `rzc_ae_tendstoUniformlyOn_locDiff`: (3.9) (`Core.RescaledLoc`) along a sequence `(ε_j, r_j)`: a.s., for every
  `R > 0`, `ĝ_{ε_j/r_j, ε_j}(h) − h ∗ K_{ε_j/r_j} → 0` uniformly on `B̄_R` (countably many a.s. events: integer radii
  and indices).
* `rzc_exists_subseq_ae`: along a sequence with `ε_j ∈ (0,1)`, a subsequence has `𝔐_j(h) → D_h` a.s. in
  `C(ℝ^d × ℝ^d, ℝ)` (`l8_exists_subseq_ae_of_prob` for `N_{δ_j}`, then the deterministic step on the event of (3.9),
  of properness (Lemma 2.2) and of the length property of `D_h`).
* `rzc_rescaledConv_of_lt_one` and the packet target `rescaledConv_holds`: `l8_tendstoInProbLU_of_ae` and the
  subsequence criterion `Filter.tendsto_of_subseq_tendsto`; the general sequence is shifted so that `ε_j < 1`
  (`Filter.tendsto_add_atTop_iff_nat`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Rescale

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-! ## The rescaled localized field `ĝ_{ε/r,ε}` and the metric `𝔐_{ε,ε/r}` -/

section Deterministic

variable {d : ℕ}

/-- For a smooth kernel and `locRad ε / r > 0`, the rescaled localized field `ĝ_{ε/r,ε}` of (3.8) is continuous for
every distribution `g`. -/
theorem rzc_continuous_locFieldR {κ : Rd d → ℝ} {ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < locRad ε / r) (g : DistRd d) :
    Continuous (Core.locFieldR κ ε r g) :=
  continuous_const.mul (continuous_apply_locTest hK hs g)

/-- Where it is continuous (smooth kernel, `locRad ε / r > 0`), the bundled field `Core.locFieldRC` is `ĝ_{ε/r,ε}`. -/
theorem rzc_locFieldRC_coe {κ : Rd d → ℝ} {ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < locRad ε / r) (g : DistRd d) :
    ⇑(Core.locFieldRC κ ε r g) = Core.locFieldR κ ε r g := by
  unfold Core.locFieldRC
  rw [dite_eq_left (rzc_continuous_locFieldR hK hs g)]
  rfl

theorem rzc_mepsR_eq_smul {κ : Rd d → ℝ} {ξ ε r : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ (ε / r)) :
    Core.MepsR κ ξ ε r g =
      (fieldLfppMetric ξ (Core.locFieldRC κ ε r g)).smul (aEps κ ξ (ε / r))⁻¹ (inv_pos.2 ha) := by
  unfold Core.MepsR
  rw [dite_eq_left ha]

theorem rzc_mepsR_apply {κ : Rd d → ℝ} {ξ ε r : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ (ε / r))
    (p : Rd d × Rd d) :
    (Core.MepsR κ ξ ε r g).1 p = (aEps κ ξ (ε / r))⁻¹ * fieldLfpp ξ (Core.locFieldRC κ ε r g) p := by
  rw [rzc_mepsR_eq_smul g ha, ContMetric.smul_apply, fieldLfppMetric_apply]

/-- **`𝔐_{ε,ε/r}` is the Weyl scaling `e^{ξ(ĝ_{ε/r,ε} − g ∗ K_{ε/r})} · N_{ε/r}`** of the length metric `N_{ε/r}`
(for `𝔞_{ε/r} > 0`; no continuity hypothesis: both sides use the bundled fields). -/
theorem rzc_mepsR_eq_weylMetric {κ : Rd d → ℝ} {ξ ε r : ℝ} (g : DistRd d)
    (ha : 0 < aEps κ ξ (ε / r)) :
    (Core.MepsR κ ξ ε r g).1 =
      (weylMetric ξ (Core.locFieldRC κ ε r g - Core.convFieldC κ (ε / r) g)
        (Core.Neps κ ξ (ε / r) g) (Localize.neps_isLength κ ξ (ε / r) g)).1 := by
  ext p
  rw [weylMetric_apply]
  have hN := Localize.neps_eq_smul (κ := κ) (ξ := ξ) g ha
  have hW : (weylScale ξ (Core.locFieldRC κ ε r g - Core.convFieldC κ (ε / r) g)
      (Core.Neps κ ξ (ε / r) g) p.1 p.2).toReal = (aEps κ ξ (ε / r))⁻¹ * fieldLfpp ξ
        (⇑(Core.convFieldC κ (ε / r) g) + ⇑(Core.locFieldRC κ ε r g - Core.convFieldC κ (ε / r) g))
        (p.1, p.2) := by
    rw [hN]
    exact l6c_scaledLfpp_weyl_field ξ (aEps κ ξ (ε / r)) ha _ _ p.1 p.2
  rw [hW, rzc_mepsR_apply g ha]
  congr 2
  funext z
  simp only [Pi.add_apply, ContinuousMap.coe_sub, Pi.sub_apply, add_sub_cancel]

/-- For a smooth kernel, `locRad ε / r > 0` and `𝔞_{ε/r} > 0`, `ω ↦ 𝔐_{ε,ε/r}(h ω)` is measurable. -/
theorem rzc_measurable_mepsR {κ : Rd d → ℝ} {ξ ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < locRad ε / r)
    (ha : 0 < aEps κ ξ (ε / r)) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistRd d}
    (hh : Measurable h) :
    Measurable fun ω => (Core.MepsR κ ξ ε r (h ω)).1 := by
  have hloc : Measurable fun ω => Core.locFieldRC κ ε r (h ω) := by
    refine ContinuousMap.measurable_iff_eval.2 fun z => ?_
    have heq : (fun ω => Core.locFieldRC κ ε r (h ω) z) =
        fun ω => Core.locFieldR κ ε r (h ω) z := by
      funext ω
      rw [rzc_locFieldRC_coe hK hs]
    rw [heq]
    have hm : Measurable fun g : DistRd d => Core.locFieldR κ ε r g z :=
      measurable_const.mul (measurable_distOn_apply _)
    exact hm.comp hh
  have heq : (fun ω => (Core.MepsR κ ξ ε r (h ω)).1) =
      (fun φ : C(Rd d, ℝ) => ((fieldLfppMetric ξ φ).smul (aEps κ ξ (ε / r))⁻¹ (inv_pos.2 ha)).1) ∘
        fun ω => Core.locFieldRC κ ε r (h ω) := by
    funext ω
    simp only [Function.comp_apply, rzc_mepsR_eq_smul (h ω) ha]
  rw [heq]
  exact (Localize.measurable_smul_fieldLfppMetric ξ (inv_pos.2 ha)).comp hloc

/-- **Deterministic step** (MA1 A6.1 and A10.3, Weyl form): along sequences `ε_n, r_n` with `𝔞_{ε_n/r_n} > 0`, if
`N_{ε_n/r_n}(g) → G` locally uniformly with `G` a proper length metric and `ĝ_{ε_n/r_n,ε_n} − g ∗ K_{ε_n/r_n} → 0`
uniformly on every centred ball, then `𝔐_{ε_n,ε_n/r_n}(g) → G` locally uniformly. -/
theorem rzc_tendsto_mepsR_of_tendsto_neps {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d} {G : ContMetric d}
    (hG : G.IsLength) (hGp : IsProperFn G.1) (εs rs : ℕ → ℝ)
    (ha : ∀ n, 0 < aEps κ ξ (εs n / rs n))
    (hN : Tendsto (fun n => (Core.Neps κ ξ (εs n / rs n) g).1) atTop (𝓝 G.1))
    (hu : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n => ⇑(Core.locFieldRC κ (εs n) (rs n) g - Core.convFieldC κ (εs n / rs n) g)) 0 atTop
      (closedBall (0 : Rd d) R)) :
    Tendsto (fun n => (Core.MepsR κ ξ (εs n) (rs n) g).1) atTop (𝓝 G.1) := by
  have hNlu := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hN
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hNlu
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r, hr, hKr⟩ := Localize.exists_closedBall_prod_of_isCompact hK
  have hconvD : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n => ⇑(Core.Neps κ ξ (εs n / rs n) g).1) ⇑G.1
      atTop (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := fun R _ =>
    hNlu _ ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨R, -, s, -, -, N, hN'⟩ := Det.eventually_weyl_metric_local_comparison ξ
    (fun n => Core.Neps κ ξ (εs n / rs n) g) G
    (fun n => Localize.neps_isLength κ ξ (εs n / rs n) g) hG hGp hconvD
    (fun n => Core.locFieldRC κ (εs n) (rs n) g - Core.convFieldC κ (εs n / rs n) g) hu
    (isCompact_closedBall (0 : Rd d) r)
  have h0 : (0 : Rd d) ∈ closedBall (0 : Rd d) r := mem_closedBall_self hr.le
  have hW := (hN' N le_rfl 0 h0 0 h0).2.2
  refine (hW.congr (Eventually.of_forall fun n p _ => ?_)).mono hKr
  exact (congrFun (congrArg DFunLike.coe (rzc_mepsR_eq_weylMetric g (ha n))) p).symm

end Deterministic

/-! ## (3.9) along a sequence and the subsequence argument -/

section Probabilistic

/-- **(3.9) along a sequence** (MA1 A10.2–A10.3): for `0 < ε_j ≤ r_j ≤ 1` with `ε_j → 0`, almost surely, for every
`R > 0`, `ĝ_{ε_j/r_j, ε_j}(h) − h ∗ K_{ε_j/r_j} → 0` uniformly on `B̄_R`. The a.s. events of `Core.RescaledLoc` are
taken at the integer radii `m + 1` and at the indices `j` (countably many); on their intersection the error is at most
`C_{m+1}(ω) ρ_{m+1}(ε_j) → 0`. -/
theorem rzc_ae_tendstoUniformlyOn_locDiff {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    (hloc : Core.RescaledLoc κ P h) (εs rs : ℕ → ℝ)
    (hεr : ∀ j, 0 < εs j ∧ εs j ≤ rs j ∧ rs j ≤ 1) (hε : Tendsto εs atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun j x => Core.locFieldR κ (εs j) (rs j) (h ω) x - convMollify κ (εs j / rs j) (h ω) x) 0
      atTop (closedBall (0 : Rd d) R) := by
  unfold Core.RescaledLoc at hloc
  choose C ρ ε₀ hε₀ hρ hb using hloc
  have hpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have hae : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ j : ℕ, εs j < ε₀ ((m : ℝ) + 1) (hpos m) →
      ∀ x ∈ closedBall (0 : Rd d) ((m : ℝ) + 1),
        |Core.locFieldR κ (εs j) (rs j) (h ω) x - convMollify κ (εs j / rs j) (h ω) x| ≤
          C ((m : ℝ) + 1) (hpos m) ω * ρ ((m : ℝ) + 1) (hpos m) (εs j) := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro j
    by_cases hj : εs j < ε₀ ((m : ℝ) + 1) (hpos m)
    · filter_upwards [hb ((m : ℝ) + 1) (hpos m) (εs j) ⟨(hεr j).1, hj⟩ (rs j)
        ⟨(hεr j).2.1, (hεr j).2.2⟩] with ω hω _ x hx using hω x hx
    · exact Eventually.of_forall fun ω h' => absurd h' hj
  have hεT : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun j => (hεr j).1⟩
  filter_upwards [hae] with ω hω R hR
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have h1 : ∀ᶠ j in atTop, εs j < ε₀ ((m : ℝ) + 1) (hpos m) :=
    hε.eventually (gt_mem_nhds (hε₀ _ (hpos m)))
  have h2 : Tendsto (fun j => C ((m : ℝ) + 1) (hpos m) ω * ρ ((m : ℝ) + 1) (hpos m) (εs j)) atTop
      (𝓝 0) := by
    have h3 := ((hρ _ (hpos m)).comp hεT).const_mul (C ((m : ℝ) + 1) (hpos m) ω)
    simpa only [mul_zero, Function.comp_def] using h3
  filter_upwards [h1, h2.eventually (gt_mem_nhds he)] with j hj1 hj2 x hx
  have hb' := hω m j hj1 x (closedBall_subset_closedBall (by linarith) hx)
  rw [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs]
  exact lt_of_le_of_lt hb' hj2

/-- **A.s. convergence along a subsequence** (MA1 A10.3): along every sequence with `ε_j ∈ (0, 1)`, `ε_j ≤ r_j ≤ 1`,
`ε_j → 0` and `ε_j / r_j → 0`, some subsequence has `𝔐_{ε_j,ε_j/r_j}(h) → D_h` almost surely in
`C(ℝ^d × ℝ^d, ℝ)`. -/
theorem rzc_exists_subseq_ae {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (hloc : Core.RescaledLoc κ P h) (εs rs : ℕ → ℝ)
    (hεr : ∀ j, 0 < εs j ∧ εs j < 1 ∧ εs j ≤ rs j ∧ rs j ≤ 1) (hε : Tendsto εs atTop (𝓝 0))
    (hδ : Tendsto (fun j => εs j / rs j) atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P,
      Tendsto (fun n => (Core.MepsR κ ξ (εs (ms n)) (rs (ms n)) (h ω)).1) atTop
        (𝓝 (D (h ω)).1) := by
  have hcont := Localize.ae_continuous_convMollify hS
  have hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLength := hS.strong.length P h hS.field.1.isLGFPlusCont
  have hprop := lemma22_ae_proper_and_geodesic hS.dim hS.xi_pos hS.subcrit P h hS.field D
    hS.strong
  have hrpos : ∀ j, 0 < rs j := fun j => (hεr j).1.trans_le (hεr j).2.2.1
  have hδpos : ∀ j, 0 < εs j / rs j := fun j => div_pos (hεr j).1 (hrpos j)
  have hδT : Tendsto (fun j => εs j / rs j) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hδ, Eventually.of_forall hδpos⟩
  have ha : ∀ j, 0 < aEps κ ξ (εs j / rs j) := fun j => hS.seed.aEps_pos ξ _ (hδpos j)
  -- `N_{δ_j} → D` in probability (Assumption 1.1 (v) along `δ_j → 0⁺`)
  have hNprob : TendstoInProbLU P (fun j ω => (Core.Neps κ ξ (εs j / rs j) (h ω)).1) atTop
      (fun ω => (D (h ω)).1) := by
    intro R' hR' η' hη'
    refine Tendsto.congr' (Eventually.of_forall fun j => ?_) ((hS.conv R' hR' η' hη').comp hδT)
    simp only [Function.comp_apply]
    apply measure_congr
    filter_upwards [hcont] with ω hω
    have hfun : (aEps κ ξ (εs j / rs j))⁻¹ • lfppDist κ ξ (εs j / rs j) (h ω) =
        ⇑(Core.Neps κ ξ (εs j / rs j) (h ω)).1 :=
      funext fun p => (Localize.neps_apply_eq_lfppDist (ha j) (hω _ (hδpos j)) p).symm
    rw [hfun]
  obtain ⟨ms, hms, hae⟩ := l8_exists_subseq_ae_of_prob P
    (fun j ω => (Core.Neps κ ξ (εs j / rs j) (h ω)).1) (fun ω => (D (h ω)).1)
    (fun j => Localize.aemeasurable_neps (ha j) hS.field.1.measurable
      (hcont.mono fun ω hω => hω _ (hδpos j))) hNprob
  have hdiff := rzc_ae_tendstoUniformlyOn_locDiff hloc εs rs
    (fun j => ⟨(hεr j).1, (hεr j).2.2.1, (hεr j).2.2.2⟩) hε
  refine ⟨ms, hms, ?_⟩
  -- on the events of (1.6) along the subsequence, (3.9), continuity, length and properness
  filter_upwards [hae, hdiff, hcont, hlen, hprop] with ω hω hdω hcω hlω hpω
  refine rzc_tendsto_mepsR_of_tendsto_neps hlω (Localize.isProperFn_of_properSpace _ hpω.2.1)
    (fun n => εs (ms n)) (fun n => rs (ms n)) (fun n => ha (ms n)) hω fun R' hR' => ?_
  refine (Localize.tendstoUniformlyOn_comp_tendsto (hdω R' hR') hms.tendsto_atTop).congr
    (Eventually.of_forall fun n x _ => ?_)
  have hs : 0 < locRad (εs (ms n)) / rs (ms n) :=
    div_pos (Localize.locRad_pos_of_mem_Ioo ⟨(hεr _).1, (hεr _).2.1⟩) (hrpos _)
  have hlc := rzc_locFieldRC_coe (g := h ω) hS.seed.kernelSmooth hs
  have hcv := Localize.convFieldC_coe (hcω _ (hδpos (ms n)))
  simp only [ContinuousMap.coe_sub, Pi.sub_apply, hlc, hcv]

/-- `Core.RescaledConv` along sequences with `ε_j < 1` (where every `𝔐_j` is measurable): `l8_tendstoInProbLU_of_ae`
along the subsequences of `rzc_exists_subseq_ae`, and the subsequence criterion. -/
theorem rzc_rescaledConv_of_lt_one {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (hloc : Core.RescaledLoc κ P h) (εs rs : ℕ → ℝ)
    (hεr : ∀ j, 0 < εs j ∧ εs j < 1 ∧ εs j ≤ rs j ∧ rs j ≤ 1) (hε : Tendsto εs atTop (𝓝 0))
    (hδ : Tendsto (fun j => εs j / rs j) atTop (𝓝 0)) :
    TendstoInProbLU P (fun j ω => (Core.MepsR κ ξ (εs j) (rs j) (h ω)).1) atTop
      (fun ω => (D (h ω)).1) := by
  have hY : Measurable fun ω => (D (h ω)).1 :=
    Localize.measurable_metric_comp hS.strong.measurable hS.field.1.measurable
  have hrpos : ∀ j, 0 < rs j := fun j => (hεr j).1.trans_le (hεr j).2.2.1
  have hs : ∀ j, 0 < locRad (εs j) / rs j := fun j =>
    div_pos (Localize.locRad_pos_of_mem_Ioo ⟨(hεr j).1, (hεr j).2.1⟩) (hrpos j)
  have ha : ∀ j, 0 < aEps κ ξ (εs j / rs j) := fun j =>
    hS.seed.aEps_pos ξ _ (div_pos (hεr j).1 (hrpos j))
  intro R hR η hη
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, -, hae⟩ := rzc_exists_subseq_ae hS hloc (fun j => εs (ns j)) (fun j => rs (ns j))
    (fun j => hεr (ns j)) (hε.comp hns) (hδ.comp hns)
  have hMm : ∀ n, AEMeasurable
      (fun ω => (Core.MepsR κ ξ (εs (ns (ms n))) (rs (ns (ms n))) (h ω)).1) P := fun n =>
    (rzc_measurable_mepsR hS.seed.kernelSmooth (hs (ns (ms n))) (ha (ns (ms n)))
      hS.field.1.measurable).aemeasurable
  have hprob := l8_tendstoInProbLU_of_ae P
    (fun n ω => (Core.MepsR κ ξ (εs (ns (ms n))) (rs (ns (ms n))) (h ω)).1)
    (fun ω => (D (h ω)).1) hMm hY hae
  exact ⟨ms, hprob R hR η hη⟩

/-- **Rescaled convergence on the pinned field** (`Core.RescaledConv`; MA1 A10.3, MA3 P9(b)): from the standing
hypotheses and (3.9), along every sequence `ε_j ↓ 0` with `ε_j ≤ r_j ≤ 1` and `ε_j / r_j → 0`,
`𝔐_{ε_j,ε_j/r_j}(h) → D_h` in probability, locally uniformly. -/
theorem rescaledConv_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (hloc : Core.RescaledLoc κ P h) :
    Core.RescaledConv κ ξ D P h := by
  intro εs rs hεr hε hδ
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hε.eventually (gt_mem_nhds one_pos))
  have H := rzc_rescaledConv_of_lt_one hS hloc (fun j => εs (j + J)) (fun j => rs (j + J))
    (fun j => ⟨(hεr _).1, hJ _ (Nat.le_add_left _ _), (hεr _).2.1, (hεr _).2.2⟩)
    (hε.comp (tendsto_add_atTop_nat J)) (hδ.comp (tendsto_add_atTop_nat J))
  intro R hR η hη
  exact (tendsto_add_atTop_iff_nat J).1 (H R hR η hη)

end Probabilistic

end HigherDimLFPPAS.Rescale
