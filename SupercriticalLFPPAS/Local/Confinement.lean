import SupercriticalLFPPAS.Local.MetricTools
import SupercriticalLFPPAS.Inputs.EscapeTendsto
import SupercriticalLFPPAS.Inputs.CircleSetDistance
import SupercriticalLFPPAS.Field.LocalizedApproximation
import SupercriticalLQGUniqueness.B2.Polylog.P7Trunc
import SupercriticalLQGUniqueness.B2.PfeLocal.L4Main
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong

/-!
# Lemma 2.2: confinement of short paths (packet P32)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 2.2 (l. 196–207): for each compact `K`
and `M < ∞`, the probability that an `X̂_ε`-path of length at most `M` starting in `K` exits
`B_R(0)` tends to zero as first `ε → 0` and then `R → ∞`; the same for `X_ε`.

Following the planning audit `planning/audits/SB1-sections-1-3.md` §2.7 (item 20) and A10, the
event is the measurable, larger event `{X̂_ε(K, ∂B_R(0)) ≤ M}`: any such path, stopped at its first
hit of `∂B_R(0)`, witnesses it.

* `setDistance_thickening_le_of_compare` (deterministic): on the event of (2.8) for
  `U = B_{R+1}(0)` and `ρ = ε^{1−ζ}`, `X̂_ε(K, ∂B_R) ≤ M` implies
  `D(K^ρ, (∂B_R)^ρ) ≤ C₀(M + 1/2)`.
* `setDistance_le_of_thickening` (deterministic): lower semicontinuity and compactness,
  `D(K, S) ≤ c` if `D(K^ρ, S^ρ) ≤ c` along `ρ ↓ 0`.
* `lemma_2_2_loc_of_comparison`: the localized statement, from (2.8) (packet D6, as a hypothesis
  until it lands; instantiated in `Local/ConfinementD6.lean`) and (1.4) (`ae_d2EscapeSetDist_tendsto`).
* `lemma_2_2_of_comparison`: both statements; the ordinary LFPP part uses (2.1)
  (`Field.ae_localizedHeat_tendsto_uniform_on_compact`) on `B_{R+1}(0)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC heatMollify)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-! ### Deterministic lemmas -/

/-- **First hitting time.** -/
theorem exists_first_hit {f : ℝ → ℝ} {a b R : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ R) (hb : R ≤ f b) : ∃ t ∈ Icc a b, f t = R ∧ ∀ u ∈ Icc a t, f u ≤ R := by
  set T : Set ℝ := Icc a b ∩ f ⁻¹' Ici R with hT
  have hTc : IsClosed T := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hTne : T.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hTb : BddBelow T := ⟨a, fun u hu => hu.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTc.csInf_mem hTne hTb
  have hbelow : ∀ u ∈ Ico a t, f u < R := by
    intro u hu
    by_contra hcon
    have huT : u ∈ T := ⟨⟨hu.1, hu.2.le.trans htT.1.2⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hTb huT) (not_le.2 hu.2)
  have hft : f t = R := by
    obtain ⟨t', ht', hft'⟩ := intermediate_value_Icc htT.1.1
      (hf.mono (Icc_subset_Icc le_rfl htT.1.2)) ⟨ha, htT.2⟩
    have ht'T : t' ∈ T := ⟨⟨ht'.1, ht'.2.trans htT.1.2⟩, by rw [mem_preimage, hft']; exact Set.mem_Ici.2 (le_refl R)⟩
    have : t ≤ t' := csInf_le hTb ht'T
    rw [← le_antisymm ht'.2 this]
    exact hft'
  refine ⟨t, htT.1, hft, fun u hu => ?_⟩
  rcases hu.2.lt_or_eq with hlt | heq
  · exact (hbelow u ⟨hu.1, hlt⟩).le
  · rw [heq, hft]

/-- The metric is at most its internal metric on any set. -/
theorem apply_le_internal (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D ((p.1 : ℂ), (p.2 : ℂ)) ≤ D.internal Y p := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun _ => le_iInf fun ha => le_iInf fun hb => ?_
  rw [← ha, ← hb]
  exact LSCMetric.apply_le_len D P hP.1

/-- A curve of a length space from `x` to `y` with length below a bound. -/
theorem exists_curve_lt {L : LSCMetric} (hL : L.IsLengthSpace) {x y : ℂ} {c : ℝ≥0∞}
    (hxy : L (x, y) < c) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), L.IsCurve P a b ∧ P a = x ∧ P b = y ∧ L.len P a b < c := by
  obtain ⟨r, hr, hrc⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
  obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hL x y (lt_of_lt_of_le hxy le_top) (r : ℝ)
    (NNReal.coe_pos.2 hr)
  refine ⟨P, a, b, hP, ha, hb, lt_of_le_of_lt hlen ?_⟩
  rwa [ENNReal.ofReal_coe_nnreal]

/-- **Stopping at the first hit of `∂B_R`.** A Euclidean-continuous curve from `x` with
`|x| < R` to a point of `∂B_R` has an initial segment `[a, t]` inside `B̄_R` ending on `∂B_R`. -/
theorem exists_stopped_curve {P : ℝ → ℂ} {a b R : ℝ} (hab : a ≤ b)
    (hPc : ContinuousOn P (Icc a b)) (ha : ‖P a‖ < R) (hb : ‖P b‖ = R) :
    ∃ t ∈ Icc a b, ‖P t‖ = R ∧ ∀ u ∈ Icc a t, ‖P u‖ ≤ R :=
  exists_first_hit hab (continuous_norm.comp_continuousOn hPc) ha.le hb.ge

/-- **Lemma 2.2, deterministic step for the localized metric.** On the event of (2.8) for
`U = B_{R+1}(0)` and radius `ρ`, the inequality `L(K, ∂B_R) ≤ M` implies
`D(K^ρ, (∂B_R)^ρ) ≤ C₀(M + 1/2)`. -/
theorem setDistance_thickening_le_of_compare {L Dg : LSCMetric} {ρ C₀ M R : ℝ} {K : Set ℂ}
    (hL : L.IsLengthSpace) (hLc : ∀ P a b, L.IsCurve P a b → ContinuousOn P (Icc a b))
    (hKR : ∀ z ∈ K, ‖z‖ < R) (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M)
    (hcomp : B2.Polylog.compareHolds L Dg ρ (ball (0 : ℂ) (R + 1)) C₀)
    (hset : B2.Iface.setDistance L.1 K (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M) :
    B2.Iface.setDistance Dg.1 (thickening ρ K) (thickening ρ (sphere (0 : ℂ) R)) ≤
      ENNReal.ofReal (C₀ * (M + 1 / 2)) := by
  have hMlt : ENNReal.ofReal M < ENNReal.ofReal (M + 1 / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hlt := lt_of_le_of_lt hset hMlt
  unfold B2.Iface.setDistance at hlt
  obtain ⟨x, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hx, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨y, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hy, hxy⟩ := iInf_lt_iff.1 hlt
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := exists_curve_lt hL hxy
  have hPc := hLc P a b hP
  have hya : ‖P a‖ < R := by rw [hPa]; exact hKR x hx
  have hyb : ‖P b‖ = R := by rw [hPb]; simpa using hy
  obtain ⟨t, ht, hPt, hinside⟩ := exists_stopped_curve hP.1 hPc hya hyb
  have hPU : ∀ u ∈ Icc a t, P u ∈ ball (0 : ℂ) (R + 1) := fun u hu => by
    rw [mem_ball, dist_zero_right]
    linarith [hinside u hu]
  have hPat : L.IsCurve P a t := ⟨ht.1, hP.2.mono (Icc_subset_Icc le_rfl ht.2)⟩
  have hxU : x ∈ ball (0 : ℂ) (R + 1) := by rw [← hPa]; exact hPU a ⟨le_rfl, ht.1⟩
  have hwU : P t ∈ ball (0 : ℂ) (R + 1) := hPU t ⟨ht.1, le_rfl⟩
  have hint : L.internal (ball (0 : ℂ) (R + 1)) (⟨x, hxU⟩, ⟨P t, hwU⟩) <
      ENNReal.ofReal (M + 1 / 2) :=
    internal_lt_of_curve hPat hPU (by rw [hPa]) rfl
      (lt_of_le_of_lt (B2.PfeWeyl.len_mono_Icc L P le_rfl ht.2) hlen)
  have hc := (hcomp x (P t) hxU hwU).2
  have hbound : Dg.internalSetDist (thickening ρ (ball (0 : ℂ) (R + 1)))
      {z | (z : ℂ) ∈ ball x ρ} {z | (z : ℂ) ∈ ball (P t) ρ} ≤ ENNReal.ofReal (C₀ * (M + 1 / 2)) := by
    calc _ ≤ ENNReal.ofReal C₀ * L.internal (ball (0 : ℂ) (R + 1)) (⟨x, hxU⟩, ⟨P t, hwU⟩) := hc
      _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (M + 1 / 2) := by gcongr
      _ = ENNReal.ofReal (C₀ * (M + 1 / 2)) := (ENNReal.ofReal_mul hC₀).symm
  refine le_trans ?_ hbound
  unfold LSCMetric.internalSetDist B2.Iface.setDistance
  refine le_iInf₂ fun a' ha' => le_iInf₂ fun b' hb' => ?_
  have ha'K : (a' : ℂ) ∈ thickening ρ K := mem_thickening_iff.2 ⟨x, hx, ha'⟩
  have hb'S : (b' : ℂ) ∈ thickening ρ (sphere (0 : ℂ) R) :=
    mem_thickening_iff.2 ⟨P t, by simpa using hPt, hb'⟩
  exact (iInf₂_le_of_le (a' : ℂ) ha'K (iInf₂_le (b' : ℂ) hb'S)).trans
    (apply_le_internal Dg _ (a', b'))

/-- **Lemma 2.2, deterministic step for ordinary LFPP.** If two continuous fields satisfy
`e^{|ξ| sup_{B_{R+1}} |ψ − φ|} ≤ 2`, then `X_φ(K, ∂B_R) ≤ M` implies `X_ψ(K, ∂B_R) ≤ 2M + 1`. -/
theorem setDistance_lfpp_le_of_close {ξ : ℝ} (a : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)} {s M R : ℝ}
    {K : Set ℂ} (hKR : ∀ z ∈ K, ‖z‖ < R) (hM : 0 ≤ M) (hs2 : Real.exp (|ξ| * s) ≤ 2)
    (hclose : ∀ z ∈ ball (0 : ℂ) (R + 1), |ψ z - φ z| ≤ s)
    (hset : B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 K (sphere (0 : ℂ) R) ≤
      ENNReal.ofReal M) :
    B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 K (sphere (0 : ℂ) R) ≤
      ENNReal.ofReal (2 * M + 1) := by
  have hMlt : ENNReal.ofReal M < ENNReal.ofReal (M + 1 / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hlt := lt_of_le_of_lt hset hMlt
  unfold B2.Iface.setDistance at hlt
  obtain ⟨x, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hx, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨y, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hy, hxy⟩ := iInf_lt_iff.1 hlt
  obtain ⟨P, a', b', hP, hPa, hPb, hlen⟩ := exists_curve_lt (lfppMetric_isLengthSpace ξ a φ) hxy
  have hPc := ((B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP).2
  have hya : ‖P a'‖ < R := by rw [hPa]; exact hKR x hx
  have hyb : ‖P b'‖ = R := by rw [hPb]; simpa using hy
  obtain ⟨t, ht, hPt, hinside⟩ := exists_stopped_curve hP.1 hPc hya hyb
  have hPU : ∀ u ∈ Icc a' t, P u ∈ ball (0 : ℂ) (R + 1) := fun u hu => by
    rw [mem_ball, dist_zero_right]
    linarith [hinside u hu]
  have hcmp := B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a isOpen_ball hclose
    (hPc.mono (Icc_subset_Icc le_rfl ht.2)) hPU
  have hlen' : (B2.Median.lfppMetric ξ a ψ).len P a' t ≤ ENNReal.ofReal (2 * M + 1) := by
    calc _ ≤ ENNReal.ofReal (Real.exp (|ξ| * s)) * (B2.Median.lfppMetric ξ a φ).len P a' t := hcmp
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (M + 1 / 2) := by
          gcongr
          exact (B2.PfeWeyl.len_mono_Icc _ P le_rfl ht.2).trans hlen.le
      _ = ENNReal.ofReal (2 * M + 1) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  have hpt : (B2.Median.lfppMetric ξ a ψ) (x, P t) ≤ ENNReal.ofReal (2 * M + 1) := by
    rw [← hPa]
    exact (LSCMetric.apply_le_len _ P ht.1).trans hlen'
  unfold B2.Iface.setDistance
  exact (iInf₂_le_of_le x hx (iInf₂_le (P t) (by simpa using hPt))).trans hpt

/-- **Lower semicontinuity and compactness**: if `D(K^ρ, S^ρ) ≤ c` along `ρ = 1/(n+1)`, then
`D(K, S) ≤ c`. -/
theorem setDistance_le_of_thickening (D : LSCMetric) {K S : Set ℂ} (hK : IsCompact K)
    (hS : IsCompact S) {c : ℝ≥0∞}
    (h : ∀ n : ℕ, B2.Iface.setDistance D.1 (thickening (1 / ((n : ℝ) + 1)) K)
      (thickening (1 / ((n : ℝ) + 1)) S) ≤ c) :
    B2.Iface.setDistance D.1 K S ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c', hcc', hc'⟩ := exists_between hlt
  -- approximate minimizers
  have hpts : ∀ n : ℕ, ∃ x ∈ K, ∃ y ∈ S, ∃ x' y' : ℂ, dist x' x < 1 / ((n : ℝ) + 1) ∧
      dist y' y < 1 / ((n : ℝ) + 1) ∧ D (x', y') < c' := by
    intro n
    have hn := lt_of_le_of_lt (h n) hcc'
    unfold B2.Iface.setDistance at hn
    obtain ⟨x', hn⟩ := iInf_lt_iff.1 hn
    obtain ⟨hx', hn⟩ := iInf_lt_iff.1 hn
    obtain ⟨y', hn⟩ := iInf_lt_iff.1 hn
    obtain ⟨hy', hn⟩ := iInf_lt_iff.1 hn
    obtain ⟨x, hx, hxx⟩ := mem_thickening_iff.1 hx'
    obtain ⟨y, hy, hyy⟩ := mem_thickening_iff.1 hy'
    exact ⟨x, hx, y, hy, x', y', hxx, hyy, hn⟩
  choose x hx y hy x' y' hxx hyy hD using hpts
  obtain ⟨p, hp, φ, hφ, hlim⟩ := (hK.prod hS).tendsto_subseq (x := fun n => (x n, y n))
    (fun n => ⟨hx n, hy n⟩)
  have hsmall : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlim' : Tendsto (fun k => (x' (φ k), y' (φ k))) atTop (𝓝 p) := by
    have h1 : Tendsto (fun k => x (φ k)) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
    have h2 : Tendsto (fun k => y (φ k)) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
    have h1' : Tendsto (fun k => x' (φ k)) atTop (𝓝 p.1) :=
      tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
        (fun k => (dist_triangle _ _ _).trans (add_le_add (hxx (φ k)).le le_rfl))
        (by simpa using hsmall.add (tendsto_iff_dist_tendsto_zero.1 h1)))
    have h2' : Tendsto (fun k => y' (φ k)) atTop (𝓝 p.2) :=
      tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
        (fun k => (dist_triangle _ _ _).trans (add_le_add (hyy (φ k)).le le_rfl))
        (by simpa using hsmall.add (tendsto_iff_dist_tendsto_zero.1 h2)))
    exact h1'.prodMk_nhds h2'
  have hlsc : D p ≤ c' := by
    by_contra hcon
    rw [not_le] at hcon
    have hev := D.lowerSemicontinuous p c' hcon
    obtain ⟨k, hk⟩ := (hlim'.eventually hev).exists
    exact (lt_asymm hk) (hD (φ k))
  have hle : B2.Iface.setDistance D.1 K S ≤ D p := by
    unfold B2.Iface.setDistance
    exact iInf₂_le_of_le p.1 hp.1 (iInf₂_le p.2 hp.2)
  exact absurd (hle.trans hlsc) (not_le.2 hc')

/-- Outside a point-sampling failure event, two continuous functions are close on an open set. -/
theorem abs_sub_le_of_forall_denseSeq {W : Set ℂ} (hW : IsOpen W) {F : ℂ → ℝ}
    (hF : Continuous F) {s : ℝ}
    (h : ∀ k, TopologicalSpace.denseSeq ℂ k ∈ W → |F (TopologicalSpace.denseSeq ℂ k)| ≤ s) :
    ∀ z ∈ W, |F z| ≤ s := by
  have hclosed : IsClosed {z | |F z| ≤ s} := isClosed_le hF.abs continuous_const
  have hsub : W ∩ range (TopologicalSpace.denseSeq ℂ) ⊆ {z | |F z| ≤ s} := by
    rintro z ⟨hzW, k, rfl⟩
    exact h k hzW
  intro z hz
  exact hclosed.closure_subset_iff.2 hsub
    ((TopologicalSpace.denseRange_denseSeq ℂ).open_subset_closure_inter hW hz)

/-! ### Probability -/

/-- **(1.4) in probability**: for compact `K` and `c < ∞`, `P[D(K, ∂B_R) ≤ c] → 0`. -/
theorem tendsto_measure_setDistance_sphere_le {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {K : Set ℂ} (hK : IsCompact K) (c : ℝ) :
    Tendsto (fun R : ℝ => P {ω | B2.Iface.setDistance (D (h ω)).1 K (sphere (0 : ℂ) R) ≤
      ENNReal.ofReal c}) atTop (𝓝 0) := by
  have hhm : Measurable h := hh.1.measurable
  obtain ⟨k, hk⟩ : ∃ k : ℕ, K ⊆ closedBall (0 : ℂ) k := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨k, hk⟩ := exists_nat_ge r
    exact ⟨k, hr.trans (closedBall_subset_closedBall hk)⟩
  refine tendsto_measure_of_ae_eventually_not_mem (fun R => ?_) ?_
  · exact (measurableSet_le ((B2.PfeLocal.l4_measurable_setDistance hK
      (isCompact_sphere 0 R)).comp (hD.1.comp hhm)) measurable_const).nullMeasurableSet
  · filter_upwards [ae_d2EscapeSetDist_tendsto (B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD)
      P h hh] with ω hω
    have hgt := (hω k).eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := c)))
    filter_upwards [hgt] with R hR hle
    have hmono : Uniqueness.OptimalConstants.Ratios.setDist (D (h ω)) (closedBall (0 : ℂ) k)
        (sphere (0 : ℂ) R) ≤ B2.Iface.setDistance (D (h ω)).1 K (sphere (0 : ℂ) R) := by
      rw [iface_setDistance_eq_setDist]
      unfold Uniqueness.OptimalConstants.Ratios.setDist
      exact iInf₂_mono' fun z hz => ⟨z, hk hz, le_rfl⟩
    exact absurd (hmono.trans hle) (not_le.2 hR)

/-- **Lemma 2.2 for the localized metric, from (2.8).** -/
theorem lemma_2_2_loc_of_comparison (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {ζ : ℝ} (hζ1 : ζ < 1)
    (hcomp : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          P {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω))
            (D (h ω)) (ε ^ (1 - ζ)) U C₀} ≤ ENNReal.ofReal (c₀ * ε ^ p₀))
    (K : Set ℂ) (hK : IsCompact K) (M : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
      P {ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).1 K
          (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M} ≤ ENNReal.ofReal η := by
  intro η hη
  have hhm : Measurable h := hh.1.measurable
  obtain ⟨C₀, hC₀, hcompU⟩ := hcomp
  set Mp : ℝ := max M 0
  set c : ℝ := C₀ * (Mp + 1 / 2) with hc
  -- the escape radius
  have hesc := tendsto_measure_setDistance_sphere_le hD P h hh hK c
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (hesc.eventually (eventually_le_nhds
    (ENNReal.ofReal_pos.2 (half_pos hη))))
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖z‖ ≤ B := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨max r 0, le_max_right _ _, fun z hz =>
      le_trans (by simpa using hr hz) (le_max_left _ _)⟩
  refine ⟨max R₁ (B + 1), fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith [le_max_right R₁ (B + 1)]
  have hR1 : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hKR : ∀ z ∈ K, ‖z‖ < R := fun z hz => by
    linarith [hB z hz, le_max_right R₁ (B + 1)]
  -- the thickened events
  set A : ℕ → Set Ω := fun n => {ω | B2.Iface.setDistance (D (h ω)).1
    (thickening (1 / ((n : ℝ) + 1)) K) (thickening (1 / ((n : ℝ) + 1)) (sphere (0 : ℂ) R)) ≤
      ENNReal.ofReal c} with hA
  have hAm : ∀ n, MeasurableSet (A n) := by
    intro n
    have hm := Uniqueness.OptimalConstants.Ratios.measurable_setDist_open
      (thickening (1 / ((n : ℝ) + 1)) K) (thickening (1 / ((n : ℝ) + 1)) (sphere (0 : ℂ) R))
      isOpen_thickening isOpen_thickening
    simp only [hA, iface_setDistance_eq_setDist]
    exact measurableSet_le (hm.comp (hD.1.comp hhm)) measurable_const
  have hAanti : Antitone A := by
    intro n n' hnn' ω hω
    have hnn'' : (n : ℝ) ≤ n' := Nat.cast_le.2 hnn'
    have hρ : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    simp only [hA, mem_ofPred_eq] at hω ⊢
    refine le_trans ?_ hω
    unfold B2.Iface.setDistance
    exact iInf₂_mono' fun z hz => ⟨z, thickening_mono hρ K hz, iInf₂_mono' fun w hw =>
      ⟨w, thickening_mono hρ _ hw, le_rfl⟩⟩
  have hAint : (⋂ n, A n) ⊆ {ω | B2.Iface.setDistance (D (h ω)).1 K (sphere (0 : ℂ) R) ≤
      ENNReal.ofReal c} := fun ω hω =>
    setDistance_le_of_thickening (D (h ω)) hK (isCompact_sphere 0 R) (fun n => by
      have := mem_iInter.1 hω n
      simpa only [hA, mem_ofPred_eq] using this)
  have hAlim := tendsto_measure_iInter_atTop (fun n => (hAm n).nullMeasurableSet) hAanti
    ⟨0, measure_ne_top P _⟩
  have hint_le : P (⋂ n, A n) < ENNReal.ofReal (3 * η / 4) := by
    calc P (⋂ n, A n) ≤ _ := measure_mono hAint
      _ ≤ ENNReal.ofReal (η / 2) := hR₁ R hR1
      _ < ENNReal.ofReal (3 * η / 4) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
          (by linarith)
  obtain ⟨n₀, hn₀⟩ := (hAlim.eventually (gt_mem_nhds hint_le)).exists
  -- the comparison event
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, -, hcompR⟩ := hcompU (ball (0 : ℂ) (R + 1)) isOpen_ball
    ((convex_ball (0 : ℂ) (R + 1)).isConnected (nonempty_ball.2 (by linarith)))
    isBounded_ball
  -- small `ε`
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ ∧ c₀ * ε ^ p₀ ≤ η / 4 ∧
      ε ^ (1 - ζ) ≤ 1 / ((n₀ : ℝ) + 1) := by
    have h1 : Tendsto (fun ε : ℝ => c₀ * ε ^ p₀) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 p₀ (Or.inr hp₀.le)).tendsto).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow hp₀.ne'] using this.const_mul c₀
    have h2 : Tendsto (fun ε : ℝ => ε ^ (1 - ζ)) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 (1 - ζ) (Or.inr (by linarith))).tendsto).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow (by linarith : (1 - ζ) ≠ 0)] using this
    filter_upwards [Ioo_mem_nhdsGT hε₀,
      h1.eventually (eventually_le_nhds (show (0 : ℝ) < η / 4 by positivity)),
      h2.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) by positivity))]
      with ε hε h1' h2'
    exact ⟨hε.2, h1', h2'⟩
  filter_upwards [hsmall] with ε hε hεI
  obtain ⟨hεε₀, hcε, hρε⟩ := hε
  have hsub : {ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hεI (h ω)).1 K
      (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M} ⊆
      {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hεI (h ω))
        (D (h ω)) (ε ^ (1 - ζ)) (ball (0 : ℂ) (R + 1)) C₀} ∪ A n₀ := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or, mem_ofPred_eq, not_not] at hnot
    obtain ⟨hcmp, hAω⟩ := hnot
    apply hAω
    have hω' : B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hεI (h ω)).1 K
        (sphere (0 : ℂ) R) ≤ ENNReal.ofReal Mp :=
      hω.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hthick := setDistance_thickening_le_of_compare
      (lfppMetric_isLengthSpace _ _ _)
      (fun P a b hP => ((B2.Polylog.lfppMetric_isCurve_iff _ _ _).1 hP).2) hKR hC₀.le
      (le_max_right _ _) hcmp hω'
    refine le_trans ?_ hthick
    unfold B2.Iface.setDistance
    exact iInf₂_mono' fun z hz => ⟨z, thickening_mono hρε K hz, iInf₂_mono' fun w hw =>
      ⟨w, thickening_mono hρε _ hw, le_rfl⟩⟩
  calc _ ≤ P ({ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hεI (h ω))
        (D (h ω)) (ε ^ (1 - ζ)) (ball (0 : ℂ) (R + 1)) C₀} ∪ A n₀) := measure_mono hsub
    _ ≤ P {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hεI (h ω))
        (D (h ω)) (ε ^ (1 - ζ)) (ball (0 : ℂ) (R + 1)) C₀} + P (A n₀) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (3 * η / 4) :=
        add_le_add ((hcompR ε hεI hεε₀).trans (ENNReal.ofReal_le_ofReal hcε)) hn₀.le
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ### The ordinary LFPP part -/

open Classical in
/-- The failure event of (2.1) on `B_{R+1}(0)`, sampled on a countable dense set:
`|h*_ε − ĥ_ε| > s` somewhere (empty when `ε ∉ (0, 1)`). -/
def heatLocFailure {Ω : Type*} (h : Ω → DistC) (R s ε : ℝ) : Set Ω :=
  if hε : ε ∈ Ioo (0 : ℝ) 1 then
    {ω | ∃ k : ℕ, TopologicalSpace.denseSeq ℂ k ∈ ball (0 : ℂ) (R + 1) ∧
      s < |heatMollify ε (h ω) (TopologicalSpace.denseSeq ℂ k) -
        Field.localizedHeatField ε hε (h ω) (TopologicalSpace.denseSeq ℂ k)|}
  else ∅

theorem measurableSet_heatLocFailure {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistC}
    (hhm : Measurable h) (R s ε : ℝ) : MeasurableSet (heatLocFailure h R s ε) := by
  unfold heatLocFailure
  split_ifs with hε
  · have hF : ∀ k : ℕ, Measurable fun ω =>
        |heatMollify ε (h ω) (TopologicalSpace.denseSeq ℂ k) -
          Field.localizedHeatField ε hε (h ω) (TopologicalSpace.denseSeq ℂ k)| :=
      fun k => (((LQGMetric.measurable_heatMollify_left ε _).comp hhm).sub
        (measurable_const.mul ((LQGMetric.measurable_distOn_apply _).comp hhm))).abs
    have heq : {ω | ∃ k : ℕ, TopologicalSpace.denseSeq ℂ k ∈ ball (0 : ℂ) (R + 1) ∧
        s < |heatMollify ε (h ω) (TopologicalSpace.denseSeq ℂ k) -
          Field.localizedHeatField ε hε (h ω) (TopologicalSpace.denseSeq ℂ k)|} =
        ⋃ k : ℕ, {ω | TopologicalSpace.denseSeq ℂ k ∈ ball (0 : ℂ) (R + 1) ∧
          s < |heatMollify ε (h ω) (TopologicalSpace.denseSeq ℂ k) -
            Field.localizedHeatField ε hε (h ω) (TopologicalSpace.denseSeq ℂ k)|} := by
      ext ω
      simp only [mem_iUnion, mem_ofPred_eq]
    rw [heq]
    refine MeasurableSet.iUnion fun k => ?_
    by_cases hk : TopologicalSpace.denseSeq ℂ k ∈ ball (0 : ℂ) (R + 1)
    · simp only [hk, true_and]
      exact measurableSet_lt measurable_const (hF k)
    · simp only [hk, false_and]
      exact MeasurableSet.empty
  · exact MeasurableSet.empty

/-- **(2.1) in probability** on `B_{R+1}(0)`. -/
theorem tendsto_measure_heatLocFailure {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (R : ℝ)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => P (heatLocFailure h R s ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_measure_of_ae_eventually_not_mem
    (fun ε => (measurableSet_heatLocFailure hh.1.measurable R s ε).nullMeasurableSet) ?_
  filter_upwards [Field.ae_localizedHeat_tendsto_uniform_on_compact P h hh
    (closedBall (0 : ℂ) (R + 1)) (isCompact_closedBall _ _)] with ω hω
  filter_upwards [hω s hs] with ε hε hmem
  unfold heatLocFailure at hmem
  split_ifs at hmem with hεI
  · obtain ⟨k, hk, hlt⟩ := hmem
    have := hε hεI _ (ball_subset_closedBall hk)
    linarith
  · exact hmem

/-- **Lemma 2.2** (paper l. 196–207), in the measurable form of SB1: from (2.8) (hypothesis
`hcomp`, packet D6) and (1.4), for each compact `K` and `M < ∞`, for every `η > 0` there is `R₀`
such that for `R ≥ R₀` and all small `ε`, both `P[X̂_ε(K, ∂B_R) ≤ M] ≤ η` and
`P[X_ε(K, ∂B_R) ≤ M] ≤ η`. -/
theorem lemma_2_2_of_comparison (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) {ζ : ℝ} (hζ1 : ζ < 1)
    (hcomp : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          P {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω))
            (D (h ω)) (ε ^ (1 - ζ)) U C₀} ≤ ENNReal.ofReal (c₀ * ε ^ p₀))
    (K : Set ℂ) (hK : IsCompact K) (M : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
      P {ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).1 K
          (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M} ≤ ENNReal.ofReal η ∧
      P {ω | B2.Iface.setDistance (B2.Median.lfppMetric (ξ : ℝ) (m ⟨ε, hε.1⟩) (X ⟨ε, hε.1⟩ ω)).1 K
          (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M} ≤ ENNReal.ofReal η := by
  intro η hη
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hhm : Measurable h := hh.1.measurable
  set M₂ : ℝ := 2 * max M 0 + 1
  obtain ⟨R₁, hR₁⟩ := lemma_2_2_loc_of_comparison ξ Q D hD m P h hh hζ1 hcomp K hK M η hη
  obtain ⟨R₂, hR₂⟩ := lemma_2_2_loc_of_comparison ξ Q D hD m P h hh hζ1 hcomp K hK M₂ (η / 2)
    (half_pos hη)
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖z‖ ≤ B := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨max r 0, le_max_right _ _, fun z hz =>
      le_trans (by simpa using hr hz) (le_max_left _ _)⟩
  refine ⟨max (max R₁ R₂) (B + 1), fun R hR => ?_⟩
  have hR₁' : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR₂' : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hKR : ∀ z ∈ K, ‖z‖ < R := fun z hz => by
    linarith [hB z hz, le_max_right (max R₁ R₂) (B + 1)]
  set s : ℝ := Real.log 2 / ξ with hsdef
  have hs : 0 < s := div_pos (Real.log_pos (by norm_num)) hξ
  have hs2 : Real.exp (|(ξ : ℝ)| * s) ≤ 2 := by
    rw [abs_of_pos hξ, hsdef, mul_div_cancel₀ _ hξ.ne', Real.exp_log (by norm_num)]
  have hF := (tendsto_measure_heatLocFailure P h hh R hs).eventually
    (eventually_le_nhds (ENNReal.ofReal_pos.2 (half_pos hη)))
  filter_upwards [hR₁ R hR₁', hR₂ R hR₂', hF] with ε h1 h2 h3 hε
  refine ⟨h1 hε, ?_⟩
  set ε' : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  set N : Set Ω := {ω | ¬ ∀ z : ℂ, X ε' ω z = heatMollify ε (h ω) z}
  have hN : P N = 0 := by
    rw [← ae_iff]
    exact B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh ε' (X ε') (hX ε')
  have hsub : {ω | B2.Iface.setDistance (B2.Median.lfppMetric (ξ : ℝ) (m ε') (X ε' ω)).1 K
      (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M} ⊆
      {ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).1 K
        (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M₂} ∪ heatLocFailure h R s ε ∪ N := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or, mem_ofPred_eq, not_not, N] at hnot
    obtain ⟨⟨hXh, hFω⟩, hXω⟩ := hnot
    apply hXh
    have hclose : ∀ z ∈ ball (0 : ℂ) (R + 1),
        |B2.Polylog.plMollifyC 1 ε hε (h ω) z - X ε' ω z| ≤ s := by
      refine abs_sub_le_of_forall_denseSeq isOpen_ball
        ((ContinuousMap.continuous _).sub (X ε' ω).continuous) fun k hk => ?_
      by_contra hcon
      apply hFω
      unfold heatLocFailure
      rw [dite_eq_left hε]
      refine ⟨k, hk, ?_⟩
      rw [abs_sub_comm, ← hXω]
      exact not_le.1 hcon
    have h' := setDistance_lfpp_le_of_close (ξ := (ξ : ℝ)) (m ε') (φ := X ε' ω)
      (ψ := B2.Polylog.plMollifyC 1 ε hε (h ω)) hKR (le_max_right M 0) hs2 hclose
      (hω.trans (ENNReal.ofReal_le_ofReal (le_max_left M 0)))
    exact h'
  calc _ ≤ P ({ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).1 K
        (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M₂} ∪ heatLocFailure h R s ε ∪ N) :=
        measure_mono hsub
    _ ≤ P {ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).1 K
        (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M₂} + P (heatLocFailure h R s ε) + P N := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) + 0 := by
        rw [hN]
        exact add_le_add (add_le_add (h2 hε) h3) le_rfl
    _ = ENNReal.ofReal η := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end SupercriticalLFPPAS.Local
