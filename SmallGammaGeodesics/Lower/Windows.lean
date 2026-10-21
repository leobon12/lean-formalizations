import SmallGammaGeodesics.Lower.Mobius
import SmallGammaGeodesics.Core.PathFunctionals
import LQGMetric.Metric.InternalC
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Papers.GM.S3.GoodAnnulusUnique
import LQGMetric.Papers.GM.S5.Tubes55Det

/-!
# Midline window events of source §7 (packet P-L1)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7, the events `B_k` of the proof of
Proposition 7.1, replaced (planning audit GA4, finding GA4-2) by the **window events** of GA4
"Details for later use", items **A6** and **A7**.

For `d : ℂ → ℂ → [0, ∞]` and `S ⊆ L = {Re z = 1/2}`,
`Win(d, S) :⟺ d(0,1) < ∞ ∧ ∃ δ > 0, ∀ q ∈ ℚ, 1/2 + iq ∈ S → d(0, 1/2 + iq) + d(1/2 + iq, 1) ≥ d(0,1) + δ`
(`winEvent`).

* (W1) `measurableSet_winEvent`: `Win` only reads countably many values of `d`.
* (W2) `winEvent_smul_iff`: `Win(λ d, S) ⟺ Win(d, S)` for `λ ∈ (0, ∞)`.
* (W3) `not_winEvent_and_winEvent`: for the internal metric of a continuous length metric on
  `U = U_R`, the window events of two windows at distance `> 2ρ` are disjoint. Ingredients: every
  path in `U` from `0` to `1` crosses the midline (`exists_midline_lt_of_internal_lt`), continuity
  of `D(·,·;U)` and density of `ℚ` (`le_add_of_forall_midQ`).
* (A7) `winEvent_of_geod_subset_tube`: if the `D`-geodesic `P` from `0` to `1` is unique, lies in
  `T_r`, and `D(·,·;ψ_θ(U_R)) = c · d′(φ_θ ·, φ_θ ·)` (the Möbius covariance (MC) at one sample
  point), then `Win(d′, (U_R ∩ L) \ J)` for the window `J` of radius `2r` around `tan(θ/2)/2`.
  Ingredients: `D(0,1;V) = D(0,1)` (`internal_eq_of_isGeod01`), a strict triangle inequality off
  the unique geodesic (`lt_dist_add_dist_of_notMem_range`, via concatenation of geodesics,
  `LQGMetric.GM.exists_geod_through`), made uniform on a compact band of the midline
  (`exists_gap_of_isCompact`), and the geometry A2 (iv) of `Lower/Mobius.lean`.
* `maxDev_le_iff_forall_mem_tube`: the event `A = {M ≤ r}` is `{P ⊆ T_r}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric

/-- Rational midline points `1/2 + iq`. -/
def midQ (q : ℚ) : ℂ := (1 / 2 : ℂ) + ((q : ℝ) : ℂ) * Complex.I

/-- The window event `Win(d, S)` (GA4 A6). -/
def winEvent (d : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) : Prop :=
  d 0 1 < ⊤ ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ q : ℚ, midQ q ∈ S → d 0 1 + δ ≤ d 0 (midQ q) + d (midQ q) 1

@[simp] theorem midQ_re (q : ℚ) : (midQ q).re = 1 / 2 := re_half_add_mul_I _

@[simp] theorem midQ_im (q : ℚ) : (midQ q).im = q := im_half_add_mul_I _

/-! ### (W1) Measurability -/

/-- The gap `δ` may be taken of the form `1/n`. -/
theorem winEvent_iff_exists_nat (d : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) :
    winEvent d S ↔ d 0 1 < ⊤ ∧ ∃ n : ℕ, ∀ q : ℚ, midQ q ∈ S →
      d 0 1 + (n : ℝ≥0∞)⁻¹ ≤ d 0 (midQ q) + d (midQ q) 1 := by
  refine and_congr_right fun _ => ⟨fun ⟨δ, hδ, h⟩ => ?_, fun ⟨n, h⟩ =>
    ⟨_, ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n), h⟩⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  exact ⟨n, fun q hq => (add_le_add le_rfl hn.le).trans (h q hq)⟩

/-- **(W1)**: the window event of a random distance function is measurable as soon as each
value `d(z, w)` is. -/
theorem measurableSet_winEvent {Ω : Type*} [MeasurableSpace Ω] (d : Ω → ℂ → ℂ → ℝ≥0∞)
    (hd : ∀ z w, Measurable fun ω => d ω z w) (S : Set ℂ) :
    MeasurableSet {ω | winEvent (d ω) S} := by
  simp_rw [winEvent_iff_exists_nat]
  rw [ofPred_and]
  refine (measurableSet_lt (hd 0 1) measurable_const).inter ?_
  rw [ofPred_exists]
  refine MeasurableSet.iUnion fun n => ?_
  rw [ofPred_forall]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : midQ q ∈ S
  · simp only [hq, forall_const]
    exact measurableSet_le ((hd 0 1).add measurable_const) ((hd 0 (midQ q)).add (hd (midQ q) 1))
  · simp only [hq, IsEmpty.forall_iff, ofPred_true, MeasurableSet.univ]

/-! ### (W2) Scale invariance -/

/-- **(W2)**: `Win(c d, S) ⟺ Win(d, S)` for `c ∈ (0, ∞)`. -/
theorem winEvent_smul_iff (d : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) : winEvent (fun z w => c * d z w) S ↔ winEvent d S := by
  unfold winEvent
  have hfin : c * d 0 1 < ⊤ ↔ d 0 1 < ⊤ := by
    refine ⟨fun h => lt_top_iff_ne_top.2 fun h' => ?_, fun h => ENNReal.mul_lt_top
      (lt_top_iff_ne_top.2 hct) h⟩
    rw [h', ENNReal.mul_top hc0] at h
    exact lt_irrefl _ h
  rw [hfin]
  refine and_congr_right fun _ => ⟨fun ⟨δ, hδ, h⟩ => ⟨δ / c, ?_, fun q hq => ?_⟩,
    fun ⟨δ, hδ, h⟩ => ⟨c * δ, ?_, fun q hq => ?_⟩⟩
  · exact ENNReal.div_pos_iff.2 ⟨hδ.ne', hct⟩
  · rw [← ENNReal.mul_le_mul_iff_right hc0 hct, mul_add, mul_add, ENNReal.mul_div_cancel hc0 hct]
    exact h q hq
  · exact ENNReal.mul_pos hc0 hδ.ne'
  · rw [← mul_add, ← mul_add]
    exact (ENNReal.mul_le_mul_iff_right hc0 hct).2 (h q hq)

/-! ### (W3) Disjointness -/

/-- `D(a, ·; U) + D(·, b; U)` is continuous on an open `U ∋ a, b` (LM Lemma 1.1). -/
theorem continuousOn_internal_add (D : ContMetric) (hD : D.IsLength) {U : Set ℂ} (hU : IsOpen U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    ContinuousOn (fun u => D.internal U a u + D.internal U u b) U := by
  have hc := D.continuousOn_internal hD hU
  have h1 : ContinuousOn (fun u => D.internal U a u) U :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn fun u hu => ⟨ha, hu⟩
  have h2 : ContinuousOn (fun u => D.internal U u b) U :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hu, hb⟩
  exact h1.add h2

/-- **Crossing** (GA4 A6, step 1): a path in `U` from `0` to `1` meets the midline `Re z = 1/2`,
so `D(0,1;U) < x` gives a midline point `u ∈ U` with `D(0,u;U) + D(u,1;U) < x`. -/
theorem exists_midline_lt_of_internal_lt (D : ContMetric) {U : Set ℂ} {x : ℝ≥0∞}
    (hx : D.internal U 0 1 < x) :
    ∃ u ∈ U, u.re = 1 / 2 ∧ D.internal U 0 u + D.internal U u 1 < x := by
  obtain ⟨⟨γ, hγU⟩, hγ⟩ := iInf_lt_iff.1 hx
  have hf : Continuous fun t : unitInterval => (D.unpt (γ t)).re :=
    Complex.continuous_re.comp (D.continuous_unpt.comp γ.continuous)
  obtain ⟨s, hs⟩ : (1 / 2 : ℝ) ∈ range fun t : unitInterval => (D.unpt (γ t)).re := by
    refine intermediate_value_univ 0 1 hf ⟨?_, ?_⟩
    · simp only [Path.source]
      norm_num [ContMetric.unpt_pt]
    · simp only [Path.target]
      norm_num [ContMetric.unpt_pt]
  refine ⟨D.unpt (γ s), D.mem_image_pt.1 (hγU s), hs, lt_of_le_of_lt ?_ hγ⟩
  have hQc : Continuous γ.extend := γ.continuous_extend
  have hmaps : ∀ a b : ℝ, MapsTo γ.extend (Icc a b) (D.pt '' U) := by
    intro a b t _
    obtain ⟨t', ht'⟩ : γ.extend t ∈ range γ := γ.extend_range ▸ mem_range_self t
    rw [← ht']
    exact hγU t'
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have l1 := MetricGeometry.internalEDist_le_curveLength hs0 hQc.continuousOn (hmaps 0 s)
  have l2 := MetricGeometry.internalEDist_le_curveLength hs1 hQc.continuousOn (hmaps s 1)
  rw [Path.extend_zero, γ.extend_extends' s] at l1
  rw [Path.extend_one, γ.extend_extends' s] at l2
  calc D.internal U 0 (D.unpt (γ s)) + D.internal U (D.unpt (γ s)) 1
      = MetricGeometry.internalEDist (D.pt '' U) (D.pt 0) (γ s) +
          MetricGeometry.internalEDist (D.pt '' U) (γ s) (D.pt 1) := rfl
    _ ≤ MetricGeometry.curveLength γ.extend 0 s + MetricGeometry.curveLength γ.extend s 1 :=
        add_le_add l1 l2
    _ = MetricGeometry.curveLength γ.extend 0 1 := MetricGeometry.curveLength_add _ hs0 hs1
    _ = MetricGeometry.pathLength γ := rfl

/-- **Density** (GA4 A6, step 3): a lower bound for `D(0,·;U) + D(·,1;U)` at the rational
midline points of `(U ∩ L) \ W`, `W` closed, holds at every point of `(U ∩ L) \ W`. -/
theorem le_add_of_forall_midQ (D : ContMetric) (hD : D.IsLength) {U : Set ℂ} (hU : IsOpen U)
    (h0 : (0 : ℂ) ∈ U) (h1 : (1 : ℂ) ∈ U) {W : Set ℂ} (hW : IsClosed W) {x : ℝ≥0∞}
    (hq : ∀ q : ℚ, midQ q ∈ (U ∩ {z | z.re = 1 / 2}) \ W →
      x ≤ D.internal U 0 (midQ q) + D.internal U (midQ q) 1)
    {u : ℂ} (hu : u ∈ (U ∩ {z | z.re = 1 / 2}) \ W) :
    x ≤ D.internal U 0 u + D.internal U u 1 := by
  obtain ⟨⟨huU, hure⟩, huW⟩ := hu
  by_contra hle
  have hlt := not_le.1 hle
  set F : ℂ → ℝ≥0∞ := fun z => D.internal U 0 z + D.internal U z 1 with hF
  have hFc : ContinuousOn F U := continuousOn_internal_add D hD hU h0 h1
  set g : ℝ → ℂ := fun y => (1 / 2 : ℂ) + (y : ℂ) * Complex.I with hg
  have hgc : Continuous g := by fun_prop
  have hgu : g u.im = u := (eq_half_add_mul_I hure).symm
  have hev : ∀ᶠ y in 𝓝 u.im, F (g y) < x ∧ g y ∈ U ∧ g y ∉ W := by
    have hA : ∀ᶠ y in 𝓝 u.im, F (g y) < x := by
      have hcont : ContinuousAt (F ∘ g) u.im :=
        ContinuousAt.comp_of_eq (hFc.continuousAt (hU.mem_nhds huU)) hgc.continuousAt hgu
      exact hcont.eventually (gt_mem_nhds (by simpa only [Function.comp_apply, hgu] using hlt))
    have hB : ∀ᶠ y in 𝓝 u.im, g y ∈ U :=
      hgc.continuousAt.eventually_mem (hU.mem_nhds (by rw [hgu]; exact huU))
    have hC : ∀ᶠ y in 𝓝 u.im, g y ∉ W :=
      hgc.continuousAt.eventually_mem (hW.isOpen_compl.mem_nhds (by rw [hgu]; exact huW))
    exact hA.and (hB.and hC)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u.im < u.im + ε by linarith)
  have hqd : dist (q : ℝ) u.im < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  obtain ⟨hFq, hqU, hqW⟩ := hball hqd
  have hgq : g q = midQ q := rfl
  rw [hgq] at hFq hqU hqW
  exact absurd (hq q ⟨⟨hqU, midQ_re q⟩, hqW⟩) (not_le.2 hFq)

/-- **(W3)** (GA4 A6): for the internal metric on `U_R` of a continuous length metric, the window
events of two windows whose centres are more than `2ρ` apart cannot both hold. -/
theorem not_winEvent_and_winEvent (D : ContMetric) (hD : D.IsLength) {K R : ℝ} (hKR : 0 < K * R)
    {c c' ρ : ℝ} (hcc : 2 * ρ < |c - c'|) :
    ¬ (winEvent (D.internal (rectU K R)) ((rectU K R ∩ {z | z.re = 1 / 2}) \ window c ρ) ∧
       winEvent (D.internal (rectU K R)) ((rectU K R ∩ {z | z.re = 1 / 2}) \ window c' ρ)) := by
  rintro ⟨⟨hfin, δ, hδ, hW⟩, ⟨-, δ', hδ', hW'⟩⟩
  have hU : IsOpen (rectU K R) := isOpen_rectU K R
  have h0 := zero_mem_rectU hKR
  have h1 := one_mem_rectU hKR
  have hδm : 0 < min δ δ' := lt_min hδ hδ'
  obtain ⟨u, huU, hure, hu⟩ := exists_midline_lt_of_internal_lt D
    (ENNReal.lt_add_right hfin.ne hδm.ne')
  refine absurd hu (not_lt.2 ?_)
  by_cases hJ : u ∈ window c ρ
  · have hJ' : u ∉ window c' ρ := by
      rintro ⟨-, h'⟩
      have h := hJ.2
      have : |c - c'| ≤ 2 * ρ := by
        calc |c - c'| = |(u.im - c') - (u.im - c)| := by ring_nf
          _ ≤ |u.im - c'| + |u.im - c| := abs_sub _ _
          _ ≤ 2 * ρ := by linarith
      linarith
    exact (add_le_add le_rfl (min_le_right _ _)).trans
      (le_add_of_forall_midQ D hD hU h0 h1 (isClosed_window c' ρ) hW' ⟨⟨huU, hure⟩, hJ'⟩)
  · exact (add_le_add le_rfl (min_le_left _ _)).trans
      (le_add_of_forall_midQ D hD hU h0 h1 (isClosed_window c ρ) hW ⟨⟨huU, hure⟩, hJ⟩)

/-! ### (A7) The window event for the Möbius-transported metric -/

/-- `D(z, w) ≤ D(z, w; V)`, with `D(z, w) ∈ ℝ` embedded in `[0, ∞]`. -/
theorem ofReal_le_internal (D : ContMetric) (V : Set ℂ) (z w : ℂ) :
    ENNReal.ofReal (D.1 (z, w)) ≤ D.internal V z w := by
  have h := MetricGeometry.edist_le_internalEDist (X := D.Space) (D.pt '' V) (D.pt z) (D.pt w)
  rw [edist_dist] at h
  exact h

/-- A constant-speed geodesic contained in `V` realizes the internal distance of `V`:
`D(z, w; V) = D(z, w)` (GA4 A7, step 1). -/
theorem internal_eq_of_isGeod01 {D : ContMetric} {z w : ℂ} {η : C(unitInterval, ℂ)} {V : Set ℂ}
    (hη : Blueprint.IsGeod01 D z w η) (hV : range η ⊆ V) :
    D.internal V z w = ENNReal.ofReal (D.1 (z, w)) :=
  le_antisymm (GM.internal_le_of_isGeod01 hη hV) (ofReal_le_internal D V z w)

/-- **Strict triangle inequality off the unique geodesic** (GA4 A7, step 2): if geodesics join all
pairs of points and the geodesic `P` from `a` to `b ≠ a` is unique, then every `z ∉ {a, b}` off
`P` has `D(a, b) < D(a, z) + D(z, b)`. Otherwise geodesics `a → z → b` concatenate to a geodesic
from `a` to `b` through `z` (`LQGMetric.GM.exists_geod_through`), which must be `P`. -/
theorem lt_dist_add_dist_of_notMem_range (D : ContMetric)
    (hgeo : ∀ z w : ℂ, ∃ η, Blueprint.IsGeod01 D z w η) {a b : ℂ} (hab : a ≠ b)
    {P : C(unitInterval, ℂ)} (huniq : ∀ η, Blueprint.IsGeod01 D a b η → η = P)
    {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) (hzP : z ∉ range P) :
    D.1 (a, b) < D.1 (a, z) + D.1 (z, b) := by
  have hpos : ∀ x y : ℂ, x ≠ y → 0 < D.1 (x, y) := fun x y hxy =>
    lt_of_le_of_ne (dist_nonneg (x := D.pt x) (y := D.pt y)) fun h =>
      hxy (D.2.eq_of_eq_zero x y h.symm)
  refine lt_of_le_of_ne (D.2.triangle a z b) fun heq => hzP ?_
  have hL := hpos a b hab
  have haz := hpos a z (Ne.symm hza)
  have hzb' := hpos z b hzb
  set t := D.1 (a, z) / D.1 (a, b) with ht
  have ht0 : 0 < t := div_pos haz hL
  have ht1 : t < 1 := (div_lt_one hL).2 (by linarith)
  have hmid : GM.midPt D a b t z := by
    refine ⟨(div_mul_cancel₀ _ hL.ne').symm, ?_⟩
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hL.ne']
    linarith
  obtain ⟨η₁, h₁⟩ := hgeo a z
  obtain ⟨η₂, h₂⟩ := hgeo z b
  obtain ⟨η, hη, hηt⟩ := GM.exists_geod_through ht0 ht1 h₁ h₂ hmid
  exact ⟨GM.pj t, by rw [← huniq η hη, hηt]⟩

/-- The strict triangle inequality of `lt_dist_add_dist_of_notMem_range` is uniform on compact
sets (GA4 A7, step 2: "a compactness gap"). -/
theorem exists_gap_of_isCompact (D : ContMetric)
    (hgeo : ∀ z w : ℂ, ∃ η, Blueprint.IsGeod01 D z w η) {a b : ℂ} (hab : a ≠ b)
    {P : C(unitInterval, ℂ)} (huniq : ∀ η, Blueprint.IsGeod01 D a b η → η = P)
    {Z : Set ℂ} (hZ : IsCompact Z) (hZP : ∀ z ∈ Z, z ∉ range P ∧ z ≠ a ∧ z ≠ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Z, D.1 (a, b) + δ ≤ D.1 (a, z) + D.1 (z, b) := by
  have hcont : Continuous fun z => D.1 (a, z) + D.1 (z, b) :=
    (D.1.continuous.comp (continuous_const.prodMk continuous_id)).add
      (D.1.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨a', ha', h⟩ := hZ.exists_forall_le' hcont.continuousOn fun z hz =>
    lt_dist_add_dist_of_notMem_range D hgeo hab huniq (hZP z hz).2.1 (hZP z hz).2.2 (hZP z hz).1
  exact ⟨a' - D.1 (a, b), by linarith, fun z hz => by linarith [h z hz]⟩

/-- The compact midline band `{1/2 + iy : a ≤ |y| ≤ b}`. -/
theorem isCompact_midline_band (a b : ℝ) :
    IsCompact {z : ℂ | z.re = 1 / 2 ∧ a ≤ |z.im| ∧ |z.im| ≤ b} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |b|)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [hz.1, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hz.2.2, le_abs_self b]

/-- Points of `U_R` (`R ≤ 1/1000`) have norm at most `2`. -/
theorem norm_le_two_of_mem_rectU {R : ℝ} (hR : R ≤ 1 / 1000) {u : ℂ} (hu : u ∈ rectU 100 R) :
    ‖u‖ ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine (Complex.norm_le_abs_re_add_abs_im u).trans ?_
  have : |u.re| ≤ 5 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- The event `A = {M ≤ r}` of §7 is `{P ⊆ T_r}`. -/
theorem maxDev_le_iff_forall_mem_tube (η : C(unitInterval, ℂ)) (r : ℝ) :
    maxDev η ≤ r ↔ ∀ t, η t ∈ tube r :=
  ciSup_le_iff (bddAbove_infDist η)

/-- **(A7)**, deterministic: on the event `{P ⊆ T_r}`, with unique geodesic `P` from `0` to `1`,
existence of geodesics, and the Möbius covariance `D(·,·;V) = c · d′(φ_θ ·, φ_θ ·)` on
`V = ψ_θ(U_R)`, the transported distance `d′` satisfies the window event for the window of
radius `2r` around `tan(θ/2)/2`. -/
theorem winEvent_of_geod_subset_tube (D : ContMetric) (_hlen : D.IsLength)
    (hgeo : ∀ z w : ℂ, ∃ η, Blueprint.IsGeod01 D z w η)
    {P : C(unitInterval, ℂ)} (hP : Blueprint.IsGeod01 D 0 1 P)
    (huniq : ∀ η, Blueprint.IsGeod01 D 0 1 η → η = P)
    {r R θ : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R)
    (hPT : ∀ t, P t ∈ tube r)
    {d' : ℂ → ℂ → ℝ≥0∞} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hMC : ∀ z ∈ mobPhi (-θ) '' rectU 100 R, ∀ w ∈ mobPhi (-θ) '' rectU 100 R,
      D.internal (mobPhi (-θ) '' rectU 100 R) z w = c * d' (mobPhi θ z) (mobPhi θ w)) :
    winEvent d' ((rectU 100 R ∩ {z | z.re = 1 / 2}) \ window (Real.tan (θ / 2) / 2) (2 * r)) := by
  set V := mobPhi (-θ) '' rectU 100 R with hV
  have hR0 : 0 < R := hr.trans_le hrR
  have hKR : (0 : ℝ) < 100 * R := by linarith
  have h0V : (0 : ℂ) ∈ V := ⟨0, zero_mem_rectU hKR, mobPhi_zero _⟩
  have h1V : (1 : ℂ) ∈ V := ⟨1, one_mem_rectU hKR, mobPhi_one _⟩
  -- Step 1: `D(0,1;V) = D(0,1)`, since `P ⊆ T_r ⊆ V`.
  have hPV : range P ⊆ V := by
    rintro _ ⟨t, rfl⟩
    exact tube_subset_image_rectU hr hrR hR hθ (hPT t)
  have h01 : D.internal V 0 1 = ENNReal.ofReal (D.1 (0, 1)) := internal_eq_of_isGeod01 hP hPV
  have h01' : D.internal V 0 1 = c * d' 0 1 := by
    rw [hMC 0 h0V 1 h1V, mobPhi_zero, mobPhi_one]
  -- Step 2: a uniform gap on the compact band `{1/2 + iy : 5r/3 ≤ |y| ≤ 1}`.
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ {z : ℂ | z.re = 1 / 2 ∧ 5 * r / 3 ≤ |z.im| ∧
      |z.im| ≤ 1}, D.1 (0, 1) + δ ≤ D.1 (0, z) + D.1 (z, 1) := by
    refine exists_gap_of_isCompact D hgeo zero_ne_one huniq (isCompact_midline_band _ _) ?_
    intro z hz
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨t, rfl⟩
      have := abs_im_le_of_mem_tube (hPT t)
      linarith [hz.2.1]
    · rintro rfl
      norm_num at hz
    · rintro rfl
      norm_num at hz
  -- Steps 3–4: the window bound with gap `δ / c`.
  refine ⟨?_, ENNReal.ofReal δ / c, ENNReal.div_pos_iff.2 ⟨by simpa using hδ, hct⟩,
    fun q hq => ?_⟩
  · refine lt_top_iff_ne_top.2 fun htop => ?_
    rw [htop, ENNReal.mul_top hc0, h01] at h01'
    exact ENNReal.ofReal_ne_top h01'
  · obtain ⟨⟨hqU, hqre⟩, hqJ⟩ := hq
    obtain ⟨hzre, hzim⟩ := midline_preimage hr hrR hR hθ hqU hqre hqJ
    have hzim1 := abs_im_mobPhi_neg_le_one hR hθ hqU hqre
    have hzV : mobPhi (-θ) (midQ q) ∈ V := ⟨midQ q, hqU, rfl⟩
    have hφz : mobPhi θ (mobPhi (-θ) (midQ q)) = midQ q :=
      mobPhi_mobPhi_neg_of_norm_le (by linarith)
        ((norm_le_two_of_mem_rectU hR hqU).trans (by norm_num))
    have e1 : D.internal V 0 (mobPhi (-θ) (midQ q)) = c * d' 0 (midQ q) := by
      rw [hMC 0 h0V _ hzV, mobPhi_zero, hφz]
    have e2 : D.internal V (mobPhi (-θ) (midQ q)) 1 = c * d' (midQ q) 1 := by
      rw [hMC _ hzV 1 h1V, hφz, mobPhi_one]
    have hnn : ∀ x y : ℂ, 0 ≤ D.1 (x, y) := fun x y => dist_nonneg (x := D.pt x) (y := D.pt y)
    rw [← ENNReal.mul_le_mul_iff_right hc0 hct, mul_add, mul_add, ENNReal.mul_div_cancel hc0 hct,
      ← h01', ← e1, ← e2, h01]
    calc ENNReal.ofReal (D.1 (0, 1)) + ENNReal.ofReal δ = ENNReal.ofReal (D.1 (0, 1) + δ) :=
          (ENNReal.ofReal_add (hnn 0 1) hδ.le).symm
      _ ≤ ENNReal.ofReal (D.1 (0, mobPhi (-θ) (midQ q)) + D.1 (mobPhi (-θ) (midQ q), 1)) :=
          ENNReal.ofReal_le_ofReal (hgap _ ⟨hzre, hzim.le, hzim1⟩)
      _ = ENNReal.ofReal (D.1 (0, mobPhi (-θ) (midQ q))) +
            ENNReal.ofReal (D.1 (mobPhi (-θ) (midQ q), 1)) :=
          ENNReal.ofReal_add (hnn _ _) (hnn _ _)
      _ ≤ D.internal V 0 (mobPhi (-θ) (midQ q)) + D.internal V (mobPhi (-θ) (midQ q)) 1 :=
          add_le_add (ofReal_le_internal D V _ _) (ofReal_le_internal D V _ _)

end SmallGammaGeodesics
