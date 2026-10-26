import HigherDimLFPPAS.Localize.Confine

/-!
# Lemma 2.4: both assertions

Packet L24; planning audit MA1 §2.7 and Details A6.3 (`source/…txt` l. 263–287).

* `isOpen_exists_lt_on`, `isOpen_exists_gt_on`: the sets of continuous functions on `ℝ^d × ℝ^d` that
  exceed (resp. undercut) a level somewhere on `A × B` are open (compact-open topology).
* `exists_diam_bound`: a deterministic `T₀ ≥ 1` with `P[diam(F; D) > T₀ − 1] ≤ η`.
* `exists_exit_radius`: given a.s. escape from `F`, a deterministic `R` with `F ⊆ B_R` and
  `P[D(F, S_R) < c] ≤ η`.
* `meps_confine_of_bounds` (deterministic): from `D ≤ T₀ − 1` on `F × F`, `D ≥ 10 T₀ + 1` from `F` to `S_R`
  and `sup_{B̄_R²} |M_ε − D| < T₀`, the confinement and geodesic clauses of Lemma 2.4 for `M_ε`.
* `lemma24Confine_of_conv`: the interface `Core.Lemma24Confine` from `Core.Setting` and `Core.Lemma24Conv`.
* `lemma24_holds`: `Core.Lemma24Conv ∧ Core.Lemma24Confine` from `Core.Setting` and `Core.Lemma23i`.

Outer measures throughout: the good events of Lemma 2.4 are never claimed measurable; only the auxiliary
events `{D ∈ U}` (`U` open) are, through the measurability of the assignment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Localize

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ## Open events of a random continuous function -/

theorem isOpen_exists_lt_on (A B : Set (Rd d)) (c : ℝ) :
    IsOpen {f : C(Rd d × Rd d, ℝ) | ∃ x ∈ A, ∃ y ∈ B, c < f (x, y)} := by
  have heq : {f : C(Rd d × Rd d, ℝ) | ∃ x ∈ A, ∃ y ∈ B, c < f (x, y)} =
      ⋃ x ∈ A, ⋃ y ∈ B, {f : C(Rd d × Rd d, ℝ) | c < f (x, y)} := by
    ext f
    simp only [mem_iUnion, exists_prop]
    rfl
  rw [heq]
  exact isOpen_biUnion fun x _ => isOpen_biUnion fun y _ =>
    isOpen_lt continuous_const (continuous_eval_const _)

theorem isOpen_exists_gt_on (A B : Set (Rd d)) (c : ℝ) :
    IsOpen {f : C(Rd d × Rd d, ℝ) | ∃ x ∈ A, ∃ y ∈ B, f (x, y) < c} := by
  have heq : {f : C(Rd d × Rd d, ℝ) | ∃ x ∈ A, ∃ y ∈ B, f (x, y) < c} =
      ⋃ x ∈ A, ⋃ y ∈ B, {f : C(Rd d × Rd d, ℝ) | f (x, y) < c} := by
    ext f
    simp only [mem_iUnion, exists_prop]
    rfl
  rw [heq]
  exact isOpen_biUnion fun x _ => isOpen_biUnion fun y _ =>
    isOpen_lt (continuous_eval_const _) continuous_const

/-! ## Deterministic levels from the law of `D` -/

/-- **Choice of `T₀`** (MA1 A6.3): for a measurable random continuous function `Y` and a compact `F`, some
deterministic `T₀ ≥ 1` has `P[sup_{F×F} Y > T₀ − 1] ≤ η`. -/
theorem exists_diam_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → C(Rd d × Rd d, ℝ)} (hY : Measurable Y) {F : Set (Rd d)} (hF : IsCompact F)
    {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ P {ω | ∃ x ∈ F, ∃ y ∈ F, T₀ - 1 < Y ω (x, y)} ≤ ENNReal.ofReal η := by
  let S : ℕ → Set Ω := fun n => {ω | ∃ x ∈ F, ∃ y ∈ F, (n : ℝ) < Y ω (x, y)}
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    hY (isOpen_exists_lt_on F F (n : ℝ)).measurableSet
  have hanti : Antitone S := by
    intro n m hnm ω hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    exact ⟨x, hx, y, hy, lt_of_le_of_lt (by exact_mod_cast hnm) hlt⟩
  have hempty : ⋂ n, S n = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    obtain ⟨B, hB⟩ := (hF.prod hF).exists_bound_of_continuousOn (Y ω).continuous.continuousOn
    obtain ⟨n, hn⟩ := exists_nat_gt B
    obtain ⟨x, hx, y, hy, hlt⟩ := mem_iInter.1 hω n
    have hle := (Real.le_norm_self _).trans (hB (x, y) ⟨hx, hy⟩)
    linarith
  have hT := tendsto_measure_iInter_atTop (μ := P) (fun n => (hSm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hT
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη))).exists
  refine ⟨n + 1, by linarith [n.cast_nonneg (α := ℝ)], ?_⟩
  have hn1 : (n : ℝ) + 1 - 1 = n := by ring
  simp only [hn1]
  exact hn.le

/-- **Choice of `R`** (MA1 A6.3): if a.s. the random continuous function `Y` exceeds `c` from `F` to every
point outside some random ball, then some deterministic `R > 0` has `F ⊆ B_R` and
`P[inf_{F × S_R} Y < c] ≤ η`. -/
theorem exists_exit_radius {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → C(Rd d × Rd d, ℝ)} (hY : Measurable Y) {F : Set (Rd d)} (hF : IsCompact F) (c : ℝ)
    (hesc : ∀ᵐ ω ∂P, ∃ R₀ : ℝ, ∀ x ∈ F, ∀ y : Rd d, R₀ ≤ ‖y‖ → c < Y ω (x, y))
    {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ F ⊆ ball (0 : Rd d) R ∧
      P {ω | ∃ x ∈ F, ∃ z ∈ sphere (0 : Rd d) R, Y ω (x, z) < c} ≤ ENNReal.ofReal η := by
  let A : ℕ → Set Ω := fun m => {ω | ∃ x ∈ F, ∃ z ∈ sphere (0 : Rd d) (m : ℝ), Y ω (x, z) < c}
  let B : ℕ → Set Ω := fun n => ⋃ m ∈ Ici n, A m
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.biUnion (to_countable _) fun m _ =>
      hY (isOpen_exists_gt_on F (sphere (0 : Rd d) (m : ℝ)) c).measurableSet
  have hanti : Antitone B := fun n n' hnn' =>
    biUnion_subset_biUnion_left (Ici_subset_Ici.2 hnn')
  have hnull : P (⋂ n, B n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hesc)
    rintro ⟨R₀, hR₀⟩
    obtain ⟨n, hn⟩ := exists_nat_ge R₀
    obtain ⟨m, hm, x, hx, z, hz, hlt⟩ := mem_iUnion₂.1 (mem_iInter.1 hω n)
    have hzn : ‖z‖ = m := by simpa using hz
    have hgt := hR₀ x hx z (by rw [hzn]; exact hn.trans (Nat.cast_le.2 hm))
    linarith
  have hT := tendsto_measure_iInter_atTop (μ := P) (fun n => (hBm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hnull] at hT
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη)))
  obtain ⟨r, hr⟩ := hF.isBounded.subset_ball (0 : Rd d)
  let n : ℕ := max N (⌈r⌉₊ + 1)
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := le_trans (Nat.le_add_left 1 _) (le_max_right _ _)
    exact_mod_cast this
  have hrn : r < n := by
    have h1 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
    have h2 : ((⌈r⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast le_max_right N (⌈r⌉₊ + 1)
    push_cast at h2
    linarith
  refine ⟨n, by linarith, hr.trans (ball_subset_ball hrn.le), ?_⟩
  have hsub : A n ⊆ B n := subset_biUnion_of_mem (u := A) (mem_Ici.2 le_rfl)
  exact (measure_mono hsub).trans (hN n (le_max_left _ _)).le

/-! ## The deterministic good event -/

/-- **Lemma 2.4's good event** (MA1 A6.3, deterministic): if `G ≤ T₀ − 1` on `F × F`, `G ≥ 10 T₀ + 1` from
`F` to `S_R`, `F ⊆ B_R`, and `M_ε` is within `T₀` of `G` on `B̄_R × B̄_R`, then every pair of `F` has a
unit-speed `M_ε`-geodesic and every `M_ε`-geodesic between points of `F` stays in `B_R`. -/
theorem meps_confine_of_bounds {κ : Rd d → ℝ} {ξ ε : ℝ} (hξ : 0 < ξ) (ha : 0 < aEps κ ξ ε)
    {g : DistRd d} {G : C(Rd d × Rd d, ℝ)} {F : Set (Rd d)} {R T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (hFR : F ⊆ ball (0 : Rd d) R)
    (h1 : ∀ x ∈ F, ∀ y ∈ F, G (x, y) ≤ T₀ - 1)
    (h2 : ∀ x ∈ F, ∀ z ∈ sphere (0 : Rd d) R, 10 * T₀ + 1 ≤ G (x, z))
    (h3 : ⨆ q ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        edist ((Core.Meps κ ξ ε g).1 q) (G q) < ENNReal.ofReal T₀) :
    ∀ x ∈ F, ∀ y ∈ F,
      (∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
          ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Core.Meps κ ξ ε g).1 (γ s, γ t) = |t - s|) ∧
        ∀ (γ : ℝ → Rd d) (T : ℝ), γ 0 = x → γ T = y →
          IsGeodesicCurve ((Core.Meps κ ξ ε g).pt ∘ γ) 0 T → MapsTo γ (Icc 0 T) (ball 0 R) := by
  have hclose : ∀ q ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
      |(Core.Meps κ ξ ε g).1 q - G q| < T₀ := by
    intro q hq
    have hlt := (le_iSup₂ (f := fun q (_ : q ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) =>
      edist ((Core.Meps κ ξ ε g).1 q) (G q)) q hq).trans_lt h3
    rw [← Real.dist_eq]
    exact edist_lt_ofReal.1 hlt
  have hFcl : ∀ x ∈ F, x ∈ closedBall (0 : Rd d) R := fun x hx => ball_subset_closedBall (hFR hx)
  have hMeq : Core.Meps κ ξ ε g = fieldLfppMetric ξ
      (Core.locFieldC κ ε g + ContinuousMap.const (Rd d) (ξ⁻¹ * Real.log (aEps κ ξ ε)⁻¹)) := by
    rw [meps_eq_smul g ha, smul_fieldLfppMetric_eq hξ.ne']
  have hpair : ∀ x ∈ F, ∀ y ∈ F, (Core.Meps κ ξ ε g).1 (x, y) < 2 * T₀ := by
    intro x hx y hy
    have hc := (abs_lt.1 (hclose (x, y) ⟨hFcl x hx, hFcl y hy⟩)).2
    linarith [h1 x hx y hy]
  have hexit : ∀ x ∈ F, ∀ z ∈ sphere (0 : Rd d) R, 9 * T₀ ≤ (Core.Meps κ ξ ε g).1 (x, z) := by
    intro x hx z hz
    have hc := (abs_lt.1 (hclose (x, z) ⟨hFcl x hx, sphere_subset_closedBall hz⟩)).1
    linarith [h2 x hx z hz]
  rw [hMeq] at hpair hexit ⊢
  exact fieldLfppMetric_confine hξ _ (by linarith) hFR hpair hexit

/-! ## Outer-probability bookkeeping -/

/-- If the complement of `G` is covered by three sets of outer probability `≤ η` and `p + 3η ≤ 1`, then
`G` has outer probability `≥ p`. -/
theorem ofReal_le_measure_of_compl_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G A₁ A₂ A₃ : Set Ω} {p η : ℝ} (hp : 0 ≤ p) (hη : 0 ≤ η)
    (hpη : p + 3 * η ≤ 1) (h₁ : P A₁ ≤ ENNReal.ofReal η) (h₂ : P A₂ ≤ ENNReal.ofReal η)
    (h₃ : P A₃ ≤ ENNReal.ofReal η) (hsub : Gᶜ ⊆ A₁ ∪ A₂ ∪ A₃) :
    ENNReal.ofReal p ≤ P G := by
  have hGc : P Gᶜ ≤ ENNReal.ofReal (3 * η) := by
    calc P Gᶜ ≤ P (A₁ ∪ A₂ ∪ A₃) := measure_mono hsub
      _ ≤ P A₁ + P A₂ + P A₃ :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ ≤ ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η :=
        add_le_add (add_le_add h₁ h₂) h₃
      _ = ENNReal.ofReal (3 * η) := by
        rw [← ENNReal.ofReal_add hη hη, ← ENNReal.ofReal_add (by positivity) hη]
        congr 1
        ring
  have h1 : (1 : ℝ≥0∞) ≤ P G + ENNReal.ofReal (3 * η) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ = P (G ∪ Gᶜ) := by rw [union_compl_self]
      _ ≤ P G + P Gᶜ := measure_union_le _ _
      _ ≤ P G + ENNReal.ofReal (3 * η) := add_le_add_right hGc _
  have h2 : ENNReal.ofReal p + ENNReal.ofReal (3 * η) ≤ 1 := by
    rw [← ENNReal.ofReal_add hp (by positivity), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hpη
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (h2.trans h1)

/-! ## Lemma 2.4 -/

/-- **Lemma 2.4, second assertion** (MA1 A6.3): confinement and existence of unit-speed `M_ε`-geodesics,
from the first assertion and the standing hypotheses. -/
theorem lemma24Confine_of_conv {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (hconv : Core.Lemma24Conv κ ξ D P h) :
    Core.Lemma24Confine κ ξ P h := by
  intro F hF p hp
  rcases le_or_gt p 0 with hp0 | hp0
  · exact ⟨1, one_pos, Eventually.of_forall fun ε => by
      rw [ENNReal.ofReal_of_nonpos hp0]
      exact zero_le⟩
  have hη : 0 < (1 - p) / 4 := by linarith
  have hY : Measurable fun ω => (D (h ω)).1 :=
    measurable_metric_comp hS.strong.measurable hS.field.1.measurable
  obtain ⟨T₀, hT₀, hA₁⟩ := exists_diam_bound (P := P) hY hF hη
  have hesc : ∀ᵐ ω ∂P, ∃ R₀ : ℝ, ∀ x ∈ F, ∀ y : Rd d, R₀ ≤ ‖y‖ →
      10 * T₀ + 1 < (D (h ω)).1 (x, y) := by
    filter_upwards [lemma22_ae_proper_and_geodesic hS.dim hS.xi_pos hS.subcrit P h hS.field D
      hS.strong] with ω hω
    exact hω.2.1 F hF _
  obtain ⟨R, hR, hFR, hA₂⟩ := exists_exit_radius (P := P) hY hF (10 * T₀ + 1) hesc hη
  refine ⟨R, hR, ?_⟩
  have hA₃ := (hconv R hR T₀ (by linarith)).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη))
  filter_upwards [hA₃, self_mem_nhdsWithin] with ε hε₃ hε
  refine ofReal_le_measure_of_compl_subset hp0.le hη.le (by linarith) hA₁ hA₂ hε₃.le ?_
  intro ω hω
  by_contra hnot
  simp only [mem_union, not_or] at hnot
  obtain ⟨⟨hn₁, hn₂⟩, hn₃⟩ := hnot
  refine hω (meps_confine_of_bounds (G := (D (h ω)).1) hS.xi_pos (hS.seed.aEps_pos ξ ε hε) hT₀ hFR
    ?_ ?_ ?_)
  · intro x hx y hy
    by_contra hlt
    exact hn₁ ⟨x, hx, y, hy, lt_of_not_ge hlt⟩
  · intro x hx z hz
    by_contra hlt
    exact hn₂ ⟨x, hx, z, hz, lt_of_not_ge hlt⟩
  · exact lt_of_not_ge hn₃

/-- **Lemma 2.4** (packet L24 target): both interfaces `Core.Lemma24Conv` and `Core.Lemma24Confine`, from
the standing hypotheses `Core.Setting` and Lemma 2.3(i) (`Core.Lemma23i`, used in probability only). -/
theorem lemma24_holds {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h23 : Core.Lemma23i κ P h) :
    Core.Lemma24Conv κ ξ D P h ∧ Core.Lemma24Confine κ ξ P h :=
  ⟨lemma24Conv_of_setting hS h23, lemma24Confine_of_conv hS (lemma24Conv_of_setting hS h23)⟩

end HigherDimLFPPAS.Localize
