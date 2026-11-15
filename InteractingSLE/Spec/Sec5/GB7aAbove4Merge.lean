/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GB7aAbove4Chart

/-!
# GB7a's pathwise half above `κ = 4`: first visits and the merged-group picture

Packet PROVE-CFBARRIER2. Deterministic facts about one path of an integrated `SLE_κ(ρ)` evolution (force part
`Sec2.IsForcePath`) with a continuous generating trace, **without injectivity of the trace**:

* `exists_first_visit_le`: the first visit of a closed real half-line `[X₀, ∞)` before a visit time;
* `rightCmpPath_of_merged`: **the comparison picture of a merged group.** If the right marks at or left of `x_k` are
  merged with the driver at a time `s₀ > 0` at which the trace is at a positive real point, and mark `k` collides with
  the driver again at `s₁ < ζ` while the trace stays off `[a', ∞)` up to `s₁`, then `GB7a.RightCmpPath` holds at a
  rational restart time: after `s₀` the merged marks move together, so their comparison weights `S − ∑ ρⱼ = 0` cancel in
  the drift, and the remaining marks stay at a positive distance from the driver up to the next collision of `k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5.GB7aAbove4

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open GB7a

/-! ### First visits -/

/-- **First visit of a closed real half-line before a visit time.** A curve continuous on `[0, t₀]` with `η 0 = 0`
that visits a real point `y ≥ X₀ > 0` at `t₀` visits `[X₀, ∞)` for a first time `u ∈ (0, t₀]`, at a real point
`X ≥ X₀`, and stays off `[X₀, ∞)` before `u`. -/
theorem exists_first_visit_le {η : ℝ≥0 → ℂ} {t₀ : ℝ≥0} (hc : ContinuousOn η (Icc 0 t₀)) (h0 : η 0 = 0)
    {X₀ : ℝ} (hX₀ : 0 < X₀) {y : ℝ} (hy : X₀ ≤ y) (hvis : η t₀ = y) :
    ∃ u : ℝ≥0, 0 < u ∧ u ≤ t₀ ∧ ∃ X : ℝ, X₀ ≤ X ∧ η u = X ∧
      ∀ s : ℝ≥0, s < u → ∀ r : ℝ, X₀ ≤ r → η s ≠ r := by
  set S : Set ℂ := {z | z.im = 0 ∧ X₀ ≤ z.re} with hS
  have hSc : IsClosed S :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  set A : Set ℝ≥0 := Icc 0 t₀ ∩ η ⁻¹' S with hA
  have hAc : IsClosed A := hc.preimage_isClosed_of_isClosed isClosed_Icc hSc
  have hmem : ∀ s : ℝ≥0, η s ∈ S ↔ ∃ r : ℝ, X₀ ≤ r ∧ η s = r := fun s => by
    constructor
    · intro hs
      exact ⟨(η s).re, hs.2, Complex.ext (by simp) (by simp [hs.1])⟩
    · rintro ⟨r, hr, he⟩
      rw [he]
      exact ⟨by simp, by simpa using hr⟩
  have ht₀A : t₀ ∈ A := ⟨⟨zero_le, le_rfl⟩, (hmem t₀).2 ⟨y, hy, hvis⟩⟩
  have hbdd : BddBelow A := ⟨0, fun _ _ => zero_le⟩
  have huA : sInf A ∈ A := hAc.csInf_mem ⟨t₀, ht₀A⟩ hbdd
  obtain ⟨X, hX, hηu⟩ := (hmem _).1 huA.2
  refine ⟨sInf A, ?_, csInf_le hbdd ht₀A, X, hX, hηu, fun s hs r hr he => ?_⟩
  · refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, h0] at hηu
    have := congrArg Complex.re hηu
    simp only [Complex.zero_re, Complex.ofReal_re] at this
    linarith
  · have hst : s ≤ t₀ := hs.le.trans (csInf_le hbdd ht₀A)
    exact notMem_of_lt_csInf hs hbdd ⟨⟨zero_le, hst⟩, (hmem s).2 ⟨r, hr, he⟩⟩

/-! ### The comparison picture of a merged group -/

section Merged

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- A time before the lifetime, read in `ℝ`. -/
theorem lt_zeta_of_le {s₁ : ℝ≥0} (hs₁ζ : (s₁ : ℝ≥0∞) < ζ) {t : ℝ≥0} (ht : t ≤ s₁) : (t : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hs₁ζ

/-- **The comparison picture of a merged group** (one path, no injectivity). -/
theorem rightCmpPath_of_merged (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    {k : Fin nR} {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    {s₀ s₁ : ℝ≥0} (hs₀₁ : s₀ < s₁) (hs₁ζ : (s₁ : ℝ≥0∞) < ζ)
    (hm₀ : ∀ j, xR j ≤ xR k → vR j s₀ = w s₀) (hz₁ : vR k s₁ = w s₁)
    {X₀ : ℝ} (hX₀ : 0 < X₀) (hηs₀ : η s₀ = X₀)
    (hfar : ∀ s : ℝ≥0, s ≤ s₁ → ∀ r : ℝ, a' ≤ r → η s ≠ r) :
    ∃ q : ℚ, RightCmpPath ρL ρR w vL vR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal := by
  classical
  have hwc := h.continuousOn_w
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hζ : ∀ t : ℝ≥0, t ≤ s₁ → (t : ℝ≥0∞) < ζ := fun t ht => lt_zeta_of_le hs₁ζ ht
  -- (1) a driver on `ℝ` and the trace before a time `t₂ ∈ (s₁, ζ)`
  obtain ⟨t₂, hs₁t₂, ht₂ζ⟩ := exists_real_btwn_of_lt hs₁ζ
  set U := frozenDrive w t₂ with hUdef
  have hU : Continuous U := continuous_frozenDrive_of_lt hwc ht₂ζ
  have ht₂0 : 0 ≤ t₂ := s₁.coe_nonneg.trans hs₁t₂.le
  have hU0 : U 0 = 0 := by rw [hUdef, frozenDrive_zero ht₂0, h.w_zero]
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR : IsLoewnerTraceLT U t₂ ηR := hη.isLoewnerTraceLT ht₂ζ
  have hT₂ : ((t₂.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := by
    have : ENNReal.ofReal t₂ = ((t₂.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
    rw [← this]; exact ht₂ζ.le
  have hUw : ∀ s : ℝ, 0 ≤ s → s < (t₂.toNNReal : ℝ) → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, (hs.trans_eq (Real.coe_toNNReal _ ht₂0)).le⟩
  have hlt₂ : ∀ t : ℝ≥0, t ≤ s₁ → (t : ℝ) < (t₂.toNNReal : ℝ) := fun t ht => by
    rw [Real.coe_toNNReal _ ht₂0]; exact (NNReal.coe_le_coe.2 ht).trans_lt hs₁t₂
  have pkgR := fun j (t : ℝ≥0) (ht : t ≤ s₁) => centredPkg hwc (h.continuousOn_vR j)
    (fun t ht => h.integrable_gapR ht j) (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hT₂ hUw
    t.coe_nonneg (hlt₂ t ht)
  have pkgL := fun i (t : ℝ≥0) (ht : t ≤ s₁) => centredPkg hwc (h.continuousOn_vL i)
    (fun t ht => h.integrable_gapL ht i) (fun t ht => h.vL_eq ht i) (h.volume_collisionL i) hT₂ hUw
    t.coe_nonneg (hlt₂ t ht)
  have hle₂ : ∀ t : ℝ≥0, t ≤ s₁ → ∀ s ∈ Icc (0 : ℝ) t, s.toNNReal ≤ s₁ := fun t ht s hs =>
    (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
  -- the tip at a right collision of a mark `j` at `t ≤ s₁`
  have htipR : ∀ j (t : ℝ≥0), t ≤ s₁ → vR j t = w t →
      ∃ x : ℝ, η t = x ∧ xR j ≤ x ∧ ∀ y : ℝ, x < y → ∃ v, IsForwardSol U (y : ℂ) t v := by
    intro j t ht he
    obtain ⟨hc, hue, hi, hn⟩ := pkgR j t ht
    obtain ⟨x, hx, hx0, hxy⟩ := hηR.exists_tip_real_of_collision_right hU hU0 t.coe_nonneg
      ((NNReal.coe_le_coe.2 ht).trans_lt hs₁t₂) hc
      (fun s hs => sub_nonneg.2 (h.w_le_vR (hζ _ (hle₂ t ht s hs)) j)) hue hi hn (by simp [he])
    refine ⟨x, by simpa [hηRdef] using hx, ?_, hxy⟩
    simpa [h.vR_zero j, h.w_zero] using hx0
  have htipL : ∀ i (t : ℝ≥0), t ≤ s₁ → vL i t = w t → ∃ x : ℝ, η t = x ∧ x ≤ xL i := by
    intro i t ht he
    obtain ⟨hc, hue, hi, hn⟩ := pkgL i t ht
    obtain ⟨x, hx, hx0, -⟩ := hηR.exists_tip_real_of_collision_left hU hU0 t.coe_nonneg
      ((NNReal.coe_le_coe.2 ht).trans_lt hs₁t₂) hc
      (fun s hs => sub_nonpos.2 (h.vL_le_w (hζ _ (hle₂ t ht s hs)) i)) hue hi hn (by simp [he])
    refine ⟨x, by simpa [hηRdef] using hx, ?_⟩
    simpa [h.vL_zero i, h.w_zero] using hx0
  -- (2) the marks at or left of `x_k` move with `k` after `s₀`
  have hmerge : ∀ j, xR j ≤ xR k → ∀ t : ℝ≥0, s₀ ≤ t → t ≤ s₁ → vR j t = vR k t := fun j hj t ht0 ht1 =>
    Sec2.Assembly.vR_eq_of_eq h hs₁ζ (by rw [hm₀ j hj, hm₀ k le_rfl]) ⟨ht0, ht1⟩
  -- (3) a time `r₁ ∈ (s₀, s₁)` at which `k` is off the driver
  obtain ⟨r₁, hr₁0, hr₁1, hr₁⟩ : ∃ r₁ : ℝ≥0, s₀ < r₁ ∧ r₁ < s₁ ∧ vR k r₁ - w r₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Ioo (s₀ : ℝ) s₁ ⊆
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR k s.toNNReal} := by
      intro s hs
      have hs0 : 0 ≤ s := s₀.coe_nonneg.trans hs.1.le
      have h1 : s₀ < s.toNNReal := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.1
      have h2 : s.toNNReal < s₁ := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.2
      exact ⟨hs0, hζ _ h2.le, (sub_eq_zero.1 (hcon _ h1 h2)).symm⟩
    have h0 := measure_mono_null hsub (h.volume_collisionR k)
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    have : (s₀ : ℝ) < s₁ := hs₀₁
    linarith
  -- (4) the next collision `b` of `k` after `r₁`
  set Zk : Set ℝ≥0 := Icc r₁ s₁ ∩ (fun t => vR k t - w t) ⁻¹' {0} with hZk
  have hZkc : IsClosed Zk :=
    (((h.continuousOn_vR k).sub hwc).mono fun t ht => hζ t ht.2).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton
  have hs₁Z : s₁ ∈ Zk := ⟨⟨hr₁1.le, le_rfl⟩, by simp [hz₁]⟩
  have hbdd : BddBelow Zk := ⟨0, fun _ _ => zero_le⟩
  set b := sInf Zk with hb
  have hbZ : b ∈ Zk := hZkc.csInf_mem ⟨s₁, hs₁Z⟩ hbdd
  have hbs₁ : b ≤ s₁ := hbZ.1.2
  have hr₁b : r₁ < b := lt_of_le_of_ne hbZ.1.1 fun he => hr₁ (by rw [he]; exact hbZ.2)
  have hbk : vR k b = w b := sub_eq_zero.1 hbZ.2
  have hposk : ∀ t : ℝ≥0, r₁ ≤ t → t < b → w t < vR k t := fun t ht1 ht2 => by
    have hnot : t ∉ Zk := notMem_of_lt_csInf ht2 hbdd
    have hne : vR k t - w t ≠ 0 := fun h0 => hnot ⟨⟨ht1, ht2.le.trans hbs₁⟩, h0⟩
    exact lt_of_le_of_ne (h.w_le_vR (hζ t (ht2.le.trans hbs₁)) k) (fun he => hne (by rw [he, sub_self]))
  have hs₀b : s₀ ≤ b := (hr₁0.trans hr₁b).le
  -- (5) the tip at `b` is a real point `x ≥ X₀ > 0`
  obtain ⟨x, hxb, hxk, hxal⟩ := htipR k b hbs₁ hbk
  have hX₀x : X₀ ≤ x := by
    by_contra hlt
    push Not at hlt
    obtain ⟨v, hv⟩ := hxal X₀ hlt
    have hv0 := QuantumZipper.isForwardSol_restrict hv s₀.coe_nonneg (NNReal.coe_le_coe.2 hs₀b)
    refine trace_ne_of_isForwardSol hηR hU hU0 ⟨s₀.coe_nonneg, ?_⟩ hv0 ?_
    · exact (NNReal.coe_le_coe.2 (hs₀b.trans hbs₁)).trans_lt hs₁t₂
    · simp [hηRdef, hηs₀]
  -- (6) at `b`, the left marks and the right marks beyond `x_k` are off the driver
  have hbL : ∀ i, vL i b - w b ≠ 0 := fun i he => by
    obtain ⟨x', hx', hx'0⟩ := htipL i b hbs₁ (sub_eq_zero.1 he)
    rw [hxb] at hx'
    have hxx : x = x' := Complex.ofReal_injective hx'
    linarith [hord.2.1 i]
  have hbR : ∀ j, xR k < xR j → vR j b - w b ≠ 0 := fun j hj he => by
    obtain ⟨x'', hx'', hx''j, -⟩ := htipR j b hbs₁ (sub_eq_zero.1 he)
    exact hfar b hbs₁ x'' ((hnext j hj).trans hx''j) hx''
  have hbζ : (b : ℝ≥0∞) < ζ := hζ b hbs₁
  have hevL : ∀ i, ∀ᶠ t in 𝓝 b, vL i t - w t ≠ 0 := fun i =>
    (((h.continuousOn_vL i).sub hwc).continuousAt (hopen.mem_nhds hbζ)).eventually_ne (hbL i)
  have hevR : ∀ j, ∀ᶠ t in 𝓝 b, xR k < xR j → vR j t - w t ≠ 0 := fun j => by
    by_cases hj : xR k < xR j
    · exact ((((h.continuousOn_vR j).sub hwc).continuousAt (hopen.mem_nhds hbζ)).eventually_ne
        (hbR j hj)).mono fun t ht _ => ht
    · exact Eventually.of_forall fun t ht => absurd ht hj
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 ((Filter.eventually_all.2 hevL).and
    (Filter.eventually_all.2 hevR))
  -- (7) the rational restart time
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (r₁ : ℝ) ((b : ℝ) - ε / 2) < b from
    max_lt (NNReal.coe_lt_coe.2 hr₁b) (by linarith))
  have hq0 : 0 ≤ (q : ℝ) := r₁.coe_nonneg.trans ((le_max_left _ _).trans hq1.le)
  set qN : ℝ≥0 := (q : ℝ).toNNReal with hqN
  have hqNq : (qN : ℝ) = q := Real.coe_toNNReal _ hq0
  have hqNb : qN < b := by rw [← NNReal.coe_lt_coe, hqNq]; exact hq2
  have hwin : ∀ t : ℝ≥0, qN ≤ t → t ≤ b → r₁ ≤ t ∧ (∀ i, vL i t - w t ≠ 0) ∧
      ∀ j, xR k < xR j → vR j t - w t ≠ 0 := by
    intro t ht1 ht2
    have ht1' : (q : ℝ) ≤ t := by rw [← hqNq]; exact NNReal.coe_le_coe.2 ht1
    have hd : dist t b < ε := by
      rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 ht2))]
      linarith [le_max_right (r₁ : ℝ) ((b : ℝ) - ε / 2)]
    refine ⟨?_, (hεP hd).1, (hεP hd).2⟩
    rw [← NNReal.coe_le_coe]
    linarith [le_max_left (r₁ : ℝ) ((b : ℝ) - ε / 2)]
  -- (8) the drift: the merged group cancels
  set S := ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i with hS
  set F : ℝ → ℝ := fun s => (∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
    ∑ j ∈ univ.filter (fun j => xR k < xR j), -ρR j / (w s.toNNReal - vR j s.toNNReal) with hF
  have hdrift : ∀ s : ℝ, qN ≤ s.toNNReal → s.toNNReal < b →
      (∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (refWeightR k none S j - ρR j) / (w s.toNNReal - vR j s.toNNReal) = F s := by
    intro s hs1 hs2
    have hm : ∀ j, xR j ≤ xR k → vR j s.toNNReal = vR k s.toNNReal := fun j hj =>
      hmerge j hj _ (hr₁0.le.trans (hwin _ hs1 hs2.le).1) (hs2.le.trans hbs₁)
    simp only [hF]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => xR j ≤ xR k)]
    have h1 : ∑ j ∈ univ.filter (fun j => xR j ≤ xR k),
        (refWeightR k none S j - ρR j) / (w s.toNNReal - vR j s.toNNReal) = 0 := by
      rw [Finset.sum_congr rfl fun j hj => by rw [hm j (Finset.mem_filter.1 hj).2], ← Finset.sum_div,
        Finset.sum_sub_distrib]
      have href : ∑ j ∈ univ.filter (fun j => xR j ≤ xR k), refWeightR k none S j = S := by
        simp only [refWeightR, reduceCtorEq, ite_false, sub_zero]
        rw [Finset.sum_ite_eq']
        simp
      rw [href, ← hS, sub_self, zero_div]
    have h2 : univ.filter (fun j => ¬ xR j ≤ xR k) = univ.filter (fun j => xR k < xR j) :=
      Finset.filter_congr fun j _ => not_le
    rw [h1, zero_add, h2]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≠ k := fun he => by rw [he] at hj; exact lt_irrefl _ (Finset.mem_filter.1 hj).2
    simp [refWeightR, hjk]
  -- (9) `F` is bounded on `[q, b]`
  have hmaps : ∀ s ∈ Icc (q : ℝ) b, qN ≤ s.toNNReal ∧ s.toNNReal ≤ b := fun s hs => by
    have hs0 : 0 ≤ s := hq0.trans hs.1
    refine ⟨?_, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
    rw [← NNReal.coe_le_coe, hqNq, Real.coe_toNNReal _ hs0]
    exact hs.1
  have hcont : ∀ g : ℝ≥0 → ℝ, ContinuousOn g {t | (t : ℝ≥0∞) < ζ} →
      ContinuousOn (fun s : ℝ => g s.toNNReal) (Icc (q : ℝ) b) := fun g hg =>
    hg.comp continuous_real_toNNReal.continuousOn fun s hs => hζ _ ((hmaps s hs).2.trans hbs₁)
  have hFc : ContinuousOn F (Icc (q : ℝ) b) := by
    refine (continuousOn_finsetSum _ fun i _ => ?_).add (continuousOn_finsetSum _ fun j hj => ?_)
    · refine continuousOn_const.div ((hcont _ hwc).sub (hcont _ (h.continuousOn_vL i))) fun s hs h0 => ?_
      exact (hwin _ (hmaps s hs).1 (hmaps s hs).2).2.1 i (by linarith)
    · refine continuousOn_const.div ((hcont _ hwc).sub (hcont _ (h.continuousOn_vR j))) fun s hs h0 => ?_
      exact (hwin _ (hmaps s hs).1 (hmaps s hs).2).2.2 j (Finset.mem_filter.1 hj).2 (by linarith)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  -- (10) the comparison picture
  refine ⟨q, b, hqNb, hbζ.le, fun t ht1 ht2 => ⟨fun i _ he => ?_, fun j _ he => ?_⟩,
    ⟨M ^ 2 * b, fun t ht1 ht2 => ?_⟩, ?_⟩
  · exact (hwin t ht1 ht2.le).2.1 i (by rw [he, sub_self])
  · by_cases hj : xR j ≤ xR k
    · have hlt := hposk t (hwin t ht1 ht2.le).1 ht2
      rw [← hmerge j hj t (hr₁0.le.trans (hwin t ht1 ht2.le).1) (ht2.le.trans hbs₁)] at hlt
      exact hlt.ne he
    · exact (hwin t ht1 ht2.le).2.2 j (not_le.1 hj) (by rw [he, sub_self])
  · have hqt : (q : ℝ) ≤ t := by rw [← hqNq]; exact NNReal.coe_le_coe.2 ht1
    rw [hqNq]
    have heq : ∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (refWeightR k none S j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2 =
        ∫ s in (q : ℝ)..t, F s ^ 2 := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hqt] at hs
      have hs0 : 0 ≤ s := hq0.trans hs.1
      have h1 : qN ≤ s.toNNReal := by
        rw [← NNReal.coe_le_coe, hqNq, Real.coe_toNNReal _ hs0]; exact hs.1
      have h2 : s.toNNReal < b := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.2.trans_lt (NNReal.coe_lt_coe.2 ht2)
      rw [hdrift s h1 h2]
    rw [heq]
    have hb' : ∀ s ∈ Set.uIoc (q : ℝ) t, ‖F s ^ 2‖ ≤ M ^ 2 := fun s hs => by
      rw [uIoc_of_le hqt] at hs
      have hsI : s ∈ Icc (q : ℝ) b := ⟨hs.1.le, hs.2.trans (NNReal.coe_le_coe.2 ht2.le)⟩
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hM s hsI) 2
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hb'
    have htb : |(t : ℝ) - q| ≤ b := by
      rw [abs_of_nonneg (sub_nonneg.2 hqt)]
      linarith [NNReal.coe_lt_coe.2 ht2]
    calc _ ≤ ‖∫ s in (q : ℝ)..t, F s ^ 2‖ := Real.le_norm_self _
      _ ≤ M ^ 2 * |(t : ℝ) - q| := hn
      _ ≤ M ^ 2 * b := mul_le_mul_of_nonneg_left htb (sq_nonneg M)
  · have hk' : Tendsto (fun t => vR k t - w t) (𝓝 b) (𝓝 (vR k b - w b)) :=
      ((h.continuousOn_vR k).continuousAt (hopen.mem_nhds hbζ)).tendsto.sub
        (hwc.continuousAt (hopen.mem_nhds hbζ)).tendsto
    rw [hbk, sub_self] at hk'
    exact hk'.mono_left nhdsWithin_le_nhds

end Merged

end Sec5.GB7aAbove4

end InteractingSLE
