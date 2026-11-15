/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux85Sides
import InteractingSLE.Spec.Supplement.RetChartAsm

/-!
# Aux. lemma 85 in the retained chart: the untouched zones of a touching pair

Packet PROVE-T15-AUX85 (Aux. lemma 85, supplement p. 300: "The filled real base is an interval. […] Only the two
extremes of the base can join the remaining original real boundary"). In the setting `Aux85.IsTSetting` (two good
paths at a touching ordinary retained pair, retained chart `ψ` with the second tip at `0`), with `a₂ = baseL β`,
`b₁ = baseR α`:

* the real points of the union lie in `[a₂, b₁]` (`realK_mem_Icc`, from W0 through the tail completions);
* the **untouched** real points (off the union, adherent to the domain) are exactly those of the two outer zones
  `(−∞, a₂)` and `(b₁, ∞)` (`mem_closure_of_zone`, `zone_of_untouched`; the union is connected, so a real point
  strictly inside its base that is off it is trapped);
* each untouched point has exactly one chart point `T(x)` (`chartPt_zone`), the chart points are in the same order
  as the points (`T_lt_T`), and they are left (resp. right) of every chart point of the union
  (`T_lt_of_mem`, `lt_T_of_mem`; `Sec7.Lemma76G.lt_of_inv_mem` with the connected union);
* `L₂ = sup T(a₂⁻)` and `R₁ = inf T(b₁⁺)` of the touching zone data are the chart points of `a₂` and `b₁`
  (`ψ_L₂`, `ψ_R₁`), every real chart point in `[L₂, R₁]` is mapped into the union (`mem_K_of_mem_Icc`), and the chart
  points left of `L₂` (right of `R₁`) are those of the left (right) zone (`zone₀_of_lt`, `zone₂_of_gt`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace Aux85

open HalfPlaneSep Restart Supp7 Sec7.Lemma76G RetChart

namespace IsTSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsTSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

/-! ### The real base -/

/-- **The real points of the union lie in `[baseL β, baseR α]`.** -/
theorem realK_mem_Icc {z : ℂ} (hz : z ∈ prefixSet α a β b) (hz0 : z.im = 0) :
    baseL β b ≤ z.re ∧ z.re ≤ baseR α a := by
  rcases hz with h | h
  · exact ⟨hs.baseL_le_re h hz0, (re_mem_Icc_base hs.hp₁ hs.ha h hz0).2⟩
  · exact ⟨(re_mem_Icc_base hs.hp₂ hs.hb h hz0).1, hs.re_le_baseR h hz0⟩

theorem baseL_le_baseR : baseL β b ≤ baseR α a :=
  (baseL_le_seed hs.hp₂ hs.hb).trans (hs.hx.trans (seed_le_baseR hs.hp₁ hs.ha))

theorem baseL_mem_K : ((baseL β b : ℝ) : ℂ) ∈ prefixSet α a β b := Or.inr (baseL_mem hs.hp₂ hs.hb)

theorem baseR_mem_K : ((baseR α a : ℝ) : ℂ) ∈ prefixSet α a β b := Or.inl (baseR_mem hs.hp₁ hs.ha)

theorem notMem_K_of_zone {x : ℝ} (hx : x < baseL β b ∨ baseR α a < x) :
    ((x : ℝ) : ℂ) ∉ prefixSet α a β b := fun h => by
  have := hs.realK_mem_Icc h (by simp)
  simp only [ofReal_re] at this
  rcases hx with hx | hx <;> linarith [this.1, this.2]

omit hs in
theorem ofReal_notMem_HD (x : ℝ) : ((x : ℝ) : ℂ) ∉ H \ fillH (prefixSet α a β b) := fun h =>
  (lt_irrefl (0 : ℝ)) (by simpa using (show (0 : ℝ) < ((x : ℝ) : ℂ).im from h.1))

/-- **The outer zones are adherent to the domain.** -/
theorem mem_closure_of_zone {x : ℝ} (hx : x < baseL β b ∨ baseR α a < x) :
    ((x : ℝ) : ℂ) ∈ closure (activeDomain α a β b) := by
  obtain ⟨ρ, hρ, -, hdis⟩ : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (prefixSet α a β b) ∧
      Disjoint (ball (x : ℂ) ρ) (fillH (prefixSet α a β b)) := by
    rcases hx with hx | hx
    · exact Restart.exists_ball_disjoint_of_lt hs.isCompact_K hx fun z hz hz0 => (hs.realK_mem_Icc hz hz0).1
    · exact Restart.exists_ball_disjoint_of_gt hs.isCompact_K hx fun z hz hz0 => (hs.realK_mem_Icc hz hz0).2
  rw [hs.D_eq]
  refine Metric.mem_closure_iff.2 fun δ hδ => ?_
  set t : ℝ := min ρ δ / 2 with ht
  have ht0 : 0 < t := half_pos (lt_min hρ hδ)
  have hzb : dist ((x : ℂ) + (t : ℂ) * I) (x : ℂ) = t := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht0]
  refine ⟨(x : ℂ) + (t : ℂ) * I, ⟨show 0 < ((x : ℂ) + (t : ℂ) * I).im by simp [ht0], fun h => ?_⟩,
    by rw [dist_comm, hzb]; linarith [min_le_right ρ δ]⟩
  exact Set.disjoint_left.1 hdis (mem_ball.2 (by rw [hzb]; linarith [min_le_left ρ δ])) h

/-- **An untouched real point lies in an outer zone** (inside the base it is trapped by the connected union). -/
theorem zone_of_untouched {x : ℝ} (hK : ((x : ℝ) : ℂ) ∉ prefixSet α a β b)
    (hcl : ((x : ℝ) : ℂ) ∈ closure (activeDomain α a β b)) : x < baseL β b ∨ baseR α a < x := by
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have h1' : baseL β b < x := lt_of_le_of_ne h1 fun h => hK (h ▸ hs.baseL_mem_K)
  have h2' : x < baseR α a := lt_of_le_of_ne h2 fun h => hK (h ▸ hs.baseR_mem_K)
  obtain ⟨ε, hε, hdis⟩ :=
    Sec7.isTrappedAt_of_isPreconnected hs.isCompact_K hs.pcK hs.imK hs.baseL_mem_K hs.baseR_mem_K h1' h2' hK
  rw [hs.D_eq] at hcl
  obtain ⟨z, hzD, hz⟩ := Metric.mem_closure_iff.1 hcl ε hε
  exact Set.disjoint_left.1 hdis (mem_ball.2 (by rwa [dist_comm])) hzD

/-- The chart point of a point of an outer zone. -/
theorem chartPt_zone {x : ℝ} (hx : x < baseL β b ∨ baseR α a < x) :
    Tendsto φ (𝓝[activeDomain α a β b] (x : ℂ)) (𝓝 ((chartPt φ (activeDomain α a β b) x : ℝ) : ℂ)) ∧
      ψ (chartPt φ (activeDomain α a β b) x) = x ∧
      ∀ w ∈ Hbar, ψ w = x → w = ((chartPt φ (activeDomain α a β b) x : ℝ) : ℂ) :=
  hs.chartPt_spec (hs.mem_closure_of_zone hx) (fun h => ofReal_notMem_HD x (hs.D_eq ▸ h))
    (isChartRegularPoint_of_notMem hs.hc₁ hs.hc₂ hs.h0₁ hs.h0₂ (hs.notMem_K_of_zone hx))

/-- **The untouched case of a real chart point**: its image `x` is in an outer zone and `T(x) = w`. -/
theorem untouched_cases {w : ℝ} (h : (ψ w).im = 0 ∧ ψ w ∉ prefixSet α a β b) :
    ψ w = (((ψ w).re : ℝ) : ℂ) ∧ ((ψ w).re < baseL β b ∨ baseR α a < (ψ w).re) ∧
      chartPt φ (activeDomain α a β b) (((ψ w).re : ℝ) : ℂ) = w := by
  have he : ψ w = (((ψ w).re : ℝ) : ℂ) := (Restart.ofReal_re_eq h.1).symm
  have hz : (ψ w).re < baseL β b ∨ baseR α a < (ψ w).re :=
    hs.zone_of_untouched (by rw [← he]; exact h.2) (by rw [← he]; exact hs.inv_mem_closure w)
  refine ⟨he, hz, ?_⟩
  have := (hs.chartPt_zone hz).2.2 w (ofReal_mem_Hbar w) he
  exact (ofReal_injective this).symm

/-! ### The order of the zone chart points -/

omit hs in
theorem singleton_D (x : ℝ) : ∀ z ∈ ({((x : ℝ) : ℂ)} : Set ℂ), z ∉ H \ fillH (prefixSet α a β b) := by
  rintro _ rfl; exact ofReal_notMem_HD x

omit hs in
theorem singleton_im (x : ℝ) : ∀ z ∈ ({((x : ℝ) : ℂ)} : Set ℂ), 0 ≤ z.im := by
  rintro _ rfl; simp

omit hs in
theorem K_D : ∀ z ∈ prefixSet α a β b, z ∉ H \ fillH (prefixSet α a β b) := fun _ hz => notMem_D_of_mem_K hz

/-- **Chart points of the left zone precede those of the union.** -/
theorem T_lt_of_mem {x : ℝ} (hx : x < baseL β b) {w : ℝ} (hw : ψ w ∈ prefixSet α a β b) :
    chartPt φ (activeDomain α a β b) x < w := by
  obtain ⟨M, hM⟩ := hs.disp
  exact lt_of_inv_mem' hs.isCompact_K hs.ψc hs.bij hs.real hM isCompact_singleton isPreconnected_singleton
    (singleton_im x) (singleton_D x) hs.isCompact_K hs.pcK hs.imK K_D
    (Set.disjoint_singleton_left.2 (hs.notMem_K_of_zone (Or.inl hx))) (mem_singleton _)
    (fun z hz hz0 => hx.trans_le (hs.realK_mem_Icc hz hz0).1) (Or.inr hs.seed₂)
    (by rw [(hs.chartPt_zone (Or.inl hx)).2.1]; exact mem_singleton _) hw

/-- **Chart points of the right zone follow those of the union.** -/
theorem lt_T_of_mem {x : ℝ} (hx : baseR α a < x) {w : ℝ} (hw : ψ w ∈ prefixSet α a β b) :
    w < chartPt φ (activeDomain α a β b) x := by
  obtain ⟨M, hM⟩ := hs.disp
  exact lt_of_inv_mem hs.isCompact_K hs.ψc hs.bij hs.real hM isCompact_singleton isPreconnected_singleton
    (singleton_im x) (singleton_D x) hs.isCompact_K hs.pcK hs.imK K_D
    (Set.disjoint_singleton_left.2 (hs.notMem_K_of_zone (Or.inr hx))) (mem_singleton _)
    (fun z hz hz0 => lt_of_le_of_lt (hs.realK_mem_Icc hz hz0).2 hx) (Or.inr hs.seed₂)
    (by rw [(hs.chartPt_zone (Or.inr hx)).2.1]; exact mem_singleton _) hw

/-- **Chart points of zone points are in the same order as the points.** -/
theorem T_lt_T {x x' : ℝ} (hx : x < baseL β b ∨ baseR α a < x) (hx' : x' < baseL β b ∨ baseR α a < x')
    (hxx : x < x') : chartPt φ (activeDomain α a β b) x < chartPt φ (activeDomain α a β b) x' := by
  obtain ⟨M, hM⟩ := hs.disp
  exact lt_of_inv_mem hs.isCompact_K hs.ψc hs.bij hs.real hM isCompact_singleton isPreconnected_singleton
    (singleton_im x') (singleton_D x') isCompact_singleton isPreconnected_singleton (singleton_im x)
    (singleton_D x)
    (Set.disjoint_singleton.2 fun h => (ne_of_lt hxx) (ofReal_injective h).symm) (mem_singleton _)
    (fun _ hz _ => by rw [mem_singleton_iff.1 hz]; simpa using hxx) (mem_singleton _)
    (by rw [(hs.chartPt_zone hx').2.1]; exact mem_singleton _)
    (by rw [(hs.chartPt_zone hx).2.1]; exact mem_singleton _)

theorem T_lt_zero {x : ℝ} (hx : x < baseL β b) : chartPt φ (activeDomain α a β b) x < 0 :=
  hs.T_lt_of_mem hx (by rw [ofReal_zero, hs.ψ0]; exact Or.inr (tip₂_mem (β := β) (b := b)))

theorem M₁_lt_T {x : ℝ} (hx : baseR α a < x) :
    chartPt φ (activeDomain α a β b) (α a) < chartPt φ (activeDomain α a β b) x :=
  hs.lt_T_of_mem hx (by rw [hs.chartPt_tip₁.2.1]; exact Or.inl (tip₁_mem (α := α) (a := a)))

/-! ### The extreme chart points `L₂` and `R₁` -/

theorem bddAbove_L₂ :
    BddAbove (range fun n : ℕ => chartPt φ (activeDomain α a β b) ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact (hs.T_lt_zero (sub_lt_self _ (one_div_succ_pos n))).le⟩

theorem bddBelow_R₁ :
    BddBelow (range fun n : ℕ => chartPt φ (activeDomain α a β b) ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) :=
  ⟨chartPt φ (activeDomain α a β b) (α a), by
    rintro _ ⟨n, rfl⟩; exact (hs.M₁_lt_T (lt_add_of_pos_right _ (one_div_succ_pos n))).le⟩

omit hs in
theorem L₂_eq : (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ =
    ⨆ n : ℕ, chartPt φ (activeDomain α a β b) ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := rfl

omit hs in
theorem R₁_eq : (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ =
    ⨅ n : ℕ, chartPt φ (activeDomain α a β b) ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := rfl

theorem T_lt_L₂ {x : ℝ} (hx : x < baseL β b) :
    chartPt φ (activeDomain α a β b) x < (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
  rw [L₂_eq]
  refine lt_of_lt_of_le (hs.T_lt_T (Or.inl hx) (Or.inl (sub_lt_self _ (one_div_succ_pos n))) (by linarith))
    (le_ciSup hs.bddAbove_L₂ n)

theorem lt_R₁_T {x : ℝ} (hx : baseR α a < x) :
    (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ < chartPt φ (activeDomain α a β b) x := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
  rw [R₁_eq]
  refine lt_of_le_of_lt (ciInf_le hs.bddBelow_R₁ n)
    (hs.T_lt_T (Or.inr (lt_add_of_pos_right _ (one_div_succ_pos n))) (Or.inr hx) (by linarith))

theorem L₂_le_zero : (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ ≤ 0 := by
  rw [L₂_eq]
  exact ciSup_le fun n => (hs.T_lt_zero (sub_lt_self _ (one_div_succ_pos n))).le

theorem M₁_le_R₁ :
    chartPt φ (activeDomain α a β b) (α a) ≤ (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ := by
  rw [R₁_eq]
  exact le_ciInf fun n => (hs.M₁_lt_T (lt_add_of_pos_right _ (one_div_succ_pos n))).le

theorem L₂_le_of_mem {w : ℝ} (hw : ψ w ∈ prefixSet α a β b) :
    (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ ≤ w := by
  rw [L₂_eq]
  exact ciSup_le fun n => (hs.T_lt_of_mem (sub_lt_self _ (one_div_succ_pos n)) hw).le

theorem le_R₁_of_mem {w : ℝ} (hw : ψ w ∈ prefixSet α a β b) :
    w ≤ (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ := by
  rw [R₁_eq]
  exact le_ciInf fun n => (hs.lt_T_of_mem (lt_add_of_pos_right _ (one_div_succ_pos n)) hw).le

theorem L₂_lt_R₁ :
    (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ < (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ :=
  lt_of_le_of_lt hs.L₂_le_zero (hs.zero_lt_M₁.trans_le hs.M₁_le_R₁)

/-- `ψ(L₂)` is the left end of the base. -/
theorem ψ_L₂ : ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ = ((baseL β b : ℝ) : ℂ) := by
  set f : ℕ → ℝ := fun n => chartPt φ (activeDomain α a β b) ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hf
  have hmono : Monotone f := by
    intro n n' hnn'
    rcases hnn'.lt_or_eq with h | h
    · refine (hs.T_lt_T (Or.inl (sub_lt_self _ (one_div_succ_pos n))) (Or.inl (sub_lt_self _ (one_div_succ_pos n')))
        ?_).le
      have : 1 / ((n' : ℝ) + 1) < 1 / ((n : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.add_lt_add_right h 1)
      linarith
    · rw [h]
  have hlim : Tendsto f atTop (𝓝 (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂) := by
    rw [L₂_eq]; exact tendsto_atTop_ciSup hmono hs.bddAbove_L₂
  have hψf : ∀ n, ψ (f n) = ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := fun n =>
    (hs.chartPt_zone (Or.inl (sub_lt_self _ (one_div_succ_pos n)))).2.1
  have h1 : Tendsto (fun n => ψ (f n)) atTop (𝓝 (ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂)) := by
    have hc := hs.ψc _ (ofReal_mem_Hbar (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂)
    refine hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto _).comp hlim,
      Eventually.of_forall fun n => ofReal_mem_Hbar _⟩)
  have h2 : Tendsto (fun n => ψ (f n)) atTop (𝓝 ((baseL β b : ℝ) : ℂ)) := by
    simp_rw [hψf]
    have : Tendsto (fun n : ℕ => (baseL β b - 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (baseL β b)) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (continuous_ofReal.tendsto _).comp this
  exact tendsto_nhds_unique h1 h2

/-- `ψ(R₁)` is the right end of the base. -/
theorem ψ_R₁ : ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ = ((baseR α a : ℝ) : ℂ) := by
  set f : ℕ → ℝ := fun n => chartPt φ (activeDomain α a β b) ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hf
  have hanti : Antitone f := by
    intro n n' hnn'
    rcases hnn'.lt_or_eq with h | h
    · refine (hs.T_lt_T (Or.inr (lt_add_of_pos_right _ (one_div_succ_pos n')))
        (Or.inr (lt_add_of_pos_right _ (one_div_succ_pos n))) ?_).le
      have : 1 / ((n' : ℝ) + 1) < 1 / ((n : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.add_lt_add_right h 1)
      linarith
    · rw [h]
  have hlim : Tendsto f atTop (𝓝 (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁) := by
    rw [R₁_eq]; exact tendsto_atTop_ciInf hanti hs.bddBelow_R₁
  have hψf : ∀ n, ψ (f n) = ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := fun n =>
    (hs.chartPt_zone (Or.inr (lt_add_of_pos_right _ (one_div_succ_pos n)))).2.1
  have h1 : Tendsto (fun n => ψ (f n)) atTop (𝓝 (ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁)) := by
    have hc := hs.ψc _ (ofReal_mem_Hbar (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁)
    refine hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto _).comp hlim,
      Eventually.of_forall fun n => ofReal_mem_Hbar _⟩)
  have h2 : Tendsto (fun n => ψ (f n)) atTop (𝓝 ((baseR α a : ℝ) : ℂ)) := by
    simp_rw [hψf]
    have : Tendsto (fun n : ℕ => (baseR α a + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (baseR α a)) := by
      simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (continuous_ofReal.tendsto _).comp this
  exact tendsto_nhds_unique h1 h2

/-! ### Where a real chart point lands -/

/-- **Between `L₂` and `R₁`, real chart points are mapped into the union.** -/
theorem mem_K_of_mem_Icc {w : ℝ} (h1 : (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ ≤ w)
    (h2 : w ≤ (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁) : ψ w ∈ prefixSet α a β b := by
  rcases hs.inv_cases w with h | h | hu
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨-, hz, hT⟩ := hs.untouched_cases hu
    rcases hz with hz | hz
    · have := hs.T_lt_L₂ hz
      rw [hT] at this
      exact absurd h1 (not_le.2 this)
    · have := hs.lt_R₁_T hz
      rw [hT] at this
      exact absurd h2 (not_le.2 this)

/-- **Left of `L₂` the chart point is that of a point of the left zone.** -/
theorem zone₀_of_lt {w : ℝ} (hw : w < (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂) :
    (ψ w).im = 0 ∧ (ψ w).re < baseL β b ∧ chartPt φ (activeDomain α a β b) (((ψ w).re : ℝ) : ℂ) = w := by
  rcases hs.inv_cases w with h | h | hu
  · exact absurd (hs.L₂_le_of_mem (Or.inl h)) (not_le.2 hw)
  · exact absurd (hs.L₂_le_of_mem (Or.inr h)) (not_le.2 hw)
  · obtain ⟨-, hz, hT⟩ := hs.untouched_cases hu
    rcases hz with hz | hz
    · exact ⟨hu.1, hz, hT⟩
    · have := hs.lt_R₁_T hz
      rw [hT] at this
      linarith [hs.L₂_lt_R₁]

/-- **Right of `R₁` the chart point is that of a point of the right zone.** -/
theorem zone₂_of_gt {w : ℝ} (hw : (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ < w) :
    (ψ w).im = 0 ∧ baseR α a < (ψ w).re ∧ chartPt φ (activeDomain α a β b) (((ψ w).re : ℝ) : ℂ) = w := by
  rcases hs.inv_cases w with h | h | hu
  · exact absurd (hs.le_R₁_of_mem (Or.inl h)) (not_le.2 hw)
  · exact absurd (hs.le_R₁_of_mem (Or.inr h)) (not_le.2 hw)
  · obtain ⟨-, hz, hT⟩ := hs.untouched_cases hu
    rcases hz with hz | hz
    · have := hs.T_lt_L₂ hz
      rw [hT] at this
      linarith [hs.L₂_lt_R₁]
    · exact ⟨hu.1, hz, hT⟩

end IsTSetting

end Aux85

end RLC

end InteractingSLE
