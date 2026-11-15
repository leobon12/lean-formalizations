/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11ChartBdry
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# Lemma GB11's local growth from Loewner representations on compact intervals

Packet PROVE-T14-GW4T5, item (1b), Loewner-theoretic part. `GB11Conn.GB11RelLocalGrowthStatement` (one driving
function `U`, `U 0 = 0`, continuous on every `[0, T]`, `T < σ − τ`, with uniformly small increments
`g_{B s}(B t \ B s) ⊆ B̄(U s, ε)` of the relative hulls `B u = Φ(K'_{τ+u} ∩ R⁻¹(C))`) is reduced to the named input
**`GB11RelLoewnerStatement`**: on every compact `[0, T]`, `T < σ − τ`, the relative hulls are the hulls of a Loewner
chain with continuous driver `W`, `W 0 = 0`, after a continuous strictly increasing time change `σ`, `σ 0 = 0` (the
conclusion of Yuan's continuous-own-future criterion, `YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture`).

## The argument

* **Loewner increments** (`norm_mapOut_sub_le`): by the domain Markov property (`fwdHull_add_diff`) and the hull radius
  bound (`fwdHull_subset_closedBall`), `|g_{K_a}(z) − W(a)| ≤ sup_{[0,s]} |W(a + ·) − W(a)| + 3√s` on `K_{a+s} \ K_a`.
* **Uniform local growth of a representation** (`localGrowth_of_loewner`): uniform continuity of `σ` on `[0, T]` and
  of `W` on `[0, σ(T)]`.
* **One driver for all `T`**: the centre `W(σ(s))` is intrinsic — it is the only point `x` such that, for every
  `ε > 0`, all short nonempty increments `g_{B s}(B t \ B s)` lie in `B̄(x, ε)` (`IsGrowthCentre`,
  `eq_of_isGrowthCentre`). So `U s` is defined as that centre, and on every `[0, T]` it equals `W ∘ σ` for a
  representation on a larger `[0, T']`.

## Main results

* `norm_mapOut_sub_le`, `localGrowth_of_loewner`, `eq_of_isGrowthCentre`;
* `GB11RelLoewnerStatement` (named input);
* **`gb11RelLocalGrowthStatement_of_loewner`**, `gb11RelParamStatement_of_loewner`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE

namespace Theorem14

namespace GB11Chart

open GW4Traverse GW4Reg GB11Conn ConformalImage

/-! ### Loewner increments -/

/-- **Loewner increments are small**: on `K_{a+s} \ K_a`, `|g_{K_a}(z) − W(a)| ≤ M + 3√s` when
`|W(a + r) − W(a)| ≤ M` on `[0, s]`. -/
theorem norm_mapOut_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {a s M : ℝ} (ha : 0 ≤ a)
    (hs : 0 < s) (hM : ∀ r ∈ Icc (0 : ℝ) s, |W (a + r) - W a| ≤ M) {z : ℂ}
    (hz : z ∈ fwdHull W (a + s) \ fwdHull W a) :
    ‖ConformalImage.mapOut (fwdHull W a) z - W a‖ ≤ M + 3 * Real.sqrt s := by
  rw [QuantumZipper.fwdHull_add_diff hW ha hs.le] at hz
  obtain ⟨hzK, hzs⟩ := hz
  have hb := QuantumZipper.CaraR.fwdHull_subset_closedBall (A := fun r => W (a + r) - W a)
    ((hW.comp (continuous_const.add continuous_id)).sub continuous_const) hs hM hzs
  have heq : ConformalImage.mapOut (fwdHull W a) z = QuantumZipper.fwdMap W a z + W a :=
    IsMapOut.eqOn (isHPHull_fwdHull hW ha) (ConformalImage.isMapOut_mapOut (isHPHull_fwdHull hW ha))
      (isMapOut_fwdMap hW hW0 ha) hzK
  rw [heq, add_sub_cancel_right]
  simpa [mem_closedBall, dist_zero_right] using hb

/-- **Uniform local growth of a Loewner representation**: if `B u = K_{σ(u)}` on `[0, T]` for a continuous driver
`W` (`W 0 = 0`) and a continuous strictly increasing `σ` with `σ 0 = 0`, then the increments `g_{B s}(B t \ B s)` lie,
uniformly in `s`, in small closed balls around `W(σ(s))`. -/
theorem localGrowth_of_loewner {B : ℝ → Set ℂ} {W σ : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hσ0 : σ 0 = 0) (hσm : StrictMonoOn σ (Icc 0 T)) (hσc : ContinuousOn σ (Icc 0 T))
    (hB : ∀ u ∈ Icc (0 : ℝ) T, fwdHull W (σ u) = B u) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → t - s ≤ δ →
      ConformalImage.mapOut (B s) '' (B t \ B s) ⊆ closedBall (W (σ s) : ℂ) ε := by
  intro ε hε
  have hσnn : ∀ u ∈ Icc (0 : ℝ) T, 0 ≤ σ u := fun u hu => by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h, hσ0]
    · exact hσ0 ▸ (hσm ⟨le_rfl, h.le.trans hu.2⟩ hu h).le
  have hσle : ∀ u ∈ Icc (0 : ℝ) T, σ u ≤ σ T := fun u hu =>
    hσm.monotoneOn hu ⟨hu.1.trans hu.2, le_rfl⟩ hu.2
  -- uniform continuity of `W` on `[0, σ T]` and of `σ` on `[0, T]`
  obtain ⟨δ₁, hδ₁, hW'⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := σ T + 1)).uniformContinuousOn_of_continuous hW.continuousOn) (ε / 2)
    (half_pos hε)
  set δ₂ : ℝ := min (δ₁ / 2) ((ε / 6) ^ 2) with hδ₂
  have hδ₂pos : 0 < δ₂ := lt_min (half_pos hδ₁) (by positivity)
  obtain ⟨δ, hδ, hσ'⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous hσc) δ₂ hδ₂pos
  refine ⟨δ / 2, half_pos hδ, fun s hs t ht hst hts => ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hs0 := hσnn s hs
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact absurd hz.1 hz.2
  have hσst : σ s < σ t := hσm hs ht hlt
  set d := σ t - σ s with hd
  have hdpos : 0 < d := sub_pos.2 hσst
  have hdδ : d < δ₂ := by
    have := hσ' t ht s hs (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq, abs_of_nonneg (by linarith)] at this
    exact this
  have hz' : z ∈ fwdHull W (σ s + d) \ fwdHull W (σ s) := by
    rw [hd, add_sub_cancel, hB t ht, hB s hs]; exact hz
  have hM : ∀ r ∈ Icc (0 : ℝ) d, |W (σ s + r) - W (σ s)| ≤ ε / 2 := by
    intro r hr
    have h1 : σ s + r ∈ Icc (0 : ℝ) (σ T + 1) :=
      ⟨by linarith [hr.1], by linarith [hr.2, hσle t ht]⟩
    have h2 : σ s ∈ Icc (0 : ℝ) (σ T + 1) := ⟨hs0, by linarith [hσle s hs]⟩
    have h3 := hW' _ h1 _ h2 (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hr.1]
      linarith [hr.2, min_le_left (δ₁ / 2) ((ε / 6) ^ 2)])
    rw [Real.dist_eq] at h3
    exact h3.le
  have hb := norm_mapOut_sub_le hW hW0 hs0 hdpos hM hz'
  have hsq : 3 * Real.sqrt d ≤ ε / 2 := by
    have h1 : Real.sqrt d ≤ Real.sqrt ((ε / 6) ^ 2) :=
      Real.sqrt_le_sqrt (le_of_lt (lt_of_lt_of_le hdδ (min_le_right _ _)))
    rw [Real.sqrt_sq (by positivity)] at h1
    linarith
  rw [← hB s hs, mem_closedBall, dist_eq_norm]
  linarith

/-! ### One driver for all horizons -/

/-- `x` is a **growth centre** of the family `B` at `s`: for every `ε > 0`, all short increments after `s` are nonempty
and mapped out into `B̄(x, ε)`. -/
def IsGrowthCentre (B : ℝ → Set ℂ) (s x : ℝ) : Prop :=
  ∀ ε > 0, ∃ t > s, ∀ t' ∈ Ioc s t, (B t' \ B s).Nonempty ∧
    ConformalImage.mapOut (B s) '' (B t' \ B s) ⊆ closedBall (x : ℂ) ε

/-- **A growth centre is unique.** -/
theorem eq_of_isGrowthCentre {B : ℝ → Set ℂ} {s x x' : ℝ} (h : IsGrowthCentre B s x)
    (h' : IsGrowthCentre B s x') : x = x' := by
  by_contra hne
  have hpos : 0 < |x - x'| := abs_pos.2 (sub_ne_zero.2 hne)
  set ε := |x - x'| / 3 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨t₁, ht₁, h₁⟩ := h ε hεpos
  obtain ⟨t₂, ht₂, h₂⟩ := h' ε hεpos
  have ht : min t₁ t₂ ∈ Ioc s t₁ := ⟨lt_min ht₁ ht₂, min_le_left _ _⟩
  have ht' : min t₁ t₂ ∈ Ioc s t₂ := ⟨lt_min ht₁ ht₂, min_le_right _ _⟩
  obtain ⟨⟨z, hz⟩, hb₁⟩ := h₁ _ ht
  have hb₂ := (h₂ _ ht').2 ⟨z, hz, rfl⟩
  have hb₁' := hb₁ ⟨z, hz, rfl⟩
  rw [mem_closedBall, dist_eq_norm] at hb₁' hb₂
  set m := ConformalImage.mapOut (B s) z
  have hle : ‖((x : ℂ) - x')‖ ≤ 2 * ε := by
    calc ‖(x : ℂ) - x'‖ = ‖(m - x') - (m - x)‖ := by ring_nf
      _ ≤ ‖m - x'‖ + ‖m - x‖ := norm_sub_le _ _
      _ ≤ ε + ε := add_le_add hb₂ hb₁'
      _ = 2 * ε := by ring
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hle
  linarith

/-- The driver value `W(σ(s))` of a Loewner representation on `[0, T]` is a growth centre at every `s < T`. -/
theorem isGrowthCentre_of_loewner {B : ℝ → Set ℂ} {W σ : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hσ0 : σ 0 = 0) (hσm : StrictMonoOn σ (Icc 0 T)) (hσc : ContinuousOn σ (Icc 0 T))
    (hB : ∀ u ∈ Icc (0 : ℝ) T, fwdHull W (σ u) = B u) {s : ℝ} (hs : s ∈ Ico 0 T) :
    IsGrowthCentre B s (W (σ s)) := by
  intro ε hε
  obtain ⟨δ, hδ, hLG⟩ := localGrowth_of_loewner hW hW0 hσ0 hσm hσc hB ε hε
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.le⟩
  refine ⟨min (s + δ) T, lt_min (by linarith) hs.2, fun t' ht' => ?_⟩
  have ht'T : t' ∈ Icc 0 T := ⟨hs.1.trans ht'.1.le, ht'.2.trans (min_le_right _ _)⟩
  refine ⟨?_, hLG s hsT t' ht'T ht'.1.le (by linarith [ht'.2, min_le_left (s + δ) T])⟩
  rw [← hB t' ht'T, ← hB s hsT]
  have hσs0 : 0 ≤ σ s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hσ0]
    · exact hσ0 ▸ (hσm ⟨le_rfl, hs.1.trans hsT.2⟩ hsT h).le
  obtain ⟨z, hz1, hz2⟩ := exists_of_ssubset (QuantumZipper.RS.fwdHull_ssubset hW hW0 hσs0 (hσm hsT ht'T ht'.1))
  exact ⟨z, hz1, hz2⟩

/-- Inside a horizon `[0, L)` every `T` has room to the right. -/
theorem exists_gt_mem_horizon {L : ℝ≥0∞} {T : ℝ} (hT : T ∈ horizon L) : ∃ T' ∈ horizon L, T < T' := by
  by_cases hL : L = ⊤
  · exact ⟨T + 1, ⟨by linarith [hT.1], by rw [hL]; exact ENNReal.ofReal_lt_top⟩, by linarith⟩
  · have hlt : T < L.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hT.1 hL).1 hT.2
    refine ⟨(T + L.toReal) / 2, ⟨by linarith [hT.1], ?_⟩, by linarith⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hT.1]) hL).2 (by linarith)

/-! ### The reduction -/

/-- **Named input: the relative hulls are Loewner hulls on every compact time interval** (the conclusion of Yuan's
continuous-own-future criterion, `YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture`, for the relative
trace; source: GB11, "relative continuity by the continuous-trace criterion of Aux. lemma 41 / Proposition 6.12").
Hypotheses of `GB11Conn.GB11RelLocalGrowthStatement`; for every `T < σ − τ` there are a continuous driver `W`,
`W 0 = 0`, and a continuous strictly increasing `σ` on `[0, T]`, `σ 0 = 0`, with `K^W_{σ(u)} = B u` on `[0, T]`. -/
def GB11RelLoewnerStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    ∀ T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂), ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 T) ∧ ContinuousOn σ (Icc 0 T) ∧
        ∀ u ∈ Icc (0 : ℝ) T, fwdHull W (σ u) = relHull W' c C (entryTime γ αR s₂) u

/-- **`GB11RelLocalGrowthStatement` from Loewner representations on compact intervals** (conditional helper): the
single driver is the growth centre `U s` (`IsGrowthCentre`), equal to `W(σ(s))` for every representation on a larger
interval. -/
theorem gb11RelLocalGrowthStatement_of_loewner (h : GB11RelLoewnerStatement) : GB11RelLocalGrowthStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  have hrep := h W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  set L := GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂ with hL
  set B := relHull W' c C (entryTime γ αR s₂) with hBdef
  classical
  set U : ℝ → ℝ := fun s => if hx : ∃ x : ℝ, IsGrowthCentre B s x then hx.choose else 0 with hU
  have hUeq : ∀ T : ℝ, ∀ W σ : ℝ → ℝ, Continuous W → W 0 = 0 → σ 0 = 0 → StrictMonoOn σ (Icc 0 T) →
      ContinuousOn σ (Icc 0 T) → (∀ u ∈ Icc (0 : ℝ) T, fwdHull W (σ u) = B u) →
      ∀ s ∈ Ico (0 : ℝ) T, U s = W (σ s) := by
    intro T W σ hW hW0 hσ0 hσm hσc hBr s hs
    have hcen := isGrowthCentre_of_loewner hW hW0 hσ0 hσm hσc hBr hs
    have hx : ∃ x : ℝ, IsGrowthCentre B s x := ⟨_, hcen⟩
    simp only [hU, hx, ↓reduceDIte]
    exact eq_of_isGrowthCentre hx.choose_spec hcen
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hLpos : 0 < L := tsub_pos_of_lt (entryTime_lt_firstVisit hγ.1 hγc hB hs)
  have h0 : (0 : ℝ) ∈ horizon L := ⟨le_rfl, by rw [ENNReal.ofReal_zero]; exact hLpos⟩
  refine ⟨U, ?_, fun T hT => ?_⟩
  · obtain ⟨T', hT', hlt⟩ := exists_gt_mem_horizon h0
    obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hBr⟩ := hrep T' hT'
    rw [hUeq T' W σ hW hW0 hσ0 hσm hσc hBr 0 ⟨le_rfl, hlt⟩, hσ0, hW0]
  · obtain ⟨T', hT', hlt⟩ := exists_gt_mem_horizon hT
    obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hBr⟩ := hrep T' hT'
    have hEq : EqOn U (fun s => W (σ s)) (Icc 0 T) := fun s hs =>
      hUeq T' W σ hW hW0 hσ0 hσm hσc hBr s ⟨hs.1, hs.2.trans_lt hlt⟩
    refine ⟨(hW.comp_continuousOn (hσc.mono (Icc_subset_Icc_right hlt.le))).congr hEq, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hLG⟩ := localGrowth_of_loewner hW hW0 hσ0 hσm hσc hBr ε hε
    refine ⟨δ, hδ, fun s hs t ht hst hts => ?_⟩
    rw [hEq hs]
    exact hLG s ⟨hs.1, hs.2.trans hlt.le⟩ t ⟨ht.1, ht.2.trans hlt.le⟩ hst hts

/-- **`GB11RelParamStatement` from Loewner representations of the relative hulls** (conditional helper; the boundary
correspondence is proved, `gb11ChartBdryStatement`). -/
theorem gb11RelParamStatement_of_loewner (h : GB11RelLoewnerStatement) : GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_localGrowth (gb11RelLocalGrowthStatement_of_loewner h)

end GB11Chart

end Theorem14

end InteractingSLE
