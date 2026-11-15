/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.ThresholdVisit
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.RLCFAvg

/-!
# No visit of a boundary jump before the lifetime: `RLC.JumpVisitStatement`

Packet PROVE-RLC-G, first part. W5's real local frame (supplement p. 535: "For real `p`, G12 excludes an original
jump, since both paths continue"); Lemma G12 (p. 504); the continuation threshold of Definition 2.1. PROVE-RLC-F's
named input `RLC.JumpVisitStatement` (`RLCFAvgDatum.lean`) is proved here, so the RLC-F route to Theorem W5 no longer
needs it.

**Pathwise argument at a mark** (`RLC.vR_eq_w_of_visit_mark`). Let the trace visit the right mark `x_k > 0` at
`t₀ < ζ`, the cumulative weight up to `x_k` being `≤ −2`. For small `δ > 0` take the first real contact `T ≤ t₀` with
`(x_k − δ, x_k + δ)` after an interior rational time (`GB7a.exists_firstContact`), at the point `y'`:

1. `y' ≤ x_k`: a contact right of `x_k` is a visit of the open interval after the mark, excluded at cumulative
   weight `≤ −2` (`RLC.not_visit_right`, PROVE-RLC-E);
2. `T` is close to `t₀`: the prefix up to `t₀ − ε/2` is a compact set missing `x_k` (injectivity of the trace);
3. `v_k(T) − w(T) ≤ x_k − y' < δ` (`RLC.le_max_of_firstContact`): while `y'` is alive, the gap between the force
   coordinate of `x_k` and the real flow of `y'` does not grow (forward comparison, `Aux25.sub_le_max_of_centredEq`),
   and the real flow of `y'` cannot stay bounded below up to `T` — else `y'` would be alive at `T`
   (`GB7a.exists_isForwardSol_of_le`), while the trace reaches it from the hulls (`GB7a.not_isForwardSol_of_tendsto`).

By continuity of `v_k − w` at `t₀`, `v_k(t₀) = w(t₀)`. Then the marks `x_j ≤ x_k` are merged with the driver at `t₀`
(order of the force coordinates) and the marks `x_j > x_k` are not (at a right collision the tip is a real point
`≥ x_j`: `RLC.vR_ne_w_of_lt_tip`), so the threshold condition holds at `t₀ < ζ`, which the lifetime forbids
(`RLC.not_visit_mark_right`; left side by reflection, `RLC.not_visit_mark_left`).

**The flow-line statement** (`RLC.jumpVisitStatement`). For a jump `y ≠ x`, if the outward cumulative weight through
`y` exceeds `κ/2 − 4`, Lemma G12 (`Supp7.g12FlowStatement`, proved) excludes the visit; otherwise it is `≤ −2`
(`κ < 4`), and the visit is excluded by the mark lemma (when `y` is a mark of the flow-line word) or by
`RLC.not_visit_right` / `RLC.not_visit_left` (when `y` lies inside an interval of constant data).

Main results:

* **`RLC.le_max_of_firstContact`** (deterministic, chart level);
* `RLC.vR_ne_w_of_lt_tip`, **`RLC.vR_eq_w_of_visit_mark`**, **`RLC.not_visit_mark_right`**,
  `RLC.not_visit_mark_left` (one path);
* **`RLC.jumpVisitStatement : RLC.JumpVisitStatement`**;
* `RLC.retainedChartRealCompletionAtStatement_of_frames`, **`RLC.w5Statement_of_g2a_g3_g8_param`**: PROVE-RLC-F's
  results without the jump-visit hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace RLC

open GB7a
open QuantumZipper (fwdMap IsForwardSol)
open Aux25 (exists_real_of_isForwardSol pos_of_ne_zero_of_pos sub_le_max_of_centredEq)

/-- **The gap of a right force coordinate at a first real contact.** Let the trace `η` (driver `U`) stay in `ℍ` on
`(p, T)`, be injective on `[0, T]`, and reach the real point `y > 0` at `T`. Let `u` be a solution of the centred real
Loewner equation on every `[0, s]`, `s < T`, continuous from the left at `T`. Then `u(T) ≤ max (u(0) − y) 0`: the real
flow `X` of `y` satisfies `u − X ≤ max (u(0) − y) 0` while `y` is alive (forward comparison), and `X` cannot stay
bounded below up to `T` (else `y` would be alive at `T`, while the trace reaches it from the hulls). -/
theorem le_max_of_firstContact {U : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTraceLT U T η)
    (hU : Continuous U) (hU0 : U 0 = 0) {p : ℝ} (hp : 0 ≤ p) (hpT : p < T)
    (hH : ∀ s ∈ Ioo p T, η s ∈ H) (hinj : InjOn η (Icc 0 T)) {y : ℝ} (hy : 0 < y) (hηT : η T = y)
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) {u : ℝ → ℝ}
    (hu : ∀ s, 0 ≤ s → s < T → ContinuousOn u (Icc 0 s) ∧
      (∀ s₁ ∈ Icc (0 : ℝ) s, ∀ s₂ ∈ Icc (0 : ℝ) s, s₁ ≤ s₂ →
        u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r) ∧
      IntervalIntegrable (fun r => 2 / u r) volume 0 s)
    (huT : Tendsto u (𝓝[<] T) (𝓝 (u T))) : u T ≤ max (u 0 - y) 0 := by
  by_contra hlt
  rw [not_le] at hlt
  set d := max (u 0 - y) 0 with hd
  set c := (u T - d) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hev : ∀ᶠ s in 𝓝[<] T, d + c < u s := huT (lt_mem_nhds (by rw [hc]; linarith))
  obtain ⟨q₁, hq₁, hq₁sub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
  set q := (max q₁ p + T) / 2 with hqdef
  have hmax : max q₁ p < T := max_lt hq₁ hpT
  have hq₁q : q₁ < q := by have := le_max_left q₁ p; rw [hqdef]; linarith
  have hpq : p < q := by have := le_max_right q₁ p; rw [hqdef]; linarith
  have hqT : q < T := by rw [hqdef]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq.le
  have hT0 : 0 ≤ T := hq0.trans hqT.le
  -- the limit point is alive at every `s ∈ [q, T)`
  have halive : ∀ s ∈ Ico q T, ∃ v, IsForwardSol U (y : ℂ) s v := by
    intro s hs
    have hs0 : 0 ≤ s := hq0.trans hs.1
    refine exists_isForwardSol_at_restart hη hU hU0 hs0 hs.2
      (fun r hr => hH r ⟨hpq.trans_le (hs.1.trans hr.1.le), hr.2⟩) ?_ hy.ne' hlim ?_
    · rintro r hr ⟨r', hr', he⟩
      have := hinj ⟨hr'.1, hr'.2.trans hs.2.le⟩ ⟨hs0.trans hr.1.le, hr.2.le⟩ he
      linarith [hr'.2, hr.1]
    · rintro ⟨r', hr', he⟩
      have := hinj ⟨hr'.1, hr'.2.trans hs.2.le⟩ ⟨hT0, le_rfl⟩ (he.trans hηT.symm)
      linarith [hr'.2, hs.2]
  -- the real flow of `y`, read through `fwdMap`
  set f : ℝ → ℝ := fun s => (fwdMap U s (y : ℂ)).re with hfdef
  have hfX : ∀ s ∈ Ico q T, ∃ X : ℝ → ℝ, ContinuousOn X (Icc 0 s) ∧ (∀ r ∈ Icc (0 : ℝ) s, f r = X r) ∧
      (∀ r ∈ Icc (0 : ℝ) s, 0 < X r) ∧ X 0 = y ∧
      (∀ s₁ ∈ Icc (0 : ℝ) s, ∀ s₂ ∈ Icc (0 : ℝ) s, s₁ ≤ s₂ →
        X s₂ - X s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / X r) ∧
      IntervalIntegrable (fun r => 2 / X r) volume 0 s := by
    intro s hs
    obtain ⟨v, hv⟩ := halive s hs
    have hs0 : 0 ≤ s := hq0.trans hs.1
    obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := exists_real_of_isForwardSol hU hs0 hv
    rw [hU0, sub_zero] at hX0
    have hXpos := pos_of_ne_zero_of_pos hXc (fun r hr => (hXv r hr).1) (by rw [hX0]; exact hy)
    refine ⟨X, hXc, fun r hr => ?_, hXpos, hX0, hXeq, hXint⟩
    simp only [hfdef]
    rw [fwdMap_eq_of_isForwardSol hU hv hr, (hXv r hr).2, Complex.ofReal_re]
  -- on `[q, T)` the real flow of `y` stays above `c`
  have hcf : ∀ s ∈ Ico q T, c ≤ f s := by
    intro s hs
    obtain ⟨X, hXc, hfX', hXpos, hX0, hXeq, hXint⟩ := hfX s hs
    have hs0 : 0 ≤ s := hq0.trans hs.1
    obtain ⟨huc, hueq, huint⟩ := hu s hs0 hs.2
    have hnull : volume {r | r ∈ Icc (0 : ℝ) s ∧ X r = 0} = 0 :=
      measure_mono_null (fun r hr => absurd hr.2 (hXpos r hr.1).ne') measure_empty
    have hcmp := sub_le_max_of_centredEq (W := U) (u := X) (X := u) hXc (fun r hr => (hXpos r hr).le)
      hXeq hXint hnull huc hueq huint s ⟨hs0, le_rfl⟩
    rw [hX0] at hcmp
    have hus : d + c < u s := hq₁sub ⟨hq₁q.trans_le hs.1, hs.2⟩
    rw [hfX' s ⟨hs0, le_rfl⟩]
    linarith
  obtain ⟨vq, hvq⟩ := halive q ⟨le_rfl, hqT⟩
  have hu' : ∀ s ∈ Ico q T, ContinuousOn f (Icc q s) ∧
      (∀ s₁ ∈ Icc q s, ∀ s₂ ∈ Icc q s, s₁ ≤ s₂ → f s₂ - f s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / f r) ∧
      IntervalIntegrable (fun r => 2 / f r) volume q s := by
    intro s hs
    obtain ⟨X, hXc, hfX', -, -, hXeq, hXint⟩ := hfX s hs
    have hsub : Icc q s ⊆ Icc 0 s := Icc_subset_Icc_left hq0
    refine ⟨(hXc.mono hsub).congr fun r hr => hfX' r (hsub hr), fun s₁ h₁ s₂ h₂ h₁₂ => ?_, ?_⟩
    · rw [hfX' s₁ (hsub h₁), hfX' s₂ (hsub h₂), hXeq s₁ (hsub h₁) s₂ (hsub h₂) h₁₂]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      have hr' : r ∈ Icc (0 : ℝ) s := uIcc_subset_Icc (hsub h₁) (hsub h₂) hr
      simp only [hfX' r hr']
    · have hXint' : IntervalIntegrable (fun r => 2 / X r) volume q s :=
        hXint.mono_set (by rw [uIcc_of_le hs.1, uIcc_of_le (hq0.trans hs.1)]; exact hsub)
      rw [intervalIntegrable_iff] at hXint' ⊢
      refine hXint'.congr_fun (fun r hr => ?_) measurableSet_uIoc
      rw [uIoc_of_le hs.1] at hr
      simp only [hfX' r ⟨hq0.trans hr.1.le, hr.2⟩]
  have huq : f q ≤ (vq q).re := by
    simp only [hfdef]
    rw [fwdMap_eq_of_isForwardSol hU hvq ⟨hq0, le_rfl⟩]
  have halT := exists_isForwardSol_of_le hU hU0 hy hq0 hqT.le hvq hc0 hu' hcf huq
  refine not_isForwardSol_of_tendsto hU (p := q) hqT hT0 (fun s hs => ?_) hlim halT
  have hs0 : 0 ≤ s := hq0.trans hs.1
  rw [hη.2.2 s hs0 hs.2]
  exact ⟨hH s ⟨hpq.trans_le hs.1, hs.2⟩, Or.inl (subset_closure ⟨s, ⟨hs0, le_rfl⟩, rfl⟩)⟩

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **A right mark beyond a real tip does not collide** (one path): if the tip at `t₀ < ζ` is the real point `y`
and `y < x_j`, then `v_j(t₀) ≠ w(t₀)` (at a right collision the tip is a real point `≥ x_j`,
`IsLoewnerTraceLT.exists_tip_real_of_collision_right`). -/
theorem vR_ne_w_of_lt_tip (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hη : IsGeneratingTrace w ζ η)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {y : ℝ} (he : η t₀ = y) {j : Fin nR} (hj : y < xR j) :
    vR j t₀ ≠ w t₀ := by
  intro hjw
  have hwc := h.continuousOn_w
  obtain ⟨T₂, ht₀T₂e, hT₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
  have ht₀T₂ : (t₀ : ℝ) < T₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht₀T₂e)
  have hT₂0 : (0 : ℝ) < T₂ := t₀.coe_nonneg.trans_lt ht₀T₂
  set U : ℝ → ℝ := frozenDrive w T₂ with hUdef
  have hU : Continuous U :=
    continuous_frozenDrive_of_lt hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hT₂ζ)
  have hUw₂ : ∀ s : ℝ, 0 ≤ s → s < T₂ → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, hs.le⟩
  have hU0 : U 0 = 0 := by rw [hUw₂ 0 le_rfl hT₂0, Real.toNNReal_zero, h.w_zero]
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR₂ : IsLoewnerTraceLT U T₂ ηR := isLoewnerTraceLT_of_agree hη hT₂ζ.le hUw₂
  have hltζ : ∀ t : ℝ≥0, (t : ℝ) < T₂ → (t : ℝ≥0∞) < ζ := fun t ht =>
    (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ht)).trans hT₂ζ
  obtain ⟨hc, hue, hi, hn⟩ := centredPkg hwc (h.continuousOn_vR j) (fun t ht => h.integrable_gapR ht j)
    (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hT₂ζ.le hUw₂ t₀.coe_nonneg ht₀T₂
  have hnn : ∀ s ∈ Icc (0 : ℝ) t₀, 0 ≤ vR j s.toNNReal - w s.toNNReal := fun s hs => by
    refine sub_nonneg.2 (h.w_le_vR (hltζ _ ?_) j)
    rw [Real.coe_toNNReal _ hs.1]
    exact hs.2.trans_lt ht₀T₂
  obtain ⟨x, hx, hx0, -⟩ := hηR₂.exists_tip_real_of_collision_right hU hU0 t₀.coe_nonneg ht₀T₂ hc hnn hue hi
    hn (by simp only [Real.toNNReal_coe, hjw, sub_self])
  have hxT : η t₀ = x := by simpa [hηRdef] using hx
  rw [he] at hxT
  have hxy : y = x := Complex.ofReal_injective hxT
  simp only [Real.toNNReal_zero, h.vR_zero j, h.w_zero, sub_zero] at hx0
  linarith

/-- **A visited right mark collides with the driver at the visit** (one path). Let the trace visit the right mark
`x_k > 0` at `t₀ < ζ`, and let the cumulative weight up to `x_k` be `≤ −2`. Then `v_k(t₀) = w(t₀)`. For small `δ`,
the first real contact with `(x_k − δ, x_k + δ)` before `t₀` is not right of `x_k` (`RLC.not_visit_right`), happens
close to `t₀` (injectivity), and there the gap `v_k − w` is at most `x_k − y' < δ` (`RLC.le_max_of_firstContact`);
continuity of the gap at `t₀` gives `0`. -/
theorem vR_eq_w_of_visit_mark (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) {k : Fin nR} (hk0 : 0 < xR k) {a' : ℝ} (hka : xR k < a')
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i ≤ -2)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (he : η t₀ = xR k) : vR k t₀ = w t₀ := by
  have hwc := h.continuousOn_w
  have ht₀0 : 0 < t₀ := by
    rcases eq_zero_or_pos t₀ with h0 | h0
    · rw [h0, hη.1] at he
      have : xR k = 0 := by exact_mod_cast he.symm
      linarith
    · exact h0
  -- a horizon `T₂ ∈ (t₀, ζ)` and a continuous driver agreeing with `w` up to it
  obtain ⟨T₂, ht₀T₂e, hT₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
  have ht₀T₂ : (t₀ : ℝ) < T₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht₀T₂e)
  have ht₀0' : (0 : ℝ) < t₀ := NNReal.coe_pos.2 ht₀0
  set U : ℝ → ℝ := frozenDrive w T₂ with hUdef
  have hU : Continuous U :=
    continuous_frozenDrive_of_lt hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hT₂ζ)
  have hUw₂ : ∀ s : ℝ, 0 ≤ s → s < T₂ → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, hs.le⟩
  have hU0 : U 0 = 0 := by rw [hUw₂ 0 le_rfl (ht₀0'.trans ht₀T₂), Real.toNNReal_zero, h.w_zero]
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  set û : ℝ → ℝ := fun r => vR k r.toNNReal - w r.toNNReal with hûdef
  have pkg := fun (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T₂) => centredPkg hwc (h.continuousOn_vR k)
    (fun t ht => h.integrable_gapR ht k) (fun t ht => h.vR_eq ht k) (h.volume_collisionR k) hT₂ζ.le hUw₂
    hs0 hsT
  have hûcont : ∀ s : ℝ, 0 < s → s < T₂ → ContinuousAt û s := by
    intro s hs0 hsT
    have hs' : s < (s + T₂) / 2 := by linarith
    exact (pkg ((s + T₂) / 2) (by linarith) (by linarith)).1.continuousAt (Icc_mem_nhds hs0 hs')
  by_contra hne
  have hpos : 0 < û t₀ := by
    have h1 := h.w_le_vR ht₀ k
    simp only [hûdef, Real.toNNReal_coe]
    exact sub_pos.2 (lt_of_le_of_ne h1 (Ne.symm hne))
  set c := û t₀ with hcdef
  obtain ⟨ε, hε, hεc⟩ := Metric.continuousAt_iff.1 (hûcont t₀ ht₀0' ht₀T₂) (c / 2) (half_pos hpos)
  -- the prefix up to `t₁ = t₀ − ε/2` stays a positive distance `r` from the mark
  set t₁ : ℝ≥0 := ((t₀ : ℝ) - ε / 2).toNNReal with ht₁def
  have ht₁t₀ : t₁ < t₀ := by
    rw [← NNReal.coe_lt_coe, ht₁def]
    rcases le_or_gt ((t₀ : ℝ) - ε / 2) 0 with hle | hgt
    · rw [Real.toNNReal_of_nonpos hle, NNReal.coe_zero]
      exact ht₀0'
    · rw [Real.coe_toNNReal _ hgt.le]
      linarith
  have hmemζ' : ∀ s : ℝ≥0, s ≤ t₀ → (s : ℝ≥0∞) ≤ ζ := fun s hs =>
    (ENNReal.coe_le_coe.2 hs).trans ht₀.le
  have hA : IsCompact (η '' Icc 0 t₁) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun s hs => hmemζ' s (hs.2.trans ht₁t₀.le))
  have hxA : ((xR k : ℝ) : ℂ) ∉ η '' Icc 0 t₁ := by
    rintro ⟨s, hs, hse⟩
    have hst := hinj (hmemζ' s (hs.2.trans ht₁t₀.le)) (hmemζ' t₀ le_rfl) (hse.trans he.symm)
    rw [hst] at hs
    exact absurd hs.2 (not_le.2 ht₁t₀)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hA.isClosed.isOpen_compl _ hxA
  set δ := min (min (c / 2) r) (min (xR k / 2) (a' - xR k)) with hδdef
  have hδc : δ ≤ c / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have hδk : δ ≤ xR k / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ a' - xR k := (min_le_right _ _).trans (min_le_right _ _)
  have hδ0 : 0 < δ := lt_min (lt_min (half_pos hpos) hr) (lt_min (half_pos hk0) (sub_pos.2 hka))
  -- the first real contact with `(x_k − δ, x_k + δ)`
  obtain ⟨p, T, y', hp0, hpT, hTt₀, hy', hηT, hH⟩ := exists_firstContact hη hwc h.w_zero
    (a := xR k - δ) (b := xR k + δ) (by linarith) ht₀.le ⟨by linarith, by linarith⟩ he
  have hTζ : (T : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 hTt₀).trans_lt ht₀
  have hT0 : (0 : ℝ) < T := hp0.trans hpT
  rcases lt_or_ge (xR k) y' with hgt | hle
  · -- a contact right of the mark is excluded at cumulative weight `≤ −2`
    refine not_visit_right h hord hη hinj (k := k) (a' := xR k + δ) (fun j hj => ?_) hS
      ⟨T, hTζ, y', ⟨hgt, hy'.2⟩, hηT⟩
    have := hnext j hj
    linarith
  -- the contact time is within `ε` of `t₀`
  have hTt₁ : t₁ < T := by
    by_contra hTle
    rw [not_lt] at hTle
    refine hball ?_ ⟨T, ⟨zero_le, hTle⟩, rfl⟩
    rw [Metric.mem_ball, hηT, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_lt]
    constructor <;> linarith [hy'.1, hy'.2]
  have hdist : dist (T : ℝ) t₀ < ε := by
    have h1 : (t₀ : ℝ) - ε / 2 ≤ t₁ := Real.le_coe_toNNReal _
    have h2 := NNReal.coe_lt_coe.2 hTt₁
    have h3 := NNReal.coe_le_coe.2 hTt₀
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hûT := hεc hdist
  -- the chart at the contact
  have hTT₂ : (T : ℝ) < T₂ := (NNReal.coe_le_coe.2 hTt₀).trans_lt ht₀T₂
  have hUw : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal := fun s hs0 hs => hUw₂ s hs0 (hs.trans hTT₂)
  have hηR : IsLoewnerTraceLT U T ηR := isLoewnerTraceLT_of_agree hη hTζ.le hUw
  have hmemζ : ∀ r : ℝ, r ≤ T → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun r hr =>
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr)).trans hTζ.le
  have hinjR : InjOn ηR (Icc 0 T) := by
    intro r hr s hs hrs
    have h1 := hinj (hmemζ r hr.2) (hmemζ s hs.2) hrs
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h1
    simp only [Real.coe_toNNReal _ hr.1, Real.coe_toNNReal _ hs.1] at h2
    exact h2
  have hHR : ∀ s ∈ Ioo (p : ℝ) T, ηR s ∈ H := fun s hs => by
    have hs0 : 0 ≤ s := (hp0.trans hs.1).le
    refine hH s.toNNReal ?_ ?_
    · rw [Real.coe_toNNReal _ hs0]
      exact hs.1.le
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
      exact hs.2
  have hηRT : ηR T = y' := by simp only [hηRdef, Real.toNNReal_coe, hηT]
  have hlimR : Tendsto ηR (𝓝[<] (T : ℝ)) (𝓝 (y' : ℂ)) := by
    rw [← hηT]
    exact tendsto_comp_toNNReal hη hTζ.le (NNReal.coe_pos.1 hT0)
  have hy'0 : 0 < y' := by linarith [hy'.1]
  have hbound := le_max_of_firstContact hηR hU hU0 hp0.le hpT hHR hinjR hy'0 hηRT hlimR (u := û)
    (fun s hs0 hsT => let P := pkg s hs0 (hsT.trans hTT₂); ⟨P.1, P.2.1, P.2.2.1⟩)
    ((hûcont T hT0 hTT₂).tendsto.mono_left nhdsWithin_le_nhds)
  have hû0 : û 0 = xR k := by simp [hûdef, h.vR_zero k, h.w_zero]
  rw [hû0] at hbound
  have hmax : max (xR k - y') 0 < δ := max_lt (by linarith [hy'.1]) hδ0
  rw [Real.dist_eq, abs_lt] at hûT
  linarith [hûT.1]

/-- **No visit of a right mark before the lifetime at cumulative weight `≤ −2`** (one path): at a visit of `x_k`
the marks `x_j ≤ x_k` are merged with the driver (`RLC.vR_eq_w_of_visit_mark` and the order of the force
coordinates) and the others are not (`RLC.vR_ne_w_of_lt_tip`), so the threshold condition would hold before `ζ`. -/
theorem not_visit_mark_right (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) {k : Fin nR} (hk0 : 0 < xR k) {a' : ℝ} (hka : xR k < a')
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i ≤ -2) :
    ¬ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ η t = xR k := by
  rintro ⟨t₀, ht₀, he⟩
  have hk := vR_eq_w_of_visit_mark h hord hη hinj hk0 hka hnext hS ht₀ he
  refine h.not_threshold ht₀ (Or.inr ?_)
  have e : univ.filter (fun i => vR i t₀ = w t₀) = univ.filter (fun i => xR i ≤ xR k) := by
    refine Finset.filter_congr fun j _ => ⟨fun hj => ?_, fun hj => ?_⟩
    · by_contra hlt
      exact vR_ne_w_of_lt_tip h hη ht₀ he (not_le.1 hlt) hj
    · have hw := h.w_le_vR ht₀ j
      rcases le_total j k with hjk | hkj
      · have := h.monotone_vR ht₀ hjk
        simp only at this
        linarith
      · have := h.vR_sub_vR_le ht₀ hkj
        linarith
  show (∑ i ∈ univ.filter (fun i => vR i t₀ = w t₀), ρR i) ≤ -2
  rw [e]
  exact hS

/-- **No visit of a left mark before the lifetime at cumulative weight `≤ −2`** (one path): the right case for the
reflected path and the reflected trace `−η̄`. -/
theorem not_visit_mark_left (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) {k : Fin nL} (hk0 : xL k < 0) {a : ℝ} (hka : a < xL k)
    (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hS : ∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i ≤ -2) :
    ¬ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ η t = xL k := by
  rintro ⟨t, ht, he⟩
  have hinj' : InjOn (fun t => LP.reflectC (η t)) {t | (t : ℝ≥0∞) ≤ ζ} := fun s hs t ht hst => by
    have := congrArg LP.reflectC hst
    simp only [LP.reflectC_reflectC] at this
    exact hinj hs ht this
  have hnext' : ∀ j, (-xL) k < (-xL) j → -a ≤ (-xL) j := fun j hj => by
    simp only [Pi.neg_apply, neg_lt_neg_iff] at hj
    simp only [Pi.neg_apply, neg_le_neg_iff]
    exact hnext j hj
  have e : univ.filter (fun i => (-xL) i ≤ (-xL) k) = univ.filter (fun i => xL k ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  refine not_visit_mark_right h.reflect (isOrderedForceWord_reflect hord) (LP.isGeneratingTrace_reflect hη) hinj'
    (k := k) (by simp only [Pi.neg_apply]; linarith) (a' := -a) (by simp only [Pi.neg_apply]; linarith) hnext'
    (by rw [e]; exact hS) ⟨t, ht, ?_⟩
  rw [he]
  simp [LP.reflectC]

end Path

/-- **`RLC.JumpVisitStatement` holds** (W5's real local frame, p. 535: "For real `p`, G12 excludes an original jump,
since both paths continue"). For a jump `y ≠ x`, on the right say, let `S` be the outward cumulative weight through
`y`. If `S > κ/2 − 4`, Lemma G12 (`Supp7.g12FlowStatement`) excludes every visit of `y`. Otherwise `S ≤ −2`: the
last mark `x_k ≤ y − x` of the flow-line word before the constant interval right of `y` carries the cumulative weight
`S` (`Supp8.exists_mark_right`); if `x_k = y − x` a visit of the mark is excluded by `RLC.not_visit_mark_right`, and
otherwise `y − x` lies in the open interval after `x_k`, excluded by `RLC.not_visit_right`. The left side is the
reflection. -/
theorem jumpVisitStatement : JumpVisitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ Ω _ P _ h hh η ζ hη
  have hd : κ / 2 - 4 ≤ -2 := by linarith
  have hG12 := Supp7.g12FlowStatement.{u} κ hκ hκ4 b jumps hb x θ
  have key : ∀ ω t (y : ℝ), η ω t = y → η ω t - x = ((y - x : ℝ) : ℂ) := fun ω t y he => by
    rw [he]
    push_cast
    ring
  obtain ⟨_h', 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := id hη
  have hord := Theorem15.isOrderedForceWord_flowLine b jumps x
  have hE := hcpl.1
  have hinj := Theorem15.aux25Statement κ hκ hκ4 _ _ _ _ hord P 𝓕 W VL VR B ζ hE
  have hpath := hE.2.2.2.2
  suffices hall : ∀ y ∈ jumps, ∀ᵐ ω ∂P, y ≠ x → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → η ω t ≠ y by
    filter_upwards [(Filter.eventually_all_finset jumps).2 hall] with ω hω t ht0 ht y hy hyx
    exact hω y hy hyx t ht0 ht
  intro y _
  rcases lt_trichotomy y x with hlt | heq | hgt
  · -- a jump left of the seed
    by_cases hS : κ / 2 - 4 <
        Sec4.cumWeightLeft κ (PiecewiseConstantBoundaryData.leftLim b y + θ * QuantumZipper.chiC κ)
    · filter_upwards [(hG12 y P h hh η ζ hη).2 hlt hS] with ω hω _ t _ ht using hω t ht.le
    rw [not_lt] at hS
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_eq_lims hb y
    have hv : ∀ z ∈ Ioo (y - δ / 2) y, z ∉ jumps → b z = PiecewiseConstantBoundaryData.leftLim b y := by
      intro z hz _
      have e : z = y - (y - z) := by ring
      rw [e]
      exact (hδJ (y - z) (by linarith [hz.2]) (by linarith [hz.1])).2.2.2
    obtain ⟨k, hka, hnext, hsum⟩ := Supp8.exists_mark_left hκ hb θ (a := y - δ / 2) (a' := y) hlt.le
      (by linarith) hv
    filter_upwards [hinj, hpath, htr] with ω h1 h3 h4 _ t _ ht hyη
    rcases eq_or_lt_of_le hka with he | hlt'
    · exact not_visit_mark_left h3.isForcePath hord h4 (h1 _ h4) (k := k) (by rw [← he]; linarith)
        (a := y - δ / 2 - x) (by rw [← he]; linarith) hnext (by rw [hsum]; linarith)
        ⟨t, ht, by rw [← he]; exact key ω t y hyη⟩
    · exact not_visit_left h3.isForcePath hord h4 (h1 _ h4) (k := k) (a := y - δ / 2 - x) hnext
        (by rw [hsum]; linarith) ⟨t, ht, y - x, ⟨by linarith, hlt'⟩, key ω t y hyη⟩
  · exact ae_of_all _ fun ω hyx => absurd heq hyx
  · -- a jump right of the seed
    by_cases hS : κ / 2 - 4 <
        Sec4.cumWeightRight κ (PiecewiseConstantBoundaryData.rightLim b y + θ * QuantumZipper.chiC κ)
    · filter_upwards [(hG12 y P h hh η ζ hη).1 hgt hS] with ω hω _ t _ ht using hω t ht.le
    rw [not_lt] at hS
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_eq_lims hb y
    have hv : ∀ z ∈ Ioo y (y + δ / 2), z ∉ jumps → b z = PiecewiseConstantBoundaryData.rightLim b y := by
      intro z hz _
      have e : z = y + (z - y) := by ring
      rw [e]
      exact (hδJ (z - y) (by linarith [hz.1]) (by linarith [hz.2])).2.2.1
    obtain ⟨k, hka, hnext, hsum⟩ := Supp8.exists_mark_right hκ hb θ (a := y) (a' := y + δ / 2) hgt.le
      (by linarith) hv
    filter_upwards [hinj, hpath, htr] with ω h1 h3 h4 _ t _ ht hyη
    rcases eq_or_lt_of_le hka with he | hlt'
    · exact not_visit_mark_right h3.isForcePath hord h4 (h1 _ h4) (k := k) (by rw [he]; linarith)
        (a' := y + δ / 2 - x) (by rw [he]; linarith) hnext (by rw [hsum]; linarith)
        ⟨t, ht, by rw [he]; exact key ω t y hyη⟩
    · exact not_visit_right h3.isForcePath hord h4 (h1 _ h4) (k := k) (a' := y + δ / 2 - x) hnext
        (by rw [hsum]; linarith) ⟨t, ht, y - x, ⟨hlt', by linarith⟩, key ω t y hyη⟩

/-- **`RetainedChartRealCompletionAtStatement` from G2a, G3, G8 and the strengthened retained-pair restart**
(`RLC.retainedChartRealCompletionAtStatement_of_restart` with `RLC.jumpVisitStatement`). -/
theorem retainedChartRealCompletionAtStatement_of_frames (hG2a : G2aReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hG8 : G8FrameStatement.{0})
    (hR : RetainedPairRestartUntouchedStatement.{u}) : RetainedChartRealCompletionAtStatement.{u} :=
  retainedChartRealCompletionAtStatement_of_restart hG2a hG3 hG8 jumpVisitStatement.{0} hR

/-- **Theorem W5** (`Theorem15.W5Statement`) from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the
common-seed comparison, G2a, G3, G8, Theorems 1.2 (param), 1.3 and the strengthened two-tip input
(`RLC.w5Statement_of_frames_param` with `RLC.jumpVisitStatement`; R43/R48: for Theorem 1.5 only). -/
theorem w5Statement_of_g2a_g3_g8_param (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : Supp9D.JointRetainedPairStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hG2a : G2aReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hG8 : G8FrameStatement.{0})
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0})
    (hD : RetainedCanonCondDetUntouchedStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_frames_param h25 hW0a hW0b h77 hJ hCS hG2a hG3 hG8 jumpVisitStatement.{0} h12p h13 hD

end RLC

end InteractingSLE
