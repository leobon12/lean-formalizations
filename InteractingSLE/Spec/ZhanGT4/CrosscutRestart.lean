/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutShift
import InteractingSLE.Spec.ZhanGT4.CrosscutConcat

/-!
# §A.4.2: the open driver sides at a stopping time, from the first-swallow crosscut (A.3)

Packet PROVE-ZHAN-GT4-A2. Source: Astra, *Follow-up proofs and dependency audit*, §A.4.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L743–L777, ruling R38).

**Main result.** `stoppingOpenSidesStatement_of_firstSwallowCrosscut`: for `κ > 4`,
`FirstSwallowCrosscutStatement κ → StoppingOpenSidesStatement κ`. Together with PROVE-ZHAN-GT4-A's reductions
(`stoppingCollarStatement_of_openSides_of_tip`), the stopping-time collar (G7) now rests on A.3 and the real-tip
step A.4.3 only.

## Proof

Fix a positive finite stopping time `T` and a right coordinate `u > 0` off the exterior coordinates at which `f_T`
has no interior boundary value. Pick a rational `q ∈ (0, u]`, an integer `n` with `−n` alive at `T` (the hull is
bounded), and a rational `p' ≤ g_T(−n) − W_T < 0`. If the fresh chain after `T` swallows `p'` while `q` is alive,
it swallows `g_T(−n) − W_T` first, and the deterministic §A.4.2 (`exists_tendsto_fwdMapInv_of_restart_pos`, with
A.3 at `−n` and the trace extension at the first swallowing time of `−n`) gives an interior boundary value at `u`:
a contradiction. That fresh event has positive probability (A.4.1, `exists_measurableSet_swallow_neg_first`).

The failure set need not be measurable, so the contradiction is run on `Ω × Ω` with `P ⊗ P` and the concatenated
Brownian motion `concatBM` (a Brownian motion by the strong Markov property, `isBrownianReal_concatBM`): A.3 and the
trace theorem hold `P ⊗ P`-a.s. for it, the failure for `ω` and the fresh event for `ω'` put `(ω, ω')` in that
null set, and Fubini (`measure_eq_zero_of_ae_mem_section`) makes the failure set `P`-null. Countably many
`(n, q, p')` and the reflected left side finish the proof.
-/

set_option autoImplicit false

universe u

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### Dependence on the driver up to the current time -/

section Congr

variable {W W' : ℝ → ℝ}

theorem fwdMap_real_congr (hW : Continuous W) (hW' : Continuous W') {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) {x : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) :
    fwdMap W T x = fwdMap W' T x := by
  rw [fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩,
    fwdMap_eq_of_isForwardSol hW' (QuantumZipper.isForwardSol_congr_drive h hu) ⟨hT, le_rfl⟩]

theorem exteriorCoords_congr (hW : Continuous W) (hW' : Continuous W') {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) : exteriorCoords W T = exteriorCoords W' T := by
  have h' : ∀ r ∈ Icc (0 : ℝ) T, W' r = W r := fun r hr => (h r hr).symm
  unfold exteriorCoords
  congr 1
  ext r
  constructor
  · rintro ⟨x, ⟨u, hu⟩, rfl⟩
    exact ⟨x, ⟨u, QuantumZipper.isForwardSol_congr_drive h hu⟩, by rw [fwdMap_real_congr hW hW' hT h hu]⟩
  · rintro ⟨x, ⟨u, hu⟩, rfl⟩
    exact ⟨x, ⟨u, QuantumZipper.isForwardSol_congr_drive h' hu⟩, by rw [fwdMap_real_congr hW' hW hT h' hu]⟩

/-- The inverse map at time `t` reads the driver on `[0, t]` only. -/
theorem fwdMapInv_congr (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (h : ∀ r ∈ Icc (0 : ℝ) t, W r = W' r) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv W t z = fwdMapInv W' t z := by
  rw [QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hz,
    QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W' hW' hW'0 ht hz]
  refine QuantumZipper.ReverseFlow.revMap_congr_drive z fun r hr => ?_
  have h1 : t - r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h2 : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  simp only [h _ h1, h _ h2]

theorem realSwallowAt_congr {σ : ℝ} (h : ∀ r ∈ Icc (0 : ℝ) σ, W r = W' r) {x : ℝ} :
    RealSwallowAt W x σ → RealSwallowAt W' x σ := by
  rintro ⟨hσ, halive, hdead⟩
  refine ⟨hσ, fun s hs => ?_, fun ⟨v, hv⟩ => hdead ⟨v, QuantumZipper.isForwardSol_congr_drive
    (fun r hr => (h r hr).symm) hv⟩⟩
  obtain ⟨v, hv⟩ := halive s hs
  exact ⟨v, QuantumZipper.isForwardSol_congr_drive (fun r hr => h r ⟨hr.1, hr.2.trans hs.2.le⟩) hv⟩

end Congr

/-! ### A Fubini lemma for non-measurable sets -/

/-- If for every `ω ∈ A` the section of a `P ⊗ P`-null set `N` at `ω` almost contains a fixed event `E` of positive
probability, then `A` is `P`-null (no measurability of `A` is needed). -/
theorem measure_eq_zero_of_ae_mem_section {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : Set (Ω × Ω)} (hN : (P.prod P) N = 0) {E : Set Ω} (hE : 0 < P E)
    {A : Set Ω} (hA : ∀ ω ∈ A, ∀ᵐ ω' ∂P, ω' ∈ E → (ω, ω') ∈ N) : P A = 0 := by
  set N' := toMeasurable (P.prod P) N with hN'
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN'0 : (P.prod P) N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
  have hsec : Measurable fun ω => P (Prod.mk ω ⁻¹' N') := measurable_measure_prodMk_left hN'm
  have hint : ∫⁻ ω, P (Prod.mk ω ⁻¹' N') ∂P = 0 := by rw [← Measure.prod_apply hN'm]; exact hN'0
  have hae : ∀ᵐ ω ∂P, P (Prod.mk ω ⁻¹' N') = 0 := (lintegral_eq_zero_iff hsec).1 hint
  have hsub : A ⊆ {ω | P (Prod.mk ω ⁻¹' N') ≠ 0} := by
    intro ω hω
    have hle : P E ≤ P (Prod.mk ω ⁻¹' N') := by
      refine measure_mono_ae ?_
      filter_upwards [hA ω hω] with ω' h hE'
      exact subset_toMeasurable _ _ (h hE')
    exact (lt_of_lt_of_le hE hle).ne'
  exact measure_mono_null hsub (by
    rw [← ae_iff] at *
    exact hae)

/-! ### The deterministic step for one pair `(past, fresh)` -/

section Pair

variable {W W₁ V : ℝ → ℝ}

/-- The data a pair must satisfy: `W` agrees with the past driver `W₁` on `[0, T]`, its increments after `T` are
the fresh driver `V`, and A.3 and the trace extension hold for `W` at the real point `x`. -/
structure PairData (W W₁ V : ℝ → ℝ) (T x : ℝ) : Prop where
  contW : Continuous W
  zeroW : W 0 = 0
  contW₁ : Continuous W₁
  zeroW₁ : W₁ 0 = 0
  contV : Continuous V
  pos : 0 < T
  past : ∀ r ∈ Icc (0 : ℝ) T, W r = W₁ r
  fresh : ∀ r, 0 ≤ r → W (T + r) - W T = V r
  crosscut : ∃ σ₀ : ℝ, RealSwallowAt W x σ₀ ∧ ∃ F γ, CrosscutAt W σ₀ F γ

/-- **One pair, right side.** If `x < 0` is alive at `T` for the past driver, the fresh driver swallows some
`p' ≤ g_T(x) − W_T` while `q > 0` is alive, then every `u ≥ q` off the exterior coordinates at `T` has an interior
boundary value of `f_T`. -/
theorem PairData.exists_tendsto_pos {T x : ℝ} (hd : PairData W W₁ V T x) (hx : x < 0) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W₁ (x : ℂ) T u₀) {p' q σ' : ℝ} (hp' : p' ≤ (fwdMap W₁ T x).re) (hq : 0 < q)
    (hsw' : RealSwallowAt V p' σ') (hqa : ∃ v, IsForwardSol V (q : ℂ) σ' v) {u : ℝ} (hqu : q ≤ u)
    (hu : u ∉ exteriorCoords W₁ T) : ∃ P ∈ H, Tendsto (fwdMapInv W₁ T) (𝓝[H] (u : ℂ)) (𝓝 P) := by
  have hT := hd.pos.le
  have hpast' : ∀ r ∈ Icc (0 : ℝ) T, W₁ r = W r := fun r hr => (hd.past r hr).symm
  have hu₀W : IsForwardSol W (x : ℂ) T u₀ := QuantumZipper.isForwardSol_congr_drive hpast' hu₀
  have hfeq : fwdMap W T x = fwdMap W₁ T x := fwdMap_real_congr hd.contW₁ hd.contW hT hpast' hu₀ |>.symm
  set p := (fwdMap W₁ T x).re with hp
  have hpneg : p < 0 := re_fwdMap_neg hd.contW₁ hd.zeroW₁ hx hu₀ ⟨hT, le_rfl⟩
  have hV0 : V 0 = 0 := by rw [← hd.fresh 0 le_rfl, add_zero, sub_self]
  -- the fresh chain swallows `p` while `q` is alive
  have hσ' := hsw'.1
  have hpdead : ¬ ∃ v, IsForwardSol V (p : ℂ) σ' v := by
    rintro ⟨v, hv⟩
    rcases eq_or_lt_of_le hp' with h | h
    · exact hsw'.2.2 ⟨v, h ▸ hv⟩
    · obtain ⟨w, hw⟩ := (exists_isForwardSol_neg_iff (W := V) (x := p) (T := σ')).2 ⟨v, hv⟩
      have h2 := RS.exists_isForwardSol_of_lt (W := fun t => -V t) hd.contV.neg hσ'.le (q := -p) (y := -p')
        (by simp [hV0]; linarith) (by linarith) hw
      exact hsw'.2.2 ((exists_isForwardSol_neg_iff (W := V)).1 (by simpa using h2))
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt_of_neg hd.contV hV0 hpneg hσ'.le hpdead
  obtain ⟨v, hv⟩ := hqa
  have hqa' : ∃ v, IsForwardSol V (q : ℂ) σ v := ⟨v, isForwardSol_restrict hv hσ.1.le hσ.2⟩
  -- transfer to the increments of `W`
  have hVW : ∀ r ∈ Icc (0 : ℝ) σ, V r = W (T + r) - W T := fun r hr => (hd.fresh r hr.1).symm
  have hsw2 : RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ := by
    rw [hfeq]; exact realSwallowAt_congr hVW hsw
  have hqa2 : ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v := by
    obtain ⟨v, hv⟩ := hqa'; exact ⟨v, QuantumZipper.isForwardSol_congr_drive hVW hv⟩
  obtain ⟨σ₀, hσ₀, F, γ, hC⟩ := hd.crosscut
  have huW : u ∉ exteriorCoords W T := by rwa [exteriorCoords_congr hd.contW hd.contW₁ hT hd.past]
  obtain ⟨P, hPH, hlim⟩ := exists_tendsto_fwdMapInv_of_restart_pos hd.contW hd.zeroW hT hu₀W hsw2 hq hqa2
    hσ₀ hC hqu huW
  refine ⟨P, hPH, hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact fwdMapInv_congr hd.contW hd.contW₁ hd.zeroW hd.zeroW₁ hT hd.past hz

/-- **One pair, left side** (reflection of `PairData.exists_tendsto_pos`). -/
theorem PairData.exists_tendsto_neg {T x : ℝ} (hd : PairData W W₁ V T x) (hx : 0 < x) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W₁ (x : ℂ) T u₀) {p' q σ' : ℝ} (hp' : (fwdMap W₁ T x).re ≤ p') (hq : q < 0)
    (hsw' : RealSwallowAt V p' σ') (hqa : ∃ v, IsForwardSol V (q : ℂ) σ' v) {u : ℝ} (hqu : u ≤ q)
    (hu : u ∉ exteriorCoords W₁ T) : ∃ P ∈ H, Tendsto (fwdMapInv W₁ T) (𝓝[H] (u : ℂ)) (𝓝 P) := by
  have hT := hd.pos.le
  have hpast' : ∀ r ∈ Icc (0 : ℝ) T, W₁ r = W r := fun r hr => (hd.past r hr).symm
  have hu₀W : IsForwardSol W (x : ℂ) T u₀ := QuantumZipper.isForwardSol_congr_drive hpast' hu₀
  have hfeq : fwdMap W T x = fwdMap W₁ T x := fwdMap_real_congr hd.contW₁ hd.contW hT hpast' hu₀ |>.symm
  set p := (fwdMap W₁ T x).re with hp
  have hppos : 0 < p := re_fwdMap_pos hd.contW₁ hd.zeroW₁ hx hu₀ ⟨hT, le_rfl⟩
  have hV0 : V 0 = 0 := by rw [← hd.fresh 0 le_rfl, add_zero, sub_self]
  have hσ' := hsw'.1
  have hpdead : ¬ ∃ v, IsForwardSol V (p : ℂ) σ' v := by
    rintro ⟨v, hv⟩
    rcases eq_or_lt_of_le hp' with h | h
    · exact hsw'.2.2 ⟨v, h ▸ hv⟩
    · exact hsw'.2.2 (RS.exists_isForwardSol_of_lt hd.contV hσ'.le (by rw [hV0]; exact hppos) h hv)
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hd.contV hV0 hppos hσ'.le hpdead
  obtain ⟨v, hv⟩ := hqa
  have hqa' : ∃ v, IsForwardSol V (q : ℂ) σ v := ⟨v, isForwardSol_restrict hv hσ.1.le hσ.2⟩
  have hVW : ∀ r ∈ Icc (0 : ℝ) σ, V r = W (T + r) - W T := fun r hr => (hd.fresh r hr.1).symm
  have hsw2 : RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ := by
    rw [hfeq]; exact realSwallowAt_congr hVW hsw
  have hqa2 : ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v := by
    obtain ⟨v, hv⟩ := hqa'; exact ⟨v, QuantumZipper.isForwardSol_congr_drive hVW hv⟩
  obtain ⟨σ₀, hσ₀, F, γ, hC⟩ := hd.crosscut
  have huW : u ∉ exteriorCoords W T := by rwa [exteriorCoords_congr hd.contW hd.contW₁ hT hd.past]
  obtain ⟨P, hPH, hlim⟩ := exists_tendsto_fwdMapInv_of_restart_neg hd.contW hd.zeroW hT hu₀W hsw2 hq hqa2
    hσ₀ hC hqu huW
  refine ⟨P, hPH, hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact fwdMapInv_congr hd.contW hd.contW₁ hd.zeroW hd.zeroW₁ hT hd.past hz

/-- The fresh swallowing data of a pair, right side: transferred to the increments of `W`. -/
theorem PairData.exists_swallow_pos {T x : ℝ} (hd : PairData W W₁ V T x) (hx : x < 0) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W₁ (x : ℂ) T u₀) {p' q σ' : ℝ} (hp' : p' ≤ (fwdMap W₁ T x).re)
    (hsw' : RealSwallowAt V p' σ') (hqa : ∃ v, IsForwardSol V (q : ℂ) σ' v) :
    ∃ σ, RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ ∧
      ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v := by
  have hT := hd.pos.le
  have hpast' : ∀ r ∈ Icc (0 : ℝ) T, W₁ r = W r := fun r hr => (hd.past r hr).symm
  have hfeq : fwdMap W T x = fwdMap W₁ T x := fwdMap_real_congr hd.contW₁ hd.contW hT hpast' hu₀ |>.symm
  set p := (fwdMap W₁ T x).re with hp
  have hpneg : p < 0 := re_fwdMap_neg hd.contW₁ hd.zeroW₁ hx hu₀ ⟨hT, le_rfl⟩
  have hV0 : V 0 = 0 := by rw [← hd.fresh 0 le_rfl, add_zero, sub_self]
  have hσ' := hsw'.1
  have hpdead : ¬ ∃ v, IsForwardSol V (p : ℂ) σ' v := by
    rintro ⟨v, hv⟩
    rcases eq_or_lt_of_le hp' with h | h
    · exact hsw'.2.2 ⟨v, h ▸ hv⟩
    · obtain ⟨w, hw⟩ := (exists_isForwardSol_neg_iff (W := V) (x := p) (T := σ')).2 ⟨v, hv⟩
      have h2 := RS.exists_isForwardSol_of_lt (W := fun t => -V t) hd.contV.neg hσ'.le (q := -p) (y := -p')
        (by simp [hV0]; linarith) (by linarith) hw
      exact hsw'.2.2 ((exists_isForwardSol_neg_iff (W := V)).1 (by simpa using h2))
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt_of_neg hd.contV hV0 hpneg hσ'.le hpdead
  obtain ⟨v, hv⟩ := hqa
  have hVW : ∀ r ∈ Icc (0 : ℝ) σ, V r = W (T + r) - W T := fun r hr => (hd.fresh r hr.1).symm
  refine ⟨σ, by rw [hfeq]; exact realSwallowAt_congr hVW hsw, v, ?_⟩
  exact QuantumZipper.isForwardSol_congr_drive hVW (isForwardSol_restrict hv hσ.1.le hσ.2)

/-- The fresh swallowing data of a pair, left side. -/
theorem PairData.exists_swallow_neg {T x : ℝ} (hd : PairData W W₁ V T x) (hx : 0 < x) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W₁ (x : ℂ) T u₀) {p' q σ' : ℝ} (hp' : (fwdMap W₁ T x).re ≤ p')
    (hsw' : RealSwallowAt V p' σ') (hqa : ∃ v, IsForwardSol V (q : ℂ) σ' v) :
    ∃ σ, RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ ∧
      ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v := by
  have hT := hd.pos.le
  have hpast' : ∀ r ∈ Icc (0 : ℝ) T, W₁ r = W r := fun r hr => (hd.past r hr).symm
  have hfeq : fwdMap W T x = fwdMap W₁ T x := fwdMap_real_congr hd.contW₁ hd.contW hT hpast' hu₀ |>.symm
  set p := (fwdMap W₁ T x).re with hp
  have hppos : 0 < p := re_fwdMap_pos hd.contW₁ hd.zeroW₁ hx hu₀ ⟨hT, le_rfl⟩
  have hV0 : V 0 = 0 := by rw [← hd.fresh 0 le_rfl, add_zero, sub_self]
  have hσ' := hsw'.1
  have hpdead : ¬ ∃ v, IsForwardSol V (p : ℂ) σ' v := by
    rintro ⟨v, hv⟩
    rcases eq_or_lt_of_le hp' with h | h
    · exact hsw'.2.2 ⟨v, h ▸ hv⟩
    · exact hsw'.2.2 (RS.exists_isForwardSol_of_lt hd.contV hσ'.le (by rw [hV0]; exact hppos) h hv)
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hd.contV hV0 hppos hσ'.le hpdead
  obtain ⟨v, hv⟩ := hqa
  have hVW : ∀ r ∈ Icc (0 : ℝ) σ, V r = W (T + r) - W T := fun r hr => (hd.fresh r hr.1).symm
  refine ⟨σ, by rw [hfeq]; exact realSwallowAt_congr hVW hsw, v, ?_⟩
  exact QuantumZipper.isForwardSol_congr_drive hVW (isForwardSol_restrict hv hσ.1.le hσ.2)

/-- Boundary values of `f_T` for the past driver are those for `W`. -/
theorem PairData.tendsto_iff {T x : ℝ} (hd : PairData W W₁ V T x) {u : ℝ} {p : ℂ} :
    Tendsto (fwdMapInv W₁ T) (𝓝[H] (u : ℂ)) (𝓝 p) ↔ Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 p) := by
  refine tendsto_congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (fwdMapInv_congr hd.contW hd.contW₁ hd.zeroW hd.zeroW₁ hd.pos.le hd.past hz).symm

/-- **One pair, injectivity on the right.** -/
theorem PairData.eq_pos {T x : ℝ} (hd : PairData W W₁ V T x) (hx : x < 0) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W₁ (x : ℂ) T u₀) {p' q σ' : ℝ} (hp' : p' ≤ (fwdMap W₁ T x).re) (hq : 0 < q)
    (hsw' : RealSwallowAt V p' σ') (hqa : ∃ v, IsForwardSol V (q : ℂ) σ' v) {u₁ u₂ : ℝ} (hq₁ : q ≤ u₁)
    (hq₂ : q ≤ u₂) {p₁ p₂ : ℂ} (h₁ : Tendsto (fwdMapInv W₁ T) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁))
    (h₂ : Tendsto (fwdMapInv W₁ T) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂)) (hp : p₁ = p₂) : u₁ = u₂ := by
  obtain ⟨σ, hsw, hqa2⟩ := hd.exists_swallow_pos hx hu₀ hp' hsw' hqa
  obtain ⟨σ₀, hσ₀, F, γ, hC⟩ := hd.crosscut
  have hu₀W : IsForwardSol W (x : ℂ) T u₀ :=
    QuantumZipper.isForwardSol_congr_drive (fun r hr => (hd.past r hr).symm) hu₀
  exact eq_of_restart_pos hd.contW hd.zeroW hd.pos.le hu₀W hsw hq hqa2 hσ₀ hC hq₁ hq₂
    (hd.tendsto_iff.1 h₁) (hd.tendsto_iff.1 h₂) hp

/-- **One pair, injectivity on the left.** -/
theorem PairData.eq_neg {T x : ℝ} (hd : PairData W W₁ V T x) (hx : 0 < x) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W₁ (x : ℂ) T u₀) {p' q σ' : ℝ} (hp' : (fwdMap W₁ T x).re ≤ p') (hq : q < 0)
    (hsw' : RealSwallowAt V p' σ') (hqa : ∃ v, IsForwardSol V (q : ℂ) σ' v) {u₁ u₂ : ℝ} (hq₁ : u₁ ≤ q)
    (hq₂ : u₂ ≤ q) {p₁ p₂ : ℂ} (h₁ : Tendsto (fwdMapInv W₁ T) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁))
    (h₂ : Tendsto (fwdMapInv W₁ T) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂)) (hp : p₁ = p₂) : u₁ = u₂ := by
  obtain ⟨σ, hsw, hqa2⟩ := hd.exists_swallow_neg hx hu₀ hp' hsw' hqa
  obtain ⟨σ₀, hσ₀, F, γ, hC⟩ := hd.crosscut
  have hu₀W : IsForwardSol W (x : ℂ) T u₀ :=
    QuantumZipper.isForwardSol_congr_drive (fun r hr => (hd.past r hr).symm) hu₀
  exact eq_of_restart_neg hd.contW hd.zeroW hd.pos.le hu₀W hsw hq hqa2 hσ₀ hC hq₁ hq₂
    (hd.tendsto_iff.1 h₁) (hd.tendsto_iff.1 h₂) hp

end Pair

/-! ### The stopping-time statement -/

section Version

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A version of a filtered Brownian motion with every path continuous and vanishing at `0`, Brownian for the usual
augmentation (`Sec2.Restart.exists_continuous_version`, keeping `B 0 = 0`). -/
theorem exists_continuous_version_zero (hB : IsFilteredBrownianReal 𝓕 B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous (B' · ω)) ∧ (∀ ω, B' 0 ω = 0) ∧
      IsFilteredBrownianReal (usualAugmentation 𝓕 P) B' P ∧ ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω := by
  obtain ⟨B', hm, hc, h0, hBM, hae⟩ := QuantumZipper.RS.exists_good_version0 hB.1
  have hU := Ito.isFilteredBrownianReal_usualAugmentation hB
  have hae' : ∀ t, B t =ᵐ[P] B' t := fun t => hae.mono fun ω h => (h t).symm
  refine ⟨B', hm, hc, h0, ⟨hBM, fun t => ?_, fun s t hst => ?_⟩, hae⟩
  · exact Sec2.Restart.measurable_of_ae_eq_of_null ((usualAugmentation 𝓕 P).le t)
      (fun S hS h0 => Ito.measurableSet_usualAugmentation_of_null hS h0 t) (hU.2.1 t) (hm t) (hae' t)
  · refine Sec2.Restart.indep_comap_congr ?_ (hU.2.2 s t hst)
    filter_upwards [hae] with ω h
    simp [h]

end Version

/-- The data `CrosscutAt` from A.3's conclusion and a continuous trace. -/
theorem exists_crosscutAt {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {σ : ℝ} (hσ : 0 ≤ σ) {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (h0 : (γ 0).re < 0)
    (h1 : 0 < (γ 1).re) (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1) : ∃ F, CrosscutAt W σ F γ := by
  have hLT : IsLoewnerTraceLT W (σ + 1) η :=
    ⟨hη.1, hη.2.1.mono Ico_subset_Ici_self, fun t ht _ => hη.2.2 t ht⟩
  obtain ⟨F, hFeq, hFc, hFb⟩ := hLT.exists_extension hW hW0 hσ (by linarith)
  exact ⟨F, ⟨hFeq, hFc, hFb, hγ, h0, h1, hfr⟩⟩

/-- **The setup of §A.4.2 on `Ω × Ω`.** A continuous version `B₁` of `B` vanishing at `0`, and a `P ⊗ P`-null set
`N` off which every pair `(ω, ω')` carries the data of the deterministic step (`PairData`) for the concatenated
driver at the points `∓(n + 1)`: A.3 and the trace extension for the concatenated Brownian motion. -/
theorem exists_pairData {κ : ℝ} (hκ : 4 < κ) (hA3 : FirstSwallowCrosscutStatement.{u} κ) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) (hTpos : ∀ ω, 0 < T ω) :
    ∃ B₁ : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B₁ t)) ∧ (∀ ω, Continuous (B₁ · ω)) ∧ (∀ ω, B₁ 0 ω = 0) ∧
      IsBrownianReal B₁ P ∧ (∀ᵐ ω ∂P, ∀ t, B₁ t ω = B t ω) ∧ ∃ N : Set (Ω × Ω), (P.prod P) N = 0 ∧
        ∀ ω ω' : Ω, (ω, ω') ∉ N → ∀ n : ℕ,
          PairData (drive κ (concatBM B₁ T) (ω, ω')) (drive κ B₁ ω) (drive κ B₁ ω') (T ω) (-((n : ℝ) + 1)) ∧
          PairData (drive κ (concatBM B₁ T) (ω, ω')) (drive κ B₁ ω) (drive κ B₁ ω') (T ω) ((n : ℝ) + 1) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁F, hae⟩ := exists_continuous_version_zero hB
  have hB₁BM : IsBrownianReal B₁ P := hB₁F.1
  have hT𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) (fun ω => (T ω : WithTop ℝ≥0)) := fun i =>
    Ito.le_usualAugmentation 𝓕 P i _ (hT i)
  have hind := Sec2.Restart.indep_future hB₁F
  have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P) B₁ :=
    isStronglyProgressive_of_rightContinuous (fun t => (hB₁F.2.1 t).stronglyMeasurable)
      fun ω _ => (hB₁c ω).continuousWithinAt
  have hB' : IsBrownianReal (concatBM B₁ T) (P.prod P) :=
    isBrownianReal_concatBM hB₁BM.toIsPreBrownianReal hB₁c hB₁m hind hprog hT𝓖
  set B' := concatBM B₁ T with hB'def
  have hB'c : ∀ q, Continuous (drive κ B' q) := fun q => drive_continuous (continuous_concatBM hB₁c T q)
  have hB'0 : ∀ q, drive κ B' q 0 = 0 := fun q => by simp [drive, hB'def, concatBM, hB₁0]
  have hW₁c : ∀ ω, Continuous (drive κ B₁ ω) := fun ω => drive_continuous (hB₁c ω)
  have hW₁0 : ∀ ω, drive κ B₁ ω 0 = 0 := fun ω => by simp [drive, hB₁0]
  -- A.3 and the trace on the product
  have hgood : ∀ᵐ q ∂(P.prod P), ∀ n : ℕ,
      (∃ σ₀, RealSwallowAt (drive κ B' q) (-((n : ℝ) + 1)) σ₀ ∧ ∃ F γ, CrosscutAt (drive κ B' q) σ₀ F γ) ∧
      (∃ σ₀, RealSwallowAt (drive κ B' q) ((n : ℝ) + 1) σ₀ ∧ ∃ F γ, CrosscutAt (drive κ B' q) σ₀ F γ) := by
    rw [ae_all_iff]
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := hA3 hκ (P.prod P) B' hB' (-((n : ℝ) + 1)) (by linarith)
    have h2 := hA3 hκ (P.prod P) B' hB' ((n : ℝ) + 1) hn.ne'
    have htr := ae_isLoewnerTrace_sleTrace hB' hκ0
    filter_upwards [h1, h2, htr] with q hq1 hq2 htq
    obtain ⟨σ₁, hσ₁, γ₁, hγ₁, h01, h11, hfr1, -⟩ := hq1
    obtain ⟨σ₂, hσ₂, γ₂, hγ₂, h02, h12, hfr2, -⟩ := hq2
    obtain ⟨F₁, hF₁⟩ := exists_crosscutAt (hB'c q) (hB'0 q) htq hσ₁.1.le hγ₁ h01 h11 hfr1
    obtain ⟨F₂, hF₂⟩ := exists_crosscutAt (hB'c q) (hB'0 q) htq hσ₂.1.le hγ₂ h02 h12 hfr2
    exact ⟨⟨σ₁, hσ₁, F₁, γ₁, hF₁⟩, ⟨σ₂, hσ₂, F₂, γ₂, hF₂⟩⟩
  obtain ⟨N, hNnull, hNgood⟩ : ∃ N : Set (Ω × Ω), (P.prod P) N = 0 ∧ ∀ q ∉ N, ∀ n : ℕ,
      (∃ σ₀, RealSwallowAt (drive κ B' q) (-((n : ℝ) + 1)) σ₀ ∧ ∃ F γ, CrosscutAt (drive κ B' q) σ₀ F γ) ∧
      (∃ σ₀, RealSwallowAt (drive κ B' q) ((n : ℝ) + 1) σ₀ ∧ ∃ F γ, CrosscutAt (drive κ B' q) σ₀ F γ) :=
    ⟨_, ae_iff.1 hgood, fun q hq => not_not.1 hq⟩
  -- the pair data
  have hpair : ∀ ω ω' : Ω, (ω, ω') ∉ N → ∀ n : ℕ,
      PairData (drive κ B' (ω, ω')) (drive κ B₁ ω) (drive κ B₁ ω') (T ω) (-((n : ℝ) + 1)) ∧
      PairData (drive κ B' (ω, ω')) (drive κ B₁ ω) (drive κ B₁ ω') (T ω) ((n : ℝ) + 1) := by
    intro ω ω' hq n
    have hpast : ∀ r ∈ Icc (0 : ℝ) (T ω), drive κ B' (ω, ω') r = drive κ B₁ ω r := by
      intro r hr
      simp only [drive, hB'def]
      rw [concatBM_of_le B₁ T (q := (ω, ω')) (show r.toNNReal ≤ T ω from
        Real.toNNReal_le_iff_le_coe.2 hr.2)]
    have hfresh : ∀ r, 0 ≤ r → drive κ B' (ω, ω') ((T ω : ℝ) + r) - drive κ B' (ω, ω') (T ω) =
        drive κ B₁ ω' r := by
      intro r hr
      simp only [drive, hB'def]
      rw [Real.toNNReal_add (NNReal.coe_nonneg _) hr, Real.toNNReal_coe, ← mul_sub,
        concatBM_add B₁ T r.toNNReal (ω, ω'), hB₁0, sub_zero]
    have hTp : (0 : ℝ) < T ω := NNReal.coe_pos.2 (hTpos ω)
    exact ⟨⟨hB'c _, hB'0 _, hW₁c ω, hW₁0 ω, hW₁c ω', hTp, hpast, hfresh, (hNgood _ hq n).1⟩,
      ⟨hB'c _, hB'0 _, hW₁c ω, hW₁0 ω, hW₁c ω', hTp, hpast, hfresh, (hNgood _ hq n).2⟩⟩
  exact ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁BM, hae, N, hNnull, hpair⟩

/-- **§A.4.2 at a stopping time, from the first-swallow crosscut A.3.** For `κ > 4`, if A.3 holds then almost surely
at every positive finite stopping time the open driver sides of the inverse map are interior. -/
theorem stoppingOpenSidesStatement_of_firstSwallowCrosscut {κ : ℝ} (hκ : 4 < κ)
    (hA3 : FirstSwallowCrosscutStatement.{u} κ) : StoppingOpenSidesStatement.{u} κ := by
  intro Ω mΩ P hP 𝓕 B hB T hT hTpos
  obtain ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁BM, hae, N, hNnull, hpair⟩ := exists_pairData hκ hA3 hB hT hTpos
  have hW₁c : ∀ ω, Continuous (drive κ B₁ ω) := fun ω => drive_continuous (hB₁c ω)
  have hW₁0 : ∀ ω, drive κ B₁ ω 0 = 0 := fun ω => by simp [drive, hB₁0]
  -- reduce to the version
  suffices h : ∀ᵐ ω ∂P, HasInteriorOpenSides (drive κ B₁ ω) (T ω) by
    filter_upwards [h, hae] with ω h1 h2
    have : drive κ B ω = drive κ B₁ ω := funext fun r => by simp only [drive, h2]
    rwa [this]
  -- the failure sets
  set W₁ : Ω → ℝ → ℝ := fun ω => drive κ B₁ ω with hW₁def
  set Fpos : ℕ → ℚ → ℤ → Set Ω := fun n q p' => {ω | 0 < (q : ℝ) ∧ (p' : ℝ) < 0 ∧
    (∃ v, IsForwardSol (W₁ ω) ((-((n : ℝ) + 1) : ℝ) : ℂ) (T ω) v) ∧
    (p' : ℝ) ≤ (fwdMap (W₁ ω) (T ω) ((-((n : ℝ) + 1) : ℝ) : ℂ)).re ∧
    ∃ u : ℝ, (q : ℝ) ≤ u ∧ u ∉ exteriorCoords (W₁ ω) (T ω) ∧
      ¬ ∃ p ∈ H, Tendsto (fwdMapInv (W₁ ω) (T ω)) (𝓝[H] (u : ℂ)) (𝓝 p)} with hFpos
  set Fneg : ℕ → ℚ → ℤ → Set Ω := fun n q p' => {ω | (q : ℝ) < 0 ∧ 0 < (p' : ℝ) ∧
    (∃ v, IsForwardSol (W₁ ω) ((((n : ℝ) + 1) : ℝ) : ℂ) (T ω) v) ∧
    (fwdMap (W₁ ω) (T ω) ((((n : ℝ) + 1) : ℝ) : ℂ)).re ≤ (p' : ℝ) ∧
    ∃ u : ℝ, u ≤ (q : ℝ) ∧ u ∉ exteriorCoords (W₁ ω) (T ω) ∧
      ¬ ∃ p ∈ H, Tendsto (fwdMapInv (W₁ ω) (T ω)) (𝓝[H] (u : ℂ)) (𝓝 p)} with hFneg
  have hFpos0 : ∀ n q p', P (Fpos n q p') = 0 := by
    intro n q p'
    by_cases hqp : 0 < (q : ℝ) ∧ (p' : ℝ) < 0
    swap
    · refine measure_mono_null (fun ω hω => hqp ⟨hω.1, hω.2.1⟩) measure_empty
    obtain ⟨E, -, hEP, hE⟩ := exists_measurableSet_swallow_neg_first hB₁BM hB₁m hB₁c hB₁0 hκ hqp.2 hqp.1
    refine measure_eq_zero_of_ae_mem_section hNnull hEP fun ω hω => ?_
    filter_upwards [hE] with ω' hω' hω'E
    by_contra hq
    obtain ⟨σ', hsw', hqa⟩ := hω' hω'E
    obtain ⟨-, -, ⟨u₀, hu₀⟩, hp', u, hqu, hu, hno⟩ := hω
    exact hno ((hpair ω ω' hq n).1.exists_tendsto_pos (by linarith) hu₀ hp' hqp.1 hsw' hqa hqu hu)
  have hFneg0 : ∀ n q p', P (Fneg n q p') = 0 := by
    intro n q p'
    by_cases hqp : (q : ℝ) < 0 ∧ 0 < (p' : ℝ)
    swap
    · refine measure_mono_null (fun ω hω => hqp ⟨hω.1, hω.2.1⟩) measure_empty
    obtain ⟨E, -, hEP, hE⟩ := exists_measurableSet_swallow_pos_first hB₁BM hB₁m hB₁c hB₁0 hκ hqp.1 hqp.2
    refine measure_eq_zero_of_ae_mem_section hNnull hEP fun ω hω => ?_
    filter_upwards [hE] with ω' hω' hω'E
    by_contra hq
    obtain ⟨σ', hsw', hqa⟩ := hω' hω'E
    obtain ⟨-, -, ⟨u₀, hu₀⟩, hp', u, hqu, hu, hno⟩ := hω
    exact hno ((hpair ω ω' hq n).2.exists_tendsto_neg (by positivity) hu₀ hp' hqp.1 hsw' hqa hqu hu)
  -- every failure is in one of the countably many sets
  have hcover : {ω | ¬ HasInteriorOpenSides (W₁ ω) (T ω)} ⊆
      ⋃ n : ℕ, ⋃ q : ℚ, ⋃ p' : ℤ, (Fpos n q p' ∪ Fneg n q p') := by
    intro ω hω
    simp only [HasInteriorOpenSides, not_forall, mem_ofPred_eq] at hω
    obtain ⟨u, hu, hu0, hno⟩ := hω
    have hTp : (0 : ℝ) < T ω := NNReal.coe_pos.2 (hTpos ω)
    -- a large real point on either side is alive
    obtain ⟨M, hM⟩ := exists_abs_le_of_continuous (hW₁c ω) (T ω)
    obtain ⟨n, hn⟩ := exists_nat_ge (M + 3 * Real.sqrt (T ω) + 1)
    have hball : ∀ x : ℝ, |x| = (n : ℝ) + 1 → Disjoint (ball (x : ℂ) 1) (fwdHull (W₁ ω) (T ω)) := by
      intro x hx
      refine Set.disjoint_left.2 fun z hz hzK => ?_
      have h1 := CaraR.fwdHull_subset_closedBall (hW₁c ω) hTp hM hzK
      rw [mem_closedBall, dist_zero_right] at h1
      rw [mem_ball, dist_eq_norm] at hz
      have h2 := norm_sub_norm_le (x : ℂ) z
      rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, hx] at h2
      linarith
    simp only [mem_iUnion, mem_union]
    refine ⟨n, ?_⟩
    rcases lt_or_gt_of_ne hu0 with hneg | hpos
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hneg
      have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball (hW₁c ω) (hW₁0 ω) hx.ne' hTp.le one_pos
        (hball _ (abs_of_pos hx))
      have hp := re_fwdMap_pos (hW₁c ω) (hW₁0 ω) hx hv ⟨hTp.le, le_rfl⟩
      refine ⟨q, ⌈(fwdMap (W₁ ω) (T ω) ((((n : ℝ) + 1) : ℝ) : ℂ)).re⌉, Or.inr ⟨hq2, ?_, ⟨v, hv⟩, ?_,
        u, hq1.le, hu, hno⟩⟩
      · exact_mod_cast Int.ceil_pos.2 hp
      · exact Int.le_ceil _
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hpos
      have hx : -((n : ℝ) + 1) < 0 := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball (hW₁c ω) (hW₁0 ω) hx.ne hTp.le one_pos
        (hball _ (by rw [abs_neg, abs_of_pos (by positivity)]))
      have hp := re_fwdMap_neg (hW₁c ω) (hW₁0 ω) hx hv ⟨hTp.le, le_rfl⟩
      refine ⟨q, ⌊(fwdMap (W₁ ω) (T ω) ((-((n : ℝ) + 1) : ℝ) : ℂ)).re⌋, Or.inl ⟨hq1, ?_, ⟨v, hv⟩, ?_,
        u, hq2.le, hu, hno⟩⟩
      · have : ⌊(fwdMap (W₁ ω) (T ω) ((-((n : ℝ) + 1) : ℝ) : ℂ)).re⌋ < 0 :=
          Int.floor_lt.2 (by exact_mod_cast hp)
        exact_mod_cast this
      · exact Int.floor_le _
  rw [ae_iff]
  refine measure_mono_null hcover (measure_iUnion_null fun n => measure_iUnion_null fun q =>
    measure_iUnion_null fun p' => measure_union_null (hFpos0 n q p') (hFneg0 n q p'))

/-! ### Injective open sides -/

/-- **The boundary map is injective on each side of the driver** (§A.4.2, L743: "`f` is injective on each of
`(c, W)` and `(W, d)`"): two real coordinates on the same side of `0` at which `f_T = g_T⁻¹(W_T + ·)` has the same
boundary value are equal. (Stated on the whole of each side; on the exterior coordinates it is the injectivity of
the real flow.) -/
def HasInjectiveOpenSides (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ u₁ u₂ : ℝ, 0 < u₁ * u₂ → ∀ p₁ p₂ : ℂ, Tendsto (fwdMapInv W T) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁) →
    Tendsto (fwdMapInv W T) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂) → p₁ = p₂ → u₁ = u₂

/-- **A.4.2 at a stopping time, in full** (L743–L744): for ordinary `SLE_κ` and every positive finite stopping time,
almost surely the inverse map has interior boundary values on the open driver sides and is injective on each side. -/
def StoppingOpenSidesInjStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) → (∀ ω, 0 < T ω) →
      ∀ᵐ ω ∂P, HasInteriorOpenSides (drive κ B ω) (T ω) ∧ HasInjectiveOpenSides (drive κ B ω) (T ω)

theorem stoppingOpenSidesStatement_of_inj {κ : ℝ} (h : StoppingOpenSidesInjStatement.{u} κ) :
    StoppingOpenSidesStatement.{u} κ := fun P _ 𝓕 B hB T hT hTpos =>
  (h P 𝓕 B hB T hT hTpos).mono fun _ hω => hω.1

/-- **§A.4.2 in full at a stopping time, from A.3**: interior and injective open sides. -/
theorem stoppingOpenSidesInjStatement_of_firstSwallowCrosscut {κ : ℝ} (hκ : 4 < κ)
    (hA3 : FirstSwallowCrosscutStatement.{u} κ) : StoppingOpenSidesInjStatement.{u} κ := by
  intro Ω mΩ P hP 𝓕 B hB T hT hTpos
  have h1 := stoppingOpenSidesStatement_of_firstSwallowCrosscut hκ hA3 P 𝓕 B hB T hT hTpos
  obtain ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁BM, hae, N, hNnull, hpair⟩ := exists_pairData hκ hA3 hB hT hTpos
  have hW₁c : ∀ ω, Continuous (drive κ B₁ ω) := fun ω => drive_continuous (hB₁c ω)
  have hW₁0 : ∀ ω, drive κ B₁ ω 0 = 0 := fun ω => by simp [drive, hB₁0]
  suffices h : ∀ᵐ ω ∂P, HasInjectiveOpenSides (drive κ B₁ ω) (T ω) by
    filter_upwards [h1, h, hae] with ω h1 h2 h3
    have : drive κ B ω = drive κ B₁ ω := funext fun r => by simp only [drive, h3]
    exact ⟨h1, by rw [this]; exact h2⟩
  set W₁ : Ω → ℝ → ℝ := fun ω => drive κ B₁ ω with hW₁def
  set Ipos : ℕ → ℚ → ℤ → Set Ω := fun n q p' => {ω | 0 < (q : ℝ) ∧ (p' : ℝ) < 0 ∧
    (∃ v, IsForwardSol (W₁ ω) ((-((n : ℝ) + 1) : ℝ) : ℂ) (T ω) v) ∧
    (p' : ℝ) ≤ (fwdMap (W₁ ω) (T ω) ((-((n : ℝ) + 1) : ℝ) : ℂ)).re ∧
    ∃ u₁ u₂ : ℝ, (q : ℝ) ≤ u₁ ∧ (q : ℝ) ≤ u₂ ∧ u₁ ≠ u₂ ∧ ∃ p₁ p₂ : ℂ,
      Tendsto (fwdMapInv (W₁ ω) (T ω)) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁) ∧
      Tendsto (fwdMapInv (W₁ ω) (T ω)) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂) ∧ p₁ = p₂} with hIpos
  set Ineg : ℕ → ℚ → ℤ → Set Ω := fun n q p' => {ω | (q : ℝ) < 0 ∧ 0 < (p' : ℝ) ∧
    (∃ v, IsForwardSol (W₁ ω) ((((n : ℝ) + 1) : ℝ) : ℂ) (T ω) v) ∧
    (fwdMap (W₁ ω) (T ω) ((((n : ℝ) + 1) : ℝ) : ℂ)).re ≤ (p' : ℝ) ∧
    ∃ u₁ u₂ : ℝ, u₁ ≤ (q : ℝ) ∧ u₂ ≤ (q : ℝ) ∧ u₁ ≠ u₂ ∧ ∃ p₁ p₂ : ℂ,
      Tendsto (fwdMapInv (W₁ ω) (T ω)) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁) ∧
      Tendsto (fwdMapInv (W₁ ω) (T ω)) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂) ∧ p₁ = p₂} with hIneg
  have hIpos0 : ∀ n q p', P (Ipos n q p') = 0 := by
    intro n q p'
    by_cases hqp : 0 < (q : ℝ) ∧ (p' : ℝ) < 0
    swap
    · exact measure_mono_null (fun ω hω => hqp ⟨hω.1, hω.2.1⟩) measure_empty
    obtain ⟨E, -, hEP, hE⟩ := exists_measurableSet_swallow_neg_first hB₁BM hB₁m hB₁c hB₁0 hκ hqp.2 hqp.1
    refine measure_eq_zero_of_ae_mem_section hNnull hEP fun ω hω => ?_
    filter_upwards [hE] with ω' hω' hω'E
    by_contra hq
    obtain ⟨σ', hsw', hqa⟩ := hω' hω'E
    obtain ⟨-, -, ⟨u₀, hu₀⟩, hp', u₁, u₂, hq₁, hq₂, hne, p₁, p₂, h₁, h₂, hp⟩ := hω
    exact hne ((hpair ω ω' hq n).1.eq_pos (by linarith) hu₀ hp' hqp.1 hsw' hqa hq₁ hq₂ h₁ h₂ hp)
  have hIneg0 : ∀ n q p', P (Ineg n q p') = 0 := by
    intro n q p'
    by_cases hqp : (q : ℝ) < 0 ∧ 0 < (p' : ℝ)
    swap
    · exact measure_mono_null (fun ω hω => hqp ⟨hω.1, hω.2.1⟩) measure_empty
    obtain ⟨E, -, hEP, hE⟩ := exists_measurableSet_swallow_pos_first hB₁BM hB₁m hB₁c hB₁0 hκ hqp.1 hqp.2
    refine measure_eq_zero_of_ae_mem_section hNnull hEP fun ω hω => ?_
    filter_upwards [hE] with ω' hω' hω'E
    by_contra hq
    obtain ⟨σ', hsw', hqa⟩ := hω' hω'E
    obtain ⟨-, -, ⟨u₀, hu₀⟩, hp', u₁, u₂, hq₁, hq₂, hne, p₁, p₂, h₁, h₂, hp⟩ := hω
    exact hne ((hpair ω ω' hq n).2.eq_neg (by positivity) hu₀ hp' hqp.1 hsw' hqa hq₁ hq₂ h₁ h₂ hp)
  have hcover : {ω | ¬ HasInjectiveOpenSides (W₁ ω) (T ω)} ⊆
      ⋃ n : ℕ, ⋃ q : ℚ, ⋃ p' : ℤ, (Ipos n q p' ∪ Ineg n q p') := by
    intro ω hω
    simp only [HasInjectiveOpenSides, not_forall, mem_ofPred_eq] at hω
    obtain ⟨u₁, u₂, hside, p₁, p₂, h₁, h₂, hp, hne⟩ := hω
    have hTp : (0 : ℝ) < T ω := NNReal.coe_pos.2 (hTpos ω)
    obtain ⟨M, hM⟩ := exists_abs_le_of_continuous (hW₁c ω) (T ω)
    obtain ⟨n, hn⟩ := exists_nat_ge (M + 3 * Real.sqrt (T ω) + 1)
    have hball : ∀ x : ℝ, |x| = (n : ℝ) + 1 → Disjoint (ball (x : ℂ) 1) (fwdHull (W₁ ω) (T ω)) := by
      intro x hx
      refine Set.disjoint_left.2 fun z hz hzK => ?_
      have h1 := CaraR.fwdHull_subset_closedBall (hW₁c ω) hTp hM hzK
      rw [mem_closedBall, dist_zero_right] at h1
      rw [mem_ball, dist_eq_norm] at hz
      have h2 := norm_sub_norm_le (x : ℂ) z
      rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, hx] at h2
      linarith
    simp only [mem_iUnion, mem_union]
    refine ⟨n, ?_⟩
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hside with ⟨hu₁, hu₂⟩ | ⟨hu₁, hu₂⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hu₁ hu₂)
      have hx : -((n : ℝ) + 1) < 0 := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball (hW₁c ω) (hW₁0 ω) hx.ne hTp.le one_pos
        (hball _ (by rw [abs_neg, abs_of_pos (by positivity)]))
      have hpn := re_fwdMap_neg (hW₁c ω) (hW₁0 ω) hx hv ⟨hTp.le, le_rfl⟩
      refine ⟨q, ⌊(fwdMap (W₁ ω) (T ω) ((-((n : ℝ) + 1) : ℝ) : ℂ)).re⌋, Or.inl ⟨hq1, ?_, ⟨v, hv⟩,
        Int.floor_le _, u₁, u₂, (hq2.trans_le (min_le_left _ _)).le, (hq2.trans_le (min_le_right _ _)).le,
        hne, p₁, p₂, h₁, h₂, hp⟩⟩
      have : ⌊(fwdMap (W₁ ω) (T ω) ((-((n : ℝ) + 1) : ℝ) : ℂ)).re⌋ < 0 :=
        Int.floor_lt.2 (by exact_mod_cast hpn)
      exact_mod_cast this
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hu₁ hu₂)
      have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball (hW₁c ω) (hW₁0 ω) hx.ne' hTp.le one_pos
        (hball _ (abs_of_pos hx))
      have hpp := re_fwdMap_pos (hW₁c ω) (hW₁0 ω) hx hv ⟨hTp.le, le_rfl⟩
      refine ⟨q, ⌈(fwdMap (W₁ ω) (T ω) ((((n : ℝ) + 1) : ℝ) : ℂ)).re⌉, Or.inr ⟨hq2, ?_, ⟨v, hv⟩,
        Int.le_ceil _, u₁, u₂, ((le_max_left _ _).trans_lt hq1).le, ((le_max_right _ _).trans_lt hq1).le,
        hne, p₁, p₂, h₁, h₂, hp⟩⟩
      exact_mod_cast Int.ceil_pos.2 hpp
  rw [ae_iff]
  refine measure_mono_null hcover (measure_iUnion_null fun n => measure_iUnion_null fun q =>
    measure_iUnion_null fun p' => measure_union_null (hIpos0 n q p') (hIneg0 n q p'))

end InteractingSLE.ZhanGT4
