import InteractingSLE.Spec.Supplement.LP4HalfBallDet
import InteractingSLE.Spec.Supplement.LP4HalfBallLP3
import InteractingSLE.Spec.Supplement.LP4AvoidHalfBall
import InteractingSLE.Spec.ZhanGT4.NoClusterGirsanov
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# LP4's collar step: the future after a deterministic time

Packet PROVE-LP17. Specification p. 483 (proof of Proposition LP4): "Apply LP3 to ordinary SLE in this mapped-out
half-plane, taking the two force coordinates as protected outer points. … Both force drifts have bounded energy
through `τ_m`, so Girsanov gives equivalence of the entire capped stopped driving laws. Apply Zhan's independent
ordinary-SLE result [Zha10, Corollary 6.1] at this positive finite stopping time … Both the success event and this
stopped hull property transfer under the equivalent capped laws."

Here the restart is at a **deterministic** time `σ`, and LP3's construction runs up to a deterministic time `τ`
(`LP3.lp3_zero_bdd`), so the collar is applied at the constant stopping time `τ` of the restarted filtration. The
Girsanov change is the cut-drift change of the whole two-seed evolution (`Girsanov.girsanov_cutDrift`, the template of
`ZhanGT4.IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary_level`): under the equivalent measure `Q`, `B̂` is a
Brownian motion of `𝓕`; its increments after `σ` are a Brownian motion of `s ↦ 𝓕_{σ+s}` independent of `𝓕_σ`.
On the event where the force gaps stay `≥ δ/2` on `[σ, σ + t]`, the driver increments are `√κ` times those of `B̂`
(`Dimension.sub_eq_sqrt_mul_sub_of_cut`); LP3's driver bounds keep the gaps `≥ δ` (the forces move outward), so the
identification holds on all of `[σ, σ + τ]` (`forall_le_of_bootstrap`).

## Main results

* `shiftFiltration`, `isFilteredBrownianReal_shift`: the restarted Brownian motion.
* `forall_le_of_bootstrap`: a continuity (bootstrap) lemma.
* **`frequently_halfBall_of_cluster`**: for the two-seed evolution, if on an event `A ∈ 𝓕_σ` of positive probability
  the force coordinates at `σ` lie `δ` beyond `ℓq < pm < 0 < pp < rq` and the cluster condition holds at `σ` with an
  interval inside `(pm, pp)`, then with positive probability some hull contains a half-ball around `0` (given the
  stopping-time collar `ZhanGT4.StoppingCollarStatement κ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS InteractingSLE.Girsanov

universe u

namespace InteractingSLE.LP.LP4HB

/-! ### The restarted Brownian motion -/

/-- The filtration `s ↦ 𝓕_{σ+s}`. -/
def shiftFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (σ : ℝ≥0) :
    Filtration ℝ≥0 mΩ where
  seq s := 𝓕 (σ + s)
  mono' _ _ h := 𝓕.mono (add_le_add le_rfl h)
  le' s := 𝓕.le (σ + s)

theorem isFilteredBrownianReal_shift {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) (σ : ℝ≥0) :
    IsFilteredBrownianReal (shiftFiltration 𝓕 σ) (fun s ω => B (σ + s) ω - B σ ω) P := by
  refine ⟨hB.1.shift σ, fun s => ?_, fun s t hst => ?_⟩
  · exact (hB.2.1 (σ + s)).sub ((hB.2.1 σ).mono (𝓕.mono le_self_add) le_rfl)
  · have e : (fun ω => (B (σ + t) ω - B σ ω) - (B (σ + s) ω - B σ ω)) =
        fun ω => B (σ + t) ω - B (σ + s) ω := by
      funext ω; ring
    rw [e]
    exact hB.2.2 (σ + s) (σ + t) (add_le_add le_rfl hst)

/-! ### A bootstrap lemma -/

/-- **Bootstrap.** If `g` is continuous on `[0, τ]`, `g 0 ≥ c > δ`, and `g t ≥ c` whenever `g ≥ δ` on `[0, t]`,
then `g ≥ c` on `[0, τ]`. -/
theorem forall_le_of_bootstrap {g : ℝ → ℝ} {τ c δ : ℝ} (hg : ContinuousOn g (Icc 0 τ)) (hδc : δ < c)
    (h0 : c ≤ g 0) (hstep : ∀ t ∈ Icc (0 : ℝ) τ, (∀ s ∈ Icc (0 : ℝ) t, δ ≤ g s) → c ≤ g t) :
    ∀ t ∈ Icc (0 : ℝ) τ, c ≤ g t := by
  suffices hδ : ∀ t ∈ Icc (0 : ℝ) τ, δ < g t by
    exact fun t ht => hstep t ht fun s hs => (hδ s ⟨hs.1, hs.2.trans ht.2⟩).le
  by_contra hcon
  push Not at hcon
  set Z : Set ℝ := Icc 0 τ ∩ g ⁻¹' Iic δ with hZ
  have hZc : IsClosed Z := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := by
    obtain ⟨t, ht, hgt⟩ := hcon
    exact ⟨t, ht, hgt⟩
  have hbdd : BddBelow Z := ⟨0, fun s hs => hs.1.1⟩
  set t₀ := sInf Z with ht₀
  have ht₀Z : t₀ ∈ Z := hZc.csInf_mem hZne hbdd
  have hbefore : ∀ s ∈ Icc (0 : ℝ) t₀, s < t₀ → δ < g s := fun s hs hst => by
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd ⟨⟨hs.1, hs.2.trans ht₀Z.1.2⟩, h⟩) (not_le.2 hst)
  have hτ0 : 0 ≤ τ := ht₀Z.1.1.trans ht₀Z.1.2
  have ht₀pos : 0 < t₀ := by
    rcases ht₀Z.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := ht₀Z.2
      simp only [mem_preimage, mem_Iic] at this
      rw [← h] at this
      linarith
  -- `g t₀ ≥ δ` by continuity from the left
  have hgt₀ : δ ≤ g t₀ := by
    have hcw : ContinuousWithinAt g (Icc 0 t₀) t₀ :=
      (hg t₀ ht₀Z.1).mono (Icc_subset_Icc le_rfl ht₀Z.1.2)
    have hne : (𝓝[Ico 0 t₀] t₀).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico ht₀pos.ne]
      exact ⟨ht₀pos.le, le_rfl⟩
    have h1 : Tendsto g (𝓝[Ico 0 t₀] t₀) (𝓝 (g t₀)) :=
      hcw.tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)
    exact ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun s hs =>
      (hbefore s ⟨hs.1, hs.2.le⟩ hs.2).le)
  have hc := hstep t₀ ht₀Z.1 fun s hs => by
    rcases hs.2.lt_or_eq with h | h
    · exact (hbefore s hs h).le
    · rw [h]; exact hgt₀
  have := ht₀Z.2
  simp only [mem_preimage, mem_Iic] at this
  linarith


/-! ### Monotonicity of the force coordinates -/

/-- A right force coordinate of a path is nondecreasing in time (its drift `2/(v − w)` is `≥ 0`). -/
theorem le_of_forceR {w v : ℝ≥0 → ℝ} {x : ℝ} (hle : ∀ s : ℝ≥0, w s ≤ v s)
    (hint : ∀ s : ℝ≥0, IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 s)
    (heq : ∀ s : ℝ≥0, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal))
    {s t : ℝ≥0} (hst : s ≤ t) : v s ≤ v t := by
  have hI : ∀ u : ℝ≥0, IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 u :=
    fun u => by
      have e : (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) =
          fun r => (-2) * (w r.toNNReal - v r.toNNReal)⁻¹ := by
        funext r
        rw [div_eq_mul_inv, ← neg_sub, inv_neg]
        ring
      rw [e]; exact (hint u).const_mul _
  rw [heq s, heq t, ← intervalIntegral.integral_add_adjacent_intervals (hI s) ((hI s).symm.trans (hI t))]
  have hnn : 0 ≤ ∫ r in (s : ℝ)..(t : ℝ), 2 / (v r.toNNReal - w r.toNNReal) :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hst) fun r _ =>
      div_nonneg zero_le_two (sub_nonneg.2 (hle _))
  linarith

/-- A left force coordinate of a path is nonincreasing in time. -/
theorem le_of_forceL {w v : ℝ≥0 → ℝ} {x : ℝ} (hle : ∀ s : ℝ≥0, v s ≤ w s)
    (hint : ∀ s : ℝ≥0, IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 s)
    (heq : ∀ s : ℝ≥0, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal))
    {s t : ℝ≥0} (hst : s ≤ t) : v t ≤ v s := by
  have hI : ∀ u : ℝ≥0, IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 u :=
    fun u => by
      have e : (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) =
          fun r => (-2) * (w r.toNNReal - v r.toNNReal)⁻¹ := by
        funext r
        rw [div_eq_mul_inv, ← neg_sub, inv_neg]
        ring
      rw [e]; exact (hint u).const_mul _
  rw [heq s, heq t, ← intervalIntegral.integral_add_adjacent_intervals (hI s) ((hI s).symm.trans (hI t))]
  have hnp : ∫ r in (s : ℝ)..(t : ℝ), 2 / (v r.toNNReal - w r.toNNReal) ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun r : ℝ => -(2 / (v r.toNNReal - w r.toNNReal))) (by exact_mod_cast hst) fun r _ =>
        neg_nonneg.2 (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hle _)))
    rw [intervalIntegral.integral_neg] at h
    exact neg_nonneg.1 h
  linarith

/-! ### The future after a deterministic time -/

variable {κ rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **LP4's collar step at a deterministic restart time.** For the two-seed evolution, let `A ∈ 𝓕_σ` have positive
probability, and almost surely on `A` let the force coordinates at `σ` lie `δ` beyond `ℓq < pm < 0 < pp < rq`, and
the cluster condition hold at `σ` with `[m₁, m₂] ⊆ (pm, pp)`. Given the stopping-time collar, with positive
probability some hull `K_T` contains a half-ball around `0`. -/
theorem frequently_halfBall_of_cluster [IsProbabilityMeasure P] (hκ : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hcol : ZhanGT4.StoppingCollarStatement.{u} κ)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    (σ : ℝ≥0) {ℓq pm pp rq δ ε m₁ m₂ : ℝ} (hℓq : ℓq < pm) (hpm : pm < 0) (hpp : 0 < pp) (hrq : pp < rq)
    (hδ : 0 < δ) (hε : 0 < ε) (hm₁ : pm < m₁) (hm₂ : m₂ < pp)
    {A : Set Ω} (hAm : MeasurableSet[𝓕 σ] A) (hA : P A ≠ 0)
    (hAgood : ∀ᵐ ω ∂P, ω ∈ A →
      VL 0 σ ω - W σ ω ≤ ℓq - δ ∧ rq + δ ≤ VR 0 σ ω - W σ ω ∧
      ∀ z ∈ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) σ, ‖z‖ < ε →
        m₁ ≤ (fwdMap (fun s : ℝ => W s.toNNReal ω) σ z).re ∧
          (fwdMap (fun s : ℝ => W s.toNNReal ω) σ z).re ≤ m₂) :
    ∃ᵐ ω ∂P, ∃ T : ℝ≥0, ∃ ε' > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε' →
      z ∈ fwdHull (fun s : ℝ => W s.toNNReal ω) T := by
  have hκ0 : 0 < κ := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    Sec7.ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) hκ0 hL hR
      Sec7.jacobiDiffusionExistsStatement hE
  -- the deterministic time of LP3
  obtain ⟨B₀, hB₀m, hB₀c, hB₀0, hB₀, -⟩ := exists_good_version0 hE.1.1
  obtain ⟨τ, hτ, hLP3⟩ := LP3.lp3_zero_bdd hB₀ hB₀m hB₀c hB₀0 hκ hℓq hpm hpp hrq
  set τ' : ℝ≥0 := τ.toNNReal with hτ'def
  have hττ' : (τ' : ℝ) = τ := Real.coe_toNNReal _ hτ.le
  have hτ'pos : 0 < τ' := Real.toNNReal_pos.2 hτ
  -- the cut-drift Girsanov change
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  set δc : ℝ := δ / 2 with hδcdef
  have hδc : 0 < δc := by positivity
  set U : Fin (1 + 1) → ℝ≥0 → Ω → ℝ := allMarks VL VR with hUdef
  set σw : Fin (1 + 1) → ℝ := Fin.addCases (motive := fun _ => ℝ) (fun _ : Fin 1 => rL)
    (fun _ : Fin 1 => rR) with hσw
  set F : ℝ → (Fin (1 + 1) → ℝ) → ℝ := fun w u => (Real.sqrt κ)⁻¹ * addedDriftCut σw δc w u
    with hFdef
  have hFc : Continuous fun p : ℝ × (Fin (1 + 1) → ℝ) => F p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σw hδc)
  have hFb : ∀ w u, |F w u| ≤ (Real.sqrt κ)⁻¹ * ((∑ j, |σw j|) * δc⁻¹) := fun w u => by
    rw [hFdef, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg κ))]
    exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σw hδc w u)
      (inv_nonneg.2 (Real.sqrt_nonneg κ))
  set N : ℝ≥0 := σ + τ' + 1 with hN
  set τs : Ω → ℝ≥0∞ := fun ω => min (ζ ω) (N : ℝ≥0∞) with hτsdef
  have hτs : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τs ω ≤ s} := by
    intro s
    have h1 : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)} :=
      hW s univ MeasurableSet.univ
    have h2 : {ω | τs ω ≤ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)}ᶜ ∪
        {_ω : Ω | (N : ℝ≥0∞) ≤ s} := by
      ext ω
      simp [hτsdef, min_le_iff, not_lt]
    rw [h2]
    exact h1.compl.union (MeasurableSet.const _)
  have hτζ : ∀ ω, τs ω ≤ ζ ω := fun ω => min_le_left _ _
  have hτT : ∀ ω, τs ω ≤ (N : ℝ≥0∞) := fun ω => min_le_right _ _
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (U k) := fun k => by
    cases k using Fin.addCases with
    | left i =>
      show AdaptedBefore 𝓕 ζ (allMarks VL VR (Fin.castAdd 1 i))
      simp only [allMarks, Fin.addCases_left]; exact hVL i
    | right i =>
      show AdaptedBefore 𝓕 ζ (allMarks VL VR (Fin.natAdd 1 i))
      simp only [allMarks, Fin.addCases_right]; exact hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => U k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i =>
      show ContinuousOn (fun s => allMarks VL VR (Fin.castAdd 1 i) s ω) _
      simp only [allMarks, Fin.addCases_left]; exact hp.2.2.2.2.1 i
    | right i =>
      show ContinuousOn (fun s => allMarks VL VR (Fin.natAdd 1 i) s ω) _
      simp only [allMarks, Fin.addCases_right]; exact hp.2.2.2.2.2.1 i
  obtain ⟨hequiv, hBM, hident⟩ := girsanov_cutDrift hBF hFc hFb hW hU hτs hτζ hτT hcont
  set θ := cutDrift τs ζ F W U with hθ
  set Q := girsanovMeasure P 𝓕 B θ (N + 1) with hQ
  set Bh := girsanovProcess B θ with hBh
  have : IsProbabilityMeasure Q := hequiv.isProb
  -- the restarted Brownian motion under `Q`
  set B' : ℝ≥0 → Ω → ℝ := fun s ω => Bh (σ + s) ω - Bh σ ω with hB'def
  have hB'F : IsFilteredBrownianReal (shiftFiltration 𝓕 σ) B' Q := isFilteredBrownianReal_shift hBM σ
  have hind := Sec2.Restart.indep_future hBM σ
  -- LP3 for a continuous version of `B'`
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hB''eq⟩ := exists_good_version0 hB'F.1
  obtain ⟨E, hEm, hEQ, hEprop⟩ := hLP3 hB'' hB''m hB''c hB''0
  obtain ⟨S, hS, hSE⟩ := hEm
  set E' : Set Ω := (StrongMarkov.smPath Bh (fun _ => σ)) ⁻¹' S with hE'def
  have hEE' : E =ᵐ[Q] E' := by
    filter_upwards [hB''eq] with ω hω
    have e : (fun t : ℝ≥0 => B'' t ω) = StrongMarkov.smPath Bh (fun _ => σ) ω := by
      funext t; rw [hω t]; rfl
    show (ω ∈ E) = (ω ∈ E')
    rw [← hSE]
    simp only [mem_preimage, hE'def]
    rw [e]
  have hQAE : Q (A ∩ E) = Q A * Q E := by
    rw [measure_congr (ae_eq_set_inter (ae_eq_refl A) hEE'), measure_congr hEE']
    exact (Indep_iff _ _ _).1 hind A E' hAm ⟨S, hS, rfl⟩
  have hQA : Q A ≠ 0 := fun h => hA (hequiv.ac' h)
  have hpos : P (A ∩ E) ≠ 0 := by
    intro h
    have h1 : Q (A ∩ E) = 0 := hequiv.ac h
    rw [hQAE] at h1
    exact (mul_ne_zero hQA hEQ.ne') h1
  -- the collar for `√κ B'` at `τ`
  have hcolQ := hcol Q (shiftFiltration 𝓕 σ) B' hB'F (fun _ => τ') (isStoppingTime_const _ _)
    (fun _ => hτ'pos)
  have hcolP := hequiv.ac'.ae_le hcolQ
  have hB''P := hequiv.ac'.ae_le hB''eq
  -- the pathwise conclusion
  intro hcon
  apply hpos
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hcon, hζ, hpath, hident, hcolP, hB''P, hAgood] with ω hnot hζω hp hid hcolω hB''ω hAω
  intro hω
  obtain ⟨hgL, hgR, hcl⟩ := hAω hω.1
  have hEω := hEprop ω (hSE ▸ hω.2)
  obtain ⟨hdm, hdp, hbd⟩ := hEω
  rw [hζω] at hp
  have hdrive : drive κ B'' ω = drive κ B' ω := by
    funext t; simp only [drive, hB''ω]
  rw [hdrive] at hdm hdp hbd
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  obtain ⟨-, -, -, -, hvLc, hvRc, -, hvLw, hwvR, -, hgapL, hgapR, hweq, hvLeq, hvReq, -⟩ := hp
  have hvLc' : Continuous (VL 0 · ω) := continuousOn_univ.1 (by simpa using hvLc 0)
  have hvRc' : Continuous (VR 0 · ω) := continuousOn_univ.1 (by simpa using hvRc 0)
  have hτsω : τs ω = (N : ℝ≥0∞) := by simp [hτsdef, hζω]
  have hT : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ := fun t => ENNReal.coe_lt_top
  -- the increments of the driver are those of `√κ B̂` while the gaps are `≥ δ/2`
  have hsplit : ∀ r : ℝ≥0, (∑ k, ∫ s in (0 : ℝ)..(r : ℝ), σw k / (W s.toNNReal ω - U k s.toNNReal ω))
      = (∑ i, ∫ s in (0 : ℝ)..(r : ℝ), (fun _ : Fin 1 => rL) i / (W s.toNNReal ω - VL i s.toNNReal ω))
        + (∑ i, ∫ s in (0 : ℝ)..(r : ℝ), (fun _ : Fin 1 => rR) i / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
    intro r
    rw [Fin.sum_univ_add]
    simp only [hσw, hUdef, allMarks, Fin.addCases_left, Fin.addCases_right]
  have hint : ∀ r : ℝ≥0, ∀ k, IntervalIntegrable
      (fun s : ℝ => σw k / (W s.toNNReal ω - U k s.toNNReal ω)) volume 0 (r : ℝ) := fun r k => by
    cases k using Fin.addCases with
    | left i =>
      simp only [hσw, hUdef, allMarks, Fin.addCases_left, div_eq_mul_inv]
      exact (hgapL r (hT r) i).const_mul rL
    | right i =>
      simp only [hσw, hUdef, allMarks, Fin.addCases_right, div_eq_mul_inv]
      exact (hgapR r (hT r) i).const_mul rR
  have hUc : ∀ k, Continuous fun s => U k s ω := fun k => by
    cases k using Fin.addCases with
    | left i =>
      show Continuous fun s => allMarks VL VR (Fin.castAdd 1 i) s ω
      simp only [allMarks, Fin.addCases_left]
      exact continuousOn_univ.1 (by simpa using hvLc i)
    | right i =>
      show Continuous fun s => allMarks VL VR (Fin.natAdd 1 i) s ω
      simp only [allMarks, Fin.addCases_right]
      exact continuousOn_univ.1 (by simpa using hvRc i)
  have hfint : ∀ r : ℝ≥0, IntervalIntegrable (fun s : ℝ => (Real.sqrt κ)⁻¹ *
      addedDriftCut σw δc (W s.toNNReal ω) (fun k => U k s.toNNReal ω)) volume 0 (r : ℝ) := fun r => by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((continuous_addedDriftCut σw hδc).comp
      (f := fun s : ℝ => (W s.toNNReal ω, fun k => U k s.toNNReal ω))
      ((hwc.comp continuous_real_toNNReal).prodMk
        (continuous_pi fun k => (hUc k).comp continuous_real_toNNReal)))
  have hincr : ∀ s' : ℝ≥0, s' ≤ τ' →
      (∀ s : ℝ≥0, σ ≤ s → s ≤ σ + s' → ∀ k, δc ≤ |W s ω - U k s ω|) →
      W (σ + s') ω - W σ ω = Real.sqrt κ * (Bh (σ + s') ω - Bh σ ω) := by
    intro s' hs' hgap
    have hle1 : ((σ + s' : ℝ≥0) : ℝ≥0∞) ≤ τs ω := by
      rw [hτsω, ENNReal.coe_le_coe, hN]
      calc σ + s' ≤ σ + τ' := add_le_add le_rfl hs'
        _ ≤ σ + τ' + 1 := le_self_add
    have hle2 : ((σ : ℝ≥0) : ℝ≥0∞) ≤ τs ω :=
      le_trans (ENNReal.coe_le_coe.2 le_self_add) hle1
    refine Dimension.sub_eq_sqrt_mul_sub_of_cut (u := fun k s => U k s ω) (w := fun s => W s ω)
      (b := fun s => B s ω) (bh := fun s => Bh s ω) hκ0 hδc σw (hint (σ + s')) (hfint (σ + s')) ?_ ?_
      (hid _ hle1) (hid _ hle2) hgap
    · have h1 := hweq (σ + s') (hT _)
      rw [hsplit]; linarith
    · have h1 := hweq σ (hT _)
      rw [hsplit]; linarith
  -- the bootstrap on `[0, τ]`
  set g : ℝ → ℝ := fun t => min (W (σ + t.toNNReal) ω - VL 0 (σ + t.toNNReal) ω)
    (VR 0 (σ + t.toNNReal) ω - W (σ + t.toNNReal) ω) with hgdef
  have hcσ : Continuous fun t : ℝ => σ + t.toNNReal := continuous_const.add continuous_real_toNNReal
  have hgc : ContinuousOn g (Icc 0 τ) :=
    (((hwc.comp hcσ).sub (hvLc'.comp hcσ)).min ((hvRc'.comp hcσ).sub (hwc.comp hcσ))).continuousOn
  have hgapOf : ∀ t ∈ Icc (0 : ℝ) τ, (∀ s ∈ Icc (0 : ℝ) t, δc ≤ g s) →
      ∀ s : ℝ≥0, σ ≤ s → s ≤ σ + t.toNNReal → ∀ k, δc ≤ |W s ω - U k s ω| := by
    intro t ht hg s hσs hs k
    set r : ℝ := (s : ℝ) - σ with hr
    have hr0 : 0 ≤ r := by rw [hr]; exact sub_nonneg.2 (by exact_mod_cast hσs)
    have hrt : r ≤ t := by
      have h1 : (s : ℝ) ≤ σ + t := by
        have := (NNReal.coe_le_coe.2 hs)
        rwa [NNReal.coe_add, Real.coe_toNNReal _ ht.1] at this
      rw [hr]; linarith
    have hsr : σ + r.toNNReal = s := by
      rw [← NNReal.coe_inj, NNReal.coe_add, Real.coe_toNNReal _ hr0, hr]; ring
    have hgr := hg r ⟨hr0, hrt⟩
    simp only [hgdef, hsr, le_min_iff] at hgr
    cases k using Fin.addCases with
    | left i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      show δc ≤ |W s ω - allMarks VL VR (Fin.castAdd 1 0) s ω|
      simp only [allMarks, Fin.addCases_left]
      rw [abs_of_nonneg (by linarith [hgr.1])]
      exact hgr.1
    | right i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      show δc ≤ |W s ω - allMarks VL VR (Fin.natAdd 1 0) s ω|
      simp only [allMarks, Fin.addCases_right]
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hgr.2])]
      exact hgr.2
  have hσ0 : (σ : ℝ≥0) + (0 : ℝ).toNNReal = σ := by simp
  have hboot := forall_le_of_bootstrap (c := δ) (δ := δc) hgc (by rw [hδcdef]; linarith)
    (by
      simp only [hgdef, hσ0, le_min_iff]
      constructor <;> linarith)
    (fun t ht hg => by
      have hid' := hincr t.toNNReal (Real.toNNReal_le_toNNReal ht.2) (hgapOf t ht hg)
      have hb := hbd t ht
      simp only [drive, B'] at hb
      rw [← hid'] at hb
      have hR' := le_of_forceR (fun s => hwvR s (hT s) 0) (fun s => hgapR s (hT s) 0)
        (fun s => hvReq s (hT s) 0) (le_self_add : σ ≤ σ + t.toNNReal)
      have hL' := le_of_forceL (fun s => hvLw s (hT s) 0) (fun s => hgapL s (hT s) 0)
        (fun s => hvLeq s (hT s) 0) (le_self_add : σ ≤ σ + t.toNNReal)
      simp only [hgdef, le_min_iff]
      constructor <;> linarith [hb.1, hb.2])
  -- the future driver is `√κ B'` on `[0, τ]`
  set W₀ : ℝ → ℝ := fun s => W s.toNNReal ω with hW₀
  have hW₀c : Continuous W₀ := hwc.comp continuous_real_toNNReal
  have hW₀0 : W₀ 0 = 0 := by simp [hW₀, hw0]
  have hagree : ∀ r ∈ Icc (0 : ℝ) τ, drive κ B' ω r = shiftDrive W₀ σ r := by
    intro r hr
    have hid' := hincr r.toNNReal (Real.toNNReal_le_toNNReal hr.2)
      (hgapOf r hr fun s hs => le_trans (by rw [hδcdef]; linarith) (hboot s ⟨hs.1, hs.2.trans hr.2⟩))
    simp only [drive, B', shiftDrive, hW₀]
    rw [Sec2.Restart.toNNReal_add_of_nonneg σ hr.1, Real.toNNReal_coe, hid']
  have hdc : Continuous (drive κ B' ω) := hdrive ▸ drive_continuous (hB''c ω)
  have hsc : Continuous (shiftDrive W₀ σ) := continuous_shiftDrive hW₀c σ
  have hcol' : ZhanGT4.HasRealCollar (shiftDrive W₀ σ) τ :=
    hasRealCollar_congr hdc hsc hτ.le hagree (hττ' ▸ hcolω.2)
  obtain ⟨ε', hε', hball⟩ := halfBall_of_cluster_of_collar hW₀c hW₀0 σ.coe_nonneg hτ.le hε hm₁ hm₂ hcl
    (isSwallowedBy_congr hagree hdm) (isSwallowedBy_congr hagree hdp) hcol'
  refine hnot ⟨σ + τ', ε', hε', fun z hz hzn => ?_⟩
  have e : ((σ + τ' : ℝ≥0) : ℝ) = (σ : ℝ) + τ := by rw [NNReal.coe_add, hττ']
  rw [e]
  exact hball z hz hzn

end InteractingSLE.LP.LP4HB
