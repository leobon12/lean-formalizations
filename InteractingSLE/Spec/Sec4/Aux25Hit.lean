/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Scale
import InteractingSLE.Spec.Sec4.Aux25Mart
import InteractingSLE.Spec.Sec2.AddMarksFlow

/-!
# Aux. lemma 25: the hitting bound for the one-group process

Packet PROVE-AUX25. Driven by a Brownian motion `B` (every path continuous), the one-group process with weight
`ρ > −2`, initial force gap `g₀` (random, `𝓖_0`-measurable) and initial passive gap `y₀`, is realized by two
tamed real flows (`Sec2.markFlow`, PROVE-SEC2-GIR2), with the reciprocal cut below at `c > 0`:

* `û = g₀ + U₁ − √κ B`, `U₁ = ∫ (2 + ρ)/max(û, c)` (the force gap);
* `X = y₀ + U₂ + (ρ/(2 + ρ)) U₁ − √κ B`, `U₂ = ∫ 2/max(X, c)` (the passive gap).

Both are defined for every `ω`, continuous and adapted. The state `(0, V, ·, Y)` with `V = g₀ + U₁` and
`Y = y₀ + U₂ + (ρ/(2 + ρ)) U₁` solves `Λ' = Ψ(Λ, B)`, and in the region `û ≥ c`, `X ≥ c` the field `Ψ` is the
one-group field, along which the scale observable `F(û/X)` has no drift (`Aux25Scale.lean`). Optional
stopping (`Aux25Mart.lean`) at the exit from the compact region `K_L` gives

  `S∞ · Q(S ∩ {û_σ ≤ X_σ/2}) ≤ ∫_S (S∞ − F(g₀/y₀)) dQ`,  `S ∈ 𝓖_0`,  `S∞ = ∫_{1/2}^1 g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux25

section Tamed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- The tamed force increment `U₁ = ∫ (2 + ρ)/max(û, c)`, `û = g₀ + U₁ − √κ B`. -/
def tU1 (sk ρ c : ℝ) (g₀ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Sec2.markFlow (Bessel.regDrift (2 + ρ) c) 0 (fun _ => ⊤) (fun t ω => sk * B t ω - g₀ ω)

/-- The tamed passive increment `U₂ = ∫ 2/max(X, c)`, `X = y₀ + U₂ + (ρ/(2 + ρ)) U₁ − √κ B`. -/
def tU2 (sk ρ c y₀ : ℝ) (g₀ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Sec2.markFlow (Bessel.regDrift 2 c) 0 (fun _ => ⊤)
    (fun t ω => sk * B t ω - y₀ - ρ / (2 + ρ) * tU1 sk ρ c g₀ B t ω)

/-- The tamed state `(0, V, ·, Y)`. -/
def tState (sk ρ c y₀ : ℝ) (g₀ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : StateE 0 1 :=
  (0, fun _ => g₀ ω + tU1 sk ρ c g₀ B t ω, fun _ => 0,
    y₀ + tU2 sk ρ c y₀ g₀ B t ω + ρ / (2 + ρ) * tU1 sk ρ c g₀ B t ω)

/-- The tamed field. -/
def tPsi (sk ρ c : ℝ) (p : StateE 0 1 × ℝ) : StateE 0 1 :=
  (0, fun _ => Bessel.regDrift (2 + ρ) c (gapU sk 0 p), fun _ => 0,
    Bessel.regDrift 2 c (gapX sk p) + ρ / (2 + ρ) * Bessel.regDrift (2 + ρ) c (gapU sk 0 p))

variable {sk ρ c y₀ : ℝ} {g₀ : Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}

theorem lipschitz_regDrift' (hρ : -2 < ρ) (hc : 0 < c) :
    LipschitzWith (Real.toNNReal ((2 + ρ) / c ^ 2)) (Bessel.regDrift (2 + ρ) c) :=
  Bessel.lipschitzWith_regDrift (by linarith) hc

theorem continuous_tPsi (hρ : -2 < ρ) (hc : 0 < c) : Continuous (tPsi sk ρ c) := by
  have h1 := (lipschitz_regDrift' hρ hc).continuous
  have h2 := (Bessel.lipschitzWith_regDrift (c := 2) (by norm_num) hc).continuous
  have hU := continuous_gapU (nL := 0) sk (0 : Fin 1)
  have hX := continuous_gapX (nL := 0) (nR := 1) sk
  unfold tPsi
  refine continuous_const.prodMk (Continuous.prodMk ?_ (continuous_const.prodMk ?_))
  · exact continuous_pi fun _ => h1.comp hU
  · exact (h2.comp hX).add (continuous_const.mul (h1.comp hU))

/-- The path facts of the tamed flows for one `ω` (every `ω` when `B` has continuous paths). -/
theorem tU_facts (hρ : -2 < ρ) (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous (fun t => tU1 sk ρ c g₀ B t ω) ∧
      (∀ t : ℝ≥0, tU1 sk ρ c g₀ B t ω = ∫ s in (0 : ℝ)..t,
        Bessel.regDrift (2 + ρ) c (tU1 sk ρ c g₀ B s.toNNReal ω - (sk * B s.toNNReal ω - g₀ ω))) ∧
      Continuous (fun t => tU2 sk ρ c y₀ g₀ B t ω) ∧
      ∀ t : ℝ≥0, tU2 sk ρ c y₀ g₀ B t ω = ∫ s in (0 : ℝ)..t,
        Bessel.regDrift 2 c (tU2 sk ρ c y₀ g₀ B s.toNNReal ω -
          (sk * B s.toNNReal ω - y₀ - ρ / (2 + ρ) * tU1 sk ρ c g₀ B s.toNNReal ω)) := by
  have hlip1 := lipschitz_regDrift' hρ hc
  have hlip2 := Bessel.lipschitzWith_regDrift (c := 2) (by norm_num) hc
  have hb1 : ∀ x, |Bessel.regDrift (2 + ρ) c x| ≤ (2 + ρ) / c := fun x =>
    Bessel.abs_regDrift_le (by linarith) hc x
  have hb2 : ∀ x, |Bessel.regDrift 2 c x| ≤ 2 / c := fun x =>
    Bessel.abs_regDrift_le (by norm_num) hc x
  have hW1 : ContinuousOn (fun s => sk * B s ω - g₀ ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} :=
    ((continuous_const.mul hBc).sub continuous_const).continuousOn
  obtain ⟨h1c, h1eq⟩ := Sec2.markFlow_eq_of_continuousOn (y := 0) (ζ := fun _ : Ω => (⊤ : ℝ≥0∞))
    (W := fun t ω => sk * B t ω - g₀ ω) hlip1 hb1 hW1
  have h1c' : Continuous fun t => tU1 sk ρ c g₀ B t ω := by
    rw [← continuousOn_univ]
    exact h1c.mono fun s _ => ENNReal.coe_lt_top
  have hW2 : ContinuousOn (fun s => sk * B s ω - y₀ - ρ / (2 + ρ) * tU1 sk ρ c g₀ B s ω)
      {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} :=
    (((continuous_const.mul hBc).sub continuous_const).sub (continuous_const.mul h1c')).continuousOn
  obtain ⟨h2c, h2eq⟩ := Sec2.markFlow_eq_of_continuousOn (y := 0) (ζ := fun _ : Ω => (⊤ : ℝ≥0∞))
    (W := fun t ω => sk * B t ω - y₀ - ρ / (2 + ρ) * tU1 sk ρ c g₀ B t ω) hlip2 hb2 hW2
  refine ⟨h1c', fun t => ?_, ?_, fun t => ?_⟩
  · have := h1eq t ENNReal.coe_lt_top
    rw [zero_add] at this
    exact this
  · rw [← continuousOn_univ]
    exact h2c.mono fun s _ => ENNReal.coe_lt_top
  · have := h2eq t ENNReal.coe_lt_top
    rw [zero_add] at this
    exact this

end Tamed

/-! ### The state equation and adaptedness -/

section State

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
variable {sk ρ c y₀ : ℝ} {g₀ : Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- Integrals of `StateE 0 1`-valued paths, componentwise. -/
theorem integral_stateE01 {a b : ℝ} {f : ℝ → StateE 0 1} (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).1 = ∫ x in a..b, (f x).1 ∧
      (∫ x in a..b, f x).2.1 0 = ∫ x in a..b, (f x).2.1 0 ∧
      (∫ x in a..b, f x).2.2.2 = ∫ x in a..b, (f x).2.2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((ContinuousLinearMap.fst ℝ ℝ _).intervalIntegral_comp_comm hf).symm
  · have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ((Fin 0 → ℝ) × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ _))).intervalIntegral_comp_comm hf
    exact h.symm
  · have h := ((ContinuousLinearMap.snd ℝ (Fin 0 → ℝ) ℝ).comp
      ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 0 → ℝ) × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ _))).intervalIntegral_comp_comm hf
    exact h.symm

theorem stateE01_ext {p q : StateE 0 1} (h1 : p.1 = q.1) (h2 : p.2.1 0 = q.2.1 0)
    (h3 : p.2.2.2 = q.2.2.2) : p = q := by
  refine Prod.ext h1 (Prod.ext (funext fun i => ?_) (Prod.ext (Subsingleton.elim _ _) h3))
  rw [Fin.fin_one_eq_zero i]
  exact h2

theorem gapU_tState (t : ℝ≥0) (ω : Ω) :
    gapU sk 0 (statePath (tState sk ρ c y₀ g₀ B) B t ω) =
      tU1 sk ρ c g₀ B t ω - (sk * B t ω - g₀ ω) := by
  simp only [gapU, stW, statePath, tState]; ring

theorem gapX_tState (t : ℝ≥0) (ω : Ω) :
    gapX sk (statePath (tState sk ρ c y₀ g₀ B) B t ω) =
      tU2 sk ρ c y₀ g₀ B t ω - (sk * B t ω - y₀ - ρ / (2 + ρ) * tU1 sk ρ c g₀ B t ω) := by
  simp only [gapX, stW, statePath, tState]; ring

theorem continuous_tState (hρ : -2 < ρ) (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous fun t => tState sk ρ c y₀ g₀ B t ω := by
  obtain ⟨h1, -, h2, -⟩ := tU_facts (y₀ := y₀) (g₀ := g₀) (sk := sk) hρ hc hBc
  unfold tState
  refine continuous_const.prodMk (Continuous.prodMk ?_ (continuous_const.prodMk ?_))
  · exact continuous_pi fun _ => continuous_const.add h1
  · exact (continuous_const.add h2).add (continuous_const.mul h1)

/-- **The state equation** `Λ_t = Λ_0 + ∫₀ᵗ Ψ(Λ_s, B_s) ds`, for every `ω` along which `B` is continuous. -/
theorem tState_eq (hρ : -2 < ρ) (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) (t : ℝ≥0) :
    tState sk ρ c y₀ g₀ B t ω = tState sk ρ c y₀ g₀ B 0 ω +
      ∫ s in (0 : ℝ)..t, tPsi sk ρ c (statePath (tState sk ρ c y₀ g₀ B) B s.toNNReal ω) := by
  obtain ⟨h1c, h1eq, h2c, h2eq⟩ := tU_facts (y₀ := y₀) (g₀ := g₀) (sk := sk) hρ hc hBc
  have hpc : Continuous fun s : ℝ => statePath (tState sk ρ c y₀ g₀ B) B s.toNNReal ω :=
    ((continuous_tState hρ hc hBc).prodMk hBc).comp continuous_real_toNNReal
  have hint : IntervalIntegrable (fun s : ℝ =>
      tPsi sk ρ c (statePath (tState sk ρ c y₀ g₀ B) B s.toNNReal ω)) volume 0 t :=
    ((continuous_tPsi hρ hc).comp hpc).intervalIntegrable _ _
  obtain ⟨e1, e2, e3⟩ := integral_stateE01 hint
  have hz1 : tU1 sk ρ c g₀ B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω
  have hz2 : tU2 sk ρ c y₀ g₀ B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω
  refine stateE01_ext ?_ ?_ ?_
  · rw [Prod.fst_add, e1]
    simp [tState, tPsi]
  · rw [Prod.snd_add, Prod.fst_add, Pi.add_apply, e2]
    simp only [tState, tPsi, hz1, add_zero]
    rw [h1eq t]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    show _ = Bessel.regDrift (2 + ρ) c (gapU sk 0 _)
    rw [gapU_tState]
  · rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, e3]
    simp only [tState, tPsi, hz1, hz2, add_zero, mul_zero]
    rw [h2eq t, h1eq t]
    have hi1 : IntervalIntegrable (fun s : ℝ => Bessel.regDrift 2 c
        (gapX sk (statePath (tState sk ρ c y₀ g₀ B) B s.toNNReal ω))) volume 0 t :=
      ((Bessel.lipschitzWith_regDrift (c := 2) (by norm_num) hc).continuous.comp
        ((continuous_gapX sk).comp hpc)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s : ℝ => Bessel.regDrift (2 + ρ) c
        (gapU sk 0 (statePath (tState sk ρ c y₀ g₀ B) B s.toNNReal ω))) volume 0 t :=
      ((lipschitz_regDrift' hρ hc).continuous.comp
        ((continuous_gapU sk 0).comp hpc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 (hi2.const_mul _), intervalIntegral.integral_const_mul]
    simp only [gapU_tState, gapX_tState]
    ring

/-- `AdaptedBefore` for the infinite lifetime is adaptedness. -/
theorem adaptedBefore_top {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, Measurable[𝓖 t] (X t)) :
    AdaptedBefore 𝓖 (fun _ => ⊤) X := fun t A hA => by
  have h : {ω | (t : ℝ≥0∞) < ⊤ ∧ X t ω ∈ A} = X t ⁻¹' A := by
    ext ω; simp
  rw [h]
  exact hX t hA

theorem measurable_tU1 (hρ : -2 < ρ) (hc : 0 < c) (hB : ∀ t, Measurable[𝓖 t] (B t))
    (hg₀ : Measurable[𝓖 0] g₀) (t : ℝ≥0) : Measurable[𝓖 t] (tU1 sk ρ c g₀ B t) := by
  refine Sec2.measurable_markFlow (lipschitz_regDrift' hρ hc).continuous.measurable
    (adaptedBefore_top fun s => ?_) t
  exact ((hB s).const_mul sk).sub (hg₀.mono (𝓖.mono zero_le) le_rfl)

theorem measurable_tU2 (hρ : -2 < ρ) (hc : 0 < c) (hB : ∀ t, Measurable[𝓖 t] (B t))
    (hg₀ : Measurable[𝓖 0] g₀) (t : ℝ≥0) : Measurable[𝓖 t] (tU2 sk ρ c y₀ g₀ B t) := by
  refine Sec2.measurable_markFlow (Bessel.lipschitzWith_regDrift (c := 2) (by norm_num)
    hc).continuous.measurable (adaptedBefore_top fun s => ?_) t
  exact (((hB s).const_mul sk).sub measurable_const).sub
    ((measurable_tU1 hρ hc hB hg₀ s).const_mul _)

theorem measurable_tState (hρ : -2 < ρ) (hc : 0 < c) (hB : ∀ t, Measurable[𝓖 t] (B t))
    (hg₀ : Measurable[𝓖 0] g₀) (t : ℝ≥0) : Measurable[𝓖 t] (tState sk ρ c y₀ g₀ B t) := by
  have h1 := measurable_tU1 (sk := sk) hρ hc hB hg₀ t
  have h2 := measurable_tU2 (sk := sk) (y₀ := y₀) hρ hc hB hg₀ t
  have hg : Measurable[𝓖 t] g₀ := hg₀.mono (𝓖.mono zero_le) le_rfl
  unfold tState
  refine measurable_const.prodMk (Measurable.prodMk ?_ (measurable_const.prodMk ?_))
  · exact @Measurable.of_eval Ω (Fin 1) (fun _ => ℝ) (𝓖 t) _ _ fun _ => hg.add h1
  · exact (measurable_const.add h2).add (h1.const_mul _)

end State

/-! ### The localization region -/

section Region

variable {sk c L : ℝ}

/-- The compact region kept up to the exit: `u ∈ [1/2, 1 − 1/L]`, `X ∈ [2c, L]`, `‖p‖ ≤ L`. -/
def keepK (sk c L : ℝ) : Set (StateE 0 1 × ℝ) :=
  {p | gapX sk p / 2 ≤ gapU sk 0 p ∧ gapU sk 0 p ≤ (1 - 1 / L) * gapX sk p ∧ 2 * c ≤ gapX sk p ∧
    gapX sk p ≤ L ∧ ‖p‖ ≤ L}

/-- The exit set. -/
def exitC (sk c L : ℝ) : Set (StateE 0 1 × ℝ) :=
  {p | gapU sk 0 p ≤ gapX sk p / 2 ∨ (1 - 1 / L) * gapX sk p ≤ gapU sk 0 p ∨ gapX sk p ≤ 2 * c ∨
    L ≤ gapX sk p ∨ L ≤ ‖p‖}

theorem isClosed_keepK : IsClosed (keepK sk c L) := by
  have hU := continuous_gapU (nL := 0) sk (0 : Fin 1)
  have hX := continuous_gapX (nL := 0) (nR := 1) sk
  simp only [keepK, ofPred_and]
  exact (isClosed_le (hX.div_const 2) hU).inter ((isClosed_le hU (continuous_const.mul hX)).inter
    ((isClosed_le continuous_const hX).inter ((isClosed_le hX continuous_const).inter
      (isClosed_le continuous_norm continuous_const))))

theorem isClosed_exitC : IsClosed (exitC sk c L) := by
  have hU := continuous_gapU (nL := 0) sk (0 : Fin 1)
  have hX := continuous_gapX (nL := 0) (nR := 1) sk
  simp only [exitC, ofPred_or]
  exact (isClosed_le hU (hX.div_const 2)).union ((isClosed_le (continuous_const.mul hX) hU).union
    ((isClosed_le hX continuous_const).union ((isClosed_le continuous_const hX).union
      (isClosed_le continuous_const continuous_norm))))

theorem closure_compl_exitC_subset : closure (exitC sk c L)ᶜ ⊆ keepK sk c L := by
  refine closure_minimal (fun p hp => ?_) isClosed_keepK
  simp only [exitC, mem_compl_iff, mem_ofPred_eq, not_or, not_le] at hp
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.1.le, hp.2.2.2.2.le⟩

theorem isCompact_keepK : IsCompact (keepK sk c L) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_keepK
    (Metric.isBounded_closedBall (x := (0 : StateE 0 1 × ℝ)) (r := L) |>.subset fun p hp => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hp.2.2.2.2)

theorem keepK_subset (hc : 0 < c) (hL : 0 < L) : keepK sk c L ⊆ scaleRegion sk 0 := by
  intro p hp
  obtain ⟨h1, h2, h3, -, -⟩ := hp
  have hX : 0 < gapX sk p := by linarith
  refine ⟨by linarith, ?_⟩
  have : 0 < 1 / L := by positivity
  nlinarith

/-- On the region the tamed field is the one-group field, so the observable has no drift. -/
theorem itoGen_tPsi_eq_zero {κ ρ α β : ℝ} (hκ : 0 < κ) (hsk : sk ^ 2 = κ) (hρ : -2 < ρ)
    (hα : α = 2 * (2 + ρ) / κ) (hβ : β = 2 * (4 + ρ - κ) / κ) (hc : 0 < c) (hL : 0 < L)
    {p : StateE 0 1 × ℝ} (hp : p ∈ keepK sk c L) :
    Ito.itoGen (scaleObs α β sk 0) p (tPsi sk ρ c p) = 0 := by
  have hp' := hp
  obtain ⟨h1, -, h3, -, -⟩ := hp'
  have hUc : c ≤ gapU sk 0 p := by linarith
  have hXc : c ≤ gapX sk p := by linarith
  have h2ρ : (2 + ρ) ≠ 0 := by linarith
  refine itoGen_scaleObs_eq_zero hκ hsk hα hβ (keepK_subset hc hL hp) ?_ ?_
  · show Bessel.regDrift (2 + ρ) c (gapU sk 0 p) - 0 = _
    rw [Bessel.regDrift_of_le hUc, sub_zero]
  · show Bessel.regDrift 2 c (gapX sk p) + ρ / (2 + ρ) * Bessel.regDrift (2 + ρ) c (gapU sk 0 p) - 0 = _
    rw [Bessel.regDrift_of_le hUc, Bessel.regDrift_of_le hXc, sub_zero]
    field_simp

end Region

/-! ### The hitting bound -/

section Hit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ} {κ sk ρ α β c y₀ L : ℝ} {g₀ : Ω → ℝ} {N : ℝ≥0}

/-- **The hitting bound.** For the tamed one-group process with weight `ρ > −2` (and `β > −1`, i.e.
`ρ > κ/2 − 4`), stopped at its exit `σ` from `keepK` before `N`, for every `S ∈ 𝓖_0`,
`S∞ · Q(S ∩ {û_σ ≤ X_σ/2}) ≤ ∫_S (S∞ − F(g₀/y₀)) dQ`. -/
theorem hit_bound (hB : IsFilteredBrownianReal 𝓖 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hκ : 0 < κ) (hsk : sk ^ 2 = κ) (hρ : -2 < ρ)
    (hα : α = 2 * (2 + ρ) / κ) (hβ : β = 2 * (4 + ρ - κ) / κ) (hβ1 : -1 < β) (hc : 0 < c)
    (hL : 0 < L) (hg₀ : Measurable[𝓖 0] g₀)
    (hstart : ∀ ω, statePath (tState sk ρ c y₀ g₀ B) B 0 ω ∉ exitC sk c L)
    {S : Set Ω} (hS : MeasurableSet[𝓖 0] S) :
    scaleTop α β * Q.real (S ∩ {ω | gapU sk 0 (statePath (tState sk ρ c y₀ g₀ B) B
        (hitStop (tState sk ρ c y₀ g₀ B) B (exitC sk c L) N ω) ω) ≤
          gapX sk (statePath (tState sk ρ c y₀ g₀ B) B
            (hitStop (tState sk ρ c y₀ g₀ B) B (exitC sk c L) N ω) ω) / 2}) ≤
      ∫ ω in S, (scaleTop α β - scaleFn α β (g₀ ω / y₀)) ∂Q := by
  classical
  have hQ := hB.isProbabilityMeasure'
  set Λ := tState sk ρ c y₀ g₀ B with hΛdef
  set σ := hitStop Λ B (exitC sk c L) N with hσdef
  set Φ := scaleObs α β sk (0 : Fin 1) with hΦdef
  have hΛc : ∀ ω, Continuous (Λ · ω) := fun ω => continuous_tState hρ hc (hBc ω)
  have hΛm : ∀ t, Measurable[𝓖 t] (Λ t) := measurable_tState hρ hc hB.2.1 hg₀
  have hmemK : ∀ ω, statePath Λ B (σ ω) ω ∈ keepK sk c L := fun ω =>
    mem_K_of_le_hitStop hΛc hBc closure_compl_exitC_subset (hstart ω) le_rfl
  have hopt := setIntegral_hitStop_eq (Q := Q) (N := N) (Ψ := tPsi sk ρ c) (Φ := Φ) hB hBc hB0 hΛm
    hΛc (fun ω t => tState_eq hρ hc (hBc ω) t) (isOpen_scaleRegion sk 0)
    (contDiffOn_scaleObs α β sk 0) (continuous_tPsi hρ hc).continuousOn isCompact_keepK
    (keepK_subset hc hL) isClosed_exitC closure_compl_exitC_subset hstart
    (fun p hp => itoGen_tPsi_eq_zero hκ hsk hρ hα hβ hc hL hp) hS
  -- values of the observable on the region
  have hrat : ∀ p ∈ keepK sk c L, gapU sk 0 p / gapX sk p ∈ Icc (1 / 2 : ℝ) 1 := by
    intro p hp
    have hX : 0 < gapX sk p := by linarith [hp.2.2.1]
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hX]; linarith [hp.1]
    · rw [div_le_one hX]; exact (keepK_subset hc hL hp).2.le
  have hΦle : ∀ p ∈ keepK sk c L, Φ p ≤ scaleTop α β := fun p hp =>
    scaleFn_le_scaleTop hβ1 (hrat p hp)
  have hΦ0 : ∀ p ∈ keepK sk c L, 0 ≤ Φ p := fun p hp => scaleFn_nonneg (hrat p hp)
  have hΦhit : ∀ p ∈ keepK sk c L, gapU sk 0 p ≤ gapX sk p / 2 → Φ p = 0 := by
    intro p hp hle
    have hX : 0 < gapX sk p := by linarith [hp.2.2.1]
    have : gapU sk 0 p / gapX sk p = 1 / 2 := by
      rw [div_eq_iff hX.ne']; linarith [hp.1]
    show scaleFn α β _ = 0
    rw [this, scaleFn_half]
  -- measurability of the stopped path
  have hσ := isStoppingTime_hitStop (N := N) (C := exitC sk c L) hB hBc hΛm hΛc isClosed_exitC
  have hpm : Measurable fun ω => statePath Λ B (σ ω) ω := by
    have h1 := Ito.measurable_stopped_of_agree (X := Λ) hσ hΛm (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : StateE 0 1) (fun _ _ _ _ => rfl)
      (fun ω _ => (hΛc ω).continuousOn) N
    have h2 := Ito.measurable_stopped_of_agree (X := B) hσ hB.2.1 (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : ℝ) (fun _ _ _ _ => rfl)
      (fun ω _ => (hBc ω).continuousOn) N
    have hmin : ∀ ω, min N (σ ω) = σ ω := fun ω => min_eq_right (hitStop_le ω)
    simp only [mem_univ, ↓reduceIte, ← hσdef, hmin] at h1 h2
    exact (h1.mono (𝓖.le N) le_rfl).prodMk (h2.mono (𝓖.le N) le_rfl)
  have hΦc : ContinuousOn Φ (keepK sk c L) :=
    (contDiffOn_scaleObs α β sk 0).continuousOn.mono (keepK_subset hc hL)
  have hΦm : Measurable fun ω => Φ (statePath Λ B (σ ω) ω) := by
    have : (fun ω => Φ (statePath Λ B (σ ω) ω)) =
        (keepK sk c L).piecewise Φ (fun _ => 0) ∘ fun ω => statePath Λ B (σ ω) ω := by
      funext ω; simp [hmemK ω]
    rw [this]
    exact (hΦc.measurable_piecewise continuousOn_const isClosed_keepK.measurableSet).comp hpm
  have hHm : MeasurableSet {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤
      gapX sk (statePath Λ B (σ ω) ω) / 2} :=
    measurableSet_le ((continuous_gapU sk 0).measurable.comp hpm)
      (((continuous_gapX sk).measurable.comp hpm).div_const 2)
  have hint1 : Integrable (fun ω => Φ (statePath Λ B (σ ω) ω)) Q :=
    Integrable.of_bound hΦm.aestronglyMeasurable (scaleTop α β) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 _ (hmemK ω))]; exact hΦle _ (hmemK ω))
  -- the start value
  have hstartK0 : ∀ ω, statePath Λ B 0 ω ∈ keepK sk c L := fun ω =>
    mem_K_of_le_hitStop (N := N) hΛc hBc closure_compl_exitC_subset (hstart ω) zero_le
  have hp0m : Measurable fun ω => ((Λ 0 ω, (0 : ℝ)) : StateE 0 1 × ℝ) :=
    ((hΛm 0).mono (𝓖.le 0) le_rfl).prodMk measurable_const
  have hΦ0m : Measurable fun ω => Φ (Λ 0 ω, 0) := by
    have : (fun ω => Φ (Λ 0 ω, 0)) =
        (keepK sk c L).piecewise Φ (fun _ => 0) ∘ fun ω => ((Λ 0 ω, (0 : ℝ)) : StateE 0 1 × ℝ) := by
      funext ω
      have hk : ((Λ 0 ω, (0 : ℝ)) : StateE 0 1 × ℝ) ∈ keepK sk c L := by
        have := hstartK0 ω; simpa [statePath, hB0] using this
      simp [hk]
    rw [this]
    exact (hΦc.measurable_piecewise continuousOn_const isClosed_keepK.measurableSet).comp hp0m
  have hint0 : Integrable (fun ω => Φ (Λ 0 ω, 0)) Q := by
    refine Integrable.of_bound hΦ0m.aestronglyMeasurable (scaleTop α β)
      (Eventually.of_forall fun ω => ?_)
    have hk : ((Λ 0 ω, (0 : ℝ)) : StateE 0 1 × ℝ) ∈ keepK sk c L := by
      have := hstartK0 ω; simpa [statePath, hB0] using this
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 _ hk)]
    exact hΦle _ hk
  have hstartK : ∀ ω, statePath Λ B 0 ω ∈ keepK sk c L := fun ω =>
    mem_K_of_le_hitStop (N := N) hΛc hBc closure_compl_exitC_subset (hstart ω) zero_le
  have hstart_eq : ∀ ω, Φ (Λ 0 ω, 0) = scaleFn α β (g₀ ω / y₀) := fun ω => by
    have hz1 : tU1 sk ρ c g₀ B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω
    have hz2 : tU2 sk ρ c y₀ g₀ B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω
    simp only [hΦdef, scaleObs, gapU, gapX, stW, hΛdef, tState, hz1, hz2]
    congr 1
    simp
  -- conclude
  have hle : ∀ ω, scaleTop α β * S.indicator (fun _ => (1 : ℝ)) ω *
      {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤ gapX sk (statePath Λ B (σ ω) ω) / 2}.indicator
        (fun _ => (1 : ℝ)) ω ≤ S.indicator (fun ω => scaleTop α β - Φ (statePath Λ B (σ ω) ω)) ω := by
    intro ω
    have hk := hmemK ω
    by_cases hωS : ω ∈ S
    · by_cases hωH : gapU sk 0 (statePath Λ B (σ ω) ω) ≤ gapX sk (statePath Λ B (σ ω) ω) / 2
      · simp only [indicator_of_mem hωS, indicator_of_mem (show ω ∈ {ω | gapU sk 0 (statePath Λ B
          (σ ω) ω) ≤ gapX sk (statePath Λ B (σ ω) ω) / 2} from hωH), hΦhit _ hk hωH]
        simp
      · simp only [indicator_of_notMem (show ω ∉ {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤
          gapX sk (statePath Λ B (σ ω) ω) / 2} from hωH), indicator_of_mem hωS, mul_zero]
        linarith [hΦle _ hk]
    · simp [indicator_of_notMem hωS]
  have hS' : MeasurableSet S := 𝓖.le 0 S hS
  have hlhs : scaleTop α β * Q.real (S ∩ {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤
      gapX sk (statePath Λ B (σ ω) ω) / 2}) = ∫ ω, scaleTop α β * S.indicator (fun _ => (1 : ℝ)) ω *
        {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤ gapX sk (statePath Λ B (σ ω) ω) / 2}.indicator
          (fun _ => (1 : ℝ)) ω ∂Q := by
    have e : (fun ω => scaleTop α β * S.indicator (fun _ => (1 : ℝ)) ω *
        {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤ gapX sk (statePath Λ B (σ ω) ω) / 2}.indicator
          (fun _ => (1 : ℝ)) ω) = fun ω => scaleTop α β * (S ∩ {ω | gapU sk 0 (statePath Λ B (σ ω) ω)
            ≤ gapX sk (statePath Λ B (σ ω) ω) / 2}).indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤
        gapX sk (statePath Λ B (σ ω) ω) / 2} <;> simp [h1, h2]
    rw [e, integral_const_mul, integral_indicator (hS'.inter hHm)]
    simp [measureReal_def]
  rw [hlhs]
  calc ∫ ω, scaleTop α β * S.indicator (fun _ => (1 : ℝ)) ω *
        {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤ gapX sk (statePath Λ B (σ ω) ω) / 2}.indicator
          (fun _ => (1 : ℝ)) ω ∂Q
      ≤ ∫ ω, S.indicator (fun ω => scaleTop α β - Φ (statePath Λ B (σ ω) ω)) ω ∂Q := by
        refine integral_mono ?_ ?_ hle
        · refine Integrable.of_bound ?_ (|scaleTop α β|) (Eventually.of_forall fun ω => ?_)
          · exact ((measurable_const.mul (measurable_const.indicator hS')).mul
              (measurable_const.indicator hHm)).aestronglyMeasurable
          · by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ {ω | gapU sk 0 (statePath Λ B (σ ω) ω) ≤
              gapX sk (statePath Λ B (σ ω) ω) / 2} <;> simp [h1, h2]
        · exact ((integrable_const _).sub hint1).indicator hS'
    _ = ∫ ω in S, (scaleTop α β - Φ (statePath Λ B (σ ω) ω)) ∂Q := integral_indicator hS'
    _ = ∫ ω in S, (scaleTop α β - Φ (Λ 0 ω, 0)) ∂Q := by
        rw [integral_sub (integrable_const _) hint1.integrableOn,
          integral_sub (integrable_const _) hint0.integrableOn, hopt]
    _ = ∫ ω in S, (scaleTop α β - scaleFn α β (g₀ ω / y₀)) ∂Q := by simp only [hstart_eq]

end Hit

/-! ### Congruence and measurability -/

section Congr

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {sk ρ c y₀ : ℝ} {B : ℝ≥0 → Ω → ℝ}

theorem tU1_congr {g₀ g₀' : Ω → ℝ} {ω : Ω} (h : g₀ ω = g₀' ω) (t : ℝ≥0) :
    tU1 sk ρ c g₀ B t ω = tU1 sk ρ c g₀' B t ω := by
  simp only [tU1, Sec2.markFlow, Sec2.markEuler, Girsanov.killed, h]

theorem tU2_congr {g₀ g₀' : Ω → ℝ} {ω : Ω} (h : g₀ ω = g₀' ω) (t : ℝ≥0) :
    tU2 sk ρ c y₀ g₀ B t ω = tU2 sk ρ c y₀ g₀' B t ω := by
  simp only [tU2, Sec2.markFlow, Sec2.markEuler, Girsanov.killed, tU1_congr h]

theorem tState_congr {g₀ g₀' : Ω → ℝ} {ω : Ω} (h : g₀ ω = g₀' ω) (t : ℝ≥0) :
    tState sk ρ c y₀ g₀ B t ω = tState sk ρ c y₀ g₀' B t ω := by
  simp only [tState, tU1_congr h, tU2_congr h, h]

omit mΩ in
theorem hittingBtwn_congr_at {β : Type*} {X Y : ℝ≥0 → Ω → β} {C : Set β} {n m : ℝ≥0} {ω : Ω}
    (h : ∀ i, X i ω = Y i ω) : hittingBtwn X C n m ω = hittingBtwn Y C n m ω := by
  have hs : {i | X i ω ∈ C} = {i | Y i ω ∈ C} := by ext i; simp [h i]
  unfold hittingBtwn
  split_ifs with h1 h2 h2
  · rw [hs]
  · exact absurd (h1.imp fun j hj => ⟨hj.1, h j ▸ hj.2⟩) h2
  · exact absurd (h2.imp fun j hj => ⟨hj.1, (h j).symm ▸ hj.2⟩) h1
  · rfl

theorem hitStop_congr {g₀ g₀' : Ω → ℝ} {ω : Ω} (h : g₀ ω = g₀' ω) {C : Set (StateE 0 1 × ℝ)}
    {N : ℝ≥0} : hitStop (tState sk ρ c y₀ g₀ B) B C N ω = hitStop (tState sk ρ c y₀ g₀' B) B C N ω :=
  hittingBtwn_congr_at fun i => by simp only [statePath, tState_congr h]

end Congr

section HitMeas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ} {sk ρ c y₀ L : ℝ} {g₀ : Ω → ℝ} {N : ℝ≥0}

/-- The hit event is measurable. -/
theorem measurableSet_hit (hB : IsFilteredBrownianReal 𝓖 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hρ : -2 < ρ) (hc : 0 < c) (hg₀ : Measurable[𝓖 0] g₀) :
    MeasurableSet {ω | gapU sk 0 (statePath (tState sk ρ c y₀ g₀ B) B
        (hitStop (tState sk ρ c y₀ g₀ B) B (exitC sk c L) N ω) ω) ≤
          gapX sk (statePath (tState sk ρ c y₀ g₀ B) B
            (hitStop (tState sk ρ c y₀ g₀ B) B (exitC sk c L) N ω) ω) / 2} := by
  set Λ := tState sk ρ c y₀ g₀ B with hΛdef
  set σ := hitStop Λ B (exitC sk c L) N with hσdef
  have hΛc : ∀ ω, Continuous (Λ · ω) := fun ω => continuous_tState hρ hc (hBc ω)
  have hΛm : ∀ t, Measurable[𝓖 t] (Λ t) := measurable_tState hρ hc hB.2.1 hg₀
  have hσ := isStoppingTime_hitStop (N := N) (C := exitC sk c L) hB hBc hΛm hΛc isClosed_exitC
  have hpm : Measurable fun ω => statePath Λ B (σ ω) ω := by
    have h1 := Ito.measurable_stopped_of_agree (X := Λ) hσ hΛm (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : StateE 0 1) (fun _ _ _ _ => rfl)
      (fun ω _ => (hΛc ω).continuousOn) N
    have h2 := Ito.measurable_stopped_of_agree (X := B) hσ hB.2.1 (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : ℝ) (fun _ _ _ _ => rfl)
      (fun ω _ => (hBc ω).continuousOn) N
    have hmin : ∀ ω, min N (σ ω) = σ ω := fun ω => min_eq_right (hitStop_le ω)
    simp only [mem_univ, ↓reduceIte, ← hσdef, hmin] at h1 h2
    exact (h1.mono (𝓖.le N) le_rfl).prodMk (h2.mono (𝓖.le N) le_rfl)
  exact measurableSet_le ((continuous_gapU sk 0).measurable.comp hpm)
    (((continuous_gapX sk).measurable.comp hpm).div_const 2)

end HitMeas

end Aux25

end InteractingSLE
