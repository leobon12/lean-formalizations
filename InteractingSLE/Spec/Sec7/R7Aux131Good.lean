/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSeedOpen
import InteractingSLE.Spec.Sec6.Aux40InfLoewner

/-!
# Aux. lemma 131's terminal limit (CS13.2): the erased pocket traversal is transient

Packet PROVE-R7-AUX131. Specification §7.4.1, proof of Aux. lemma 131 (`source/spec/p385-432.md` L545, p. 415):
"The Jordan boundary homeomorphism sends the actual terminal endpoint of this complete traversal to infinity. Thus its
continuous curve has the limit (CS13.2). This is a property of the actual reference with the very same two-seed
driving law." Theorem R.7 (p. 477): "In its entry-to-exit half-plane chart the relative trace is continuous on
`[0, ∞)` and tends to infinity."

The pathwise property `Good` of `R7PocketStopStatement` (the relative driver with infinite capacity lifetime has a
continuous generating trace tending to infinity) is deterministic for the erased traversal of a reverse-contained
pocket in a Jordan coordinate:

* `tendsto_clockOf`: the relative clock `u ↦ L u/(1 + u)` tends to `L` from below;
* **`tendsto_norm_relCurve_of_isReversePocket`**: the relative curve `ψ ∘ γ̂_C` of the erased path tends to `∞`
  (Aux. lemma 40's continuous erasure ends at the junction `x₀`, and `ψ(x₀) = ∞`);
* **`tendsto_norm_relCurve_of_isReversePocketInf`**: the same at infinity (the counterflow is transient);
* `tendsto_capInv_of_capLife_eq_top`, `isGeneratingTrace_top_of_capLife_eq_top`, **`goodR7_of_tendsto`**: with infinite
  capacity lifetime the capacity reparametrization is a generating trace on `[0, ∞)` tending to `∞`;
* **`goodR7_cfTraversal`**, **`goodR7_cfTraversalInf`**: `Good` for the change
  pocket of two walls traversed by the counterflow (both pocket shapes).

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7Aux131

open PocketTraversal Lemma71C PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen

/-- **Theorem R.7's pathwise property of the relative driver**: a continuous generating trace on the whole
lifetime, tending to infinity when the lifetime is infinite. -/
abbrev GoodR7 (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧ (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

/-! ### The relative clock -/

/-- The relative clock `u ↦ L u/(1 + u)` tends to `L` from below. -/
theorem tendsto_clockOf {L : ℝ} (hL : 0 < L) : Tendsto (clockOf L) atTop (𝓝[<] L) := by
  have h1 : Tendsto (fun u : ℝ => (1 + u)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 : Tendsto (fun u : ℝ => L * (1 - (1 + u)⁻¹)) atTop (𝓝 (L * (1 - 0))) :=
    (tendsto_const_nhds.sub h1).const_mul L
  rw [sub_zero, mul_one] at h2
  refine tendsto_nhdsWithin_iff.2 ⟨h2.congr' ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    have hu1 : (1 + u) ≠ 0 := by positivity
    simp only [clockOf]
    congr 1
    field_simp
    ring
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact clockOf_lt hL hu

/-! ### The terminal limit of the erased traversal -/

section Pocket

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The erased path in the Jordan coordinate tends to `∞` at its terminal clock** (finite junction): Aux. lemma
40's continuous erasure ends at `x₀ = α₁ 0`, stays in `C̄ ∖ {x₀}` before, and `ψ → ∞` at `x₀` within `C̄ ∖ {x₀}`. -/
theorem tendsto_ζ_of_isReversePocket (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : Sec6.AttachmentConstancy η C α₁ α₂ τ σ) (hψ : Sec6.IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    Tendsto (fun v => ψ (Sec6.erasedPath η C τ σ v)) (𝓝[<] (Sec6.pocketClock η C τ σ σ)) (cobounded ℂ) := by
  set Lc := Sec6.pocketClock η C τ σ σ with hLc
  have hL : 0 < Lc := hP.clock_σ_pos hAC
  have hmem : Icc 0 Lc ∈ 𝓝[<] Lc := mem_of_superset (Ioo_mem_nhdsLT hL) Ioo_subset_Icc_self
  have hcw : ContinuousWithinAt (Sec6.erasedPath η C τ σ) (Iio Lc) Lc :=
    ((hP.continuousOn_erasedPath hAC) Lc ⟨hL.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
  have h1 : Tendsto (Sec6.erasedPath η C τ σ) (𝓝[<] Lc) (𝓝 (α₁ 0)) := by
    have := hcw.tendsto
    rwa [hP.erasedPath_clock_σ hAC] at this
  have h2 : Tendsto (Sec6.erasedPath η C τ σ) (𝓝[<] Lc) (𝓝[closure C \ {α₁ 0}] (α₁ 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h1, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hL] with v hv
    exact hP.erasedPath_mem ⟨hv.1.le, hv.2⟩
  exact hψ.2.2.2.2.2.2.comp h2

/-- **The erased traversal of a reverse-contained pocket tends to `∞`** (finite junction; Aux. lemma 131's (CS13.2)
for the relative curve on `[0, ∞)`). -/
theorem tendsto_norm_relCurve_of_isReversePocket (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : Sec6.AttachmentConstancy η C α₁ α₂ τ σ) (hψ : Sec6.IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    Tendsto (fun u => ‖relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ) u‖)
      atTop atTop :=
  tendsto_norm_atTop_iff_cobounded.2
    ((tendsto_ζ_of_isReversePocket hP hAC hψ).comp (tendsto_clockOf (hP.clock_σ_pos hAC)))

/-- **The erased traversal of a reverse-contained pocket at infinity tends to `∞`** when the counterflow is
transient (Aux. lemma 40 at infinity). -/
theorem tendsto_norm_relCurve_of_isReversePocketInf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : Sec6.AttachmentConstancyInf η C α₁ α₂ τ) (hψ : Sec6.IsJordanCoordInf C (α₁ 0) ψ)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun u => ‖relCurve (fun v => ψ (Sec6.erasedPathInf η C τ v)) (Sec6.clockEnd η C τ) u‖) atTop atTop :=
  tendsto_norm_atTop_iff_cobounded.2
    ((hP.tendsto_ζ hAC hψ htr).comp (tendsto_clockOf (hP.clockEnd_pos hAC)))

end Pocket

/-! ### `Good` for a driven curve tending to infinity -/

section Driven

variable {γ : ℝ → ℂ}

/-- With infinite capacity lifetime the inverse clock tends to `∞`. -/
theorem tendsto_capInv_of_capLife_eq_top (hγ : IsDrivenCurve γ) (hL : capLife γ = ⊤) :
    Tendsto (fun t : ℝ≥0 => capInv γ t) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun M => ⟨(capClock γ (max M 0)).toNNReal, fun t ht => ?_⟩
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  have htop : ENNReal.ofReal (t : ℝ) < capLife γ := by rw [hL]; exact ENNReal.ofReal_lt_top
  obtain ⟨h0, heq⟩ := hγ.capInv_spec t.coe_nonneg htop
  have hct : capClock γ (max M 0) ≤ t := by
    have := NNReal.coe_le_coe.2 ht
    rw [Real.coe_toNNReal _ (hγ.capClock_nonneg hM0)] at this
    exact this
  refine le_trans (le_max_left M 0) (not_lt.1 fun hlt => ?_)
  have := hγ.strictMonoOn_capClock h0 hM0 hlt
  rw [heq] at this
  linarith

/-- With infinite capacity lifetime the capacity reparametrization is a generating trace on `[0, ∞)`. -/
theorem isGeneratingTrace_top_of_capLife_eq_top (hγ : IsDrivenCurve γ) (hL : capLife γ = ⊤) :
    IsGeneratingTrace (segDriver γ) ⊤ (capTrace γ) := by
  refine ⟨(hγ.isGeneratingTrace_of_capLife_eq_top hL 1).1, fun s _ => ?_, fun t _ => ?_⟩
  · exact (hγ.continuousAt_capTrace (by rw [hL]; exact ENNReal.coe_lt_top)).continuousWithinAt
  · exact (hγ.isGeneratingTrace_of_capLife_eq_top hL (t + 1)).2.2 t (by exact_mod_cast lt_add_one t)

/-- **`Good` for a driven curve tending to infinity**: with infinite capacity lifetime its capacity
reparametrization is a continuous generating trace on `[0, ∞)` of the canonical driver, tending to `∞`. -/
theorem goodR7_of_tendsto (hγ : IsDrivenCurve γ) (htr : Tendsto (fun u => ‖γ u‖) atTop atTop) (hL : capLife γ = ⊤) :
    GoodR7 (fun t => segDriver γ t) ⊤ :=
  ⟨capTrace γ, isGeneratingTrace_top_of_capLife_eq_top hγ hL,
    fun _ => htr.comp (tendsto_capInv_of_capLife_eq_top hγ hL)⟩

end Driven

/-! ### The change pocket of two walls -/

section Change

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}

/-- **The erased traversal of a bounded change pocket tends to `∞`** (Aux. lemma 131's (CS13.2)). -/
theorem tendsto_norm_cfTraversal (hc : IsCfPocketConfig R L r W η) (hψ : IsCfJordan R L r ψ) :
    Tendsto (fun u => ‖cfTraversal R L r η ψ u‖) atTop atTop := by
  have hP := hc.conf.isReversePocket_of_counterflow (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
    hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
  have hψ' : Sec6.IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ := by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ
  exact tendsto_norm_relCurve_of_isReversePocket hP hc.attach hψ'

/-- **The erased traversal of a change pocket opening at the flow seed tends to `∞`**. -/
theorem tendsto_norm_cfTraversalInf (hc : IsCfPocketConfigInf R L r W η)
    (hψ : IsCfJordanInf R L r ψ) : Tendsto (fun u => ‖cfTraversalInf R L r η ψ u‖) atTop atTop := by
  have hψ' : Sec6.IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ := by
    rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  exact tendsto_norm_relCurve_of_isReversePocketInf hc.isReversePocketInf hc.attach hψ' hc.transient

/-- **`Good` for the erased traversal of a bounded change pocket** (Aux. lemma 131's (CS13.2), Theorem R.7). -/
theorem goodR7_cfTraversal (hc : IsCfPocketConfig R L r W η) (hψ : IsCfJordan R L r ψ)
    (hL : capLife (cfTraversal R L r η ψ) = ⊤) :
    GoodR7 (fun t => segDriver (cfTraversal R L r η ψ) t) ⊤ :=
  goodR7_of_tendsto (hc.isDrivenCurve hψ).1 (tendsto_norm_cfTraversal hc hψ) hL

/-- **`Good` for the erased traversal of a change pocket opening at the flow seed.** -/
theorem goodR7_cfTraversalInf (hc : IsCfPocketConfigInf R L r W η)
    (hψ : IsCfJordanInf R L r ψ) (hL : capLife (cfTraversalInf R L r η ψ) = ⊤) :
    GoodR7 (fun t => segDriver (cfTraversalInf R L r η ψ) t) ⊤ :=
  goodR7_of_tendsto (hc.isDrivenCurve hψ).1 (tendsto_norm_cfTraversalInf hc hψ) hL

end Change

end InteractingSLE.Sec7.R7Aux131
