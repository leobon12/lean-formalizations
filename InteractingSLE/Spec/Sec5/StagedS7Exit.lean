/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS7Far

/-!
# Proposition 5.9 at depth `ℓ`, step S7 (c): the restarted arc exits through a far span

Packet PROVE-STAGED-S7 (`planning/handoffs/PROVE-STAGED-S6.md` §5, item 1, the main geometric input): the staged
analogue of the template's `ae_imgExit`/`ae_imgFar`. A killed arc `γ` (the full staged image curve) is restarted at a
capacity `S₀` before its terminal capacity; the restarted word `(W, V)` (driver `kW(S₀ + ·) − kW(S₀)`, lifetime
`kLife − S₀`) is a killed word with the integrated `SLE_κ(ρ)` equations of a **stage word** (Zhan's strip hypotheses for
the left span), and its far left mark is the flow of a real point `a ≤ 0` of the full arc. Then almost surely the
terminal capacity is finite and the killed trace of the **full** arc converges there to a real point `x₀ < a`
(`ae_restartExitL`):

* restart the restarted word at a positive rational time `q` (`Prop49Exit.ae_restart_code` with the code event
  `exitCodeS`, full canonical law by `codeLaw_compl_exitCodeS_eq_zero`, Aux. lemma 22 for the left span);
* the canonical solution from the restarted state is the full arc's driver after `S₀ + q`, so the pathwise exit
  `Prop49Exit.leftExit_of_restart` applies to the **full** arc at the time `S₀ + q`, with its geometric hypothesis from
  the killed arc (`exists_extendFrom_eq_lt_of_killed`: real coordinates left of the flowed mark are alive real points
  left of `a`);
* a limit in `ℍ` is excluded by a hypothesis (`hnH`, the template's `notMem_H_of_tendsto_kTrace`).

The rightward exit (`ae_restartExitR`, for the odd stages) is the mirror image: the restarted word is reflected
(`isWordEntrance_reflect`), and the pathwise exit is applied to the reflected full driver `−kW` with the reflected
trace.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.CrossCond.StagedS7

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord MartChar.RealFlow
open Prop49Exit Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### The leftward exit of a restarted killed arc -/

section ExitL

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {𝓘 : Filtration ℝ≥0 mΩ'}

/-- **The leftward exit of a restarted killed arc.** Let `(W, V)` be a killed word before `ζ` (adapted, `{q < ζ}` in
`𝓘_q`, the integrated equations of a stage word for the left span driven by a Brownian motion of `𝓘`, separated at
positive times, below the threshold at `0`), equal to the restart at `S₀` of a family of killed arcs, whose last left
mark is the flow of a real point `a ≤ 0` of the arc. If the killed traces of the arcs never converge into `ℍ` at a
finite terminal capacity, then almost surely the terminal capacity is finite and the killed trace converges there to
a real point left of `a`. -/
theorem ae_restartExitL {m n : ℕ} {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {ρL : Fin (m + 1) → ℝ} {ρR : Fin n → ℝ}
    (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last m)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last m))| < 2)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsFilteredBrownianReal 𝓘 B μ) (hBc : ∀ ω, Continuous (B · ω))
    {W : ℝ≥0 → Ω' → ℝ} {VL : Fin (m + 1) → ℝ≥0 → Ω' → ℝ} {VR : Fin n → ℝ≥0 → Ω' → ℝ}
    (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j))
    {ζ : Ω' → ℝ≥0∞} (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < ζ ω}) (hT0 : ∀ ω, 0 < ζ ω)
    (hE : ∀ᵐ ω ∂μ, Sec7.Aux117.IsWordEntrance κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ j, W t ω < VR j t ω)
    (hthr : ∀ᵐ ω ∂μ, ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω))
    {γ : Ω' → ℝ → ℂ} {P : Ω' → Set ℝ} (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {S₀ : Ω' → ℝ≥0} {a : Ω' → ℝ}
    (hζ : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω ↔ ((S₀ ω + t : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω))
    (hWk : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω →
      W t ω = kW (γ ω) (P ω) (S₀ ω + t) - kW (γ ω) (P ω) (S₀ ω))
    (hfar : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → VL (Fin.last m) t ω - W t ω =
      -kImg (fun r => -kPath (γ ω) (P ω) r) (-a ω) (S₀ ω + t) - kW (γ ω) (P ω) (S₀ ω + t))
    (ha : ∀ᵐ ω ∂μ, a ω ≤ 0)
    (hnH : ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0) (z : ℂ), (T : WithTop ℝ≥0) = kLife (γ ω) (P ω) →
      Tendsto (kTrace (γ ω) (P ω)) (𝓝[<] T) (𝓝 z) → z ∉ H) :
    ∀ᵐ ω ∂μ, ∃ T : ℝ≥0, (T : WithTop ℝ≥0) = kLife (γ ω) (P ω) ∧ ∃ x₀ : ℝ, x₀ < a ω ∧
      Tendsto (kTrace (γ ω) (P ω)) (𝓝[<] T) (𝓝 (x₀ : ℂ)) := by
  have hS : ∀ s : (Fin (m + 1) → ℝ) × (Fin n → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw κ ρL ρR (exitCodeS κ ρL ρR fun s => s.1 (Fin.last m))ᶜ s = 0 :=
    fun s hsep hF => codeLaw_compl_exitCodeS_eq_zero hκ hκ4 hpre hq s hsep hF
  have hR := ae_restart_code hκ hB hBc hWa hVLa hVRa hTq hT0
    (measurableSet_exitCodeS ((measurable_pi_apply (Fin.last m)).comp measurable_fst)) hS hE hsepL hsepR hthr
  filter_upwards [hR, hfar, ha, hnH] with ω hω hfarω haω hnHω
  obtain ⟨q, -, hqpos, hqT⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (hT0 ω)
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ).toNNReal := by exact_mod_cast hqpos
    exact_mod_cast Real.toNNReal_pos.1 h
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  have hqT' : (q' : ℝ≥0∞) < ζ ω := hqT
  obtain ⟨x, hxC, hxS, -, hagree⟩ := hω q hq0 hqT'
  have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hst : SignStart (stAt W VL VR q' ω) := by
    refine ⟨fun i => ?_, fun j' => ?_⟩
    · show VL i q' ω - W q' ω < 0
      linarith [hsepL ω q' hq'0 hqT' i]
    · show 0 < VR j' q' ω - W q' ω
      linarith [hsepR ω q' hq'0 hqT' j']
  obtain ⟨Sx, y, hend⟩ := (mem_exitCodeS_iff hst hxC).1 hxS
  have hxp := hxC.1.2.2
  -- the full arc, restarted at `Q = S₀ + q'`
  have hγω := hγ ω
  set Q : ℝ≥0 := S₀ ω + q' with hQdef
  have hQ : (Q : WithTop ℝ≥0) < kLife (γ ω) (P ω) := (hζ ω q').1 hqT'
  have hQ0 : 0 < Q := lt_of_lt_of_le hq'0 le_add_self
  set L : ℝ≥0∞ := kLife (γ ω) (P ω) with hLdef
  have hKc : ContinuousOn (kW (γ ω) (P ω)) {t | (t : ℝ≥0∞) < L} := hγω.continuousOn_kW
  have hagree' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L - Q →
      cw x t = kW (γ ω) (P ω) (Q + t) - kW (γ ω) (P ω) Q := by
    intro t ht
    have hQt : ((Q + t : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := Assembly2.coe_lt_sub_iff.1 ht
    have hqt : ((q' + t : ℝ≥0) : ℝ≥0∞) < ζ ω := (hζ ω (q' + t)).2 (by rw [← add_assoc]; exact hQt)
    have ht' : (t : ℝ≥0∞) < ζ ω - q' := Assembly2.coe_lt_sub_iff.2 hqt
    rw [(hagree t ht').1, hWk ω _ hqt, hWk ω _ hqT', ← add_assoc]
    ring
  have hgeo : ∀ y' : ℝ, y' < (stAt W VL VR q' ω).1 (Fin.last m) →
      extendFrom H (fwdMapInv (fun s : ℝ => kW (γ ω) (P ω) s.toNNReal) Q) y' ∉ H := by
    intro y' hy'
    have hy : y' < -kImg (fun r => -kPath (γ ω) (P ω) r) (-a ω) Q - kW (γ ω) (P ω) Q := by
      have e := hfarω q' hqT'
      simp only [stAt] at hy'
      rw [← e]
      exact hy'
    obtain ⟨x₀, -, hx₀⟩ := exists_extendFrom_eq_lt_of_killed hγω hQ haω hy
    change extendFrom H (fwdMapInv (kPath (γ ω) (P ω)) Q) y' ∉ H
    rw [hx₀]
    intro hH
    have h0 : (0 : ℝ) < ((x₀ : ℝ) : ℂ).im := hH
    simp at h0
  obtain ⟨hTne, z, hz, hzalt⟩ := leftExit_of_restart hKc hγω.kW_zero
    (fun s hs => hγω.isGeneratingTraceIcc_kTrace hs) (fun t ht0 ht => hγω.kTrace_mem_H ht0 ht) hQ0 hQ
    hxp.isForcePath.continuousOn_w hxp.1 hagree' hend hgeo
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : WithTop ℝ≥0) = kLife (γ ω) (P ω) := WithTop.ne_top_iff_exists.1 hTne
  have hTn : ENNReal.toNNReal L = T := by
    rw [hLdef, ← hT]
    rfl
  rw [hTn] at hz
  refine ⟨T, hT, ?_⟩
  rcases hzalt with hzH | ⟨y', hy', rfl⟩
  · exact absurd hzH (hnHω T z hT hz)
  · have hy : y' < -kImg (fun r => -kPath (γ ω) (P ω) r) (-a ω) Q - kW (γ ω) (P ω) Q := by
      have e := hfarω q' hqT'
      simp only [stAt] at hy'
      rw [← e]
      exact hy'
    obtain ⟨x₀, hx₀a, hx₀⟩ := exists_extendFrom_eq_lt_of_killed hγω hQ haω hy
    refine ⟨x₀, hx₀a, ?_⟩
    have e : extendFrom H (fwdMapInv (fun s : ℝ => kW (γ ω) (P ω) s.toNNReal) Q) y' = (x₀ : ℂ) := hx₀
    rw [e] at hz
    exact hz

end ExitL

/-! ### The rightward exit, by reflection -/

section Reflect

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0∞}

/-- **The integrated equations are invariant under the reflection** `x ↦ −x`, which exchanges the sides
(`Sec2.IsForcePath.reflect` and `Sec2.DriverEq.reflect` without the threshold clauses). -/
theorem isWordEntrance_reflect (h : Sec7.Aux117.IsWordEntrance a xL xR ρL ρR w vL vR b T) :
    Sec7.Aux117.IsWordEntrance a (fun j => -xR j) (fun i => -xL i) ρR ρL (fun t => -w t)
      (fun j t => -vR j t) (fun i t => -vL i t) (fun t => -b t) T where
  w_zero := by simp [h.w_zero]
  vL_zero j := by simp [h.vR_zero j]
  vR_zero i := by simp [h.vL_zero i]
  continuousOn_w := h.continuousOn_w.neg
  continuousOn_vL j := (h.continuousOn_vR j).neg
  continuousOn_vR i := (h.continuousOn_vL i).neg
  antitone_vL t ht _ _ hij := neg_le_neg (h.monotone_vR t ht hij)
  vL_le_w t ht j := neg_le_neg (h.w_le_vR t ht j)
  w_le_vR t ht i := neg_le_neg (h.vL_le_w t ht i)
  monotone_vR t ht _ _ hij := neg_le_neg (h.antitone_vL t ht hij)
  integrable_gapL t ht j := by
    have e : (fun s : ℝ => (-w s.toNNReal - -vR j s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vR j s.toNNReal)⁻¹ := by
      funext s
      rw [neg_sub_neg, ← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapR t ht j).neg
  integrable_gapR t ht i := by
    have e : (fun s : ℝ => (-w s.toNNReal - -vL i s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vL i s.toNNReal)⁻¹ := by
      funext s
      rw [neg_sub_neg, ← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapL t ht i).neg
  w_eq t ht := by
    have := Sec2.DriverEq.reflect (a := a) (ρL := ρL) (ρR := ρR) (w := w) (vL := vL) (vR := vR) (b := b)
      (ζ := T) h.w_eq t ht
    simpa only [Pi.neg_apply] using this
  vL_eq t ht j := by
    have e : (fun s : ℝ => 2 / (-vR j s.toNNReal - -w s.toNNReal)) =
        fun s => -(2 / (vR j s.toNNReal - w s.toNNReal)) := by
      funext s
      exact div_neg_sub_neg _ _ _
    rw [e, intervalIntegral.integral_neg, h.vR_eq t ht j]
    ring
  vR_eq t ht i := by
    have e : (fun s : ℝ => 2 / (-vL i s.toNNReal - -w s.toNNReal)) =
        fun s => -(2 / (vL i s.toNNReal - w s.toNNReal)) := by
      funext s
      exact div_neg_sub_neg _ _ _
    rw [e, intervalIntegral.integral_neg, h.vL_eq t ht i]
    ring
  volume_collisionL j := by simpa [neg_inj] using h.volume_collisionR j
  volume_collisionR i := by simpa [neg_inj] using h.volume_collisionL i

end Reflect

section ExitR

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {𝓘 : Filtration ℝ≥0 mΩ'}

/-- **The rightward exit of a restarted killed arc** (the mirror image of `ae_restartExitL`): the restarted word is a
stage word for the right span (its reflection is one for the left span), and its last right mark is the flow of a real
point `b ≥ 0` of the arc. Then almost surely the terminal capacity is finite and the killed trace converges there to a
real point right of `b`. -/
theorem ae_restartExitR {m n : ℕ} {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {ρL : Fin m → ℝ} {ρR : Fin (n + 1) → ℝ}
    (hpre : Strip.HasStripPrefixSums κ (Fin.init ρR) ρL)
    (hq : |Strip.chargePlus κ (Fin.init ρR) ρL (ρR (Fin.last n)) -
      Strip.chargeMinus (Fin.init ρR) (ρR (Fin.last n))| < 2)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsFilteredBrownianReal 𝓘 B μ) (hBc : ∀ ω, Continuous (B · ω))
    {W : ℝ≥0 → Ω' → ℝ} {VL : Fin m → ℝ≥0 → Ω' → ℝ} {VR : Fin (n + 1) → ℝ≥0 → Ω' → ℝ}
    (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j))
    {ζ : Ω' → ℝ≥0∞} (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < ζ ω}) (hT0 : ∀ ω, 0 < ζ ω)
    (hE : ∀ᵐ ω ∂μ, Sec7.Aux117.IsWordEntrance κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ j, W t ω < VR j t ω)
    (hthr : ∀ᵐ ω ∂μ, ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω))
    {γ : Ω' → ℝ → ℂ} {P : Ω' → Set ℝ} (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {S₀ : Ω' → ℝ≥0} {b : Ω' → ℝ}
    (hζ : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω ↔ ((S₀ ω + t : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω))
    (hWk : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω →
      W t ω = kW (γ ω) (P ω) (S₀ ω + t) - kW (γ ω) (P ω) (S₀ ω))
    (hfar : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → VR (Fin.last n) t ω - W t ω =
      kImg (kPath (γ ω) (P ω)) (b ω) (S₀ ω + t) - kW (γ ω) (P ω) (S₀ ω + t))
    (hb : ∀ᵐ ω ∂μ, 0 ≤ b ω)
    (hnH : ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0) (z : ℂ), (T : WithTop ℝ≥0) = kLife (γ ω) (P ω) →
      Tendsto (kTrace (γ ω) (P ω)) (𝓝[<] T) (𝓝 z) → z ∉ H) :
    ∀ᵐ ω ∂μ, ∃ T : ℝ≥0, (T : WithTop ℝ≥0) = kLife (γ ω) (P ω) ∧ ∃ x₀ : ℝ, b ω < x₀ ∧
      Tendsto (kTrace (γ ω) (P ω)) (𝓝[<] T) (𝓝 (x₀ : ℂ)) := by
  -- the reflected restarted word
  set W' : ℝ≥0 → Ω' → ℝ := fun t ω => -W t ω with hW'def
  set VL' : Fin (n + 1) → ℝ≥0 → Ω' → ℝ := fun j t ω => -VR j t ω with hVL'def
  set VR' : Fin m → ℝ≥0 → Ω' → ℝ := fun i t ω => -VL i t ω with hVR'def
  set B' : ℝ≥0 → Ω' → ℝ := fun t ω => -B t ω with hB'def
  have hB' : IsFilteredBrownianReal 𝓘 B' μ := hB.neg
  have hBc' : ∀ ω, Continuous (B' · ω) := fun ω => (hBc ω).neg
  have hWa' : StronglyAdapted 𝓘 W' := fun t => (hWa t).neg
  have hVLa' : ∀ j, StronglyAdapted 𝓘 (VL' j) := fun j t => (hVRa j t).neg
  have hVRa' : ∀ i, StronglyAdapted 𝓘 (VR' i) := fun i t => (hVLa i t).neg
  have hE' : ∀ᵐ ω ∂μ, Sec7.Aux117.IsWordEntrance κ (fun j => VL' j 0 ω) (fun i => VR' i 0 ω) ρR ρL
      (fun t => W' t ω) (fun j t => VL' j t ω) (fun i t => VR' i t ω) (fun t => B' t ω) (ζ ω) := by
    filter_upwards [hE] with ω h
    exact isWordEntrance_reflect h
  have hsepL' : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ j, VL' j t ω < W' t ω := fun ω t ht0 ht j =>
    neg_lt_neg (hsepR ω t ht0 ht j)
  have hsepR' : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ i, W' t ω < VR' i t ω := fun ω t ht0 ht i =>
    neg_lt_neg (hsepL ω t ht0 ht i)
  have hthr' : ∀ᵐ ω ∂μ, ¬ ForceWord.ThresholdCondition ρR ρL (W' 0 ω) (fun j => VL' j 0 ω)
      (fun i => VR' i 0 ω) := by
    filter_upwards [hthr] with ω h hc
    exact h (Sec2.thresholdCondition_neg_iff.1 hc)
  have hS : ∀ s : (Fin (n + 1) → ℝ) × (Fin m → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw κ ρR ρL (exitCodeS κ ρR ρL fun s => s.1 (Fin.last n))ᶜ s = 0 :=
    fun s hsep hF => codeLaw_compl_exitCodeS_eq_zero hκ hκ4 hpre hq s hsep hF
  have hR := ae_restart_code hκ hB' hBc' hWa' hVLa' hVRa' hTq hT0
    (measurableSet_exitCodeS ((measurable_pi_apply (Fin.last n)).comp measurable_fst)) hS hE' hsepL' hsepR' hthr'
  filter_upwards [hR, hfar, hb, hnH] with ω hω hfarω hbω hnHω
  obtain ⟨q, -, hqpos, hqT⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (hT0 ω)
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ).toNNReal := by exact_mod_cast hqpos
    exact_mod_cast Real.toNNReal_pos.1 h
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  have hqT' : (q' : ℝ≥0∞) < ζ ω := hqT
  obtain ⟨x, hxC, hxS, -, hagree⟩ := hω q hq0 hqT'
  have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hst : SignStart (stAt W' VL' VR' q' ω) := by
    refine ⟨fun j => ?_, fun i => ?_⟩
    · show VL' j q' ω - W' q' ω < 0
      linarith [hsepL' ω q' hq'0 hqT' j]
    · show 0 < VR' i q' ω - W' q' ω
      linarith [hsepR' ω q' hq'0 hqT' i]
  obtain ⟨Sx, y, hend⟩ := (mem_exitCodeS_iff hst hxC).1 hxS
  have hxp := hxC.1.2.2
  have hγω := hγ ω
  set Q : ℝ≥0 := S₀ ω + q' with hQdef
  have hQ : (Q : WithTop ℝ≥0) < kLife (γ ω) (P ω) := (hζ ω q').1 hqT'
  have hQ0 : 0 < Q := lt_of_lt_of_le hq'0 le_add_self
  set L : ℝ≥0∞ := kLife (γ ω) (P ω) with hLdef
  -- the reflected full driver and trace
  set wr : ℝ≥0 → ℝ := fun t => -kW (γ ω) (P ω) t with hwrdef
  have hKc : ContinuousOn wr {t | (t : ℝ≥0∞) < L} := hγω.continuousOn_kW.neg
  have hwr0 : wr 0 = 0 := by simp only [hwrdef, hγω.kW_zero, neg_zero]
  set γr : ℝ≥0 → ℂ := fun t => LP.reflectC (kTrace (γ ω) (P ω) t) with hγrdef
  have htr : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L → Sec7.IsGeneratingTraceIcc wr s γr := by
    intro s hs
    obtain ⟨s', hss', hs'L⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    have h1 := (hγω.isGeneratingTraceIcc_kTrace hs'L).1
    have h2 := LP.isGeneratingTrace_reflect h1
    exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc h2 (hKc.mono fun t ht => lt_trans ht hs'L) hwr0 hss'
  have hγrH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < L → γr t ∈ H := fun t ht0 ht =>
    LP.reflectC_mem_H_iff.2 (hγω.kTrace_mem_H ht0 ht)
  have hagree' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L - Q → cw x t = wr (Q + t) - wr Q := by
    intro t ht
    have hQt : ((Q + t : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := Assembly2.coe_lt_sub_iff.1 ht
    have hqt : ((q' + t : ℝ≥0) : ℝ≥0∞) < ζ ω := (hζ ω (q' + t)).2 (by rw [← add_assoc]; exact hQt)
    have ht' : (t : ℝ≥0∞) < ζ ω - q' := Assembly2.coe_lt_sub_iff.2 hqt
    rw [(hagree t ht').1]
    simp only [hW'def, hwrdef]
    rw [hWk ω _ hqt, hWk ω _ hqT', ← add_assoc]
    ring
  -- real coordinates beyond the flowed mark
  have hreal : ∀ y' : ℝ, y' < (stAt W' VL' VR' q' ω).1 (Fin.last n) →
      ∃ x₀ : ℝ, x₀ < -b ω ∧ extendFrom H (fwdMapInv (fun s : ℝ => wr s.toNNReal) Q) y' = x₀ := by
    intro y' hy'
    obtain ⟨S, -, -, hQS, w, hw, hw0, hEqw, η, hηL, -, -⟩ := hγω.exists_kPath_trace hQ
    have hwn : Continuous fun s => -w s := hw.neg
    have hEqF : fwdMapInv (fun s : ℝ => wr s.toNNReal) Q = fwdMapInv (fun s => -w s) Q := by
      refine fwdMapInv_eq_of_eqOn Q.2 hQS fun r hr => ?_
      simp only [hwrdef]
      rw [← kPath, hEqw hr]
    have hBd : HasBdryLimits (fwdMapInv (fun s => -w s) Q) :=
      (CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hηL).hasBdryLimits hw.neg
        (by simp only [Pi.neg_apply, hw0, neg_zero]) Q.2
    have hk : kImg (kPath (γ ω) (P ω)) (b ω) Q = rightImg w (b ω) Q := kImg_eq hw hEqw hQS.le (b ω)
    have hkW : kW (γ ω) (P ω) Q = w Q := by
      rw [← kPath_coe]
      exact hEqw ⟨Q.2, hQS.le⟩
    have e := hfarω q' hqT'
    have hy : y' < -rightImg (fun s => -(fun s => -w s) s) (-(-b ω)) Q - (fun s => -w s) Q := by
      simp only [neg_neg]
      simp only [stAt, hVL'def, hW'def] at hy'
      rw [hk, hkW] at e
      linarith
    obtain ⟨x₀, hx₀b, hx₀⟩ := exists_extendFrom_eq_lt hwn (by simp only [hw0, neg_zero]) Q.2 hBd
      (neg_nonpos.2 hbω) hy
    exact ⟨x₀, hx₀b, by rw [hEqF]; exact hx₀⟩
  have hgeo : ∀ y' : ℝ, y' < (stAt W' VL' VR' q' ω).1 (Fin.last n) →
      extendFrom H (fwdMapInv (fun s : ℝ => wr s.toNNReal) Q) y' ∉ H := by
    intro y' hy'
    obtain ⟨x₀, -, hx₀⟩ := hreal y' hy'
    rw [hx₀]
    intro hH
    have h0 : (0 : ℝ) < ((x₀ : ℝ) : ℂ).im := hH
    simp at h0
  obtain ⟨hTne, z, hz, hzalt⟩ := leftExit_of_restart hKc hwr0 htr hγrH hQ0 hQ
    hxp.isForcePath.continuousOn_w hxp.1 hagree' hend hgeo
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : WithTop ℝ≥0) = kLife (γ ω) (P ω) := WithTop.ne_top_iff_exists.1 hTne
  have hTn : ENNReal.toNNReal L = T := by
    rw [hLdef, ← hT]
    rfl
  rw [hTn] at hz
  have hzk : Tendsto (kTrace (γ ω) (P ω)) (𝓝[<] T) (𝓝 (LP.reflectC z)) := by
    have := (LP.continuous_reflectC.tendsto z).comp hz
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, hγrdef, LP.reflectC_reflectC]
  refine ⟨T, hT, ?_⟩
  rcases hzalt with hzH | ⟨y', hy', rfl⟩
  · exact absurd (LP.reflectC_mem_H_iff.2 hzH) (hnHω T _ hT hzk)
  · obtain ⟨x₀, hx₀b, hx₀⟩ := hreal y' hy'
    refine ⟨-x₀, by linarith, ?_⟩
    rw [hx₀, LP.reflectC_ofReal] at hzk
    exact hzk

end ExitR

end InteractingSLE.Sec5.CrossCond.StagedS7
