/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Coupling.WholeField3Noise

/-!
# The frozen driving code is a Borel function of the killed state code

Packet PROVE-FLOWEXIST3 (AUD-3c N1). A history code `x ∈ XCode` (`Sec2.Assembly`) is a pair (driving-path code,
killed-state code). On the good set `DetSet` of `PROVE-FLOWEXIST` the driving path is determined by the killed
state: before the lifetime it is the recovered noise `noiseOf` of the state (`IsIntegratedSLEPath.eq_noiseOf`), and
at and after a finite positive lifetime it is frozen at its left limit there (`FrozenB`, continuity). Hence
(**`recode_snd`**) `x = recode x.2` on `DetSet`, for the Borel map `recode` (**`measurable_recode`**):

`recode s = (bOf s, s)`, `bOf s (n, k) = noise of the state at k/2ⁿ` if `k/2ⁿ < ζ`, `0` if `ζ = 0`, and otherwise
`limsup_m` of the noise at the times `ζ − 1/(m+1)`.

This is what makes the history code measurable for any σ-algebra that carries the killed state.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open Sec2.Assembly WholeField

variable {nL nR : ℕ}

/-- The times `ζ − 1/(m+1)` (truncated at `0`) below a lifetime. -/
def tmBelow (ζ : ℝ≥0∞) (m : ℕ) : ℝ≥0 := ζ.toNNReal - 1 / ((m : ℝ≥0) + 1)

theorem tmBelow_lt {ζ : ℝ≥0∞} (h0 : ζ ≠ 0) (htop : ζ ≠ ⊤) (m : ℕ) : (tmBelow ζ m : ℝ≥0∞) < ζ := by
  have hpos : 0 < ζ.toNNReal := ENNReal.toNNReal_pos h0 htop
  have hlt : tmBelow ζ m < ζ.toNNReal := tsub_lt_self hpos (by positivity)
  calc (tmBelow ζ m : ℝ≥0∞) < (ζ.toNNReal : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hlt
    _ = ζ := ENNReal.coe_toNNReal htop

theorem tendsto_tmBelow (ζ : ℝ≥0∞) : Tendsto (tmBelow ζ) atTop (𝓝 ζ.toNNReal) := by
  have h1 : Tendsto (fun m : ℕ => (1 : ℝ≥0) / ((m : ℝ≥0) + 1)) atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using this
  have := (tendsto_const_nhds (x := ζ.toNNReal)).sub h1
  rw [tsub_zero] at this
  exact this

theorem measurable_tmBelow (m : ℕ) : Measurable fun ζ : ℝ≥0∞ => tmBelow ζ m :=
  ENNReal.measurable_toNNReal.sub_const _

/-- The noise recovered from a killed-state code at time `t`. -/
def stateNoise (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (s : SCode nL nR) (t : ℝ≥0) : ℝ :=
  noiseOf κ ρL ρR xL xR (dec s.2.1 t) (fun i => dec (s.2.2.1 i) t) (fun j => dec (s.2.2.2 j) t)

theorem measurable_stateNoise (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {α : Type*} [MeasurableSpace α] {f : α → SCode nL nR} (hf : Measurable f)
    {τ : α → ℝ≥0} (hτ : Measurable τ) : Measurable fun a => stateNoise κ ρL ρR xL xR (f a) (τ a) := by
  have hd : ∀ {g : α → PCode}, Measurable g → Measurable fun a => dec (g a) (τ a) := fun hg =>
    measurable_dec.comp (hg.prodMk hτ)
  have hw : Measurable fun a => dec (f a).2.1 (τ a) := hd (measurable_fst.comp (measurable_snd.comp hf))
  have hL : Measurable fun a => (fun i => dec ((f a).2.2.1 i) (τ a) : Fin nL → ℝ) :=
    measurable_pi_iff.2 fun i => hd ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hf))))
  have hR : Measurable fun a => (fun j => dec ((f a).2.2.2 j) (τ a) : Fin nR → ℝ) :=
    measurable_pi_iff.2 fun j => hd ((measurable_pi_apply j).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hf))))
  exact (measurable_noiseOf κ ρL ρR xL xR).comp (hw.prodMk (hL.prodMk hR))

open scoped Classical in
/-- The frozen driving code read off a killed-state code. -/
def bOf (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (s : SCode nL nR) : PCode := fun n k =>
  if (dyad n k : ℝ≥0∞) < s.1 then stateNoise κ ρL ρR xL xR s (dyad n k)
  else if s.1 = 0 then 0
  else limsup (fun m => stateNoise κ ρL ρR xL xR s (tmBelow s.1 m)) atTop

/-- The history code rebuilt from its killed-state code. -/
def recode (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (s : SCode nL nR) : XCode nL nR :=
  (bOf κ ρL ρR xL xR s, s)

theorem measurable_recode (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) : Measurable (recode (nL := nL) (nR := nR) κ ρL ρR xL xR) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_) measurable_id
  classical
  change Measurable fun s : SCode nL nR => if (dyad n k : ℝ≥0∞) < s.1 then
    stateNoise κ ρL ρR xL xR s (dyad n k) else if s.1 = 0 then 0
    else limsup (fun m => stateNoise κ ρL ρR xL xR s (tmBelow s.1 m)) atTop
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (measurable_stateNoise κ ρL ρR xL xR measurable_id measurable_const) ?_
  refine Measurable.ite (measurable_fst (measurableSet_singleton 0)) measurable_const ?_
  exact Measurable.limsup fun m =>
    measurable_stateNoise κ ρL ρR xL xR measurable_id ((measurable_tmBelow m).comp measurable_fst)

/-- **On `DetSet` a history code is rebuilt from its killed-state code.** -/
theorem recode_snd {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {x : XCode nL nR} (hx : x ∈ DetSet κ xL xR ρL ρR) :
    recode κ ρL ρR xL xR x.2 = x := by
  obtain ⟨⟨⟨⟨hg, -, hp⟩, -⟩, hfr⟩, -⟩ := hx
  refine Prod.ext (funext fun n => funext fun k => ?_) rfl
  change bOf κ ρL ρR xL xR x.2 n k = x.1 n k
  have hstate : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → stateNoise κ ρL ρR xL xR x.2 t = cb x t := fun t ht =>
    (WholeField.IsIntegratedSLEPath.eq_noiseOf hκ hp ht).symm
  unfold bOf
  by_cases hlt : (dyad n k : ℝ≥0∞) < x.2.1
  · simp only [hlt, ↓reduceIte]
    rw [hstate _ hlt]
    exact (hg.1 ⌈dyad n k⌉₊).dec_dyad (Nat.le_ceil _)
  · simp only [hlt, ↓reduceIte]
    rw [hfr n k hlt]
    by_cases h0 : x.2.1 = 0
    · have h0' : cζ x = 0 := h0
      simp only [h0, h0', ↓reduceIte]
    · have h0' : cζ x ≠ 0 := h0
      have htop : cζ x ≠ ⊤ := fun h => hlt (by change (dyad n k : ℝ≥0∞) < cζ x; rw [h]; exact ENNReal.coe_lt_top)
      simp only [h0, h0', ↓reduceIte]
      have hb := hg.continuous_b
      have hlim : Tendsto (fun m => stateNoise κ ρL ρR xL xR x.2 (tmBelow x.2.1 m)) atTop
          (𝓝 (cb x (cζ x).toNNReal)) := by
        have e : (fun m => stateNoise κ ρL ρR xL xR x.2 (tmBelow x.2.1 m)) =
            fun m => cb x (tmBelow (cζ x) m) := funext fun m => hstate _ (tmBelow_lt h0' htop m)
        rw [e]
        exact (hb.tendsto _).comp (tendsto_tmBelow (cζ x))
      exact hlim.limsup_eq

/-! ### Field determination with the frozen code exported -/

universe u

/-- **Field determination, frozen form** (the proof of `exists_fieldDetermination`, with more exported): the history
code `Ψ(h₀)` is almost surely the frozen code `frz (codeOf …)` of the reference history with a continuous version `B'`
of the noise, and every code `Ψ f`, `f ∈ S`, lies in `DetSet`. -/
theorem exists_fieldDetermination_frz (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀}
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    ∃ (Ψ : LQGMetric.DistOn upperHalfPlaneOpens → XCode nL nR)
      (S : Set (LQGMetric.DistOn upperHalfPlaneOpens))
      (ηf : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ) (B' : ℝ≥0 → Ω₀ → ℝ),
      Measurable Ψ ∧ MeasurableSet S ∧ (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous (B' · ω)) ∧
      (∀ ω, B' 0 ω = 0) ∧ ProbabilityTheory.IsBrownianReal B' P₀ ∧ (∀ᵐ ω ∂P₀, ∀ t, B' t ω = B₀ t ω) ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ Ψ (h₀ ω) = frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) ∧
        cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      ∀ f ∈ S, Ψ f ∈ DetSet κ xL xR ρL ρR ∧ IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f) := by
  have hE := hcoup.1
  obtain ⟨Φ, hΦm, hΦ⟩ := h12 κ hκ xL xR ρL ρR hF hcoup
  have h13' := h13 hκ hF hE
  obtain ⟨B', hB'm, hB'c, hB'0, hB'B, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  obtain ⟨G, hGm, hG⟩ := exists_measurable_leftInverse_of_injOn
    (measurable_traceOfCode (nL := nL) (nR := nR)) (measurableSet_detSet κ xL xR ρL ρR)
    (injOn_traceOfCode hκ)
  refine ⟨G ∘ codeΦ Φ, GoodField Φ G κ xL xR ρL ρR, traceOfΦ Φ, B', hGm.comp (measurable_codeΦ hΦm),
    measurableSet_goodField hΦm hGm κ xL xR ρL ρR, hB'm, hB'c, hB'0, hB'B, hB'ae, ?_,
    fun f hf => ⟨hf.1, isGeneratingTrace_of_mem_goodField hf⟩⟩
  filter_upwards [hΦ, h13', ae_codeOf_mem hκ hE hB'c hB'ae] with ω hΦω h13ω hcode
  obtain ⟨-, η, hη, -⟩ := h13ω
  obtain ⟨hx₁, hdec⟩ := hcode
  set x₀ := frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) with hx₀def
  have hζx : cζ x₀ = ζ₀ ω := rfl
  have hcwx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → cw x₀ t = W₀ t ω := fun t ht => (hdec t ht).1
  have hηx : IsGeneratingTrace (cw x₀) (ζ₀ ω) η := Sec7.IsGeneratingTrace.congr_lt hη hcwx
  have hcrel : x₀ ∈ CRel κ xL xR ρL ρR := frz_mem_cRel hx₁
  have hmem : x₀ ∈ DetSet κ xL xR ρL ρR :=
    ⟨⟨hcrel, frozenB_frz hx₁.1.1⟩, fun n k hT => mem_traceSet_of_isGeneratingTrace hcrel hT hηx hT.le⟩
  have hcode : traceOfCode x₀ = codeΦ Φ (h₀ ω) := by
    refine Prod.ext hΦω.1.symm (funext fun n => funext fun k => ?_)
    simp only [traceOfCode, codeΦ, hζx, hΦω.1]
    by_cases hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ₀ ω
    · simp only [hlt, ↓reduceIte]
      rw [hΦω.2 η hη, min_eq_left hlt.le, ENNReal.toNNReal_coe]
      exact LP.traceAt_eq_of_isGeneratingTrace hηx hcrel.1.1.continuousOn_w hcrel.1.2.2.1 hlt
    · simp only [hlt, ↓reduceIte]
  have hΨ : G (codeΦ Φ (h₀ ω)) = x₀ := by rw [← hcode]; exact hG x₀ hmem
  have hγ := continuous_trace_min hη.2.1
  have hre : reCode Φ (h₀ ω) = enc fun t => (η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal).re := by
    funext n k; simp only [reCode, enc, hΦω.2 η hη]
  have him : imCode Φ (h₀ ω) = enc fun t => (η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal).im := by
    funext n k; simp only [imCode, enc, hΦω.2 η hη]
  refine ⟨⟨by simp only [hΨ]; exact hmem, by simp only [hΨ]; exact hcode,
    fun N => ⟨hre ▸ uc_enc (Complex.continuous_re.comp hγ).continuousOn,
      him ▸ uc_enc (Complex.continuous_im.comp hγ).continuousOn⟩, ?_⟩, by simp only [Function.comp_apply, hΨ], ?_,
      fun t ht => ?_⟩
  · rw [hΦω.2 η hη]
    simpa using hη.1
  · simp only [Function.comp_apply, hΨ]; rfl
  · simp only [Function.comp_apply, hΨ]
    exact ⟨(hdec t ht).1, (hdec t ht).2.1, (hdec t ht).2.2.1⟩

end Exist

end InteractingSLE
