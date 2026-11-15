/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripEnd
import InteractingSLE.Spec.Supplement.LPProbReflect

/-!
# Aux. lemma 22 in the strip, step 3d: the strip endpoint of an evolution whose last right mark ends the span

Packet PROVE-SEC5-L (specification §4.1, Aux. lemmas 21–22, pp. 109–115). Let `(W, V, B)` be an integrated
`SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, whose right marks `0 < XR 0 < ⋯ < XR (last j) = e` and left marks `XL < 0` give,
after reflection and dilation by `e²`, an R36 strip word (`Aux22StripWord.lean`) with the hypotheses of Zhan's strip
endpoint theorem (lower prefix sums at least `κ/2 − 2`, `|q₊ − q₋| < 2`). This is the situation after the change of
target in the proof of Aux. lemma 22: the half-line `(e, ∞)` is the image of the span `I`.

* **`ae_exists_stripEnd_of_integrated`**: almost surely the **life before the last right mark** (times `u < ζ` with
  `W < V^{R,last}` on `[0, u]`) is a bounded interval `[0, S)`, `S > 0`; a trace generates the chain on `[0, u]` for
  every `u < S`, never visits `ℝ \ {0}` before `S`, and converges to a point `y > e` as `u ↑ S`.

Proof: Zhan's strip endpoint theorem (`stripEndpointStatement_le_four`), strip noncollision
(`Zhan.ae_stripLife_noncollision`) and passive points (`IsIntegratedSLEEvolution.ae_real_alive_of_forall_ne`) for the
reflected, dilated evolution; `exists_stripEnd` along each path; the dilation and the reflection are undone pathwise
(`IsGeneratingTrace.dilate` with `c⁻¹`, `LP.isGeneratingTrace_reflect`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Strip Sec7.Dilation

variable {n j : ℕ}

/-- `√(c⁻¹)⁻¹ = √c`. -/
theorem inv_sqrt_inv (c : ℝ≥0) : (√(((c⁻¹ : ℝ≥0)) : ℝ))⁻¹ = √(c : ℝ) := by
  rw [NNReal.coe_inv, Real.sqrt_inv, inv_inv]

theorem lpReflectC_ofReal (x : ℝ) : LP.reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by
  simp [LP.reflectC]

/-- **The pathwise translation from the dilated, reflected chart back to the original one.** -/
theorem exists_stripEnd_unscale {c : ℝ≥0} (hc : c ≠ 0) {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {Sh : ℝ≥0}
    {ηh : ℝ≥0 → ℂ} {x : ℝ} (hS0 : 0 < Sh) (hx : x < -1)
    (hlife : ∀ s, IsStripLife (dilPath c fun t => -w t) (dilPath c fun t => -v t) (ζ / c) s ↔ s < Sh)
    (hgen : ∀ s, s < Sh → IsGeneratingTrace (dilPath c fun t => -w t) s ηh)
    (havoid : ∀ s, s < Sh → ∀ y : ℝ, y ≠ 0 → ηh s ≠ y) (hconv : Tendsto ηh (𝓝[<] Sh) (𝓝 (x : ℂ))) :
    ∃ (S : ℝ≥0) (η : ℝ≥0 → ℂ) (y : ℝ), 0 < S ∧ √(c : ℝ) < y ∧
      (∀ u : ℝ≥0, ((u : ℝ≥0∞) < ζ ∧ ∀ r ≤ u, w r < v r) ↔ u < S) ∧
      (∀ u, u < S → IsGeneratingTrace w u η) ∧ (∀ u, u < S → ∀ z : ℝ, z ≠ 0 → η u ≠ z) ∧
      Tendsto η (𝓝[<] S) (𝓝 (y : ℂ)) := by
  have hc0 : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
  have hsq := sqrt_pos_of_ne hc
  set e : ℝ := √(c : ℝ) with he
  set η : ℝ≥0 → ℂ := fun u => LP.reflectC ((e : ℂ) * ηh (c⁻¹ * u)) with hηdef
  have hcu : ∀ u : ℝ≥0, c * (c⁻¹ * u) = u := fun u => mul_inv_cancel_left₀ hc u
  refine ⟨c * Sh, η, -(e * x), mul_pos hc0 hS0, by nlinarith, fun u => ?_, fun u hu => ?_,
    fun u hu z hz => ?_, ?_⟩
  · -- the life before the last mark is `[0, c Sh)`
    rw [show u < c * Sh ↔ c⁻¹ * u < Sh by rw [inv_mul_lt_iff₀ hc0], ← hlife]
    unfold IsStripLife
    rw [coe_lt_div_iff hc, hcu]
    refine and_congr Iff.rfl ⟨fun h r hr => ?_, fun h r hr => ?_⟩
    · have h1 := h (c * r) (by
        calc c * r ≤ c * (c⁻¹ * u) := mul_le_mul_of_nonneg_left hr c.2
          _ = u := hcu u)
      simp only [dilPath]
      have := inv_pos.2 hsq
      nlinarith
    · have h1 := h (c⁻¹ * r) (by
        calc c⁻¹ * r ≤ c⁻¹ * u := mul_le_mul_of_nonneg_left hr (inv_nonneg.2 c.2))
      simp only [dilPath, hcu r] at h1
      have := inv_pos.2 hsq
      nlinarith
  · -- the trace
    have hs : c⁻¹ * u < Sh := by rw [inv_mul_lt_iff₀ hc0]; exact hu
    have h1 := (hgen _ hs).dilate (inv_ne_zero hc)
    rw [dilPath_inv_dilPath hc, div_inv_coe hc] at h1
    have h2 := LP.isGeneratingTrace_reflect h1
    have e1 : (-fun t => -w t) = w := by funext t; simp
    have e2 : ((((c⁻¹ * u : ℝ≥0) : ℝ≥0∞)) * (c : ℝ≥0∞)) = (u : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, mul_comm, hcu]
    rw [e1, e2, inv_sqrt_inv] at h2
    exact h2
  · -- no real point other than `0`
    have hs : c⁻¹ * u < Sh := by rw [inv_mul_lt_iff₀ hc0]; exact hu
    intro heq
    have hηh : ηh (c⁻¹ * u) = ((-(z / e) : ℝ) : ℂ) := by
      have h1 : LP.reflectC (LP.reflectC ((e : ℂ) * ηh (c⁻¹ * u))) = LP.reflectC (z : ℂ) := by
        rw [show LP.reflectC ((e : ℂ) * ηh (c⁻¹ * u)) = η u from rfl, heq]
      rw [LP.reflectC_reflectC] at h1
      have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
      rw [lpReflectC_ofReal] at h1
      rw [show ηh (c⁻¹ * u) = ((e : ℂ))⁻¹ * ((e : ℂ) * ηh (c⁻¹ * u)) by field_simp, h1]
      push_cast
      field_simp
    exact havoid _ hs _ (by
      intro h0
      have : z / e = 0 := by linarith
      exact hz ((div_eq_zero_iff.1 this).resolve_right hsq.ne')) hηh
  · -- the limit
    have h1 := hconv.comp (tendsto_inv_mul_nhdsLT hc Sh)
    have h2 : Tendsto (fun u => LP.reflectC ((e : ℂ) * ηh (c⁻¹ * u))) (𝓝[<] (c * Sh))
        (𝓝 (LP.reflectC ((e : ℂ) * x))) :=
      (LP.continuous_reflectC.tendsto _).comp (h1.const_mul _)
    have h3 : LP.reflectC ((e : ℂ) * x) = ((-(e * x) : ℝ) : ℂ) := by
      rw [show ((e : ℂ) * x) = ((e * x : ℝ) : ℂ) by push_cast; ring, lpReflectC_ofReal]
    rw [h3] at h2
    exact h2

/-- **The strip endpoint of an evolution whose last right mark ends the span** (`0 < κ ≤ 4`). Almost surely the life
before the last right mark is `[0, S)`, `S > 0`; a trace generates the chain on `[0, u]` for every `u < S`, never
visits `ℝ \ {0}` before `S`, and tends to a point `y` beyond the last right mark as `u ↑ S`. -/
theorem ae_exists_stripEnd_of_integrated {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {XL : Fin n → ℝ} {XR : Fin (j + 1) → ℝ} {ρL : Fin n → ℝ} {ρR : Fin (j + 1) → ℝ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin n → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ XL XR ρL ρR P 𝓕 W VL VR B ζ)
    (he : 0 < XR (Fin.last j)) (hR : StrictMono XR) (hR0 : ∀ k : Fin j, 0 < XR k.castSucc)
    (hL : StrictAnti XL) (hL0 : ∀ i, XL i < 0) (hpre : HasStripPrefixSums κ (Fin.init ρR) ρL)
    (hq : |chargePlus κ (Fin.init ρR) ρL (ρR (Fin.last j)) -
      chargeMinus (Fin.init ρR) (ρR (Fin.last j))| < 2) :
    ∀ᵐ ω ∂P, ∃ (S : ℝ≥0) (η : ℝ≥0 → ℂ) (y : ℝ), 0 < S ∧ XR (Fin.last j) < y ∧
      (∀ u : ℝ≥0, ((u : ℝ≥0∞) < ζ ω ∧ ∀ r ≤ u, W r ω < VR (Fin.last j) r ω) ↔ u < S) ∧
      (∀ u, u < S → IsGeneratingTrace (fun t => W t ω) u η) ∧
      (∀ u, u < S → ∀ z : ℝ, z ≠ 0 → η u ≠ z) ∧ Tendsto η (𝓝[<] S) (𝓝 (y : ℂ)) := by
  set c := stripScale XR with hcdef
  have hc := stripScale_ne_zero he
  have hS := isStripSLEEvolution_reflect_dilate hE he (fun k => hR (Fin.castSucc_lt_last k))
    (fun i => (hL0 i).trans he)
  have hsep := isSeparatedStripWord_strip he hR hR0 hL hL0
  have hend := stripEndpointStatement_le_four.{u} hκ hκ4 _ _ _ _ _ P _ _ _ _ _ _ hsep hpre hq hS
  have hnc := Zhan.ae_stripLife_noncollision hκ hsep hpre hS
  have halive := IsIntegratedSLEEvolution.ae_real_alive_of_forall_ne hκ hκ4 hS
  filter_upwards [hend, hnc, halive, hS.2.2.2.2] with ω h1 h2 h3 h4
  have hwc : ContinuousOn (fun s => dilProc c (-W) s ω) {s | (s : ℝ≥0∞) < ζ ω / c} := h4.2.2.2.1
  have hvc : ContinuousOn (fun s => dilProc c (-VR (Fin.last j)) s ω) {s | (s : ℝ≥0∞) < ζ ω / c} :=
    h4.2.2.2.2.1 (Fin.last j)
  have hw0 : dilProc c (-W) 0 ω = 0 := h4.1
  have hal : ∀ s, IsStripLife (fun s => dilProc c (-W) s ω) (fun s => dilProc c (-VR (Fin.last j)) s ω)
      (ζ ω / c) s → ∀ y : ℝ, y ≠ 0 →
        ∃ v, IsForwardSol (fun r : ℝ => dilProc c (-W) r.toNNReal ω) (y : ℂ) s v := by
    intro s hs y hy
    refine h3 s hs.1 (fun r hr => ⟨fun i => ?_, fun i => ?_⟩) y hy
    · have hr' := IsStripLife.mono hs hr
      induction i using Fin.lastCases with
      | last => exact (hr'.2 r le_rfl).ne'
      | cast k => exact ((h2 r hr').1 k).ne'
    · exact ((h2 r (IsStripLife.mono hs hr)).2 i).ne
  obtain ⟨Sh, ηh, x, hSh, hx, hlife, hgen, havoid, hconv⟩ := exists_stripEnd hwc hvc hw0 h1 hal
  obtain ⟨S, η, y, hS0, hy, hlife', hgen', havoid', hconv'⟩ :=
    exists_stripEnd_unscale (w := fun t => W t ω) (v := fun t => VR (Fin.last j) t ω) hc hSh hx hlife hgen
      havoid hconv
  rw [sqrt_stripScale he] at hy
  exact ⟨S, η, y, hS0, hy, hlife', hgen', havoid', hconv'⟩

end Aux22Strip

end Sec5

end InteractingSLE
