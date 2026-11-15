/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RefChain

/-!
# A.1 on one reference space: the conditional image law in canonical form

Packet PROVE-ZHAN-A1REF. Source: Astra, *Follow-up proofs*, §A.1 L183–L187 (R38); follow-up 4 §2.5 (R71).

A2X's `IsCondImageLaw` asks, at every stopping time `τ` of curve `k`, for SOME image driver `W'`, lifetime `ζ'` and
clock `clk` that form an image chain of curve `j` (`IsImageChainUpTo`) and a local evolution of the random image word
(`Restart.StoppedK2.IsRandomWordEvolutionUpTo`). By `A1RefChain` the image chain is pathwise and canonical. This file
reduces `IsCondImageLaw` to a statement about the **canonical** image processes only:

* `cImgDrv`, `cImgLife`, `cImgClk`, `cImgSrc`: the canonical image driver (centred at its own start
  `cImgSrc = g_τ(xj)`), image lifetime and clock of curve `j` at the stop `τ` of curve `k`, read on every sample;
* `cImgDrvM`, `cImgLifeM`: the same, masked by the live event (`0` off it);
* `IsCanonImageLaw`: at every stopping time, the masked canonical image driver up to the masked canonical image
  lifetime is a local evolution of the random image word (the law content of A.1, no geometry left);
* `ChainReg`: the pathwise regularity used (continuity of the drivers before their lifetimes, centred starts, and the
  image source `src` equal to `g_τ(xj)` whenever the contact time is positive);
* **`isCondImageLaw_of_canon`**: `ChainReg` almost surely and `IsCanonImageLaw` give `IsCondImageLaw`.

`IsImageChainUpTo.congr_drv`: the image chain only reads the image driver on `[0, ∞)`, and nothing when the contact
time is `0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Ref

open QuantumZipper (H)
open A2X

/-! ### Congruence of the image chain in the image driver -/

/-- **The image chain reads the image driver on `[0, ∞)` only, and only when the contact time is positive.** -/
theorem IsImageChainUpTo.congr_drv {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ x' : ℝ}
    {w₁ w₂ clk : ℝ → ℝ} {ζ' : ℝ≥0∞} (h : IsImageChainUpTo xj wj ζj xk wk τ x' w₁ clk ζ')
    (hw : 0 < contactTime xj wj ζj xk wk τ → ∀ σ : ℝ, 0 ≤ σ → w₁ σ = w₂ σ) :
    IsImageChainUpTo xj wj ζj xk wk τ x' w₂ clk ζ' := by
  obtain ⟨h0, hc, hm, hl, hh⟩ := h
  refine ⟨h0, hc, hm, hl, fun s hs => ?_⟩
  rw [hh s hs]
  have hc0 : 0 < contactTime xj wj ζj xk wk τ := lt_of_le_of_lt bot_le hs
  have h0mem : (0 : ℝ) ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} :=
    ⟨le_rfl, by rwa [ENNReal.ofReal_zero]⟩
  have hsmem : (s : ℝ) ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} :=
    ⟨s.coe_nonneg, by rwa [ENNReal.ofReal_coe_nnreal]⟩
  have hnn : 0 ≤ clk s := by
    rw [← h0]; exact hm.monotoneOn h0mem hsmem s.coe_nonneg
  exact physHull_congr hnn (lt_add_one _) fun σ hσ => hw hc0 σ hσ.1

/-! ### The canonical image processes -/

section Canon

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The canonical image source** `g_τ(xj)` (the start of the canonical image driver) at the stop `τ` of curve `k`. -/
def cImgSrc (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) :
    ℝ :=
  imgDrv xj (Strip.extPath (Wj · ω)) (ζj ω) xk (Strip.extPath (Wk · ω)) (τ ω) 0

/-- **The canonical image driver**, centred at its start, of curve `j` (start `xj`, driver `Wj`, lifetime `ζj`) at
the stop `τ` of curve `k` (start `xk`, driver `Wk`). -/
def cImgDrv (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => imgDrv xj (Strip.extPath (Wj · ω)) (ζj ω) xk (Strip.extPath (Wk · ω)) (τ ω) t -
    cImgSrc xj Wj ζj xk Wk τ ω

/-- **The canonical capacity clock** of the image at the stop `τ`. -/
def cImgClk (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (xk : ℝ) (Wk : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ → ℝ :=
  imgClk xj (Strip.extPath (Wj · ω)) xk (Strip.extPath (Wk · ω)) (τ ω)

/-- **The canonical image lifetime** at the stop `τ` (the clock's limit at the contact time). -/
def cImgLife (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) :
    ℝ≥0∞ :=
  imgLife xj (Strip.extPath (Wj · ω)) (ζj ω) xk (Strip.extPath (Wk · ω)) (τ ω)

open scoped Classical in
/-- **The canonical image driver masked by the live event** (`0` off it): A2X constrains the image driver only on the
live event, and off it curve `k` may be past its lifetime, where the geometric image need not be measurable. -/
def cImgDrvM (live : ℝ≥0 → Ω → Prop) (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if live (τ ω) ω then cImgDrv xj Wj ζj xk Wk τ t ω else 0

open scoped Classical in
/-- **The canonical image lifetime masked by the live event** (`0` off it). -/
def cImgLifeM (live : ℝ≥0 → Ω → Prop) (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if live (τ ω) ω then cImgLife xj Wj ζj xk Wk τ ω else 0

/-- **The conditional image law in canonical form** (A.1 L183–L187, the law content only): at every stopping time `τ`
of `𝓕k`, on the live event, the canonical image driver of curve `j` up to the canonical image lifetime (both masked by
the live event, so that adaptedness asks nothing off it) is a local integrated `SLE_a(ρ)` evolution of the
`𝓕ᵏ_τ`-measurable random image word `(ΘL(τ), ΘR(τ))`, in some filtration `𝓖 ≥ 𝓕ᵏ_τ` with some Brownian motion `B'`
and image force processes `VL'`, `VR'`. -/
def IsCanonImageLaw (a : ℝ) {nL nR : ℕ} (P : Measure Ω) (𝓕k : Filtration ℝ≥0 mΩ) (live : ℝ≥0 → Ω → Prop)
    (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Ω → ℝ)
    (ΘL : ℝ≥0 → Ω → Fin nL → ℝ) (ΘR : ℝ≥0 → Ω → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕k fun ω => (τ ω : WithTop ℝ≥0)),
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      Restart.StoppedK2.IsRandomWordEvolutionUpTo a P hτ.measurableSpace {ω | live (τ ω) ω}
        (fun ω => ΘL (τ ω) ω) (fun ω => ΘR (τ ω) ω) ρL ρR 𝓖 (cImgDrvM live xj Wj ζj xk Wk τ) VL' VR' B'
        (cImgLifeM live xj Wj ζj xk Wk τ)

/-- **Pathwise regularity for the image chain** at the sample `ω`: curve `j`'s driver is continuous before its
lifetime and starts at `0`; curve `k`'s driver starts at `0` and, at every live time `t`, is continuous slightly
beyond `t`, and the image source `src t ω` is `g_t(xj)` (the canonical image source) when the contact time is
positive. -/
def ChainReg (live : ℝ≥0 → Ω → Prop) (xj : ℝ) (Wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Ω → ℝ) (src : ℝ≥0 → Ω → ℝ) (ω : Ω) : Prop :=
  (∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (Wj · ω)) (Icc 0 T)) ∧ Wj 0 ω = 0 ∧
    Wk 0 ω = 0 ∧ ∀ t : ℝ≥0, live t ω →
      (∃ τ' : ℝ, (t : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · ω)) (Icc 0 τ')) ∧
      (0 < contactTime xj (Strip.extPath (Wj · ω)) (ζj ω) xk (Strip.extPath (Wk · ω)) t →
        src t ω = imgDrv xj (Strip.extPath (Wj · ω)) (ζj ω) xk (Strip.extPath (Wk · ω)) t 0)

theorem extPath_zero_of {f : ℝ≥0 → ℝ} (h : f 0 = 0) : Strip.extPath f 0 = 0 := by
  simp [Strip.extPath, h]

omit mΩ in
/-- **The pathwise image chain of the canonical processes**: under `ChainReg` at `ω` and on the live event, the
canonical image driver read on `ℝ`, the canonical clock and lifetime form an image chain from the source `src`. -/
theorem isImageChainUpTo_cImg {live : ℝ≥0 → Ω → Prop} {xj : ℝ} {Wj : ℝ≥0 → Ω → ℝ} {ζj : Ω → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → Ω → ℝ} {src : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0} {ω : Ω}
    (hω : ChainReg live xj Wj ζj xk Wk src ω) (hlive : live (τ ω) ω) :
    IsImageChainUpTo xj (Strip.extPath (Wj · ω)) (ζj ω) xk (Strip.extPath (Wk · ω)) (τ ω) (src (τ ω) ω)
      (Strip.extPath (cImgDrv xj Wj ζj xk Wk τ · ω)) (cImgClk xj Wj xk Wk τ ω) (cImgLife xj Wj ζj xk Wk τ ω) := by
  obtain ⟨hj, hj0, hk0, hk⟩ := hω
  obtain ⟨hkc, hsrc⟩ := hk (τ ω) hlive
  have hch := isImageChainUpTo_canonical (xj := xj) (xk := xk) (ζj := ζj ω) hj (extPath_zero_of hj0) hkc
    (extPath_zero_of hk0) (τ ω).coe_nonneg (src (τ ω) ω)
  refine IsImageChainUpTo.congr_drv hch fun hc σ hσ => ?_
  simp only [Strip.extPath, cImgDrv, cImgSrc, Real.coe_toNNReal σ hσ, hsrc hc]

/-- **`IsCondImageLaw` from its canonical form** (A1DUAL's "What remains" 1: the link `IsImageChainUpTo` is pathwise):
if `ChainReg` holds almost surely, the canonical conditional image law gives A2X's conditional image law with the
image source `src`. -/
theorem isCondImageLaw_of_canon {a : ℝ} {nL nR : ℕ} {P : Measure Ω} {𝓕k : Filtration ℝ≥0 mΩ}
    {live : ℝ≥0 → Ω → Prop} {xj : ℝ} {Wj : ℝ≥0 → Ω → ℝ} {ζj : Ω → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Ω → ℝ}
    {src : ℝ≥0 → Ω → ℝ} {ΘL : ℝ≥0 → Ω → Fin nL → ℝ} {ΘR : ℝ≥0 → Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hreg : ∀ᵐ ω ∂P, ChainReg live xj Wj ζj xk Wk src ω)
    (h : IsCanonImageLaw a P 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    IsCondImageLaw a P 𝓕k live xj Wj ζj xk Wk src ΘL ΘR ρL ρR := by
  intro τ hτ
  obtain ⟨𝓖, VL', VR', B', hev⟩ := h τ hτ
  refine ⟨𝓖, cImgDrvM live xj Wj ζj xk Wk τ, VL', VR', B', cImgLifeM live xj Wj ζj xk Wk τ,
    cImgClk xj Wj xk Wk τ, hev, ?_⟩
  filter_upwards [hreg] with ω hω hlive
  have e1 : (fun t => cImgDrvM live xj Wj ζj xk Wk τ t ω) = fun t => cImgDrv xj Wj ζj xk Wk τ t ω :=
    funext fun t => by simp only [cImgDrvM, hlive, ↓reduceIte]
  have e2 : cImgLifeM live xj Wj ζj xk Wk τ ω = cImgLife xj Wj ζj xk Wk τ ω := by
    simp only [cImgLifeM, hlive, ↓reduceIte]
  rw [e1, e2]
  exact isImageChainUpTo_cImg hω hlive

end Canon

end InteractingSLE.ZhanGT4.A1Ref
