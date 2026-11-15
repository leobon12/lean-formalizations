/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactS5
import InteractingSLE.Spec.Sec7.Lemma71CClock

/-!
# Step (S4) of the contact step, deterministic part: one image chain for all pre-contact times

Packet PROVE-WW-B15. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition
4.18 (text dump L1626–1627): "Map this domain to `H`, taking the start to `0` and `β(s)` to `∞`. Before contact, the
simple forward trace has continuous driving in this domain."

PROVE-WW-B14's `exists_imageTrace` gives, for each fixed time `t` before contact, a driver of the image `Ψ(α((0, t]))`
(chosen separately for each `t`). This file assembles **one** driver for all pre-contact times, with the capacity clock
`σ = Lemma71C.capClock (Ψ ∘ α)` (the capacity clock of Lemma 7.1's mapped segments), for a general *killed arc*: a curve
`γ` that is a simple arc in `ℍ` on an initial interval `P` of `[0, ∞)` open at its right end.

* `IsKilledArc γ P`: the hypotheses;
* `IsKilledArc.exists_localDriver`: on each `[0, S]`, `S ∈ P`, a continuous driver whose hull at `σ(u)` is `γ((0, u])`
  (Proposition 6.12 for compact simple curves, `exists_trace_of_simple`), and `σ` is its capacity clock
  (`Lemma71.hcapSet_eq_of_fwdHull_eq`);
* `IsKilledArc.strictMonoOn_capClock`, `IsKilledArc.continuousOn_capClock`, `IsKilledArc.capClock_zero`;
* `locDrv γ S`, `chainDrv γ P` (definitions, by choice): the local drivers and the glued driver;
* **`IsKilledArc.chainDrv_spec`**: on each `[0, σ(S)]`, `S ∈ P`, the glued driver agrees with a continuous driver
  started at `0` whose hulls at `σ(u)`, `u ≤ S`, are `γ((0, u])` (uniqueness of drivers with given hulls,
  `Sec6.eqOn_of_fwdHull_eq`);
* **`IsKilledArc.fwdHull_eq_of_eqOn_chainDrv`**: every driver agreeing with the glued driver on the chain's capacity
  range has the hulls `γ((0, u])` at `σ(u)`, `u ∈ P`.

Then for the forward line `α` and the chart `Ψ = revChart W_β s` of `ℍ \ G`:

* `imgCurve W s α` (`0` at nonpositive times, `Ψ ∘ α` at positive ones) is a killed arc on `preContact α G`
  (**`isKilledArc_imgCurve`**);
* `ImageDriverStatement` (**named input**, the probabilistic remainder of step (S4)): almost surely the glued driver
  of the image chain has a continuation `X̂` (continuous, `X̂(0) = 0`) whose Loewner trace is a simple proper arc;
* **`imageHullStatement_of_imageDriver`**, **`reverseTipContactStatement_of_imageDriver`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open LQGMetric (DistOn TestOn)
open LawUnique

/-! ### Killed arcs and their capacity clock -/

section Chain

/-- **A killed arc**: `γ` is a simple arc from `0` into `ℍ` on an initial interval `P` of `[0, ∞)` that is open at its
right end (the pre-contact times of the image of the forward line). -/
structure IsKilledArc (γ : ℝ → ℂ) (P : Set ℝ) : Prop where
  zero_mem : (0 : ℝ) ∈ P
  nonneg : ∀ u ∈ P, 0 ≤ u
  icc : ∀ S ∈ P, Icc 0 S ⊆ P
  exists_gt : ∀ S ∈ P, ∃ S' ∈ P, S < S'
  zero : γ 0 = 0
  cont : ContinuousOn γ P
  inj : InjOn γ P
  mem_H : ∀ u ∈ P, 0 < u → γ u ∈ H

variable {γ : ℝ → ℂ} {P : Set ℝ}

theorem IsKilledArc.fillH_eq (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) :
    fillH (γ '' Icc 0 S) = γ '' Ioc 0 S :=
  YuanCharacterisation.fillH_image_eq (hγ.nonneg S hS) (hγ.cont.mono (hγ.icc S hS)) (hγ.inj.mono (hγ.icc S hS))
    (by rw [hγ.zero, zero_im]) fun v hv => hγ.mem_H v (hγ.icc S hS ⟨hv.1.le, hv.2⟩) hv.1

/-- **Local drivers**: on each `[0, S]`, `0 < S ∈ P`, a continuous driver started at `0` whose hull at the capacity
time `σ(u)` is `γ((0, u])`; on `[0, S]` the clock `σ` is continuous and strictly increasing. -/
theorem IsKilledArc.exists_localDriver (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ capClock γ 0 = 0 ∧ StrictMonoOn (capClock γ) (Icc 0 S) ∧
      ContinuousOn (capClock γ) (Icc 0 S) ∧
      ∀ u ∈ Icc 0 S, 0 ≤ capClock γ u ∧ fwdHull W (capClock γ u) = γ '' Ioc 0 u := by
  have hsub := hγ.icc S hS
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσ, -⟩ := exists_trace_of_simple hS0 (hγ.cont.mono hsub)
    (hγ.inj.mono hsub) hγ.zero (fun u hu => hγ.mem_H u (hsub ⟨hu.1.le, hu.2⟩) hu.1)
    (t := S / 2) ⟨by linarith, by linarith⟩
  have hσnn : ∀ u ∈ Icc 0 S, 0 ≤ σ u := fun u hu => by
    rw [← hσ0]; exact hσm.monotoneOn ⟨le_rfl, hS0.le⟩ hu hu.1
  have heq : EqOn σ (capClock γ) (Icc 0 S) := fun u hu => by
    have h1 : fwdHull W (σ u) = fillH (γ '' Icc 0 u) := by
      rw [hσ u hu, hγ.fillH_eq (hsub ⟨hu.1, hu.2⟩)]
    have := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 (hσnn u hu) h1
    simp only [capClock, this]
    ring
  refine ⟨W, hW, hW0, ?_, hσm.congr heq, hσc.congr heq.symm, fun u hu => ?_⟩
  · rw [← heq ⟨le_rfl, hS0.le⟩, hσ0]
  rw [← heq hu]
  exact ⟨hσnn u hu, hσ u hu⟩

theorem IsKilledArc.capClock_zero (hγ : IsKilledArc γ P) : capClock γ 0 = 0 := by
  obtain ⟨S, hS, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  exact (hγ.exists_localDriver hS hS0).choose_spec.2.2.1

theorem IsKilledArc.strictMonoOn_capClock (hγ : IsKilledArc γ P) : StrictMonoOn (capClock γ) P := by
  intro a ha b hb hab
  have hb0 : 0 < b := lt_of_le_of_lt (hγ.nonneg a ha) hab
  obtain ⟨-, -, -, -, hm, -, -⟩ := hγ.exists_localDriver hb hb0
  exact hm ⟨hγ.nonneg a ha, hab.le⟩ ⟨hb0.le, le_rfl⟩ hab

theorem IsKilledArc.continuousOn_capClock (hγ : IsKilledArc γ P) : ContinuousOn (capClock γ) P := by
  intro t ht
  obtain ⟨S, hS, htS⟩ := hγ.exists_gt t ht
  have hS0 : 0 < S := lt_of_le_of_lt (hγ.nonneg t ht) htS
  obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.exists_localDriver hS hS0
  have hnhds : Icc 0 S ∈ 𝓝[P] t := by
    refine mem_nhdsWithin.2 ⟨Iio S, isOpen_Iio, htS, fun u hu => ⟨hγ.nonneg u hu.2, le_of_lt hu.1⟩⟩
  exact (hc t ⟨hγ.nonneg t ht, htS.le⟩).mono_of_mem_nhdsWithin hnhds

theorem IsKilledArc.capClock_nonneg (hγ : IsKilledArc γ P) {u : ℝ} (hu : u ∈ P) : 0 ≤ capClock γ u := by
  rw [← hγ.capClock_zero]
  exact hγ.strictMonoOn_capClock.monotoneOn hγ.zero_mem hu (hγ.nonneg u hu)

/-! ### The glued driver -/

open scoped Classical in
/-- A local driver on `[0, S]` (chosen; `0` if there is none). -/
def locDrv (γ : ℝ → ℂ) (S : ℝ) : ℝ → ℝ :=
  if h : ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ u ∈ Icc 0 S, fwdHull W (capClock γ u) = γ '' Ioc 0 u then
    h.choose else 0

open scoped Classical in
/-- **The glued driver of a killed arc**: at a capacity time `r`, the local driver of some `S ∈ P` with `r ≤ σ(S)`. -/
def chainDrv (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) : ℝ :=
  if h : ∃ S ∈ P, 0 < S ∧ r ≤ capClock γ S then locDrv γ h.choose r else 0

theorem IsKilledArc.locDrv_spec (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) :
    Continuous (locDrv γ S) ∧ locDrv γ S 0 = 0 ∧
      ∀ u ∈ Icc 0 S, fwdHull (locDrv γ S) (capClock γ u) = γ '' Ioc 0 u := by
  classical
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.exists_localDriver hS hS0
  have hex : ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ u ∈ Icc 0 S, fwdHull W (capClock γ u) = γ '' Ioc 0 u :=
    ⟨W, hW, hW0, fun u hu => (hK u hu).2⟩
  rw [locDrv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

/-- **Two local drivers agree** on the common capacity range (`Sec6.eqOn_of_fwdHull_eq`: drivers with the same hulls
agree). -/
theorem IsKilledArc.locDrv_eqOn (hγ : IsKilledArc γ P) {S₁ S₂ : ℝ} (hS₁ : S₁ ∈ P) (hS₂ : S₂ ∈ P) (h1 : 0 < S₁)
    (h12 : S₁ ≤ S₂) : EqOn (locDrv γ S₁) (locDrv γ S₂) (Icc 0 (capClock γ S₁)) := by
  have h2 : 0 < S₂ := lt_of_lt_of_le h1 h12
  obtain ⟨hc₁, h0₁, hK₁⟩ := hγ.locDrv_spec hS₁ h1
  obtain ⟨hc₂, h0₂, hK₂⟩ := hγ.locDrv_spec hS₂ h2
  obtain ⟨-, -, -, -, -, hcc, -⟩ := hγ.exists_localDriver hS₁ h1
  refine Sec6.eqOn_of_fwdHull_eq hc₁ hc₂ h0₁ h0₂ (hγ.capClock_nonneg hS₁) fun r hr => ?_
  obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc h1.le hcc (by rw [hγ.capClock_zero]; exact hr)
  rw [hK₁ u hu, hK₂ u ⟨hu.1, hu.2.trans h12⟩]

/-- **The glued driver**: on each `[0, σ(S)]`, `0 < S ∈ P`, it is the local driver of `S`. -/
theorem IsKilledArc.chainDrv_eq (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) :
    EqOn (chainDrv γ P) (locDrv γ S) (Icc 0 (capClock γ S)) := by
  classical
  intro r hr
  have hex : ∃ S ∈ P, 0 < S ∧ r ≤ capClock γ S := ⟨S, hS, hS0, hr.2⟩
  rw [chainDrv, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hS₁, h1, hr₁⟩ := hex.choose_spec
  rcases le_total hex.choose S with hle | hle
  · exact hγ.locDrv_eqOn hS₁ hS h1 hle ⟨hr.1, hr₁⟩
  · exact (hγ.locDrv_eqOn hS hS₁ hS0 hle hr).symm

/-- **The glued driver of a killed arc**: on each `[0, σ(S)]` it agrees with a continuous driver started at `0` whose
hulls at the capacity times `σ(u)`, `u ≤ S`, are `γ((0, u])`. -/
theorem IsKilledArc.chainDrv_spec (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ EqOn (chainDrv γ P) W (Icc 0 (capClock γ S)) ∧
      ∀ u ∈ Icc 0 S, fwdHull W (capClock γ u) = γ '' Ioc 0 u := by
  obtain ⟨hc, h0, hK⟩ := hγ.locDrv_spec hS hS0
  exact ⟨locDrv γ S, hc, h0, hγ.chainDrv_eq hS hS0, hK⟩

/-- **Hulls of a continuation**: a driver agreeing with the glued driver on `[0, σ(S)]` for every `S ∈ P` has the hull
`γ((0, u])` at `σ(u)`, for every `u ∈ P`. -/
theorem IsKilledArc.fwdHull_eq_of_eqOn_chainDrv (hγ : IsKilledArc γ P) {X : ℝ → ℝ}
    (hX : ∀ S ∈ P, EqOn X (chainDrv γ P) (Icc 0 (capClock γ S))) {u : ℝ} (hu : u ∈ P) :
    fwdHull X (capClock γ u) = γ '' Ioc 0 u := by
  obtain ⟨S, hS, huS⟩ := hγ.exists_gt u hu
  have hS0 : 0 < S := lt_of_le_of_lt (hγ.nonneg u hu) huS
  obtain ⟨W, -, -, hEq, hK⟩ := hγ.chainDrv_spec hS hS0
  have hlt : capClock γ u < capClock γ S := hγ.strictMonoOn_capClock hu hS huS
  rw [fwdHull_eq_of_eqOn (hγ.capClock_nonneg hu) hlt fun r hr => (hX S hS hr).trans (hEq hr),
    hK u ⟨hγ.nonneg u hu, huS.le⟩]

end Chain

/-! ### The image of the forward line is a killed arc -/

section Image

variable {W : ℝ → ℝ} {s : ℝ} {α : ℝ → ℂ}

/-- **The image curve** `Ψ ∘ α` of the forward line in the chart `Ψ = revChart W s` (`0` at nonpositive times). -/
def imgCurve (W : ℝ → ℝ) (s : ℝ) (α : ℝ → ℂ) (u : ℝ) : ℂ := if u ≤ 0 then 0 else revChart W s (α u)

theorem imgCurve_of_pos {u : ℝ} (hu : 0 < u) : imgCurve W s α u = revChart W s (α u) := by
  simp only [imgCurve, not_le.2 hu, ↓reduceIte]

theorem imgCurve_zero : imgCurve W s α 0 = 0 := by simp [imgCurve]

theorem image_imgCurve_Ioc (t : ℝ) : imgCurve W s α '' Ioc 0 t = revChart W s '' (α '' Ioc 0 t) := by
  rw [image_image]
  exact image_congr fun u hu => imgCurve_of_pos hu.1

/-- **The image of the forward line before contact is a killed arc** (Wang–Wu, proof of Proposition 4.18: "Before
contact, the simple forward trace has continuous driving in this domain"; PROVE-WW-B14's `exists_imageTrace` on each
compact pre-contact interval). -/
theorem isKilledArc_imgCurve (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) (hG : IsClosed (negInv '' fwdHull W s))
    (hα : IsProperArc α) : IsKilledArc (imgCurve W s α) (preContact α (negInv '' fwdHull W s)) := by
  set G := negInv '' fwdHull W s with hGdef
  have hGH : G ⊆ H := fun z ⟨w, hw, e⟩ => e ▸ negInv_mem_H hw.1
  have hmem : ∀ u ∈ preContact α G, 0 < u → α u ∈ H \ G := fun u hu hpos =>
    ⟨hα.mem_H u hpos, hu.2 u ⟨hu.1, le_rfl⟩⟩
  have h0P : (0 : ℝ) ∈ preContact α G := by
    refine ⟨le_rfl, fun u hu hu' => ?_⟩
    obtain rfl : u = 0 := le_antisymm hu.2 hu.1
    have := hGH hu'
    rw [hα.zero] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  refine ⟨h0P, fun u hu => hu.1, fun S hS => Icc_subset_preContact hS, fun S hS => ?_, imgCurve_zero, ?_, ?_,
    fun u hu hpos => ?_⟩
  · obtain ⟨S', hSS', hS'⟩ := exists_gt_forall_notMem hG hα.cont hS.2
    exact ⟨S', ⟨(hS.1.trans hSS'.le), hS'⟩, hSS'⟩
  · -- continuity
    intro u hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · rw [← h0, Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hR⟩ := Metric.tendsto_nhdsWithin_nhds.1 (tendsto_revChart_zero hW hW0 hs) ε hε
      obtain ⟨δ₂, hδ₂, hαδ⟩ := Metric.continuousWithinAt_iff.1 (hα.cont 0 self_mem_Ici) δ₁ hδ₁
      refine ⟨δ₂, hδ₂, fun {v} hv hvd => ?_⟩
      rw [imgCurve_zero, dist_zero_right]
      rcases hv.1.eq_or_lt with hv0 | hvpos
      · rw [← hv0, imgCurve_zero, norm_zero]; exact hε
      · rw [imgCurve_of_pos hvpos]
        have h1 := hαδ (mem_Ici.2 hv.1) hvd
        rw [hα.zero] at h1
        have h2 := hR (hmem v hv hvpos) h1
        rwa [dist_zero_right] at h2
    · have hcα : ContinuousAt α u := hα.cont.continuousAt (Ici_mem_nhds hpos)
      have hcR : ContinuousAt (revChart W s) (α u) :=
        (continuousOn_revChart hW hs).continuousAt
          ((isOpen_H_diff_negInv_fwdHull hW hs).mem_nhds (hmem u hu hpos))
      have hcA : ContinuousAt (fun v => revChart W s (α v)) u := hcR.comp hcα
      refine (hcA.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hpos] with v hv
      exact (imgCurve_of_pos hv).symm
  · -- injectivity
    have hH : ∀ u ∈ preContact α G, 0 < u → imgCurve W s α u ∈ H := fun u hu hpos => by
      rw [imgCurve_of_pos hpos]; exact revChart_mem_H hW hs (hmem u hu hpos)
    intro u hu v hv e
    rcases hu.1.eq_or_lt with hu0 | hupos <;> rcases hv.1.eq_or_lt with hv0 | hvpos
    · rw [← hu0, ← hv0]
    · exfalso
      have := hH v hv hvpos
      rw [← e, ← hu0, imgCurve_zero] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exfalso
      have := hH u hu hupos
      rw [e, ← hv0, imgCurve_zero] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · rw [imgCurve_of_pos hupos, imgCurve_of_pos hvpos] at e
      have e2 := injOn_revChart hW hW0 hs (hmem u hu hupos) (hmem v hv hvpos) e
      exact hα.inj (mem_Ici.2 hu.1) (mem_Ici.2 hv.1) e2
  · rw [imgCurve_of_pos hpos]; exact revChart_mem_H hW hs (hmem u hu hpos)

end Image

/-! ### The probabilistic remainder of step (S4) -/

section Reduction

/-- **Named input: the probabilistic remainder of step (S4) of the contact step** (Wang–Wu, proof of Proposition 4.18,
text dump L1627–1629: "Its conditional harmonic means and conformal-radius brackets, just identified, satisfy Lemma
2.11. Hence its law is the nonnegative-cumulative force-point law. The trace lemma and Corollary 4.13 imply …"). In the
setting of `ReverseTipContactStatement`, for each rational `s > 0`, almost surely on the glued space the glued driver
`chainDrv` of the image chain `Ψ ∘ α` (before the first contact of the forward line with `G = R(β((0, s]))`) has a
continuation: a continuous driver `X̂` with `X̂(0) = 0`, equal to the glued driver on the capacity range of every
pre-contact prefix, whose Loewner trace is a simple proper arc. (Proof route: the image driver is `SLE₄(r_L, −r_L; r_R,
−r_R)` killed at the end of the image, by Lemma 2.11 in the filtration enlarged by the reverse line; continued after its
end by an independent Brownian motion it is an `SLE₄(ρ)` chain with nonnegative cumulative weights `r, 0`, whose trace is
simple, in `ℍ` at positive times (Lemma 4.12) and transient.) -/
def ImageDriverStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s → ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
          ∃ Xh : ℝ → ℝ, Continuous Xh ∧ Xh 0 = 0 ∧ (∃ η : ℝ → ℂ, IsLoewnerTrace Xh η ∧ IsProperArc η) ∧
            ∀ S ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2),
              EqOn Xh (chainDrv (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1))
                  (preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)))
                (Icc 0 (capClock (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1)) S))

/-- `ImageHullStatement` from the probabilistic remainder: the clock is the capacity clock of the image chain, and the
hulls of the continuation are those of the glued driver (`IsKilledArc.fwdHull_eq_of_eqOn_chainDrv`). -/
theorem imageHullStatement_of_imageDriver (hI : ImageDriverStatement.{u}) : ImageHullStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  have hh : Measurable h := hC.2.1
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hC₂.2.1
  have hD₂ := measurable_killedHistory hC₂.2.2.2.1
  have hgood := ae_glue_fst (μ := P) k hh (ae_good_twoSeed hL hR hC.1)
  have hbeta : ∀ᵐ p ∂(glueMeasure P k h hh), p.2 ∈ BetaSet s :=
    ae_glue_snd hh hRh₂ hD₂ hlaw k hk (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR hL hC₂.1 hs)
  have hgh := ae_goodHist_snd_glue hL hR hC hC₂ hlaw k hk s
  filter_upwards [hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs, hgood, hbeta,
    hgh] with p hp hpα hpβ hpg
  obtain ⟨Xh, hXc, hX0, ⟨η, hη, hηp⟩, hEq⟩ := hp
  obtain ⟨hcont, h0, -, -, hhull, -, -⟩ := trace_of_mem_betaSet hs hpβ
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hG : IsClosed (negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s) := by
    rw [← hhull]; exact isClosed_image_negInv_histHull hs hpg
  have hK := isKilledArc_imgCurve hcont h0 hs' hG hpα.1
  rw [hhull] at hEq ⊢
  refine ⟨Xh, hXc, hX0, η, hη, hηp, _, hK.continuousOn_capClock, hK.strictMonoOn_capClock, hK.capClock_zero,
    fun t ht _ => ?_⟩
  rw [hK.fwdHull_eq_of_eqOn_chainDrv hEq ht, image_imgCurve_Ioc]

/-- **The contact step from the probabilistic remainder of step (S4).** -/
theorem reverseTipContactStatement_of_imageDriver (hI : ImageDriverStatement.{u}) :
    ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_imageHull (imageHullStatement_of_imageDriver hI)

end Reduction

end InteractingSLE.WangWu
