import InteractingSLE.Foundations.SLE.Transience
import InteractingSLE.Foundations.SLE.SpaceFilling.Swallow
import InteractingSLE.Foundations.SLE.SpaceFilling.HitFinal
import InteractingSLE.SLE8.SpaceFilling.Theorem
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Ordinary chordal SLE_κ for every κ > 0

Packet PROVE-SLE-ALL. This file collects the regime-by-regime results already in the project
into statements for every parameter. They are stated in the forms that the design core
(`planning/INFRA-GEO.md` §3–4, packet GEO-RSALL) and the specification use. Throughout, `B` is a
standard real Brownian motion on any probability space, in any universe, and the driver is
`W_t = √κ B_t`.

* **Trace.** For every `κ > 0`, almost surely QuantumZipper's radial-limit trace
  `η(t) = lim_{y ↓ 0} f_t⁻¹(iy)` is a continuous Loewner trace (`ae_isLoewnerTrace_sleTrace`).
  It is also the frozen `IsGeneratingTrace` on `[0, ∞)`, it is the only generating trace, and it
  is transient (`ae_isGeneratingTrace_sleTrace`, and the design statement `ae_exists_trace_all`).
  The cases are QuantumZipper (`κ < 8`), the sealed SLE₈ anchor (`κ = 8`) and GEO-RS8 (`κ > 8`).
  A measurable continuous version exists for every `κ > 0` (`exists_measurable_sleTrace_of_pos`).
* **Transience** [RS05, Theorem 7.1]: `|η(t)| → ∞` for every `κ > 0`
  (`ae_tendsto_norm_sleTrace_of_pos`), together with the design statement
  `ae_tendsto_norm_sleTrace` (`κ ≠ 8`).
* **[RS05, Lemma 7.3]** for every `κ > 4`, in the specification's simultaneous form (p. 149, in
  the proof of Proposition 5.13). Almost surely every positive-time hull contains an upper
  half-neighbourhood of `0` (`ae_forall_sleHull_halfBall_of_four_lt`).
* **[RS05, Corollary 7.4]** for every `κ ≥ 8`: `η[0, ∞) = ℍ̄`
  (`ae_sleTrace_image_eq_Hbar_of_eight_le`). This is the "independent ordinary input" of SF3
  (p. 602) and Section 23 (p. 603). The file also proves the pathwise consequence (SFL0) of p. 603
  and p. 646: on one event, `K_t ⊆ η([0, t])` for every finite `t`
  (`ae_forall_sleHull_subset_sleTrace_image_of_eight_le`, and the combined
  `ae_spaceFilling_of_eight_le`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper

/-! ### Deterministic bridge: a continuous Loewner trace is the frozen generating trace -/

section Deterministic

/-- The image of `[0, t]` under a function of `ℝ`, read on `ℝ≥0`, is its image of the real
interval `[0, t]`. -/
theorem image_coe_Icc_eq (η : ℝ → ℂ) (t : ℝ≥0) :
    (fun s : ℝ≥0 => η s) '' Icc 0 t = η '' Icc 0 (t : ℝ) := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, ⟨s.2, NNReal.coe_le_coe.2 hs.2⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.toNNReal, ⟨bot_le, ?_⟩, by simp [Real.coe_toNNReal _ hs.1]⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2

/-- A continuous Loewner trace on `[0, ∞)` of the extended driver `s ↦ w s.toNNReal` is, read on
`ℝ≥0`, a continuous generating trace in the sense of the frozen `IsGeneratingTrace` with
`T = ∞`. This is the converse of `isLoewnerTrace_of_isGeneratingTrace`. -/
theorem IsLoewnerTrace.isGeneratingTrace {w : ℝ≥0 → ℝ} {η : ℝ → ℂ}
    (h : IsLoewnerTrace (fun s : ℝ => w s.toNNReal) η) :
    IsGeneratingTrace w ⊤ (fun t : ℝ≥0 => η t) := by
  obtain ⟨h0, hc, hfill⟩ := h
  have hcont : Continuous (fun t : ℝ≥0 => η t) :=
    hc.comp_continuous NNReal.continuous_coe fun t => t.2
  refine ⟨by simpa using h0, hcont.continuousOn, fun t _ => ?_⟩
  have hA : IsCompact (η '' Icc 0 (t : ℝ)) :=
    isCompact_Icc.image_of_continuousOn (hc.mono Icc_subset_Ici_self)
  rw [image_coe_Icc_eq]
  exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).2 (hfill t t.2)

/-- **Radial limits** of a continuous Loewner trace: `f_t⁻¹(iy) → η(t)` as `y ↓ 0`, for `t ≥ 0`. -/
theorem IsLoewnerTrace.tendsto_fwdMapInv_mul_I {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (η t)) := by
  refine (hη.tendsto_fwdMapInv_tip hW hW0 ht).comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun y hy => ?_⟩
  · have h1 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      (continuous_ofReal.mul continuous_const).tendsto 0
    simpa using h1.mono_left nhdsWithin_le_nhds
  · show 0 < ((y : ℂ) * I).im
    simpa using hy

end Deterministic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The trace for every `κ > 0` -/

section Trace

/-- **The SLE_κ trace exists for every `κ > 0`.** For a Brownian motion `B` on any probability space
(any universe), almost surely the radial-limit trace `sleTrace κ B ω` is a continuous Loewner trace
of the driver `√κ B`. Cases: QuantumZipper's Rohde–Schramm theorem (`κ < 8`), the sealed SLE₈
anchor (`κ = 8`), GEO-RS8 (`κ > 8`). -/
theorem ae_isLoewnerTrace_sleTrace (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (drive κ B ω) (sleTrace κ B ω) := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  rcases lt_trichotomy κ 8 with h8 | rfl | h8
  · exact ae_drive_of_forall_canon hB κ (Q := fun W => IsLoewnerTrace W (trace W))
      fun _ _ hμ => ae_isLoewnerTrace_of_lt_eight hμ hκ h8
  · exact SLE8.ae_isLoewnerTrace_sleTrace_eight hB
  · exact ae_drive_of_forall_canon hB κ (Q := fun W => IsLoewnerTrace W (trace W))
      fun _ _ hμ => ae_isLoewnerTrace_of_eight_lt hμ h8

/-- **Transience for every `κ > 0`** ([RS05, Theorem 7.1], the SLE₈ note's Theorem 1 (ii) at
`κ = 8`): almost surely `|η(t)| → ∞` as `t → ∞`. -/
theorem ae_tendsto_norm_sleTrace_of_pos (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  rcases le_or_gt κ 4 with h4 | h4
  · exact ae_tendsto_norm_sleTrace_of_le_four hB hκ h4
  rcases lt_trichotomy κ 8 with h8 | rfl | h8
  · exact ae_tendsto_norm_sleTrace_of_interior hB hκ h8.ne fun _ _ _ _ _ hB' =>
      (ae_forall_sleHull_halfBall_of_lt_eight hB' h4 h8).mono fun _ h => h 1 one_pos
  · exact SLE8.ae_tendsto_norm_sleTrace_eight hB
  · exact ae_tendsto_norm_sleTrace_of_eight_lt hB h8

/-- **Transience** `|η(t)| → ∞` ([RS05, Thm 7.1]) for `κ > 0`, `κ ≠ 8` — the design statement of
GEO-RSALL (`planning/INFRA-GEO.md` §3), verbatim. The hypothesis `κ ≠ 8` is no longer needed:
see `ae_tendsto_norm_sleTrace_of_pos`. -/
theorem ae_tendsto_norm_sleTrace (hB : IsBrownianReal B P) [IsProbabilityMeasure P] {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ ≠ 8) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖QuantumZipper.sleTrace κ B ω t‖) atTop atTop := by
  exact (fun _ => ae_tendsto_norm_sleTrace_of_pos hB hκ) hκ8

/-- **The ordinary SLE_κ trace in the specification's form, for every `κ > 0`.** Almost surely:
the radial-limit trace, read on `ℝ≥0`, is a continuous generating trace of the driver `√κ B` on
`[0, ∞)` (frozen `IsGeneratingTrace`, `T = ∞`); it is the only one; it is the radial limit
`η(t) = lim_{y ↓ 0} f_t⁻¹(iy)` at every time; and `|η(t)| → ∞`. -/
theorem ae_isGeneratingTrace_sleTrace (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P,
      IsGeneratingTrace (fun t => Real.sqrt κ * B t ω) ⊤ (fun t : ℝ≥0 => sleTrace κ B ω t) ∧
      (∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Real.sqrt κ * B t ω) ⊤ η →
        η = fun t : ℝ≥0 => sleTrace κ B ω t) ∧
      (∀ t : ℝ≥0, Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I)) (𝓝[>] 0)
        (𝓝 (sleTrace κ B ω t))) ∧
      Tendsto (fun t : ℝ≥0 => ‖sleTrace κ B ω t‖) atTop atTop := by
  filter_upwards [ae_isLoewnerTrace_sleTrace hB hκ, ae_tendsto_norm_sleTrace_of_pos hB hκ,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hη htr hc h0
  have hgen : IsGeneratingTrace (fun t => Real.sqrt κ * B t ω) ⊤
      (fun t : ℝ≥0 => sleTrace κ B ω t) := IsLoewnerTrace.isGeneratingTrace hη
  have hw : ContinuousOn (fun t : ℝ≥0 => Real.sqrt κ * B t ω) {s | (s : ℝ≥0∞) < ⊤} :=
    (continuous_const.mul hc).continuousOn
  have hw0 : Real.sqrt κ * B 0 ω = 0 := by rw [h0]; ring
  refine ⟨hgen, fun η hη' => funext fun t => ?_, fun t => ?_, ?_⟩
  · exact ((hη'.trace_eq hw hw0 ENNReal.coe_lt_top).symm.trans
      (hgen.trace_eq hw hw0 ENNReal.coe_lt_top) :)
  · exact hgen.tendsto_fwdMapInv_mul_I hw hw0 ENNReal.coe_lt_top
  · exact htr.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)

/-- **`ae_exists_trace_all`** (design statement of GEO-RSALL, `planning/INFRA-GEO.md` §3: "trace
for every κ > 0, in the ARCH-1 `IsGeneratingTrace` shape"). For ordinary SLE_κ, `κ > 0`, almost
surely a continuous generating trace on `[0, ∞)` exists, and every such trace is transient. This
is the conclusion of Theorem 1.3 for the empty force word (`ζ = ∞`) and the shape that Aux. lemma 7
consumes (`Spec/Sec4/SpecialHeights.lean`). -/
theorem ae_exists_trace_all (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Real.sqrt κ * B t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Real.sqrt κ * B t ω) ⊤ η →
        Tendsto (fun t => ‖η t‖) atTop atTop := by
  filter_upwards [ae_isGeneratingTrace_sleTrace hB hκ] with ω h
  obtain ⟨hgen, huniq, -, htr⟩ := h
  exact ⟨⟨_, hgen⟩, fun η hη => by rw [huniq η hη]; exact htr⟩

/-- **Measurable continuous version for every `κ > 0`** (extends
`exists_measurable_sleTrace_of_ne_eight` to `κ = 8`). -/
theorem exists_measurable_sleTrace_of_pos (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) :
    ∃ η : Ω → ℝ → ℂ, Measurable η ∧ (∀ ω, Continuous (η ω)) ∧
      ∀ᵐ ω ∂P, EqOn (η ω) (sleTrace κ B ω) (Ici 0) := by
  refine exists_measurable_sleTrace_of_tendsto hB ?_
  filter_upwards [ae_isLoewnerTrace_sleTrace hB hκ, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hη hc h0
  have hW := drive_continuous (κ := κ) hc
  have hW0 := drive_zero (κ := κ) h0
  refine ⟨hη.2.1.comp_continuous NNReal.continuous_coe fun t => t.2, fun t ht => ?_⟩
  exact hη.tendsto_fwdMapInv_mul_I hW hW0 ht

end Trace

/-! ### [RS05, Lemma 7.3] for every `κ > 4` -/

section HalfBall

/-- **[RS05, Lemma 7.3] for every `κ > 4`**, in the specification's simultaneous form (p. 149, in
the proof of Proposition 5.13: "for ordinary chordal SLE_κ', κ' > 4, every positive-time hull
contains an upper half-neighborhood of its starting point"; "countability and hull monotonicity
make the assertion simultaneous for all positive times"). Cases: `4 < κ < 8` (PROVE-RS05-74b),
`κ = 8` (the SLE₈ note's Proposition 6, PROVE-SF8-A), `κ > 8` (PROVE-RS05-74c). -/
theorem ae_forall_sleHull_halfBall_of_four_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B ω t := by
  rcases lt_trichotomy κ 8 with h8 | rfl | h8
  · exact ae_forall_sleHull_halfBall_of_lt_eight hB hκ h8
  · exact SLE8.ae_forall_sleHull_halfBall_eight hB
  · exact ae_forall_sleHull_halfBall_of_eight_lt hB h8

end HalfBall

/-! ### [RS05, Corollary 7.4] for every `κ ≥ 8` -/

section SpaceFilling

/-- **[RS05, Corollary 7.4] for every `κ ≥ 8`** (with the update for `κ = 8`, here the SLE₈ note's
Theorem 1 (iii)): almost surely the SLE_κ trace fills the closed half-plane, `η[0, ∞) = ℍ̄`.
Specification p. 602 (SF3) and p. 603 (Section 23, "independent ordinary input"). -/
theorem ae_sleTrace_image_eq_Hbar_of_eight_le (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 ≤ κ) :
    ∀ᵐ ω ∂P, sleTrace κ B ω '' Ici 0 = Hbar := by
  rcases hκ.lt_or_eq with h8 | rfl
  · exact ae_sleTrace_image_eq_Hbar_of_eight_lt hB h8
  · exact SLE8.ae_sleTrace_image_eq_Hbar_eight hB

/-- **Deterministic (SFL0).** If a continuous Loewner trace fills `ℍ̄`, then every finite hull
lies on the trace up to that time: `K_t ⊆ η([0, t])`. A point of `K_t` off `η([0, t])` lies in an
open swallowed component, at positive distance from the whole trace
(`mem_image_or_notMem_closure_of_mem_fwdHull`), and this contradicts `η[0, ∞) = ℍ̄`. -/
theorem fwdHull_subset_image_of_image_eq_Hbar {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hfill : η '' Ici 0 = Hbar) {t : ℝ} (ht : 0 ≤ t) :
    fwdHull W t ⊆ η '' Icc 0 t := by
  intro z hz
  refine (mem_image_or_notMem_closure_of_mem_fwdHull hη hW hW0 ht hz).resolve_right fun hcl => ?_
  have hzH : z ∈ Hbar := le_of_lt (show 0 < z.im from hz.1)
  rw [← hfill] at hzH
  exact hcl (subset_closure hzH)

/-- **(SFL0) for every `κ ≥ 8`** (Specification p. 603 and p. 646: "on one event, every finite
ordinary hull satisfies `K_t ∩ ℍ ⊆ η([0, t])`, `0 ≤ t < ∞`"; QuantumZipper's hulls lie in `ℍ`). -/
theorem ae_forall_sleHull_subset_sleTrace_image_of_eight_le (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 8 ≤ κ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → sleHull κ B ω t ⊆ sleTrace κ B ω '' Icc 0 t := by
  filter_upwards [ae_isLoewnerTrace_sleTrace hB (by linarith : (0 : ℝ) < κ),
    ae_sleTrace_image_eq_Hbar_of_eight_le hB hκ, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hη hfill hc h0 t ht
  exact fwdHull_subset_image_of_image_eq_Hbar hη (drive_continuous hc) (drive_zero h0) hfill ht

/-- **Ordinary SLE_κ is space filling for every `κ ≥ 8`**, in the specification's form (SF3,
Section 23, p. 646): almost surely the continuous generating trace `η` on `[0, ∞)` (frozen
`IsGeneratingTrace`; it is unique, `ae_isGeneratingTrace_sleTrace`) has range `ℍ̄`, and every
finite hull lies on it: `K_t ⊆ η([0, t])` for all `t`. -/
theorem ae_spaceFilling_of_eight_le (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 ≤ κ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Real.sqrt κ * B t ω) ⊤ η →
      range η = Hbar ∧
        ∀ t : ℝ≥0, fwdHull (drive κ B ω) t ⊆ η '' Icc 0 t := by
  filter_upwards [ae_isGeneratingTrace_sleTrace hB (by linarith : (0 : ℝ) < κ),
    ae_sleTrace_image_eq_Hbar_of_eight_le hB hκ,
    ae_forall_sleHull_subset_sleTrace_image_of_eight_le hB hκ] with ω hgen hfill hsub η hη
  rw [hgen.2.1 η hη]
  refine ⟨?_, fun t => ?_⟩
  · rw [← hfill, ← image_univ]
    ext z
    constructor
    · rintro ⟨s, -, rfl⟩
      exact ⟨s, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.toNNReal, mem_univ _, by simp [Real.coe_toNNReal _ hs]⟩
  · rw [image_coe_Icc_eq]
    exact hsub t t.2

end SpaceFilling

end InteractingSLE
