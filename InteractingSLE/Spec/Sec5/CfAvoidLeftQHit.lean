/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Sec5.CfLineRegQSeed

/-!
# Boundary non-hitting for admissible words, every `κ > 0` (Aux. lemmas 24 and 6 combined, beyond `κ < 4`)

Packet PROVE-SEC5-R, toward `Prop51Q.CfAvoidLeftQStatement`: once the counterflow is read in the chart of the
complement of the flow-line prefix and then in the chart `R`, the left part of `∂(ℍ \ η(0, t])` becomes the positive
half-line, and the counterflow avoids it because its side partial sums there are admissible. This is Aux. lemma 24's
non-hitting at `κ′ = 16/κ > 4`, which PROVE-SEC5-Q lists as missing (its "What remains" 1(b): "a real contact
`η(t) = x > 0` makes the seed mark `0⁺` collide … This contradicts Aux. 6's separation"). This file proves it.

**Deterministic core** (`vR_eq_w_of_off`): PROVE-LEMMA76E's `Lemma76E.vR_eq_w_of_le` without its injectivity and
rightmost-visit hypotheses. If the trace visits a real point `X > 0` at time `u > 0` and stays off `[X, ∞)` before `u`,
then every right mark `x_i ≤ X` is merged with the driver at `u`: before `u`, `X` is alive and dominates the mark
(`V^i − W ≤ g(X) − W`), its gap becomes arbitrarily small just before `u` (otherwise `X` would be alive at `u`,
contradicting `Lemma76E.not_alive_of_visit`), and the gap of the mark is continuous.

**First visit** (`exists_first_visit`): a continuous trace from `0` that visits a real point `X₀ > 0` has a first visit
time `u > 0` of the closed set `[X₀, ∞)`, at a point `X ≥ X₀`; before `u` it stays off `[X₀, ∞) ⊇ [X, ∞)`.

**Non-hitting.** Aux. lemma 6 (`Sec4.aux6Statement`, proved for every `κ > 0`) separates every mark from the driver at
positive times; so a visit of `(x_i, ∞)`-type points is impossible on the right (`trace_ne_of_lt_of_sep`,
`ae_trace_ne_pos`), and by the reflection `z ↦ −z̄` on the left (`ae_trace_ne_neg`). With PROVE-SEC5-R's
`ae_trace_ne_zero_of_seed` (no return to the seed), the trace of an admissible seed word is never real at positive times
(`ae_trace_im_ne_zero_of_seed`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC fwdHull IsForwardSol)

universe u

namespace InteractingSLE.Sec5.CfAvoidLeftQ

open MartChar.RealFlow Sec7 Sec7.Lemma76E

/-! ### The merge lemma without injectivity -/

section Merge

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- **A right mark at or before a first-visited real point is merged with the driver** (`u > 0`): if the trace visits
`X > 0` at time `u` and stays off `[X, ∞)` on `[0, t]` for every `t < u`, then every right mark `x_i ≤ X` satisfies
`V^i_u = W_u`. (`Lemma76E.vR_eq_w_of_le` without injectivity of the trace.) -/
theorem vR_eq_w_of_off (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ) (hg : IsGeneratingTrace w ζ γ)
    {u : ℝ≥0} (hu0 : 0 < u) (hu : (u : ℝ≥0∞) < ζ) {X : ℝ} (hX0 : 0 < X) (hvis : γ u = X)
    (hoff : ∀ t : ℝ≥0, t < u → ∀ s ≤ t, ∀ r : ℝ, X ≤ r → γ s ≠ r) {i : Fin nR} (hi : xR i ≤ X) :
    vR i u = w u := by
  have hF := hp.isForcePath
  obtain ⟨t₂, hut₂, ht₂ζ⟩ := Supp7.G11.exists_real_gt_lt hu
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hF.continuousOn_w ht₂ζ
  have hWw : ∀ t : ℝ≥0, (t : ℝ) ≤ t₂ → W t = w t := fun t ht => by
    rw [hWdef, frozenDrive_eq ⟨t.coe_nonneg, ht⟩, Real.toNNReal_coe]
  have halive : ∀ t : ℝ≥0, t < u → Alive W X t := fun t htu =>
    alive_of_trace_off hg hF.continuousOn_w hF.w_zero ht₂ζ ((NNReal.coe_lt_coe.2 htu).trans hut₂) hX0
      (hoff t htu)
  have hnot := not_alive_of_visit hg hF.continuousOn_w hF.w_zero ht₂ζ hu0 hut₂ hvis
  -- the mark is dominated by `X` before `u`
  have hdom : ∀ t : ℝ≥0, t < u → vR i t - w t ≤ cflow W X t := fun t htu => by
    have htt₂ : (t : ℝ) ≤ t₂ := ((NNReal.coe_lt_coe.2 htu).trans hut₂).le
    rw [SideHeight.vR_eq_rightImg_frozenDrive hp ht₂ζ htt₂ i, ← hWw t htt₂]
    have h1 := rightImg_mono_index hW t.coe_nonneg hi (w := W)
    rw [rightImg_eq_gImg hW t.coe_nonneg (halive t htu), gImg] at h1
    linarith
  -- continuity of the gap at `u`
  have hcont : ContinuousAt (fun t => vR i t - w t) u := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact (((hF.continuousOn_vR i).sub hF.continuousOn_w).continuousAt (hopen.mem_nhds hu))
  refine le_antisymm ?_ (hF.w_le_vR hu i)
  suffices h : ∀ ε > 0, vR i u - w u < ε by
    by_contra hlt
    have := h (vR i u - w u) (by linarith)
    exact lt_irrefl _ this
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (half_pos hε)
  set s₀ : ℝ≥0 := u - min (δ / 2).toNNReal (u / 2) with hs₀
  have hmin_pos : 0 < min (δ / 2).toNNReal (u / 2) :=
    lt_min (Real.toNNReal_pos.2 (half_pos hδ)) (half_pos hu0)
  have hmin_le : min (δ / 2).toNNReal (u / 2) ≤ u := (min_le_right _ _).trans (half_le_self (by positivity))
  have hs₀u : s₀ < u := tsub_lt_self hu0 hmin_pos
  have hs₀δ : (u : ℝ) - s₀ < δ := by
    rw [hs₀, NNReal.coe_sub hmin_le]
    have h1 : ((min (δ / 2).toNNReal (u / 2) : ℝ≥0) : ℝ) ≤ δ / 2 := by
      calc ((min (δ / 2).toNNReal (u / 2) : ℝ≥0) : ℝ) ≤ ((δ / 2).toNNReal : ℝ) := by
            exact_mod_cast min_le_left _ _
        _ = δ / 2 := Real.coe_toNNReal _ (by linarith)
    linarith
  -- a time in `[s₀, u)` where the gap of `X` is below `ε / 2`
  obtain ⟨s, hs₀s, hsu, hcs⟩ : ∃ s : ℝ, (s₀ : ℝ) ≤ s ∧ s < u ∧ cflow W X s < ε / 2 := by
    by_contra hno
    push Not at hno
    refine hnot (Alive.of_forall_le_cflow hW (halive s₀ hs₀u) s₀.coe_nonneg (half_pos hε) fun t ht hal => ?_)
    rcases lt_or_eq_of_le ht.2 with htu | htu
    · exact hno t ht.1 htu
    · exact absurd (htu ▸ hal) hnot
  have hs0 : 0 ≤ s := s₀.coe_nonneg.trans hs₀s
  set s' : ℝ≥0 := s.toNNReal with hs'
  have hs'u : s' < u := by rw [hs', Real.toNNReal_lt_iff_lt_coe hs0]; exact hsu
  have hs'coe : (s' : ℝ) = s := Real.coe_toNNReal _ hs0
  have hd := hdom s' hs'u
  rw [hs'coe] at hd
  have hdist : dist s' u < δ := by
    rw [NNReal.dist_eq, hs'coe, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have h1 := hδc hdist
  rw [Real.dist_eq] at h1
  have h2 := (abs_lt.1 h1).1
  linarith

end Merge

/-! ### The first visit of a closed real half-line -/

/-- **First visit.** A curve continuous on `[0, ∞)` with `γ(0) = 0` that visits a real point `X₀ > 0` visits the
closed half-line `[X₀, ∞)` for a first time `u > 0`, at a real point `X ≥ X₀`, and stays off `[X₀, ∞)` before `u`. -/
theorem exists_first_visit {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (hγ0 : γ 0 = 0) {u₀ : ℝ≥0} {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hvis : γ u₀ = X₀) :
    ∃ u : ℝ≥0, 0 < u ∧ u ≤ u₀ ∧ ∃ X : ℝ, X₀ ≤ X ∧ γ u = X ∧
      ∀ s : ℝ≥0, s < u → ∀ r : ℝ, X₀ ≤ r → γ s ≠ r := by
  set S : Set ℂ := {z | z.im = 0 ∧ X₀ ≤ z.re} with hS
  have hSc : IsClosed S :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  set A : Set ℝ≥0 := γ ⁻¹' S with hA
  have hAc : IsClosed A := hSc.preimage hγ
  have hu₀A : u₀ ∈ A := by
    show γ u₀ ∈ S
    rw [hvis]
    exact ⟨by simp, by simp⟩
  have hne : A.Nonempty := ⟨u₀, hu₀A⟩
  have hbdd : BddBelow A := ⟨0, fun _ _ => zero_le⟩
  have huA : sInf A ∈ A := hAc.csInf_mem hne hbdd
  have hmem : ∀ s : ℝ≥0, s ∈ A ↔ ∃ r : ℝ, X₀ ≤ r ∧ γ s = r := fun s => by
    constructor
    · intro hs
      refine ⟨(γ s).re, hs.2, ?_⟩
      apply Complex.ext <;> simp [hs.1]
    · rintro ⟨r, hr, he⟩
      show γ s ∈ S
      rw [he]
      exact ⟨by simp, by simpa using hr⟩
  obtain ⟨X, hX, hγu⟩ := (hmem _).1 huA
  refine ⟨sInf A, ?_, csInf_le hbdd hu₀A, X, hX, hγu, fun s hs r hr he => ?_⟩
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, hγ0] at hγu
    have := congrArg Complex.re hγu
    simp only [Complex.zero_re, Complex.ofReal_re] at this
    linarith
  · exact notMem_of_lt_csInf hs hbdd ((hmem s).2 ⟨r, hr, he⟩)

/-! ### Non-hitting at the path level -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

/-- **A separated right mark keeps the trace off the real points beyond it** (deterministic; infinite lifetime): if the
right mark `x_i` is strictly separated from the driver at every positive time, the trace never visits a real point
`x > 0` with `x ≥ x_i` (at any time; at time `0` it is at `0`). -/
theorem trace_ne_of_lt_of_sep (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ⊤)
    (hg : IsGeneratingTrace w ⊤ γ) {i : Fin nR} (hsep : ∀ t : ℝ≥0, 0 < t → w t < vR i t) (t : ℝ≥0)
    {x : ℝ} (hx0 : 0 < x) (hix : xR i ≤ x) : γ t ≠ x := by
  intro hvis
  have hγc : Continuous γ :=
    continuousOn_univ.1 (hg.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  obtain ⟨u, hu0, -, X, hX, hγu, hoff⟩ := exists_first_visit hγc hg.1 hx0 hvis
  have hm := vR_eq_w_of_off hp hg hu0 ENNReal.coe_lt_top (hx0.trans_le hX) hγu
    (fun t' ht' s hs r hr => hoff s (hs.trans_lt ht') r (hX.trans hr)) (hix.trans hX)
  have := hsep u hu0
  rw [hm] at this
  exact lt_irrefl _ this

/-- **The left version** (reflection `z ↦ −z̄`): a separated left mark keeps the trace off the real points `x < 0` with
`x ≤ x_i`. -/
theorem trace_ne_of_gt_of_sep (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ⊤)
    (hg : IsGeneratingTrace w ⊤ γ) {i : Fin nL} (hsep : ∀ t : ℝ≥0, 0 < t → vL i t < w t) (t : ℝ≥0)
    {x : ℝ} (hx0 : x < 0) (hix : x ≤ xL i) : γ t ≠ x := by
  intro hvis
  have hp' := hp.reflect
  have hg' := LP.isGeneratingTrace_reflect hg
  have hne := trace_ne_of_lt_of_sep hp' hg' (i := i) (fun s hs => by
      have := hsep s hs
      simp only [Pi.neg_apply]
      linarith) t (x := -x) (by linarith) (by simp only [Pi.neg_apply]; linarith)
  apply hne
  simp [LP.reflectC, hvis]

end Path

/-! ### Non-hitting for evolutions -/

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Right non-hitting** (Aux. lemma 24's real-contact collision with Aux. lemma 6, every `κ > 0`): for an ordered
word with admissible side partial sums, almost surely every continuous generating trace on `[0, ∞)` never visits a real
point `x > 0` lying at or beyond some right mark. With a right seed mark (`x_i = 0`) it never visits `(0, ∞)`. -/
theorem ae_trace_ne_pos (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0,
      ∀ (i : Fin nR) (x : ℝ), 0 < x → xR i ≤ x → γ t ≠ x := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.2.2.2.2]
    with ω ⟨hζ, hsep⟩ hp γ hγ t i x hx hix
  rw [hζ] at hp
  exact trace_ne_of_lt_of_sep hp hγ (fun s hs => (hsep s hs).2 i) t hx hix

/-- **Left non-hitting** (the reflection of `ae_trace_ne_pos`). -/
theorem ae_trace_ne_neg (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0,
      ∀ (i : Fin nL) (x : ℝ), x < 0 → x ≤ xL i → γ t ≠ x := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.2.2.2.2]
    with ω ⟨hζ, hsep⟩ hp γ hγ t i x hx hix
  rw [hζ] at hp
  exact trace_ne_of_gt_of_sep hp hγ (fun s hs => (hsep s hs).1 i) t hx hix

/-- **The trace of an admissible seed word is never real at positive times** (every `κ > 0`), given its transience:
right and left non-hitting (the seed marks `0⁺`, `0⁻` lie before every real point) and no return to `0`
(`CfLineRegQ.ae_trace_ne_zero_of_seed`). Needs a mark on each side. -/
theorem ae_trace_im_ne_zero_of_seed (hκ : 0 < κ) (hnL : 0 < nL) (hnR : 0 < nR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → (γ t).im ≠ 0 := by
  have hF : IsOrderedForceWord (fun _ : Fin nL => (0 : ℝ)) (fun _ : Fin nR => (0 : ℝ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  filter_upwards [ae_trace_ne_pos hκ hF hadm hE, ae_trace_ne_neg hκ hF hadm hE,
    CfLineRegQ.ae_trace_ne_zero_of_seed hκ hadm hE htr] with ω hR hL h0 γ hγ t ht him
  have hγt : γ t = ((γ t).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rcases lt_trichotomy (γ t).re 0 with hneg | hzero | hpos
  · exact hL γ hγ t ⟨0, hnL⟩ _ hneg hneg.le hγt
  · exact h0 γ hγ t ht (by rw [hγt, hzero]; simp)
  · exact hR γ hγ t ⟨0, hnR⟩ _ hpos hpos.le hγt

end Evolution

end InteractingSLE.Sec5.CfAvoidLeftQ
