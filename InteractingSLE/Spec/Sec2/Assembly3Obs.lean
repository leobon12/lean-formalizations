/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Law
import InteractingSLE.Spec.Sec2.Assembly2Reduce

/-!
# Theorem 2.2, uniqueness for the admissible entrances: the observation from the two-seed code

Packet PROVE-SEC2-PATCH4. For an ordered word with seeds (marks at `0`) on both sides and a level
`δ > 0` below the distances of the other marks to `0`:

* `Assembly3.gapFam`: the gaps of the non-seed marks to the driver (`δ + 1` for the seeds);
  `Assembly3.entT`: the localization time, the first time a gap is `≤ δ` or the lifetime is reached
  (`killedFam`), capped at `1`;
* the code space `CSp = ℕ × ℕ → StateSp 1 1` of a two-seed evolution, the driver, merged seeds and
  Brownian motion read from a code (`codeW`, `codeL`, `codeR`, `codeB`), the marks of the full word
  (`codeVL`, `codeVR`: the seeds from the merged seeds, the other marks solved from the driver), the
  localization time read from a code (`codeT`) and the observation read from a code
  (`obsOfCode`, measurable);
* `Assembly3.obsOfCode_stCode`: **the observation of the full word up to the localization time is
  the observation read from the code of any two-seed path that agrees with the driver and the seeds
  up to that time** (pathwise: the non-seed marks are the cut mark flows of the driver,
  `eq_leftMark`, and the localization time only depends on the paths up to it).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly3

open Assembly Assembly2

variable {nL nR : ℕ}

/-! ### The gaps and the localization time -/

section Gap

variable {Ω : Type*}

/-- The gaps of the non-seed marks to the driver (`δ + 1` for the seeds). -/
def gapFam (δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Fin nL ⊕ Fin nR → ℝ≥0 → Ω → ℝ :=
  Sum.elim (fun i t ω => if xL i = 0 then δ + 1 else W t ω - VL i t ω)
    (fun j t ω => if xR j = 0 then δ + 1 else VR j t ω - W t ω)

/-- The localization time: the first time a non-seed mark is within `δ` of the driver, or the
lifetime, capped at `1`. -/
def entT (δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  min (hitTime (killedFam ζ (gapFam δ xL xR W VL VR)) δ ω) 1

variable {δ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

theorem continuousOn_gapFam {ω : Ω} (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVL : ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVR : ∀ j, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) (k : Fin nL ⊕ Fin nR) :
    ContinuousOn (gapFam δ xL xR W VL VR k · ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  rcases k with i | j
  · simp only [gapFam, Sum.elim_inl]
    split_ifs
    · exact continuousOn_const
    · exact hW.sub (hVL i)
  · simp only [gapFam, Sum.elim_inr]
    split_ifs
    · exact continuousOn_const
    · exact (hVR j).sub hW

theorem entT_le_one (ω : Ω) : entT δ xL xR ζ W VL VR ω ≤ 1 := min_le_right _ _

theorem entT_ne_top (ω : Ω) : entT δ xL xR ζ W VL VR ω ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (entT_le_one ω)

theorem entT_le_lifetime [Nonempty (Fin nL ⊕ Fin nR)] (hδ : 0 ≤ δ) (ω : Ω) :
    entT δ xL xR ζ W VL VR ω ≤ ζ ω :=
  (min_le_left _ _).trans (hitTime_killedFam_le hδ ω)

/-- Before the localization time the evolution is alive and the non-seed gaps exceed `δ`. -/
theorem lt_of_lt_entT [Nonempty (Fin nL ⊕ Fin nR)] (hδ : 0 ≤ δ) {ω : Ω} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < entT δ xL xR ζ W VL VR ω) :
    (t : ℝ≥0∞) < ζ ω ∧ ∀ k, δ < gapFam δ xL xR W VL VR k t ω :=
  lt_of_lt_hitTime_killedFam hδ (lt_of_lt_of_le ht (min_le_left _ _))

/-- The localization time is positive. -/
theorem entT_pos [Nonempty (Fin nL ⊕ Fin nR)] (hδ : 0 ≤ δ) {ω : Ω}
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVL : ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVR : ∀ j, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hζ : 0 < ζ ω)
    (h0 : ∀ k, δ < gapFam δ xL xR W VL VR k 0 ω) : 0 < entT δ xL xR ζ W VL VR ω :=
  lt_min (hitTime_killedFam_pos hδ (continuousOn_gapFam hW hVL hVR) hζ h0) one_pos

/-- **The localization time is a stopping time.** -/
theorem measurableSet_entT_le [Nonempty (Fin nL ⊕ Fin nR)] {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (hδ : 0 ≤ δ) (hW : AdaptedBefore 𝓕 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) (s : ℝ≥0) :
    MeasurableSet[𝓕 s] {ω | entT δ xL xR ζ W VL VR ω ≤ s} := by
  have hY : ∀ k, AdaptedBefore 𝓕 ζ (gapFam δ xL xR W VL VR k) := by
    have hc : ∀ (c : ℝ), AdaptedBefore 𝓕 ζ (fun _ _ => c) := fun c t A hA => by
      by_cases hcA : c ∈ A
      · simpa [hcA] using hW t univ MeasurableSet.univ
      · simp [hcA]
    have hsub : ∀ {X Y : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X → AdaptedBefore 𝓕 ζ Y →
        AdaptedBefore 𝓕 ζ (fun t ω => X t ω - Y t ω) := fun {X Y} hX hY t A hA => by
      have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω - Y t ω ∈ A} = {ω | (t : ℝ≥0∞) < ζ ω} ∩
          (fun ω => Girsanov.killed ζ X t ω - Girsanov.killed ζ Y t ω) ⁻¹' A := by
        ext ω
        simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          rw [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1]; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          rw [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1] at h2; exact ⟨h1, h2⟩
      rw [e]
      exact (by simpa using hX t univ MeasurableSet.univ : MeasurableSet[𝓕 t] _).inter
        (((Girsanov.measurable_killed hX t).sub (Girsanov.measurable_killed hY t)) hA)
    rintro (i | j)
    · simp only [gapFam, Sum.elim_inl]
      split_ifs
      · exact hc _
      · exact hsub hW (hVL i)
    · simp only [gapFam, Sum.elim_inr]
      split_ifs
      · exact hc _
      · exact hsub (hVR j) hW
  have e : {ω | entT δ xL xR ζ W VL VR ω ≤ s} =
      {ω | hitTime (killedFam ζ (gapFam δ xL xR W VL VR)) δ ω ≤ s} ∪
        {_ω | ((1 : ℝ≥0) : ℝ≥0∞) ≤ s} := by
    ext ω; simp only [entT, mem_ofPred_eq, mem_union, min_le_iff, ENNReal.coe_one]
  rw [e]
  exact (measurableSet_hitTime_killedFam_le hδ hY (fun k ω =>
    continuousOn_gapFam (hWc ω) (fun i => hVLc i ω) (fun j => hVRc j ω) k) s).union
    (MeasurableSet.const _)

end Gap

/-! ### The code space of a two-seed evolution -/

/-- The code space of a two-seed evolution: its states at the dyadic times. -/
abbrev CSp : Type := ℕ × ℕ → StateSp 1 1

/-- The driver code. -/
def cW (c : CSp) : PCode := fun n k => (c (n, k)).1

/-- The left seed code. -/
def cL (c : CSp) : PCode := fun n k => (c (n, k)).2.1 0

/-- The right seed code. -/
def cR (c : CSp) : PCode := fun n k => (c (n, k)).2.2.1 0

/-- The Brownian code. -/
def cB (c : CSp) : PCode := fun n k => (c (n, k)).2.2.2

theorem measurable_cW : Measurable cW :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    measurable_fst.comp (measurable_pi_apply (n, k))

theorem measurable_cL : Measurable cL :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    (measurable_pi_apply 0).comp (measurable_fst.comp (measurable_snd.comp
      (measurable_pi_apply (n, k))))

theorem measurable_cR : Measurable cR :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    (measurable_pi_apply 0).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_pi_apply (n, k)))))

theorem measurable_cB : Measurable cB :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply (n, k))))

/-- The driver read from a code. -/
def codeW (t : ℝ≥0) (c : CSp) : ℝ := dec (cW c) t

/-- The left seed read from a code. -/
def codeL (t : ℝ≥0) (c : CSp) : ℝ := dec (cL c) t

/-- The right seed read from a code. -/
def codeR (t : ℝ≥0) (c : CSp) : ℝ := dec (cR c) t

/-- The Brownian motion read from a code. -/
def codeB (t : ℝ≥0) (c : CSp) : ℝ := dec (cB c) t

theorem measurable_dec_comp {f : CSp → PCode} (hf : Measurable f) (t : ℝ≥0) :
    Measurable fun c => dec (f c) t :=
  measurable_dec.comp (hf.prodMk measurable_const)

/-- The left marks of the full word read from a code: the seeds are the merged left seed, the
other marks are solved from the driver (cut at `δ`). -/
def codeVL (δ : ℝ) (xL : Fin nL → ℝ) (i : Fin nL) : ℝ≥0 → CSp → ℝ :=
  if xL i = 0 then codeL else leftMark δ (xL i) (fun _ => ⊤) codeW

/-- The right marks of the full word read from a code. -/
def codeVR (δ : ℝ) (xR : Fin nR → ℝ) (j : Fin nR) : ℝ≥0 → CSp → ℝ :=
  if xR j = 0 then codeR else rightMark δ (xR j) (fun _ => ⊤) codeW

/-- The codes whose driver is uniformly continuous on bounded intervals. -/
def UCW : Set CSp := {c | ∀ N : ℕ, UC (cW c) N}

theorem measurableSet_UCW : MeasurableSet UCW := by
  have e : UCW = ⋂ N : ℕ, cW ⁻¹' {c : PCode | UC c N} := by
    ext c; simp [UCW]
  rw [e]
  exact MeasurableSet.iInter fun N => measurable_cW (measurableSet_UC N)

open Classical in
/-- The gaps read from a code (`δ + 1` off `UCW`). -/
def codeGap (δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Fin nL ⊕ Fin nR → ℝ≥0 → CSp → ℝ :=
  fun k t c => if c ∈ UCW then gapFam δ xL xR codeW (codeVL δ xL) (codeVR δ xR) k t c else δ + 1

/-- The localization time read from a code. -/
def codeT (δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (c : CSp) : ℝ≥0∞ :=
  min (hitTime (codeGap δ xL xR) δ c) 1

/-- The observation read from a code. -/
def obsOfCode (δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : CSp → ObsSpace nL nR :=
  observe (codeT δ xL xR) codeW (codeVL δ xL) (codeVR δ xR) codeB

section CodeMeas

variable {δ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

theorem adaptedBefore_codeW :
    AdaptedBefore (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace CSp) le_rfl)
      (fun _ => ⊤) codeW := fun t A hA => by
  show MeasurableSet {c : CSp | (t : ℝ≥0∞) < ⊤ ∧ codeW t c ∈ A}
  have e : {c : CSp | (t : ℝ≥0∞) < ⊤ ∧ codeW t c ∈ A} = codeW t ⁻¹' A := by
    ext c; simp
  rw [e]
  exact measurable_dec_comp measurable_cW t hA

theorem measurable_codeVL (hδ : 0 < δ) (i : Fin nL) (t : ℝ≥0) :
    Measurable (codeVL δ xL i t) := by
  unfold codeVL
  split_ifs
  · exact measurable_dec_comp measurable_cL t
  · exact measurable_markFlow (𝓕 := Filtration.const ℝ≥0 _ le_rfl)
      (lipschitzWith_leftMarkDrift hδ).continuous.measurable adaptedBefore_codeW t

theorem measurable_codeVR (hδ : 0 < δ) (j : Fin nR) (t : ℝ≥0) :
    Measurable (codeVR δ xR j t) := by
  unfold codeVR
  split_ifs
  · exact measurable_dec_comp measurable_cR t
  · exact measurable_markFlow (𝓕 := Filtration.const ℝ≥0 _ le_rfl)
      (lipschitzWith_rightMarkDrift hδ).continuous.measurable adaptedBefore_codeW t

theorem continuous_codeW {c : CSp} (hc : c ∈ UCW) : Continuous (codeW · c) :=
  continuous_dec_of_uc hc

theorem continuous_leftMark_codeW (hδ : 0 < δ) (y : ℝ) {c : CSp} (hc : c ∈ UCW) :
    Continuous (leftMark δ y (fun _ => ⊤) codeW · c) := by
  have h := (markFlow_eq_of_continuousOn (ζ := fun _ => ⊤) (y := y) (ω := c)
    (lipschitzWith_leftMarkDrift hδ) (abs_leftMarkDrift_le hδ)
    (continuous_codeW hc).continuousOn).1
  exact continuousOn_univ.1 (h.mono fun _ _ => ENNReal.coe_lt_top)

theorem continuous_rightMark_codeW (hδ : 0 < δ) (y : ℝ) {c : CSp} (hc : c ∈ UCW) :
    Continuous (rightMark δ y (fun _ => ⊤) codeW · c) := by
  have h := (markFlow_eq_of_continuousOn (ζ := fun _ => ⊤) (y := y) (ω := c)
    (lipschitzWith_rightMarkDrift hδ) (abs_rightMarkDrift_le hδ)
    (continuous_codeW hc).continuousOn).1
  exact continuousOn_univ.1 (h.mono fun _ _ => ENNReal.coe_lt_top)

theorem measurable_codeGap (hδ : 0 < δ) (k : Fin nL ⊕ Fin nR) (t : ℝ≥0) :
    Measurable (codeGap δ xL xR k t) := by
  refine Measurable.ite measurableSet_UCW ?_ measurable_const
  rcases k with i | j
  · simp only [gapFam, Sum.elim_inl]
    split_ifs
    · exact measurable_const
    · exact (measurable_dec_comp measurable_cW t).sub (measurable_codeVL hδ i t)
  · simp only [gapFam, Sum.elim_inr]
    split_ifs
    · exact measurable_const
    · exact (measurable_codeVR hδ j t).sub (measurable_dec_comp measurable_cW t)

theorem continuous_codeGap (hδ : 0 < δ) (k : Fin nL ⊕ Fin nR) (c : CSp) :
    Continuous (codeGap δ xL xR k · c) := by
  by_cases hc : c ∈ UCW
  · simp only [codeGap, hc, ↓reduceIte]
    rcases k with i | j
    · simp only [gapFam, Sum.elim_inl]
      split_ifs with hi
      · exact continuous_const
      · simp only [codeVL, hi, ↓reduceIte]
        exact (continuous_codeW hc).sub (continuous_leftMark_codeW hδ _ hc)
    · simp only [gapFam, Sum.elim_inr]
      split_ifs with hj
      · exact continuous_const
      · simp only [codeVR, hj, ↓reduceIte]
        exact (continuous_rightMark_codeW hδ _ hc).sub (continuous_codeW hc)
  · simp only [codeGap, hc, ↓reduceIte]
    exact continuous_const

theorem measurable_codeT (hδ : 0 < δ) : Measurable (codeT (nL := nL) (nR := nR) δ xL xR) := by
  refine Measurable.min ?_ measurable_const
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe s =>
    exact measurableSet_hitTime_le (𝓕 := Filtration.const ℝ≥0 _ le_rfl)
      (fun k t => measurable_codeGap hδ k t) (fun k c => continuous_codeGap hδ k c) s

/-- **The observation read from a code is measurable.** -/
theorem measurable_obsOfCode (hδ : 0 < δ) :
    Measurable (obsOfCode (nL := nL) (nR := nR) δ xL xR) := by
  have hT := measurable_codeT (nL := nL) (nR := nR) (xL := xL) (xR := xR) hδ
  have hk : ∀ {X : ℝ≥0 → CSp → ℝ}, (∀ t, Measurable (X t)) → ∀ t,
      Measurable (Girsanov.killed (codeT δ xL xR) X t) := fun {X} hX t => by
    show Measurable fun c => if (t : ℝ≥0∞) < codeT δ xL xR c then X t c else 0
    exact Measurable.ite (measurableSet_lt measurable_const hT) (hX t) measurable_const
  refine Measurable.prodMk (measurable_pi_iff.2 fun t => ?_) hT
  exact (hk (measurable_dec_comp measurable_cW) t).prodMk
    ((measurable_pi_iff.2 fun i => hk (measurable_codeVL hδ i) t).prodMk
      ((measurable_pi_iff.2 fun j => hk (measurable_codeVR hδ j) t).prodMk
        (measurable_dec_comp measurable_cB t)))

end CodeMeas

/-! ### The observation is read from the code of the two-seed path -/

section Ident

variable {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {δ : ℝ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {Ω : Type*} {ζ ζG : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {Gw : ℝ≥0 → Ω → ℝ}
  {Gl Gr : Fin 1 → ℝ≥0 → Ω → ℝ} {Bh b : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- **The observation of the full word up to the localization time is read from the code of any
continuous two-seed path agreeing with the driver and the seeds up to that time.** -/
theorem obsOfCode_stCode (hδ : 0 < δ) {pL : Fin nL} {pR : Fin nR} (hpL : xL pL = 0)
    (hpR : xR pR = 0)
    (hp : IsSLEPathUpTo a xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (b · ω) (ζ ω))
    (hT0 : 0 < entT δ xL xR ζ W VL VR ω) (hTζ : entT δ xL xR ζ W VL VR ω < ζ ω)
    (hζG : ζG ω = ⊤) (hGw : Continuous (Gw · ω)) (hGl : Continuous (Gl 0 · ω))
    (hGr : Continuous (Gr 0 · ω)) (hBh : Continuous (Bh · ω))
    (hagW : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ entT δ xL xR ζ W VL VR ω → Gw t ω = W t ω)
    (hagL : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ entT δ xL xR ζ W VL VR ω → Gl 0 t ω = VL pL t ω)
    (hagR : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ entT δ xL xR ζ W VL VR ω → Gr 0 t ω = VR pR t ω) :
    obsOfCode δ xL xR (stCode ζG Gw Gl Gr Bh ω) =
      observe (entT δ xL xR ζ W VL VR) W VL VR Bh ω := by
  classical
  have : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl pL⟩
  set T := entT δ xL xR ζ W VL VR ω with hTdef
  set c := stCode ζG Gw Gl Gr Bh ω with hcdef
  have hTfin : T ≠ ⊤ := entT_ne_top ω
  set T' : ℝ≥0 := T.toNNReal with hT'def
  have hT' : (T' : ℝ≥0∞) = T := ENNReal.coe_toNNReal hTfin
  have hT'0 : 0 < T' := by
    have : (0 : ℝ≥0∞) < T' := by rw [hT']; exact hT0
    exact_mod_cast this
  have hleT : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) ≤ T ↔ t ≤ T' := fun {t} => by
    rw [← hT']; exact ENNReal.coe_le_coe
  have hltζ : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) ≤ T → (t : ℝ≥0∞) < ζ ω := fun ht => lt_of_le_of_lt ht hTζ
  -- the codes are encodings
  have hk : ∀ (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0), Girsanov.killed ζG X u ω = X u ω := fun X u =>
    Girsanov.killed_of_lt (by rw [hζG]; exact ENNReal.coe_lt_top)
  have hcW : cW c = enc (Gw · ω) := by funext n k; simp [cW, hcdef, stCode, hk, enc]
  have hcL : cL c = enc (Gl 0 · ω) := by funext n k; simp [cL, hcdef, stCode, hk, enc]
  have hcR : cR c = enc (Gr 0 · ω) := by funext n k; simp [cR, hcdef, stCode, hk, enc]
  have hcB : cB c = enc (Bh · ω) := by funext n k; simp [cB, hcdef, stCode, enc]
  have hW' : ∀ t, codeW t c = Gw t ω := fun t => by
    rw [codeW, hcW]; exact dec_enc hGw.continuousAt.continuousWithinAt
  have hL' : ∀ t, codeL t c = Gl 0 t ω := fun t => by
    rw [codeL, hcL]; exact dec_enc hGl.continuousAt.continuousWithinAt
  have hR' : ∀ t, codeR t c = Gr 0 t ω := fun t => by
    rw [codeR, hcR]; exact dec_enc hGr.continuousAt.continuousWithinAt
  have hB' : ∀ t, codeB t c = Bh t ω := fun t => by
    rw [codeB, hcB]; exact dec_enc hBh.continuousAt.continuousWithinAt
  have hUC : c ∈ UCW := fun N => by rw [hcW]; exact uc_enc hGw.continuousOn
  have hWc : Continuous (codeW · c) := continuous_codeW hUC
  have hWeq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → codeW t c = W t ω := fun t ht => by
    rw [hW', hagW t ht]
  -- continuity of the paths up to `T`
  have hsub : Iic T' ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t ht => hltζ (hleT.2 ht)
  -- the non-seed marks are the cut mark flows of the driver
  have hint : ∀ {v : ℝ≥0 → ℝ} {s : ℝ≥0}, (s : ℝ≥0∞) ≤ T →
      ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - W r.toNNReal ω) =
        ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - codeW r.toNNReal c) := fun {v s} hs => by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le s.coe_nonneg] at hr
    have hrs : (r.toNNReal : ℝ≥0∞) ≤ T :=
      le_trans (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) hs
    simp only [hWeq _ hrs]
  have hmarkL : ∀ i, xL i ≠ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → codeVL δ xL i t c = VL i t ω := by
    intro i hi t ht
    simp only [codeVL, hi, ↓reduceIte]
    have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → VL i s ω = leftMark δ (xL i) (fun _ => ⊤) codeW s c := by
      intro s hs
      refine eq_leftMark hWc hδ (t₁ := s) ((hp.continuousOn_vL i).mono fun r hr =>
        hltζ (le_trans (by exact_mod_cast hr) hs.le)) (fun r hr => ?_) (fun r hr => ?_) le_rfl
      · have hrT : (r : ℝ≥0∞) ≤ T := le_trans (by exact_mod_cast hr) hs.le
        rw [hp.vL_eq (hltζ hrT) i]; congr 1; exact hint (v := fun s => VL i s ω) hrT
      · have hrT : (r : ℝ≥0∞) < T := lt_of_le_of_lt (by exact_mod_cast hr) hs
        have := (lt_of_lt_entT hδ.le hrT).2 (Sum.inl i)
        simp only [gapFam, Sum.elim_inl, hi, ↓reduceIte] at this
        rw [hWeq r hrT.le]; exact this.le
    rcases lt_or_eq_of_le ht with ht | ht
    · exact (hlt t ht).symm
    · have htT : t = T' := by
        have : (t : ℝ≥0∞) = T' := by rw [hT', ht]
        exact_mod_cast this
      rw [htT]
      refine (eq_of_eqOn_Iio hT'0 ((hp.continuousOn_vL i).mono hsub)
        (continuous_leftMark_codeW hδ _ hUC).continuousOn fun s hs => ?_).symm
      exact hlt s (by rw [← hT']; exact_mod_cast hs)
  have hmarkR : ∀ j, xR j ≠ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → codeVR δ xR j t c = VR j t ω := by
    intro j hj t ht
    simp only [codeVR, hj, ↓reduceIte]
    have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T →
        VR j s ω = rightMark δ (xR j) (fun _ => ⊤) codeW s c := by
      intro s hs
      refine eq_rightMark hWc hδ (t₁ := s) ((hp.continuousOn_vR j).mono fun r hr =>
        hltζ (le_trans (by exact_mod_cast hr) hs.le)) (fun r hr => ?_) (fun r hr => ?_) le_rfl
      · have hrT : (r : ℝ≥0∞) ≤ T := le_trans (by exact_mod_cast hr) hs.le
        rw [hp.vR_eq (hltζ hrT) j]; congr 1; exact hint (v := fun s => VR j s ω) hrT
      · have hrT : (r : ℝ≥0∞) < T := lt_of_le_of_lt (by exact_mod_cast hr) hs
        have := (lt_of_lt_entT hδ.le hrT).2 (Sum.inr j)
        simp only [gapFam, Sum.elim_inr, hj, ↓reduceIte] at this
        rw [hWeq r hrT.le]; exact this.le
    rcases lt_or_eq_of_le ht with ht | ht
    · exact (hlt t ht).symm
    · have htT : t = T' := by
        have : (t : ℝ≥0∞) = T' := by rw [hT', ht]
        exact_mod_cast this
      rw [htT]
      refine (eq_of_eqOn_Iio hT'0 ((hp.continuousOn_vR j).mono hsub)
        (continuous_rightMark_codeW hδ _ hUC).continuousOn fun s hs => ?_).symm
      exact hlt s (by rw [← hT']; exact_mod_cast hs)
  -- all marks
  have hVL : ∀ i, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → codeVL δ xL i t c = VL i t ω := by
    intro i t ht
    by_cases hi : xL i = 0
    · simp only [codeVL, hi, ↓reduceIte]
      rw [hL', hagL t ht, hp.vL_eq_of_xL_eq (hpL.trans hi.symm) (hltζ ht)]
    · exact hmarkL i hi t ht
  have hVR : ∀ j, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → codeVR δ xR j t c = VR j t ω := by
    intro j t ht
    by_cases hj : xR j = 0
    · simp only [codeVR, hj, ↓reduceIte]
      rw [hR', hagR t ht, hp.vR_eq_of_xR_eq (hpR.trans hj.symm) (hltζ ht)]
    · exact hmarkR j hj t ht
  -- the localization time
  have hcT : codeT δ xL xR c = T := by
    refine min_hitTime_one_eq (isClosed_killedFam hδ.le (continuousOn_gapFam
      hp.continuousOn_w hp.continuousOn_vL hp.continuousOn_vR)) fun t ht k => ?_
    rw [killedFam, Girsanov.killed_of_lt (hltζ ht)]
    simp only [codeGap, hUC, ↓reduceIte]
    rcases k with i | j
    · simp only [gapFam, Sum.elim_inl]
      split_ifs
      · rfl
      · rw [hWeq t ht, hVL i t ht]
    · simp only [gapFam, Sum.elim_inr]
      split_ifs
      · rfl
      · rw [hWeq t ht, hVR j t ht]
  -- the observations
  refine Prod.ext (funext fun t => ?_) hcT
  simp only [obsOfCode, observe, Girsanov.killed, hcT, hB', ← hTdef]
  by_cases ht : (t : ℝ≥0∞) < T
  · simp only [ht, ↓reduceIte, hWeq t ht.le, hVL _ t ht.le, hVR _ t ht.le]
  · simp only [ht, ↓reduceIte]

end Ident

end Assembly3

end Sec2

end InteractingSLE
