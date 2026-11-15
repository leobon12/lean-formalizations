/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseR7

/-!
# Theorem 1.2's R.7: the side field from R.5 up to phase and the continuity of the phase

Packet PROVE-PHASECLAUSE. Astra's follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483): "The
adopted mean continuity and the continuous Loewner coordinates make the quotient in (3.2) continuous in positive time.
It is lattice-valued, hence constant on the positive lifetime."

PROVE-HSD split the R.7 side field into (1) R.5 up to a lattice phase, (2) continuity of the phase on the positive
lifetime and (3) phase zero at one positive time. PROVE-PHASE derived (2) and (3) from Aux. lemma 122's retained
hypothesis (M); `PhaseClauseR7` derives (M) from (1) and the constancy of the phase. Here the constancy is derived
from (1)'s lattice clause and (2) (a continuous function on an interval that is lattice-valued on a dense set is
constant), so **(3) is proved from (1) and (2)**:

* `isClosed_range_int_mul`, **`eq_of_continuousOn_lattice`** (one path), **`exists_const_of_continuousOn_lattice`**
  (almost surely, with one constant `c`);
* `TwoSeedPhaseContInput(Inf)`, `R7PhaseContRemaining` (**named input**: (1) and (2) on every R.7 pocket test, the
  premises of `PhaseSide.R7PhaseMeansRemaining`) and **`r7PhaseConstRemaining_of_cont`**;
* **`r7ReferenceStatement_late_cont`**: Theorem 1.2's R.7 reference with the side field from (1) and (2).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseClause

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField R7Pocket R7Aux131
  PocketWordPerQ PhaseSel

universe u

/-! ### A continuous lattice-valued function on an interval is constant -/

section Lattice

theorem isClosed_range_int_mul {d : ℝ} (hd : d ≠ 0) : IsClosed (range fun m : ℤ => (m : ℝ) * d) := by
  have e : (range fun m : ℤ => (m : ℝ) * d) = (Homeomorph.mulRight₀ d hd) '' range ((↑) : ℤ → ℝ) := by
    ext x
    simp only [mem_range, mem_image, Homeomorph.coe_mulRight₀, exists_exists_eq_and]
  rw [e]
  exact (Homeomorph.mulRight₀ d hd).isClosedMap _ Int.isClosedEmbedding_coe_real.isClosed_range

/-- **Along one path: continuous on the positive lifetime and lattice-valued on a dense set ⇒ constant.** -/
theorem eq_of_continuousOn_lattice {f : ℝ≥0 → ℝ} {T : ℝ≥0∞} {d : ℝ} (hd : d ≠ 0) {D : Set ℝ≥0} (hD : Dense D)
    (hc : ContinuousOn f {t | 0 < t ∧ (t : ℝ≥0∞) < T})
    (hlat : ∀ q ∈ D, (q : ℝ≥0∞) < T → ∃ m : ℤ, f q = m * d)
    {s t : ℝ≥0} (hs : 0 < s ∧ (s : ℝ≥0∞) < T) (ht : 0 < t ∧ (t : ℝ≥0∞) < T) : f s = f t := by
  set I : Set ℝ≥0 := {t | 0 < t ∧ (t : ℝ≥0∞) < T} with hIdef
  have hIo : IsOpen I := isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_coe continuous_const)
  set Lat : Set ℝ := range fun m : ℤ => (m : ℝ) * d with hLat
  have hLc : IsClosed Lat := isClosed_range_int_mul hd
  have hmaps : ∀ x ∈ I, f x ∈ Lat := by
    intro x hx
    have hcl : x ∈ closure (I ∩ D) := hD.open_subset_closure_inter hIo hx
    have h1 := ((hc x hx).mono inter_subset_left).mem_closure_image hcl
    refine hLc.closure_subset_iff.2 ?_ h1
    rintro _ ⟨y, ⟨hyI, hyD⟩, rfl⟩
    obtain ⟨m, hm⟩ := hlat y hyD hyI.2
    exact ⟨m, hm.symm⟩
  have hsub : ∀ a b : ℝ≥0, a ∈ I → b ∈ I → uIcc a b ⊆ I := fun a b ha hb r hr => by
    rcases mem_uIcc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le ha.1 h1, lt_of_le_of_lt (by exact_mod_cast h2) hb.2⟩
    · exact ⟨lt_of_lt_of_le hb.1 h1, lt_of_le_of_lt (by exact_mod_cast h2) ha.2⟩
  -- distinct lattice values are at least `|d|` apart, and the midpoint value is not in the lattice
  have key : ∀ a b : ℝ≥0, a ∈ I → b ∈ I → f a < f b → False := by
    intro a b ha hb hab
    obtain ⟨m₁, hm₁⟩ := hmaps a ha
    obtain ⟨m₂, hm₂⟩ := hmaps b hb
    have hsubab : uIcc a b ⊆ I := hsub a b ha hb
    have hdpos : 0 < |d| := abs_pos.2 hd
    have hne : m₂ ≠ m₁ := by
      rintro rfl
      rw [← hm₁, ← hm₂] at hab
      exact lt_irrefl _ hab
    have hgap : |d| ≤ f b - f a := by
      have h1 : f b - f a = ((m₂ - m₁ : ℤ) : ℝ) * d := by rw [← hm₁, ← hm₂]; push_cast; ring
      have h2 : (1 : ℝ) ≤ |((m₂ - m₁ : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hne)
      have h3 : |f b - f a| = f b - f a := abs_of_pos (sub_pos.2 hab)
      calc |d| = 1 * |d| := (one_mul _).symm
        _ ≤ |((m₂ - m₁ : ℤ) : ℝ)| * |d| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = f b - f a := by rw [← abs_mul, ← h1, h3]
    set v : ℝ := f a + |d| / 2 with hv
    have hvmem : v ∈ uIcc (f a) (f b) := by
      rw [uIcc_of_le hab.le]
      constructor <;> linarith
    obtain ⟨r, hr, hfr⟩ := intermediate_value_uIcc (hc.mono hsubab) hvmem
    obtain ⟨m, hm⟩ := hmaps r (hsubab hr)
    have h1 : ((m - m₁ : ℤ) : ℝ) * d = |d| / 2 := by
      have hm' : (m : ℝ) * d = f r := hm
      have hm₁' : (m₁ : ℝ) * d = f a := hm₁
      have : (m : ℝ) * d - (m₁ : ℝ) * d = |d| / 2 := by rw [hm', hfr, hm₁']; ring
      push_cast; linarith
    have h2 : |((m - m₁ : ℤ) : ℝ)| * |d| = |d| / 2 := by rw [← abs_mul, h1, abs_div, abs_abs]; norm_num
    have h3 : |((m - m₁ : ℤ) : ℝ)| = 1 / 2 := by
      field_simp at h2 ⊢
      nlinarith [hdpos]
    rcases eq_or_ne (m - m₁) 0 with h0 | h0
    · rw [h0] at h3; norm_num at h3
    · have : (1 : ℝ) ≤ |((m - m₁ : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
      linarith
  rcases lt_trichotomy (f s) (f t) with h | h | h
  · exact (key s t hs ht h).elim
  · exact h
  · exact (key t s ht hs h).elim

/-- **Almost surely: continuous on the positive lifetime and lattice-valued at each time ⇒ one constant phase.**
The lattice condition holds almost surely at each fixed time (as in R.5 up to phase), the continuity almost surely
pathwise; on a countable dense set of times both hold together, and the path is constant. -/
theorem exists_const_of_continuousOn_lattice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℝ} (hd : d ≠ 0)
    {A : Set Ω} {T : Ω → ℝ≥0∞} {δ : ℝ≥0 → Ω → ℝ}
    (hlat : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < T ω → ∃ m : ℤ, δ q ω = m * d)
    (hcont : ∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < T ω}) :
    ∃ c : Ω → ℝ, ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < T ω → δ q ω = c ω := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hlatD : ∀ᵐ ω ∂P, ∀ q : D, ω ∈ A → ((q : ℝ≥0) : ℝ≥0∞) < T ω → ∃ m : ℤ, δ q ω = m * d :=
    ae_all_iff.2 fun q => hlat q
  refine ⟨fun ω => if h : ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ≥0∞) < T ω then δ (Classical.choose h) ω else 0,
    fun q hq => ?_⟩
  filter_upwards [hcont, hlatD] with ω hc hl hωA hqT
  have h : ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ≥0∞) < T ω := ⟨q, hq, hqT⟩
  simp only [h, ↓reduceDIte]
  exact eq_of_continuousOn_lattice hd hDd (hc hωA) (fun r hr hrT => hl ⟨r, hr⟩ hωA hrT) ⟨hq, hqT⟩
    (Classical.choose_spec h)

end Lattice

/-! ### The named input with continuity of the phase -/

section Defs

variable {Ω : Type*}

/-- **R.5 up to phase and the continuity of the phase on every test of a walls' event** (bounded change pocket):
`Hsd.TwoSeedPhaseSideInput` without the phase selection (3). -/
def TwoSeedPhaseContInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
        (∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A
          (travAll R L r η ψ) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (activeCompl A (travAll R L r η ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) ∧
        ∀ᵐ ω ∂P, ω ∈ A →
          ContinuousOn (δ · ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (travAll R L r η ψ ω)}

/-- **R.5 up to phase and the continuity of the phase on every test of a walls' event** (pocket opening at the flow
seed). -/
def TwoSeedPhaseContInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
        (∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A
          (travAllInf R L r η ψ) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (activeCompl A (travAllInf R L r η ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) ∧
        ∀ᵐ ω ∂P, ω ∈ A →
          ContinuousOn (δ · ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)}

theorem twoSeedPhaseConstInput_of_cont {κ rL rR : ℝ} (hκ : 4 < κ) {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} (h : TwoSeedPhaseContInput κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseConstInput κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, hside, hcont⟩ := h A hA hAG hPA ψ hψ hψm
  obtain ⟨c, hc⟩ := exists_const_of_continuousOn_lattice (phaseStep_ne_zero hκ) (fun q => (hside q).1) hcont
  exact ⟨n, hn, a, δ, c, hside, hc⟩

theorem twoSeedPhaseConstInputInf_of_cont {κ rL rR : ℝ} (hκ : 4 < κ) {𝓦 : MeasurableSpace Ω}
    [MeasurableSpace Ω] {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (h : TwoSeedPhaseContInputInf κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseConstInputInf κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, hside, hcont⟩ := h A hA hAG hPA ψ hψ hψm
  obtain ⟨c, hc⟩ := exists_const_of_continuousOn_lattice (phaseStep_ne_zero hκ) (fun q => (hside q).1) hcont
  exact ⟨n, hn, a, δ, c, hside, hc⟩

/-- PROVE-HSD's input `Hsd.TwoSeedPhaseSideInput` (parts (1)–(3)) implies `TwoSeedPhaseContInput` (parts (1)–(2)):
the new named input is weaker. -/
theorem twoSeedPhaseContInput_of_phaseSide {κ rL rR : ℝ} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (h : Hsd.TwoSeedPhaseSideInput κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseContInput κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, h1, h2, -⟩ := h A hA hAG hPA ψ hψ hψm
  exact ⟨n, hn, a, δ, h1, h2⟩

/-- `Hsd.TwoSeedPhaseSideInputInf` implies `TwoSeedPhaseContInputInf`. -/
theorem twoSeedPhaseContInputInf_of_phaseSide {κ rL rR : ℝ} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (h : Hsd.TwoSeedPhaseSideInputInf κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseContInputInf κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, h1, h2, -⟩ := h A hA hAG hPA ψ hψ hψm
  exact ⟨n, hn, a, δ, h1, h2⟩

end Defs

/-! ### Every R.7 configuration and Theorem 1.2's R.7 reference -/

section Remaining

open R7Outer R7Leaves StripPocketConfig RefWire Wire Hsd

/-- **R.5 up to phase and the continuity of the phase on every R.7 configuration** (named input replacing
`PhaseSide.R7PhaseMeansRemaining` and `Hsd.R7PhaseSideRemaining`): the premises are exactly those of
`Hsd.R7PhaseSideRemaining`; the conclusion is its parts (1) and (2) on every pocket test, without the phase selection
(3), which is proved (Aux. lemma 122 through `r7PhaseMeansRemaining_of_const`). -/
def R7PhaseContRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedPhaseContInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseContInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- PROVE-HSD's named input `Hsd.R7PhaseSideRemaining` implies `R7PhaseContRemaining` (the same premises; parts (1)–(3)
imply parts (1)–(2)): the new named input is weaker. -/
theorem r7PhaseContRemaining_of_phaseSide {k rL rR c c' : ℝ} (h : R7PhaseSideRemaining.{u} k rL rR c c') :
    R7PhaseContRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h₁ W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := h P h₁ W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedPhaseContInput_of_phaseSide hs, twoSeedPhaseContInputInf_of_phaseSide hsI⟩

theorem r7PhaseConstRemaining_of_cont {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hcont : R7PhaseContRemaining.{u} k rL rR c c') : R7PhaseConstRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hcont P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedPhaseConstInput_of_cont hk4 hs, twoSeedPhaseConstInputInf_of_cont hk4 hsI⟩

/-- **Theorem 1.2's R.7 reference with the side field from R.5 up to phase and the continuity of the phase**
(`r7ReferenceStatement_late_const` and `r7PhaseConstRemaining_of_cont`): the phase selection of PROVE-HSD's
`Hsd.R7PhaseSideRemaining` (part (3)) is no longer an input. The other inputs are exactly those of
`Hsd.r7ReferenceStatement_late_hsd`. -/
theorem r7ReferenceStatement_late_cont
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hcont : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7PhaseContRemaining.{0} k rL rR (Real.pi * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} :=
  r7ReferenceStatement_late_const hRect hRectEight Ref0 hCover0 hAvoid0 hQ0 hlaws
    (fun k hk4 rL rR hL hR hmax => r7PhaseConstRemaining_of_cont hk4 (hcont k hk4 rL rR hL hR hmax)) hOuter

end Remaining

end InteractingSLE.Sec7.PhaseClause
