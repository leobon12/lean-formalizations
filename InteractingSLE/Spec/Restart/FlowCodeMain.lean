/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowCode

/-!
# Canonical flow and driver codes: realization and determination

Packet PROVE-CONDDET. The corrected forms of PROVE-RESTARTKERNEL's `IsFlowCode`/`IsDriverCode` (with a measurable
lifetime; see `FlowCode.lean` for the defect of the landed predicates), strengthened by the converse direction:

* **`IsCanonicalFlowCode κ θ F`**: `F` is measurable; *(realization)* for every sorted word `c` and seed `x`, on every
  probability space, every GFF `h` with the data of `c` and every path `η` with a **measurable** lifetime `ζ` that
  almost surely match the decoded code `F ((c, x), h)` form the angle-`θ` flow line of `h` from `x`; *(determination)*
  every flow line `(η, ζ)` of `h` from `x` almost surely matches `F ((c, x), h)`.
* **`IsCanonicalDriverCode κ θ F`**: the same for drivers of flow lines from `0` (`IsFlowLineDriver`), with a measurable
  driver continuous before its measurable lifetime.
* **`isCanonicalFlowCode_flowCode`**, **`isCanonicalDriverCode_driverCode`**: the codes of `FlowCode.lean` are
  canonical, from `Exist.Staged.Theorem12ParamStatement` (Theorem 1.2 with the determination map Borel in the word,
  R44) and `Exist.Theorem13Statement` (exactly the frozen Theorem 1.3's type), at universe `0`.
* **`canonicalFlowCodeStatement_of_param`**, **`canonicalDriverCodeStatement_of_param`**: the corrected
  `FlowCodeStatement` and `DriverCodeStatement` (with determination).

Proof. Realization: the field-determined driver `drvOf (detCode Φ (w, h'))` of the flow-line word `w` of `(c, x)` at
the flow field `h' = h(· + x) + θχ` forms an optional hull coupling with `h'`
(`Exist.Staged.isOptionalHullCoupling_drv`); Theorem 1.2 applied to it identifies the code's trace with its generating
trace (Theorem 1.3), so a path matching the code is that trace; the coupling is then moved to the given lifetime
(`isOptionalHullCoupling_of_detAgree`). Determination: Theorem 1.2 (word-measurable form) applied to the coupling of
the given flow line. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open LQGMetric Sec2.Assembly Exist.Staged

/-! ### Two small facts about paths -/

/-- A generating trace on `[0, T]` may be replaced by a path that agrees with it on `[0, T]`. -/
theorem isGeneratingTrace_congr_le {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η η' : ℝ≥0 → ℂ} (h : IsGeneratingTrace w T η)
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → η' t = η t) : IsGeneratingTrace w T η' := by
  obtain ⟨h0, hc, hf⟩ := h
  refine ⟨by rw [he 0 (by simp)]; exact h0, hc.congr fun t ht => he t ht, fun t ht => ?_⟩
  have himg : η' '' Icc 0 t = η '' Icc 0 t :=
    image_congr fun s hs => he s ((ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  rw [himg]
  exact hf t ht

/-- Two real paths continuous before `L` that agree at the dyadic times before `L` agree before `L`. -/
theorem eq_of_eq_dyad_lt {f g : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < L})
    (hg : ContinuousOn g {t | (t : ℝ≥0∞) < L})
    (h : ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < L → f (dyad n k) = g (dyad n k)) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < L) :
    f s = g s := by
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hfs := (hf s hs).continuousAt (hopen.mem_nhds hs)
  have hgs := (hg s hs).continuousAt (hopen.mem_nhds hs)
  have hu := tendsto_dyad_flr s
  refine tendsto_nhds_unique (hfs.tendsto.comp hu) ((hgs.tendsto.comp hu).congr fun m => ?_)
  exact (h m (flr m s) (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyad_flr_le m s)) hs)).symm

/-! ### The corrected predicates -/

/-- **A canonical flow code** (the corrected `IsFlowCode`, with a measurable lifetime, plus determination): `F` is
measurable; for every sorted word `c` and seed `x`, on every probability space, every GFF `h` with the data of `c` and
every path `η` with a measurable lifetime `ζ` that almost surely match `F ((c, x), h)` are the angle-`θ` flow line of
`h` from `x`; and every such flow line almost surely matches `F ((c, x), h)`. -/
def IsCanonicalFlowCode (κ θ : ℝ)
    (F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞) : Prop :=
  Measurable F ∧
  (∀ (c : BoundaryWord) (x : ℝ), c.IsSorted →
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData Q h c.fn c.jumps → Measurable ζ →
      (∀ᵐ ω ∂Q, IsCodeMatch (F ((c, x), h ω)) (η ω) (ζ ω)) → IsFlowLine κ c.fn c.jumps x θ Q h η ζ) ∧
  ∀ (c : BoundaryWord) (x : ℝ) {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    IsFlowLine κ c.fn c.jumps x θ Q h η ζ → ∀ᵐ ω ∂Q, IsCodeMatch (F ((c, x), h ω)) (η ω) (ζ ω)

/-- **Canonical flow codes exist** (the corrected `FlowCodeStatement`, with determination). -/
def CanonicalFlowCodeStatement : Prop :=
  ∀ κ θ : ℝ, 0 < κ → κ < 4 → ∃ F, IsCanonicalFlowCode κ θ F

/-- **A canonical driver code** (the corrected `IsDriverCode`, with a measurable lifetime, plus determination). -/
def IsCanonicalDriverCode (κ θ : ℝ) (F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞) : Prop :=
  Measurable F ∧
  (∀ c : BoundaryWord, c.IsSorted →
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData Q h c.fn c.jumps → (∀ t, Measurable (W t)) → Measurable L →
      (∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < L ω}) →
      (∀ᵐ ω ∂Q, IsDriverCodeMatch (F (c, h ω)) (fun t => W t ω) (L ω)) →
      IsFlowLineDriver κ c.fn c.jumps θ Q h W L) ∧
  ∀ (c : BoundaryWord) {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞),
    IsFlowLineDriver κ c.fn c.jumps θ Q h W L →
      ∀ᵐ ω ∂Q, IsDriverCodeMatch (F (c, h ω)) (fun t => W t ω) (L ω)

/-- **Canonical driver codes exist** (the corrected `DriverCodeStatement`, with determination). -/
def CanonicalDriverCodeStatement : Prop :=
  ∀ κ θ : ℝ, 0 < κ → ∃ F, IsCanonicalDriverCode κ θ F

/-! ### Canonical codes are unique -/

/-- **Two canonical flow codes agree almost surely** on every GFF with the data of a sorted word: the decoded path of
`F` with its lifetime is the flow line (realization for `F`), so it matches `F'` (determination for `F'`). In
particular (Det) does not depend on the canonical code used. -/
theorem IsCanonicalFlowCode.ae_codeMatch {κ θ : ℝ}
    {F F' : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) (hF' : IsCanonicalFlowCode κ θ F') {c : BoundaryWord} (hc : c.IsSorted)
    (x : ℝ) {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h c.fn c.jumps) :
    ∀ᵐ ω ∂Q, IsCodeMatch (F' ((c, x), h ω)) (decPath (F ((c, x), h ω))) (F ((c, x), h ω)).2 := by
  have hζ : Measurable fun ω => (F ((c, x), h ω)).2 :=
    measurable_snd.comp (hF.1.comp (measurable_const.prodMk hh.1))
  have hfl := hF.2.1 c x hc Q h (fun ω => decPath (F ((c, x), h ω))) (fun ω => (F ((c, x), h ω)).2) hh hζ
    (ae_of_all _ fun _ => ⟨rfl, fun _ _ => rfl⟩)
  exact hF'.2.2 c x Q h _ _ hfl

/-! ### The canonical flow code -/

section Flow

variable (h12p : Theorem12ParamStatement.{0}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)

theorem flowCode_eq (c : BoundaryWord) (x : ℝ) (f : DistOn upperHalfPlaneOpens) :
    flowCode h12p hκ θ ((c, x), f) = encPath (fun t => (x : ℂ) + (flowTrace h12p hκ θ ((c, x), f)).2 t)
      (flowTrace h12p hκ θ ((c, x), f)).1 := rfl

/-- **Determination**: every flow line matches the canonical flow code almost surely. -/
theorem ae_codeMatch_flowCode_of_isFlowLine (c : BoundaryWord) (x : ℝ) {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ c.fn c.jumps x θ Q h η ζ) :
    ∀ᵐ ω ∂Q, IsCodeMatch (flowCode h12p hκ θ ((c, x), h ω)) (η ω) (ζ ω) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hC, hgen⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  subst hh'
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps x
  have hΦ := (h12p κ hκ _ _).choose_spec.2 _ _ _ _ hF hC
  filter_upwards [hΦ, hgen] with ω hΦω hgω
  have hT := flowTrace_mk h12p hκ θ c x (h ω)
  have h1 : (flowTrace h12p hκ θ ((c, x), h ω)).1 = ζ ω := by rw [hT]; exact hΦω.1
  have h2 : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (flowTrace h12p hκ θ ((c, x), h ω)).2 t = η ω t - x := by
    intro t ht
    rw [hT]
    refine (hΦω.2 _ hgω t).trans ?_
    rw [min_eq_left ht, ENNReal.toNNReal_coe]
  have hcont : ContinuousOn (fun t => (x : ℂ) + (flowTrace h12p hκ θ ((c, x), h ω)).2 t)
      {t | (t : ℝ≥0∞) ≤ (flowTrace h12p hκ θ ((c, x), h ω)).1} := by
    rw [h1]
    have hc0 : ContinuousOn (fun t : ℝ≥0 => (x : ℂ) + (η ω t - x)) {t | (t : ℝ≥0∞) ≤ ζ ω} :=
      continuousOn_const.add hgω.2.1
    refine hc0.congr fun t ht => ?_
    simp only [h2 t ht]
  refine ⟨h1.symm, fun t ht => ?_⟩
  rw [flowCode_eq, decPath_encPath hcont (h1 ▸ ht), h2 t ht]
  ring

/-- **Realization**: a path with a measurable lifetime that matches the canonical flow code almost surely is the flow
line. -/
theorem isFlowLine_of_codeMatch_flowCode (h13 : Exist.Theorem13Statement.{0}) (c : BoundaryWord) (x : ℝ)
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hgff : IsGFFWithBoundaryData Q h c.fn c.jumps) (hζm : Measurable ζ)
    (hmatch : ∀ᵐ ω ∂Q, IsCodeMatch (flowCode h12p hκ θ ((c, x), h ω)) (η ω) (ζ ω)) :
    IsFlowLine κ c.fn c.jumps x θ Q h η ζ := by
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps x
  have hh' := Exist.isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData x θ hgff
  set D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => drvOf (detCode
    (paramΦ h12p hκ (flowLineNL c.fn c.jumps x) (flowLineNR c.fn c.jumps x))
      (((flowLineXL c.fn c.jumps x, flowLineXR c.fn c.jumps x),
        (flowLineRhoL κ c.fn c.jumps x θ, flowLineRhoR κ c.fn c.jumps x θ)),
        Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω))) with hDdef
  have hDm : Measurable D :=
    measurable_drvOf.comp ((measurable_detCode (measurable_paramΦ h12p hκ _ _)).comp
      (measurable_const.prodMk hh'.1))
  have hWm : ∀ t, Measurable fun ω => (D ω).1 t := fun t => (measurable_pi_apply t).comp (measurable_fst.comp hDm)
  -- the coupling of the determined driver, Theorem 1.2 on it, and its trace (Theorem 1.3)
  obtain ⟨𝓕₀, VL₀, VR₀, B₀, hC₀⟩ := isOptionalHullCoupling_drv h12p h13 hκ hF hh' hDm (ae_of_all _ fun _ => rfl)
  have hΦ := (h12p κ hκ _ _).choose_spec.2 _ _ _ _ hF hC₀
  have h13' := h13 hκ hF hC₀.1
  -- the matched path is the determined trace
  have hkey : ∀ᵐ ω ∂Q, ζ ω = (D ω).2 ∧ IsGeneratingTrace (fun t => (D ω).1 t) (ζ ω) fun t => η ω t - x := by
    filter_upwards [hΦ, h13', hmatch] with ω hΦω h13ω hmω
    obtain ⟨-, η₀, hη₀, -⟩ := h13ω
    have hT := flowTrace_mk h12p hκ θ c x (h ω)
    have h1 : (flowTrace h12p hκ θ ((c, x), h ω)).1 = (D ω).2 := by rw [hT]; exact hΦω.1
    have h2 : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ω).2 → (flowTrace h12p hκ θ ((c, x), h ω)).2 t = η₀ t := by
      intro t ht
      rw [hT]
      refine (hΦω.2 _ hη₀ t).trans ?_
      rw [min_eq_left ht, ENNReal.toNNReal_coe]
    have hcont : ContinuousOn (fun t => (x : ℂ) + (flowTrace h12p hκ θ ((c, x), h ω)).2 t)
        {t | (t : ℝ≥0∞) ≤ (flowTrace h12p hκ θ ((c, x), h ω)).1} := by
      rw [h1]
      have hc0 : ContinuousOn (fun t : ℝ≥0 => (x : ℂ) + η₀ t) {t | (t : ℝ≥0∞) ≤ (D ω).2} :=
        continuousOn_const.add hη₀.2.1
      refine hc0.congr fun t ht => ?_
      simp only [h2 t ht]
    obtain ⟨hζ, hη⟩ := hmω
    have hζD : ζ ω = (D ω).2 := hζ.trans h1
    refine ⟨hζD, ?_⟩
    rw [hζD]
    refine isGeneratingTrace_congr_le hη₀ fun t ht => ?_
    rw [hη t (hζD ▸ ht), flowCode_eq, decPath_encPath hcont (h1 ▸ ht), h2 t ht]
    ring
  -- the coupling, moved to the given lifetime
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_of_detAgree h12p h13 hκ hF hh' hWm hζm
    (hkey.mono fun ω hω => ⟨hω.1, rfl, fun _ _ => rfl⟩)
  exact ⟨_, 𝓕, _, VL, VR, B, fun ω => Exist.isTranslateAddConst_flowField x _ (h ω), hC,
    hkey.mono fun ω hω => hω.2⟩

/-- **The canonical flow code is canonical** (from Theorems 1.2–1.3). -/
theorem isCanonicalFlowCode_flowCode (h13 : Exist.Theorem13Statement.{0}) :
    IsCanonicalFlowCode κ θ (flowCode h12p hκ θ) :=
  ⟨measurable_flowCode h12p hκ θ,
    fun c x _ _ _ _ _ _ _ _ hgff hζm hmatch => isFlowLine_of_codeMatch_flowCode h12p hκ θ h13 c x hgff hζm hmatch,
    fun c x _ _ _ _ _ _ _ hfl => ae_codeMatch_flowCode_of_isFlowLine h12p hκ θ c x hfl⟩

end Flow

/-- **The corrected `FlowCodeStatement`** from Theorem 1.2 (word-measurable form, R44) and Theorem 1.3. -/
theorem canonicalFlowCodeStatement_of_param (h12p : Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) : CanonicalFlowCodeStatement :=
  fun _ θ hκ _ => ⟨_, isCanonicalFlowCode_flowCode h12p hκ θ h13⟩

/-! ### The canonical driver code -/

section Driver

variable (h12p : Theorem12ParamStatement.{0}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)

/-- **Determination**: every driver of a flow line from `0` matches the canonical driver code almost surely. -/
theorem ae_driverCodeMatch_of_isFlowLineDriver (h13 : Exist.Theorem13Statement.{0}) (c : BoundaryWord)
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q h W L) :
    ∀ᵐ ω ∂Q, IsDriverCodeMatch (driverCode h12p hκ θ (c, h ω)) (fun t => W t ω) (L ω) := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  subst hh'
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hdet := ae_detCode_eq hκ hF h13 hC ((h12p κ hκ _ _).choose_spec.2 _ _ _ _ hF hC)
  filter_upwards [hdet, hC.1.2.2.2.2] with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩ hpath
  have hD : driverOf h12p hκ θ (c, h ω) = (drvPath (dOf x₀), cζ x₀) := by
    rw [driverOf_mk]
    have hcode' : detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
        (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
          (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
          Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω)) = dOf x₀ := hcode
    rw [hcode', drvOf_of_mem (dOf_mem_DSet hx₀)]
    rfl
  refine ⟨?_, ?_, fun n k hnk => ?_⟩
  · change L ω = (driverOf h12p hκ θ (c, h ω)).2
    rw [hD]
    exact hζx.symm
  · change W 0 ω = (driverOf h12p hκ θ (c, h ω)).1 (dyad 0 0)
    rw [Exist.dyad_zero_zero, driverOf_mk, (drvOf_regular _).2.1]
    exact hpath.1
  · change W (dyad n k) ω = (driverOf h12p hκ θ (c, h ω)).1 (dyad n k)
    rw [hD]
    have hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < cζ x₀ := hζx ▸ hnk
    exact ((hwx _ hnk).1.symm).trans ((drvPath_dOf_agree x₀).2 _ hlt).symm

/-- **Realization**: a measurable driver, continuous before its measurable lifetime, that matches the canonical driver
code almost surely drives the flow line from `0`. -/
theorem isFlowLineDriver_of_driverCodeMatch (h13 : Exist.Theorem13Statement.{0}) (c : BoundaryWord)
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hgff : IsGFFWithBoundaryData Q h c.fn c.jumps)
    (hWm : ∀ t, Measurable (W t)) (hLm : Measurable L)
    (hWc : ∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < L ω})
    (hmatch : ∀ᵐ ω ∂Q, IsDriverCodeMatch (driverCode h12p hκ θ (c, h ω)) (fun t => W t ω) (L ω)) :
    IsFlowLineDriver κ c.fn c.jumps θ Q h W L := by
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hh' := Exist.isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData 0 θ hgff
  have hag : ∀ᵐ ω ∂Q, L ω = (driverOf h12p hκ θ (c, h ω)).2 ∧ W 0 ω = (driverOf h12p hκ θ (c, h ω)).1 0 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → W t ω = (driverOf h12p hκ θ (c, h ω)).1 t := by
    filter_upwards [hmatch] with ω ⟨hL, h0, hd⟩
    have hL' : L ω = (driverOf h12p hκ θ (c, h ω)).2 := hL
    refine ⟨hL', ?_, fun t ht => ?_⟩
    · have h0' : W 0 ω = (driverOf h12p hκ θ (c, h ω)).1 (dyad 0 0) := h0
      rwa [Exist.dyad_zero_zero] at h0'
    · have hreg := (drvOf_regular (detCode
        (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
          (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
            (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
            Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω)))).1
      rw [← driverOf_mk, ← hL'] at hreg
      exact eq_of_eq_dyad_lt (hWc ω) hreg (fun n k hnk => hd n k hnk) ht
  simp only [driverOf_mk] at hag
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_of_detAgree h12p h13 hκ hF hh' hWm hLm hag
  exact ⟨_, 𝓕, VL, VR, B, fun ω => Exist.isTranslateAddConst_flowField 0 _ (h ω), hC⟩

/-- **The canonical driver code is canonical** (from Theorems 1.2–1.3). -/
theorem isCanonicalDriverCode_driverCode (h13 : Exist.Theorem13Statement.{0}) :
    IsCanonicalDriverCode κ θ (driverCode h12p hκ θ) :=
  ⟨measurable_driverCode h12p hκ θ,
    fun c _ _ _ _ _ _ _ _ hgff hWm hLm hWc hmatch =>
      isFlowLineDriver_of_driverCodeMatch h12p hκ θ h13 c hgff hWm hLm hWc hmatch,
    fun c _ _ _ _ _ _ _ hfl => ae_driverCodeMatch_of_isFlowLineDriver h12p hκ θ h13 c hfl⟩

end Driver

/-- **The corrected `DriverCodeStatement`** from Theorem 1.2 (word-measurable form, R44) and Theorem 1.3. -/
theorem canonicalDriverCodeStatement_of_param (h12p : Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) : CanonicalDriverCodeStatement :=
  fun _ θ hκ => ⟨_, isCanonicalDriverCode_driverCode h12p hκ θ h13⟩

end Restart

end InteractingSLE
