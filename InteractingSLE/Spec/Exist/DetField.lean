/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Determine
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# The driving history of an optional hull coupling is a Borel function of the field (from Theorems 1.2–1.3)

Packet PROVE-FLOWEXIST. The frozen Theorem 1.2 (`exists_measurable_lifetime_trace_eq_comp_field`) makes the lifetime
and the trace Borel functions `Φ` of the field; the frozen Theorem 1.3
(`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`) gives the trace. Both are taken here as named hypotheses with
exactly the anchors' types (`Theorem12Statement`, `Theorem13Statement`; the DRAFT anchors are not imported).

**`exists_fieldDetermination`**: for every optional hull coupling `(h₀, W₀, V₀, ζ₀)` there are a Borel map
`Ψ : 𝒟'(ℍ) → XCode` (lifetime and codes of the driving process), a Borel set `S` of fields with `h₀ ∈ S` almost
surely, and paths `ηf` such that

* almost surely the lifetime of `Ψ h₀` is `ζ₀` and its decoded driver and force points are `W₀`, `V₀` before `ζ₀`;
* for **every** field `f ∈ S`, `ηf f` is a continuous generating trace of the Loewner chain driven by `Ψ f` on the
  closed lifetime interval.

Proof: `Ψ = G ∘ codeΦ`, where `codeΦ f` reads the lifetime and the dyadic trace values off `Φ f`, and `G` is the
measurable left inverse (Lusin–Souslin) of the trace-code map on the good set `DetSet` of history codes, on which it is
injective (`Exist.injOn_traceOfCode`). The reference code is the evolution's code with a continuous version of its
Brownian motion, frozen at the lifetime (`frz`). The set `S` is defined by countably many measurable conditions, so the
generating-trace property holds at every point of `S`, not only almost surely: that is what lets it be transferred to
another probability space carrying a field with the same law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Exist

open Sec2.Assembly

/-- **Theorem 1.2 (field determination)**, exactly the type of the frozen anchor
`InteractingSLE.exists_measurable_lifetime_trace_eq_comp_field` (at universe `u`), as a named input. -/
def Theorem12Statement : Prop :=
  ∀ (κ : ℝ) (_ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (_ : IsOrderedForceWord xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (_ : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h),
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal

/-- **Theorem 1.3 (continuity and endpoint)**, exactly the type of the frozen anchor
`InteractingSLE.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace` (at universe `u`), as a named input. -/
def Theorem13Statement : Prop :=
  ∀ {a : ℝ} (_ : 0 < a)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (_ : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (_ : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ),
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

/-! ### Dyadic tools -/

/-- A code that is `UC` on every `[0, N]` decodes to a continuous path. -/
theorem continuous_dec_of_UC {c : PCode} (h : ∀ N : ℕ, UC c N) : Continuous (dec c) := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : t < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have : (t : ℝ) < ⌈(t : ℝ)⌉₊ + 1 := lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
    exact_mod_cast this
  exact (h (⌈(t : ℝ)⌉₊ + 1)).continuousOn.continuousAt (Iic_mem_nhds ht)

/-- Two paths continuous on `[0, T]` that agree at the dyadic times before `T` agree before `T`. -/
theorem eq_of_eq_dyad {f g : ℝ≥0 → ℂ} {T : ℝ≥0}
    (hf : ContinuousOn f {u : ℝ≥0 | (u : ℝ≥0∞) ≤ T}) (hg : ContinuousOn g {u : ℝ≥0 | (u : ℝ≥0∞) ≤ T})
    (h : ∀ m j, dyad m j < T → f (dyad m j) = g (dyad m j)) {s : ℝ≥0} (hs : s < T) : f s = g s := by
  have hu : Tendsto (fun m => dyad m (flr m s)) atTop (𝓝[{u : ℝ≥0 | (u : ℝ≥0∞) ≤ T}] s) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr s, Eventually.of_forall fun m =>
      ENNReal.coe_le_coe.2 ((dyad_flr_le m s).trans hs.le)⟩
  have hs' : s ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ T} := ENNReal.coe_le_coe.2 hs.le
  refine tendsto_nhds_unique ((hf s hs').tendsto.comp hu) (((hg s hs').tendsto.comp hu).congr fun m => ?_)
  exact (h m (flr m s) ((dyad_flr_le m s).trans_lt hs)).symm

theorem dyad_zero_zero : dyad 0 0 = 0 := by simp [dyad]

theorem dyad_le_ceil (n k : ℕ) : dyad n k ≤ ((⌈dyad n k⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil _

/-- A code in `CRel` whose decoded driver has a generating trace on `[0, T']` is in the trace set at every dyadic
`T ≤ T'` before the lifetime. -/
theorem mem_traceSet_of_isGeneratingTrace {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : XCode nL nR} (hx : x ∈ CRel a xL xR ρL ρR) {n k : ℕ}
    (hT : (dyad n k : ℝ≥0∞) < cζ x) {T' : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (cw x) T' η)
    (hTT' : (dyad n k : ℝ≥0∞) ≤ T') :
    (cw x, ((dyad n k : ℝ≥0) : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet := by
  obtain ⟨⟨hg, -, hp⟩, -⟩ := hx
  have hcw := hg.continuousOn_w
  have hc : ContinuousOn (cw x) {t : ℝ≥0 | (t : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} :=
    hcw.mono fun t ht => lt_trans ht hT
  have hlim : 0 < ((dyad n k : ℝ≥0) : ℝ≥0∞) → ((dyad n k : ℝ≥0) : ℝ≥0∞) < ⊤ →
      ∃ w₀ : ℝ, Tendsto (cw x) (𝓝[<] ((dyad n k : ℝ≥0) : ℝ≥0∞).toNNReal) (𝓝 w₀) := fun _ _ => by
    refine ⟨cw x (dyad n k), ?_⟩
    rw [ENNReal.toNNReal_coe]
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((hcw (dyad n k) hT).continuousAt (hopen.mem_nhds hT)).tendsto.mono_left nhdsWithin_le_nhds
  refine (Sec7.RandRestart.mem_traceSet_iff hc hp.1 hlim).2 ⟨η, hη.mono_horizon hTT', fun h => ?_⟩
  exact absurd h ENNReal.coe_ne_top

/-! ### Codes read off the determination map -/

section Field

open LQGMetric (DistOn)

variable {nL nR : ℕ}

/-- The lifetime and the dyadic trace values (before the lifetime) read off `Φ f`. -/
def codeΦ (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)) (f : DistOn upperHalfPlaneOpens) :
    ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  ((Φ f).1, fun n k => if (dyad n k : ℝ≥0∞) < (Φ f).1 then (Φ f).2 (dyad n k) else 0)

/-- The real parts of the dyadic values of the path of `Φ f`. -/
def reCode (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)) (f : DistOn upperHalfPlaneOpens) : PCode :=
  fun n k => ((Φ f).2 (dyad n k)).re

/-- The imaginary parts of the dyadic values of the path of `Φ f`. -/
def imCode (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)) (f : DistOn upperHalfPlaneOpens) : PCode :=
  fun n k => ((Φ f).2 (dyad n k)).im

/-- The path decoded from the dyadic values of the path of `Φ f`. -/
def traceOfΦ (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)) (f : DistOn upperHalfPlaneOpens)
    (t : ℝ≥0) : ℂ :=
  (dec (reCode Φ f) t : ℂ) + (dec (imCode Φ f) t : ℂ) * Complex.I

variable {Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)}

theorem measurable_codeΦ (hΦ : Measurable Φ) : Measurable (codeΦ Φ) :=
  (measurable_fst.comp hΦ).prodMk (measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp hΦ))
      ((measurable_pi_apply _).comp (measurable_snd.comp hΦ)) measurable_const)

theorem measurable_reCode (hΦ : Measurable Φ) : Measurable (reCode Φ) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
    Complex.measurable_re.comp ((measurable_pi_apply _).comp (measurable_snd.comp hΦ))

theorem measurable_imCode (hΦ : Measurable Φ) : Measurable (imCode Φ) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
    Complex.measurable_im.comp ((measurable_pi_apply _).comp (measurable_snd.comp hΦ))

/-- **The good set of fields**: the decoded history code is in `DetSet`, its trace code is the one read off `Φ f`,
the dyadic values of the path of `Φ f` are uniformly continuous on bounded sets, and the path starts at `0`. -/
def GoodField (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ))
    (G : ℝ≥0∞ × (ℕ → ℕ → ℂ) → XCode nL nR) (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Set (DistOn upperHalfPlaneOpens) :=
  {f | G (codeΦ Φ f) ∈ DetSet a xL xR ρL ρR ∧ traceOfCode (G (codeΦ Φ f)) = codeΦ Φ f ∧
    (∀ N : ℕ, UC (reCode Φ f) N ∧ UC (imCode Φ f) N) ∧ (Φ f).2 0 = 0}

theorem measurableSet_eq_traceCode {α : Type*} [MeasurableSpace α] {A B : α → ℝ≥0∞ × (ℕ → ℕ → ℂ)}
    (hA : Measurable A) (hB : Measurable B) : MeasurableSet {f | A f = B f} := by
  have e : {f | A f = B f} = ({f | (A f).1 ≤ (B f).1} ∩ {f | (B f).1 ≤ (A f).1}) ∩
      ⋂ n : ℕ, ⋂ k : ℕ, {f | (A f).2 n k = (B f).2 n k} := by
    ext f
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h; rw [h]; exact ⟨⟨le_rfl, le_rfl⟩, fun _ _ => rfl⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact Prod.ext (le_antisymm h1 h2) (funext fun n => funext fun k => h3 n k)
  rw [e]
  refine ((measurableSet_le (measurable_fst.comp hA) (measurable_fst.comp hB)).inter
    (measurableSet_le (measurable_fst.comp hB) (measurable_fst.comp hA))).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_)
  exact measurableSet_eq_fun ((measurable_pi_apply k).comp ((measurable_pi_apply n).comp (measurable_snd.comp hA)))
    ((measurable_pi_apply k).comp ((measurable_pi_apply n).comp (measurable_snd.comp hB)))

theorem measurableSet_goodField (hΦ : Measurable Φ) {G : ℝ≥0∞ × (ℕ → ℕ → ℂ) → XCode nL nR}
    (hG : Measurable G) (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    MeasurableSet (GoodField Φ G a xL xR ρL ρR) := by
  have hc := hG.comp (measurable_codeΦ hΦ)
  have p1 : Measurable fun f => G (codeΦ Φ f) ∈ DetSet a xL xR ρL ρR :=
    measurableSet_setOfPred.1 (hc (measurableSet_detSet a xL xR ρL ρR))
  have p2 : Measurable fun f => traceOfCode (G (codeΦ Φ f)) = codeΦ Φ f :=
    measurableSet_setOfPred.1 (measurableSet_eq_traceCode (measurable_traceOfCode.comp hc) (measurable_codeΦ hΦ))
  have p3 : Measurable fun f => ∀ N : ℕ, UC (reCode Φ f) N ∧ UC (imCode Φ f) N :=
    Measurable.forall fun N => (measurableSet_setOfPred.1 (measurable_reCode hΦ (measurableSet_UC N))).and
      (measurableSet_setOfPred.1 (measurable_imCode hΦ (measurableSet_UC N)))
  have p4 : Measurable fun f => (Φ f).2 0 = 0 :=
    measurableSet_setOfPred.1 (((measurable_pi_apply (0 : ℝ≥0)).comp (measurable_snd.comp hΦ))
      (measurableSet_singleton 0))
  exact measurableSet_setOfPred.2 (p1.and (p2.and (p3.and p4)))

theorem traceOfΦ_dyad {f : DistOn upperHalfPlaneOpens} (hUC : ∀ N : ℕ, UC (reCode Φ f) N ∧ UC (imCode Φ f) N)
    (n k : ℕ) : traceOfΦ Φ f (dyad n k) = (Φ f).2 (dyad n k) := by
  unfold traceOfΦ
  rw [(hUC _).1.dec_dyad (dyad_le_ceil n k), (hUC _).2.dec_dyad (dyad_le_ceil n k)]
  exact Complex.re_add_im _

theorem continuous_traceOfΦ {f : DistOn upperHalfPlaneOpens}
    (hUC : ∀ N : ℕ, UC (reCode Φ f) N ∧ UC (imCode Φ f) N) : Continuous (traceOfΦ Φ f) := by
  unfold traceOfΦ
  have h1 := continuous_dec_of_UC fun N => (hUC N).1
  have h2 := continuous_dec_of_UC fun N => (hUC N).2
  fun_prop

/-- **On the good set of fields, the decoded path is a continuous generating trace** of the decoded driver on the
closed lifetime interval. -/
theorem isGeneratingTrace_of_mem_goodField {G : ℝ≥0∞ × (ℕ → ℕ → ℂ) → XCode nL nR} {a : ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {f : DistOn upperHalfPlaneOpens}
    (hf : f ∈ GoodField Φ G a xL xR ρL ρR) :
    IsGeneratingTrace (cw (G (codeΦ Φ f))) (cζ (G (codeΦ Φ f))) (traceOfΦ Φ f) := by
  obtain ⟨hy, hτ, hUC, h0⟩ := hf
  set y := G (codeΦ Φ f) with hydef
  have hcont := continuous_traceOfΦ hUC
  have hζ : cζ y = (Φ f).1 := congrArg (fun p : ℝ≥0∞ × (ℕ → ℕ → ℂ) => p.1) hτ
  refine ⟨?_, hcont.continuousOn, fun t ht => ?_⟩
  · rw [← dyad_zero_zero, traceOfΦ_dyad hUC, dyad_zero_zero, h0]
  · obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
    obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_mem_detSet hy hdζ
    have hc : ContinuousOn (cw y) {s : ℝ≥0 | (s : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} :=
      hy.1.1.1.1.continuousOn_w.mono fun s hs => lt_trans hs hdζ
    have h0y : cw y 0 = 0 := hy.1.1.1.2.2.1
    have heq : ∀ s : ℝ≥0, s < dyad n k → η s = traceOfΦ Φ f s := fun s hs =>
      eq_of_eq_dyad hη.2.1 hcont.continuousOn (fun m j hmj => by
        have hmj' : ((dyad m j : ℝ≥0) : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hmj
        have hlt : ((dyad m j : ℝ≥0) : ℝ≥0∞) < cζ y := lt_trans hmj' hdζ
        have hlt' : ((dyad m j : ℝ≥0) : ℝ≥0∞) < (Φ f).1 := hζ ▸ hlt
        rw [← LP.traceAt_eq_of_isGeneratingTrace hη hc h0y hmj', traceOfΦ_dyad hUC]
        have h := congrFun (congrFun (congrArg (fun p : ℝ≥0∞ × (ℕ → ℕ → ℂ) => p.2) hτ) m) j
        simp only [traceOfCode, codeΦ, hlt, hlt', ↓reduceIte] at h
        exact h) hs
    have htT : t < dyad n k := by exact_mod_cast htd
    have himg : η '' Icc 0 t = traceOfΦ Φ f '' Icc 0 t :=
      image_congr fun s hs => heq s (lt_of_le_of_lt hs.2 htT)
    rw [← himg]
    exact hη.2.2 t (ENNReal.coe_lt_coe.2 htT)

/-- The path `t ↦ η(min(t, ζ))` of a trace continuous on `[0, ζ]` is continuous. -/
theorem continuous_trace_min {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hη : ContinuousOn η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ}) :
    Continuous fun t : ℝ≥0 => η (min (t : ℝ≥0∞) ζ).toNNReal := by
  by_cases hζ : ζ = ⊤
  · subst hζ
    have e : (fun t : ℝ≥0 => η (min (t : ℝ≥0∞) ⊤).toNNReal) = η := by
      funext t; simp
    rw [e]
    exact continuousOn_univ.1 (hη.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  · have e : (fun t : ℝ≥0 => η (min (t : ℝ≥0∞) ζ).toNNReal) = fun t => η (min t ζ.toNNReal) := by
      funext t
      rw [← ENNReal.coe_toNNReal hζ, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    rw [e]
    refine hη.comp_continuous (continuous_id.min continuous_const) fun t => ?_
    change ((min t ζ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ
    rw [ENNReal.coe_min, ENNReal.coe_toNNReal hζ]
    exact min_le_right _ _

end Field

/-! ### The determination theorem -/

/-- **The driving history of every optional hull coupling is a Borel function `Ψ` of the field, and on a Borel set
`S` of fields containing almost every sample the decoded path `ηf` is a continuous generating trace of the decoded
driver on the closed lifetime interval** (from the frozen Theorems 1.2 and 1.3, taken as named inputs). -/
theorem exists_fieldDetermination (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀}
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    ∃ (Ψ : LQGMetric.DistOn upperHalfPlaneOpens → XCode nL nR)
      (S : Set (LQGMetric.DistOn upperHalfPlaneOpens))
      (ηf : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ),
      Measurable Ψ ∧ MeasurableSet S ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      ∀ f ∈ S, IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f) := by
  have hE := hcoup.1
  obtain ⟨Φ, hΦm, hΦ⟩ := h12 κ hκ xL xR ρL ρR hF hcoup
  have h13' := h13 hκ hF hE
  obtain ⟨B', -, hB'c, -, -, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  obtain ⟨G, hGm, hG⟩ := exists_measurable_leftInverse_of_injOn
    (measurable_traceOfCode (nL := nL) (nR := nR)) (measurableSet_detSet κ xL xR ρL ρR)
    (injOn_traceOfCode hκ)
  refine ⟨G ∘ codeΦ Φ, GoodField Φ G κ xL xR ρL ρR, traceOfΦ Φ, hGm.comp (measurable_codeΦ hΦm),
    measurableSet_goodField hΦm hGm κ xL xR ρL ρR, ?_, fun f hf => isGeneratingTrace_of_mem_goodField hf⟩
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
      him ▸ uc_enc (Complex.continuous_im.comp hγ).continuousOn⟩, ?_⟩, ?_, fun t ht => ?_⟩
  · rw [hΦω.2 η hη]
    simpa using hη.1
  · simp only [Function.comp_apply, hΨ]; rfl
  · simp only [Function.comp_apply, hΨ]
    exact ⟨(hdec t ht).1, (hdec t ht).2.1, (hdec t ht).2.2.1⟩

end Exist

end InteractingSLE
