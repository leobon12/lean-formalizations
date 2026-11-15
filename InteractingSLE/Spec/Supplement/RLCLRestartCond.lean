/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKDisint
import InteractingSLE.Spec.Sec7.Lemma76FR1
import InteractingSLE.Spec.Restart.R1GlueChart

/-!
# Lemma G7's retained-pair restart conditionally on the retained histories

Packet PROVE-RLC-L, first statement: `RLC.RetainedPairRestartCondStatement` (PROVE-RLC-K, `RLCKDisint.lean`). Source:
Lemma G7 (supplement pp. 497–498) and the proof of Lemma G8 (p. 501: "Retain only these two stopped histories […] G7
supplies the stopped conditional continuation laws").

The restart kernel `K` of `RLC.retainedPairRestartUntouchedStatement_of_param` is the conditional law of the restart
variable `X = (H_c, F₁(β, H_c), F₂((β.1, 0), H_c))` given the datum `β` on the event `M`, where (R1) says that the
chart field `H_c` has, on `M` and conditionally on a σ-algebra `𝒢` containing `M` and `β`, the Gaussian
characteristic functional of the word of `β`. The conditional clause of `RetainedPairRestartCondStatement` (the same
`K` disintegrates `(β, X)` on every retained-history event `B` of the ordinary event) follows once every such `B` is a
`𝒢`-event:

* `eq_map_of_ae_snd_eq`, **`ae_kernel_eq_of_condExp`**: a kernel disintegrating `(β, (H_c, G(β, H_c)))` on a
  `𝒢`-event with (R1) is, for almost every datum, the word GFF law pushed by `H ↦ (H, G(c, H))`;
* **`map_restrict_eq_compProd_of_condExp`**: hence the same kernel disintegrates `(β, X)` on every `𝒢`-event
  `B ⊆ M`;
* `TraceAESigma`, **`measurableSet_retSigma76_of_hist`**: every event of the retained histories `histSigma d` that
  lies (almost surely) in `{u < ζ₁, r < ζ₂}` belongs to the retained σ-algebra `Sec7.Lemma76F.retSigma76` of the two
  killed flow-line histories (the stopped data paths agree with the flow lines there, and the recorded rational
  coordinates reconstruct them by continuity, `Restart.recon_histOf`);
* `RetainedCanonCondDetHistStatement` (**named input**): RLC-E's `RetainedCanonCondDetUntouchedStatement` with the
  σ-algebra `𝒢` containing `retSigma76` (the form in which PROVE-T15-CLOSE1's `Sec7.Lemma76F.exists_r1_of_meanIdent`
  produces (R1) for Lemma 7.6); `retainedCanonCondDetUntouchedStatement_of_hist` (it implies RLC-E's input);
* **`retainedPairRestartCondStatement_of_param`**: `RetainedPairRestartCondStatement` from Theorems 1.2 (param), 1.3
  and `RetainedCanonCondDetHistStatement`.

R43/R48: downstream of Theorem 1.2; for Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric

/-! ### A kernel with (R1) and a determined code coordinate -/

section Kernel

variable {T : Type*} [MeasurableSpace T] [MeasurableEq T]

omit [MeasurableEq T] in
/-- A measure on `field × codes` whose code coordinate is almost surely `G` of the field is the push-forward of its
field marginal by `H ↦ (H, G H)`. -/
theorem eq_map_of_ae_snd_eq {μ : Measure (DistOn upperHalfPlaneOpens × T)} {G : DistOn upperHalfPlaneOpens → T}
    (hG : Measurable G) (h : ∀ᵐ x ∂μ, x.2 = G x.1) :
    μ = (μ.map Prod.fst).map (fun H => (H, G H)) := by
  have hm : Measurable fun H : DistOn upperHalfPlaneOpens => (H, G H) := measurable_id.prodMk hG
  rw [Measure.map_map hm measurable_fst]
  conv_lhs => rw [← Measure.map_id (μ := μ)]
  exact Measure.map_congr (h.mono fun x hx => Prod.ext rfl hx)

variable {Ω C : Type*} [MeasurableSpace C]

/-- **A kernel disintegrating `(β, (H_c, G(β, H_c)))` on a `𝒢`-event with (R1) is determined**: for almost every
datum `c` it is the word GFF law of `w c` pushed forward by `H ↦ (H, G c H)`. -/
theorem ae_kernel_eq_of_condExp {𝒢 mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {M : Set Ω} (hM : MeasurableSet[𝒢] M) {β : Ω → C} (hβ : Measurable[𝒢] β) {w : C → BoundaryWord}
    (hw : Measurable w) (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted) {Hc : Ω → DistOn upperHalfPlaneOpens}
    (hHc : Measurable Hc) {G : C → DistOn upperHalfPlaneOpens → T} (hG : Measurable (Function.uncurry G))
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {K : Kernel C (DistOn upperHalfPlaneOpens × T)} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, (Hc ω, G (β ω) (Hc ω)))) = (P.restrict M).map β ⊗ₘ K) :
    ∀ᵐ c ∂(P.restrict M).map β, K c = ((w c).gffLaw).map (fun H => (H, G c H)) := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  have hXm : Measurable fun ω => (Hc ω, G (β ω) (Hc ω)) :=
    hHc.prodMk (hG.comp (hβm.prodMk hHc))
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word h𝒢 hM hβ hw hsort hXm
    (H := Prod.fst) measurable_fst hlaw hR1
  have hE : MeasurableSet {p : C × (DistOn upperHalfPlaneOpens × T) | p.2.2 = G p.1 p.2.1} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd)
      (hG.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have hcode := ae_ae_of_map_eq_compProd hMm hβm hXm hlaw hE
    (Eventually.of_forall fun ω _ => (rfl : (G (β ω) (Hc ω)) = G (β ω) (Hc ω)))
  filter_upwards [hgff, hcode] with c ⟨hcs, hcg⟩ hc
  have hGc : Measurable (G c) := hG.comp (measurable_const.prodMk measurable_id)
  rw [eq_map_of_ae_snd_eq hGc hc]
  congr 1
  have h := Exist.map_eq_of_isGFFWithBoundaryData hcg ((w c).isGFFWithBoundaryData_gffLaw hcs)
    ((w c).isBoundedHarmonicExtension_mean hcs)
  rw [h, Measure.map_id]

/-- **The same kernel disintegrates `(β, X)` on every `𝒢`-event `B ⊆ M`.** If `K` disintegrates
`X = (H_c, G(β, H_c))` given `β` on the `𝒢`-event `M` on which (R1) holds, then for every `𝒢`-event `B` contained
almost surely in `M`, `(P|B).map (β, X) = (P|B).map β ⊗ K`. -/
theorem map_restrict_eq_compProd_of_condExp [StandardBorelSpace T] [Nonempty T] {𝒢 mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M) {β : Ω → C}
    (hβ : Measurable[𝒢] β) {w : C → BoundaryWord} (hw : Measurable w)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    {G : C → DistOn upperHalfPlaneOpens → T} (hG : Measurable (Function.uncurry G))
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {K : Kernel C (DistOn upperHalfPlaneOpens × T)} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, (Hc ω, G (β ω) (Hc ω)))) = (P.restrict M).map β ⊗ₘ K)
    {B : Set Ω} (hB : MeasurableSet[𝒢] B) (hBM : ∀ᵐ ω ∂P, ω ∈ B → ω ∈ M) :
    (P.restrict B).map (fun ω => (β ω, (Hc ω, G (β ω) (Hc ω)))) = (P.restrict B).map β ⊗ₘ K := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hXm : Measurable fun ω => (Hc ω, G (β ω) (Hc ω)) :=
    hHc.prodMk (hG.comp (hβm.prodMk hHc))
  -- replace `B` by `B ∩ M`
  have hB' : MeasurableSet[𝒢] (B ∩ M) := hB.inter hM
  have hBeq : P.restrict B = P.restrict (B ∩ M) := by
    refine Measure.restrict_congr_set ?_
    filter_upwards [hBM] with ω hω
    exact propext ⟨fun h => ⟨h, hω h⟩, fun h => h.1⟩
  rw [hBeq]
  obtain ⟨KB, hKB, hlawB⟩ := exists_isMarkovKernel_map_eq_compProd P (B ∩ M) hβm hXm
  have h1 := ae_kernel_eq_of_condExp h𝒢 hB' hβ hw
    (by filter_upwards [hsort] with ω hω h; exact hω h.2) hHc hG
    (fun φ => by filter_upwards [hR1 φ] with ω hω h; exact hω h.2) hlawB
  have h2 := ae_kernel_eq_of_condExp h𝒢 hM hβ hw hsort hHc hG hR1 hlaw
  have hac : (P.restrict (B ∩ M)).map β ≪ (P.restrict M).map β :=
    Measure.absolutelyContinuous_of_le (Measure.map_mono (Measure.restrict_mono inter_subset_right le_rfl) hβm)
  have heq : KB =ᵐ[(P.restrict (B ∩ M)).map β] K := by
    filter_upwards [h1, hac.ae_le h2] with c hc1 hc2
    rw [hc1, hc2]
  rw [hlawB, Measure.compProd_congr heq]

end Kernel

/-! ### Events of the retained histories are events of the retained σ-algebra -/

section Hist

variable {Ω : Type*}

/-- **The trace of `aeSigma m P` on an `m`-event `T₀`**: the sets whose intersection with `T₀` coincides almost
surely with an event of `m`. -/
@[instance_reducible]
def TraceAESigma (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : @Measure Ω mΩ) (T₀ : Set Ω)
    (hT₀ : MeasurableSet[m] T₀) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[LocalSets.aeSigma m P] (A ∩ T₀)
  measurableSet_empty := by
    let _ : MeasurableSpace Ω := LocalSets.aeSigma m P
    rw [empty_inter]
    exact MeasurableSet.empty
  measurableSet_compl A hA := by
    let _ : MeasurableSpace Ω := LocalSets.aeSigma m P
    have e : Aᶜ ∩ T₀ = T₀ ∩ (A ∩ T₀)ᶜ := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff]
      tauto
    rw [e]
    exact (LocalSets.le_aeSigma m P T₀ hT₀).inter (MeasurableSet.compl hA)
  measurableSet_iUnion f hf := by
    let _ : MeasurableSpace Ω := LocalSets.aeSigma m P
    rw [iUnion_inter]
    exact MeasurableSet.iUnion hf

variable [mΩ : MeasurableSpace Ω]

/-- The retained histories are measurable: `histSigma d ≤ mΩ`. -/
theorem histSigma_le {d : RetData Ω} (hd : d.IsMeasGood) : histSigma d ≤ mΩ := by
  refine sup_le ?_ ?_
  · have hm : Measurable (retHistStop d) :=
      (measurable_pi_iff.2 fun t => hd.meas₁ _).prodMk (measurable_pi_iff.2 fun t => hd.meas₂ _)
    exact hm.comap_le
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s hs
    rw [mem_singleton_iff] at hs
    subst hs
    exact hd.measurableSet_G

/-- **Events of the retained histories in `{u < ζ₁, r < ζ₂}` are events of the retained σ-algebra.** Let `d` be
retained data at `(u, r)` agreeing almost surely, when `u < ζ₁` and `r < ζ₂`, with two paths `η₁`, `η₂` on the
prefixes (and lying in its good event). Every event `B` of the retained histories `histSigma d` contained almost surely
in `{u < ζ₁, r < ζ₂}` belongs to `Sec7.Lemma76F.retSigma76 P η₁ η₂ ζ₁ ζ₂ u r`: on that event the stopped data paths
are read, by continuity, from the recorded rational coordinates of the killed histories (`Restart.recon_histOf`),
and the event itself is recorded by the killing records. -/
theorem measurableSet_retSigma76_of_hist {P : Measure Ω} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {B : Set Ω} (hB : MeasurableSet[histSigma d] B)
    (hBT : ∀ᵐ ω ∂P, ω ∈ B → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω) :
    MeasurableSet[Sec7.Lemma76F.retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] B := by
  set R := Sec7.Lemma76F.retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r with hRdef
  set T₀ : Set Ω := {ω | (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω} with hT₀def
  have hum := Sec7.Lemma76F.lt_capR_left d.u d.r
  have hrm := Sec7.Lemma76F.lt_capR_right d.u d.r
  -- the event `{u < ζ₁, r < ζ₂}` is recorded by the killing records
  have hT₀ : MeasurableSet[MeasurableSpace.comap R inferInstance] T₀ := by
    refine ⟨{k : KHist × KHist | (d.u : ℝ≥0∞) < k.1.2 ∧ (d.r : ℝ≥0∞) < k.2.2}, ?_, ?_⟩
    · exact (measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)).inter
        (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
    · ext ω
      simp only [mem_preimage, mem_ofPred_eq, hRdef, Sec7.Lemma76F.retHist76, Sec7.Lemma76F.cstHist, khistOf, hT₀def]
      rw [Sec7.Lemma76F.lt_lifeRec_cutLife_iff hum, Sec7.Lemma76F.lt_lifeRec_cutLife_iff hrm]
  -- the reader of the stopped paths
  set Φ : KHist × KHist → (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) := fun k =>
    (fun t => Restart.recon k.1.1 (min t d.u), fun t => Restart.recon k.2.1 (min t d.r)) with hΦdef
  have hΦ : Measurable Φ := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.2 fun t =>
        (Restart.measurable_recon _).comp (measurable_fst.comp measurable_fst)
    · exact measurable_pi_iff.2 fun t =>
        (Restart.measurable_recon _).comp (measurable_fst.comp measurable_snd)
  have hcont : ∀ {η dη : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {a : ℝ≥0} {ω : Ω}, (a : ℝ≥0∞) < ζ ω →
      a < Sec7.Lemma76F.capR d.u d.r → ContinuousOn (dη ω) (Icc 0 a) → (∀ s ≤ a, dη ω s = η ω s) →
      ContinuousOn (Sec7.Lemma76F.cappedPath η ζ (Sec7.Lemma76F.capR d.u d.r) ω) {s : ℝ≥0 | (s : ℝ≥0∞) ≤ a} := by
    intro η dη ζ a ω hζ ham hc hag'
    have e : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ a} = Icc 0 a := by
      ext s
      simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and, ENNReal.coe_le_coe]
    rw [e]
    refine hc.congr fun s hs => ?_
    simp only [Sec7.Lemma76F.cappedPath]
    rw [Sec7.Lemma76F.capTime_eq_of_lt hζ ham hs.2, hag' s hs.2]
  have hkey : ∀ᵐ ω ∂P, ω ∈ T₀ → ω ∈ d.G ∧ retHistStop d ω = Φ (R ω) := by
    filter_upwards [hag] with ω hω hωT
    obtain ⟨hG, a₁, a₂⟩ := hω hωT.1 hωT.2
    have hg := hd.good ω hG
    refine ⟨hG, Prod.ext (funext fun t => ?_) (funext fun t => ?_)⟩
    · have ht : min t d.u ≤ d.u := min_le_right _ _
      show d.η₁ ω (min t d.u) = Restart.recon (R ω).1.1 (min t d.u)
      simp only [hRdef, Sec7.Lemma76F.retHist76, Sec7.Lemma76F.cstHist, khistOf]
      rw [Restart.recon_histOf (hcont hωT.1 hum hg.1 a₁) (ENNReal.coe_le_coe.2 ht) (ENNReal.coe_le_coe.2 ht)]
      simp only [Sec7.Lemma76F.cappedPath]
      rw [Sec7.Lemma76F.capTime_eq_of_lt hωT.1 hum ht, a₁ _ ht]
    · have ht : min t d.r ≤ d.r := min_le_right _ _
      show d.η₂ ω (min t d.r) = Restart.recon (R ω).2.1 (min t d.r)
      simp only [hRdef, Sec7.Lemma76F.retHist76, Sec7.Lemma76F.cstHist, khistOf]
      rw [Restart.recon_histOf (hcont hωT.2 hrm hg.2.1 a₂) (ENNReal.coe_le_coe.2 ht) (ENNReal.coe_le_coe.2 ht)]
      simp only [Sec7.Lemma76F.cappedPath]
      rw [Sec7.Lemma76F.capTime_eq_of_lt hωT.2 hrm ht, a₂ _ ht]
  -- the retained histories sit in the trace σ-algebra
  have hle : histSigma d ≤ TraceAESigma (MeasurableSpace.comap R inferInstance) P T₀ hT₀ := by
    refine sup_le ?_ ?_
    · rintro A ⟨S, hS, rfl⟩
      show MeasurableSet[LocalSets.aeSigma (MeasurableSpace.comap R inferInstance) P] (retHistStop d ⁻¹' S ∩ T₀)
      have hm : MeasurableSet[MeasurableSpace.comap R inferInstance] (R ⁻¹' (Φ ⁻¹' S)) :=
        ⟨Φ ⁻¹' S, hΦ hS, rfl⟩
      refine ⟨R ⁻¹' (Φ ⁻¹' S) ∩ T₀, hm.inter hT₀, ?_⟩
      filter_upwards [hkey] with ω hω
      show (ω ∈ retHistStop d ⁻¹' S ∩ T₀) = (ω ∈ R ⁻¹' (Φ ⁻¹' S) ∩ T₀)
      by_cases hωT : ω ∈ T₀
      · simp only [mem_inter_iff, mem_preimage, (hω hωT).2, hωT, and_true]
      · simp only [mem_inter_iff, hωT, and_false]
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s hs
      rw [mem_singleton_iff] at hs
      subst hs
      show MeasurableSet[LocalSets.aeSigma (MeasurableSpace.comap R inferInstance) P] (d.G ∩ T₀)
      refine ⟨T₀, hT₀, ?_⟩
      filter_upwards [hkey] with ω hω
      show (ω ∈ d.G ∩ T₀) = (ω ∈ T₀)
      by_cases hωT : ω ∈ T₀
      · simp only [mem_inter_iff, (hω hωT).1, hωT, and_self]
      · simp only [mem_inter_iff, hωT, and_false]
  obtain ⟨B₀, hB₀, hBe⟩ : MeasurableSet[LocalSets.aeSigma (MeasurableSpace.comap R inferInstance) P] (B ∩ T₀) :=
    hle B hB
  refine MeasurableSpace.measurableSet_inf.2 ⟨histSigma_le hd B hB, B₀, hB₀, EventuallyEq.trans ?_ hBe⟩
  filter_upwards [hBT] with ω hω
  show (ω ∈ B) = (ω ∈ B ∩ T₀)
  exact propext ⟨fun h => ⟨h, hω h⟩, fun h => h.1⟩

end Hist

/-! ### The named CONDDET input with the retained σ-algebra, and the conditional restart -/

/-- **Named input: PROVE-CONDDET's two-tip input with the untouched word, conditionally on the retained σ-algebra**
(Lemma G7, pp. 497–498: the conditional law of the chart field given the two retained killed histories; proof of
Lemma G8, p. 501). `RetainedCanonCondDetUntouchedStatement` with the σ-algebra `𝒢` of (R1) containing the retained
σ-algebra `Sec7.Lemma76F.retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r` of the two killed flow-line histories (the form in which
`Sec7.Lemma76F.exists_r1_of_meanIdent` gives (R1) for Lemma 7.6). **Not proved in Lean.** -/
def RetainedCanonCondDetHistStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (V₁ V₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) →
      (∀ t, Measurable fun ω => γ₂ ω t) → Measurable V₁ → Measurable V₂ →
      (∀ ω, ContinuousOn (γ₁ ω) {s | (s : ℝ≥0∞) ≤ V₁ ω}) → (∀ ω, ContinuousOn (γ₂ ω) {s | (s : ℝ≥0∞) ≤ V₂ ω}) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        IsCanonRetClock d η₁ η₂ ζ₁ ζ₂ γ₁ γ₂ V₁ V₂ ω) →
    ∀ F₁ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F₁ → IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord × ℝ),
      Sec7.Lemma76F.retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).1.IsSorted ∧ 0 < (β ω).2) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω).1 φ) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1 ∧
        V₁ ω ≤ (F₁ (β ω, hd.chartField κ h ω)).2 ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → γ₁ ω s = decPath (F₁ (β ω, hd.chartField κ h ω)) s) ∧
        V₂ ω ≤ (F₂ (((β ω).1, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → γ₂ ω s = decPath (F₂ (((β ω).1, 0), hd.chartField κ h ω)) s

/-- The input with the retained σ-algebra implies RLC-E's input. -/
theorem retainedCanonCondDetUntouchedStatement_of_hist (hD : RetainedCanonCondDetHistStatement.{u}) :
    RetainedCanonCondDetUntouchedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁ hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  obtain ⟨𝒢, M, β, -, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁
      hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  exact ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩

/-- **Lemma G7's retained-pair restart conditionally on the retained histories**, from Theorems 1.2 (param), 1.3 and
the two-tip input with the retained σ-algebra: the proof of `retainedPairRestartUntouchedStatement_of_param` (the
restart kernel is the conditional law of the restart variable given the datum on `M`), and every event of the retained
histories inside the ordinary event is a `𝒢`-event (`measurableSet_retSigma76_of_hist`), on which the same kernel
disintegrates the restart variable (`map_restrict_eq_compProd_of_condExp`). -/
theorem retainedPairRestartCondStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetHistStatement.{u}) :
    RetainedPairRestartCondStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  obtain ⟨γ₁, γ₂, V₁, V₂, hγ₁, hγ₂, hV₁, hV₂, hc₁, hc₂, hcanon⟩ := exists_retClock hκ hκ4 hη₁ hη₂ hd hag
  have hF := canonicalFlowCodeStatement_of_param h12p h13
  obtain ⟨F₁, hF₁⟩ := hF κ θ₁ hκ hκ4
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨𝒢, M, β, h𝒢R, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁
      hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  set Hc := hd.chartField κ h with hHc
  have hHcm : Measurable Hc := hd.measurable_chartField κ hh.1
  set G : BoundaryWord × ℝ → DistOn upperHalfPlaneOpens →
      ((Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞) × ((Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞) :=
    fun c H => (F₁ ((c.1, c.2), H), F₂ ((c.1, 0), H)) with hGdef
  have hGm : Measurable (Function.uncurry G) := by
    refine (hF₁.1.comp ?_).prodMk (hF₂.1.comp ?_)
    · exact ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)).prodMk
        measurable_snd
    · exact ((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd
  set X : Ω → RestartSpace := fun ω => (Hc ω, G (β ω) (Hc ω)) with hXdef
  have hXm : Measurable X := hHcm.prodMk (hGm.comp (hβm.prodMk hHcm))
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hco := isRestartCoordinates_restartSpace
  -- (R1) under the kernel
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word 𝒢.2 hM hβ measurable_fst
    (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).1) hXm (H := RestartSpace.field)
    measurable_fst hlaw hR1
  -- the two continuations are the canonical flows of the chart field, by construction
  have hfl₁ := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_fst measurable_snd
    (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₁) hco.2.2.2.1 hco.2.1
    hco.2.2.2.2.2.1 hF₁ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hfl₂ := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_fst (x := fun _ => (0 : ℝ))
    measurable_const (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₂) hco.2.2.2.2.1
    hco.2.2.1 hco.2.2.2.2.2.2 hF₂ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hpos : ∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 :=
    (ae_map_iff (p := fun c : BoundaryWord × ℝ => 0 < c.2) hβm.aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).2
      ((ae_restrict_iff' hMm).2 (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).2))
  refine ⟨RestartSpace, inferInstance, RestartSpace.field, RestartSpace.path₁, RestartSpace.path₂,
    RestartSpace.life₁, RestartSpace.life₂, M, β, X, K, hco, hMm, hβm, hXm, hK, hlaw, ?_, ?_, ?_⟩
  · filter_upwards [hgff, hfl₁, hfl₂, hpos] with c ⟨_, hcg⟩ h1 h2 hc
    exact ⟨hc, hcg, h1, h2⟩
  -- the clocks (`Supp7.retainedPairRestartStatement_of_clock`)
  · filter_upwards [hpath, hcanon, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, hag] with ω hω hc hg₁ hg₂ hagω hord
    obtain ⟨hMω, hW, hUW, hU₁, he₁, hU₂, he₂⟩ := hω hord
    obtain ⟨hL₁, hP₁, hL₂, hP₂⟩ := hc hord
    obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
    have hωE := hd.mem_E_of_ordinary hG a₁ a₂ hord
    obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
    have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
        ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
      ⟨x₀, fun z => by
        show d.g ω z - d.shift ω = _
        rw [hx₀, RetData.g, RetData.K_of_mem hωE]⟩
    obtain ⟨k₁, k₂⟩ :=
      isRetainedClock_of_ordinary (hd.good ω (RetData.E_subset_G hωE)) hC hφ hg₁ hg₂ a₁ a₂ hord
    have hDd : d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.D_of_mem hωE
    rw [← hDd] at k₁ k₂
    have htip : (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re = tipPos d η₁ ω := rfl
    rw [htip] at k₁
    have hΓ₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → RestartSpace.path₁ (X ω) s = γ₁ ω s :=
      fun s hs => (he₁ s hs).symm
    have hΓ₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → RestartSpace.path₂ (X ω) s = γ₂ ω s :=
      fun s hs => (he₂ s hs).symm
    refine ⟨hMω, rfl, k₁.mono (by rw [← hL₁]; exact hU₁) fun s hs => ?_,
      k₂.mono (by rw [← hL₂]; exact hU₂) fun s hs => ?_, hW, hUW⟩
    · rw [← hL₁] at hs
      rw [hΓ₁ s hs, hP₁ s hs]
    · rw [← hL₂] at hs
      rw [hΓ₂ s hs, hP₂ s hs]
  -- the conditional clause
  · intro B hB hBord
    have hBT : ∀ᵐ ω ∂P, ω ∈ B → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω := by
      filter_upwards [hBord] with ω hω hωB
      exact ⟨(hω hωB).1, (hω hωB).2.1⟩
    have hB𝒢 : MeasurableSet[𝒢.1] B := h𝒢R _ (measurableSet_retSigma76_of_hist hd hag hB hBT)
    have hBM : ∀ᵐ ω ∂P, ω ∈ B → ω ∈ M := by
      filter_upwards [hBord, hpath] with ω hω hp hωB
      exact (hp (hω hωB)).1
    exact map_restrict_eq_compProd_of_condExp 𝒢.2 hM hβ measurable_fst
      (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).1) hHcm hGm hR1 hlaw hB𝒢 hBM

end RLC

end InteractingSLE
