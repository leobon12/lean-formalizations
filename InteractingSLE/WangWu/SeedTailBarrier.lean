/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailWord

/-!
# The remaining right barrier for a killed shifted word

Packet PROVE-WW-B27. `KilledRightBarrierStatement` records the terminal right-gap
noncollision step for integrated equations before an arbitrary killing time.
It is an unproved named input, not a theorem. The reductions below prove that
this input applies to the shifted two-slit word from its mean-martingale law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open ImgDrv ImgWord MartChar Sec7.PhaseSelFull

/-- No right force gap tends to zero at a finite positive killing time. -/
def RightSafe {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VR : Fin 2 → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ∀ τ : ℝ≥0, 0 < τ → (τ : ℝ≥0∞) = T ω → ∀ j : Fin 2,
    ¬ Tendsto (fun t => VR j t ω - W t ω) (𝓝[<] τ) (𝓝 0)

/-- Named remaining stochastic input: right-side noncollision at the killing time
for the shifted word. Its equations are required only before that time. -/
def KilledRightBarrierStatement : Prop :=
  ∀ (rL rR δ : ℝ), 0 ≤ rL → 0 ≤ rR → 0 < δ → δ < 1 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 2 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞),
      IsFilteredBrownianReal 𝓖 B P → (∀ ω, Continuous (B · ω)) →
      IsKilledWord W VL VR T → StronglyAdapted 𝓖 W →
      (∀ i, StronglyAdapted 𝓖 (VL i)) → (∀ j, StronglyAdapted 𝓖 (VR j)) →
      (∀ q : ℝ≥0, MeasurableSet[𝓖 q] {ω | (q : ℝ≥0∞) < T ω}) → (∀ ω, 0 < T ω) →
      (∀ᵐ ω ∂P, Sec7.Aux117.IsWordEntrance 4 (fun i => VL i 0 ω) (fun j => VR j 0 ω)
        ![rL, -rL - δ] ![rR, -rR + δ] (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (B · ω) (T ω)) →
      ∀ᵐ ω ∂P, RightSafe W VR T ω

/-- Pulling a killed word back along a map preserves all its deterministic clauses. -/
theorem isKilledWord_comp {Ω Ω' : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}
    (hK : IsKilledWord W VL VR T) (f : Ω' → Ω) :
    IsKilledWord (fun t ω => W t (f ω)) (fun i t ω => VL i t (f ω))
      (fun j t ω => VR j t (f ω)) (fun ω => T (f ω)) where
  w_zero ω := hK.w_zero (f ω)
  contW ω := hK.contW (f ω)
  ordL ω := hK.ordL (f ω)
  ordR ω := hK.ordR (f ω)
  pathL ω := hK.pathL (f ω)
  pathR ω := hK.pathR (f ω)
  antiL ω := hK.antiL (f ω)
  monoR ω := hK.monoR (f ω)
  idxL ω := hK.idxL (f ω)
  idxR ω := hK.idxR (f ω)
  mergeL ω := hK.mergeL (f ω)
  mergeR ω := hK.mergeR (f ω)
  sepL ω := hK.sepL (f ω)
  sepR ω := hK.sepR (f ω)

/-- The terminal barrier descends from the independent Brownian extension in
Lemma 2.11. No continuation of the trace is used. -/
theorem ae_rightSafe_of_mart (hBarrier : KilledRightBarrierStatement.{u})
    {rL rR δ : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {T : Ω → ℝ≥0∞} {σ : ℕ → Ω → ℝ≥0}
    (hnull : ∀ A, MeasurableSet A → P A = 0 → MeasurableSet[𝓖 0] A)
    (hK : IsKilledWord W VL VR T) (hWa : StronglyAdapted 𝓖 W)
    (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j))
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσm : ∀ ω, Monotone (σ · ω)) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
    (hσlim : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T ω → ∃ n, t ≤ σ n ω)
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓖 q] {ω | (q : ℝ≥0∞) < T ω})
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc 4 ![rL, -rL - δ] ![rR, -rR + δ] W VL VR z)) :
    ∀ᵐ ω ∂P, RightSafe W VR T ω := by
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, hE⟩ :=
    hK.exists_isWordEntrance (by norm_num : (0 : ℝ) < 4) hnull hWa hVLa hVRa
      hσ hσm hσT hσlim hmart
  have hsafe := hBarrier rL rR δ hL hR hδ hδ1 (P.prod P₀) (WholeField.prodFiltration 𝓖 𝓦)
    (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B (fun p => T p.1)
    hB hBc (isKilledWord_comp hK Prod.fst) (stronglyAdapted_fst hWa)
    (fun i => stronglyAdapted_fst (hVLa i)) (fun j => stronglyAdapted_fst (hVRa j))
    (fun q => WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hTq q, rfl⟩)
    (fun p => lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ σ 0 p.1 from bot_le) (hσT 0 p.1)) hE
  filter_upwards [Measure.ae_ae_of_ae_prod hsafe] with ω hω
  exact hω.exists.choose_spec

/-- The same reduction for the explicit image word, with its existing filtration
and announcing sequence. -/
theorem ae_rightSafe_img_of_mart (hBarrier : KilledRightBarrierStatement.{u})
    {rL rR δ : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure (Ω × LawUnique.HistorySpace 1 1)}
    [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℚ} (hs : 0 < s)
    {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hWa : AdaptedBefore 𝓕 ζ W)
    (hgood : ∀ᵐ p ∂μ, IsGlueGood s ζ W p)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore
      (imgFilt μ s ζ W (glueGood μ s ζ W)) μ
      (fun p => min (QuantumZipper.swallowTime (wpath (imgW s ζ W (glueGood μ s ζ W)) p) z : WithTop ℝ≥0)
        (imgT s ζ W (glueGood μ s ζ W) p))
      (coupProc 4 ![rL, -rL - δ] ![rR, -rR + δ] (imgW s ζ W (glueGood μ s ζ W))
        (imgVL s ζ W (glueGood μ s ζ W)) (imgVR s ζ W (glueGood μ s ζ W)) z)) :
    ∀ᵐ p ∂μ, RightSafe (imgW s ζ W (glueGood μ s ζ W))
      (imgVR s ζ W (glueGood μ s ζ W)) (imgT s ζ W (glueGood μ s ζ W)) p := by
  let E := glueGood μ s ζ W
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := isGlueGood_of_mem_glueGood
  have hEm : MeasurableSet E := measurableSet_glueGood
  apply ae_rightSafe_of_mart hBarrier hL hR hδ hδ1
    (fun A hA h0 => Ito.measurableSet_usualAugmentation_of_null hA h0 0) (isKilledWord_img hs hEg)
    (stronglyAdapted_imgFilt_of (measurable_imgW hs hWa hEm hEg) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inl rfl⟩⟩)
    (fun i => stronglyAdapted_imgFilt_of (measurable_imgVL hs hWa hEm hEg i) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
    (fun j => stronglyAdapted_imgFilt_of (measurable_imgVR hs hWa hEm hEg j) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩)
    (σ := imgAnn s ζ W E) _ (monotone_imgAnn hs hEg) (fun n p => imgAnn_lt_imgT hs hEg n p) _ _ hmart
  · intro n r
    have he : {p : Ω × LawUnique.HistorySpace 1 1 | (imgAnn s ζ W E n p : WithTop ℝ≥0) ≤ r} =
        {p | imgAnn s ζ W E n p ≤ r} := by
      ext p
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [he]
    exact measurableSet_imgFilt_of_gen ⟨r, le_rfl, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))⟩
      (measurableSet_le (measurable_imgAnn hs hWa hEm hEg n) measurable_const)
  · filter_upwards [ae_mem_glueGood hgood] with p hp
    exact fun t ht => exists_le_imgAnn hs hEg hp ht
  · intro q
    exact measurableSet_imgFilt_of_gen ⟨q, le_rfl, Or.inr (Or.inl rfl)⟩
      (measurableSet_lt_imgT hs hWa hEm hEg q)

end InteractingSLE.WangWu.SeedTail
