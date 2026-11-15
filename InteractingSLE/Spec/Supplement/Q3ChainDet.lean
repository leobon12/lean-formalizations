/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainRet
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Supplement.WalkBdryCompare

/-!
# Field determination of hulls at stopping times from a field-determined driving history

Packet PROVE-Q3-REL3, input `hdA` of `Q3Chain.gb6_unionLaw`. Theorem 1.2 enters in the form
`LP.IsFieldDeterminedHistory P h W VL VR ζ` (the killed driving history is almost surely a Borel function of the field).
From it:

* `killedDrivingSigma_le_aeSigma`, `drivingFiltration_le_aeSigma`: the killed driving σ-algebras and the driving
  filtration (its usual augmentation) are contained, up to null sets, in `σ(h)`;
* `stopping_measurableSpace_le_aeSigma`: so is the σ-algebra of every finite stopping time;
* `avoid_hull_aeSigma`: the avoidance events `{K_τ ∩ U = ∅}` (`U ⊆ ℍ` open) of the hull at a stopping time before the
  lifetime are events of `σ(h)` up to null sets (`WholeField.exists_measurableSet_ae_iff_disjoint` on rational closed
  discs);
* `avoid_negInv_iff`: the avoidance events of a reflected set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Supp8.Q3Chain

open LocalSets

section AeSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem aeSigma_le_of_le {m G : MeasurableSpace Ω} (hmG : m ≤ aeSigma G P) : aeSigma m P ≤ aeSigma G P := by
  rintro S ⟨S', hS', he⟩
  obtain ⟨T, hT, he'⟩ := hmG S' hS'
  exact ⟨T, hT, he.trans he'⟩

theorem nullSets_le_aeSigma (G : MeasurableSpace Ω) : Ito.nullSets P ≤ aeSigma G P := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨-, hS0⟩
  refine ⟨∅, @MeasurableSet.empty _ G, ?_⟩
  rw [ae_eq_empty]
  exact hS0

end AeSigma

section History

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The killed driving σ-algebras are field-determined** when the killed driving history is. -/
theorem killedDrivingSigma_le_aeSigma (hdet : LP.IsFieldDeterminedHistory P h W VL VR ζ) (t : ℝ≥0) :
    killedDrivingSigma W VL VR ζ t ≤ aeSigma (MeasurableSpace.comap h inferInstance) P := by
  obtain ⟨Ψ, hΨm, hΨ⟩ := hdet
  refine MeasurableSpace.generateFrom_le ?_
  rintro E ⟨r, -, A, hA, rfl⟩
  set B : Set (DistOn upperHalfPlaneOpens) := {d | (r : ℝ≥0∞) < (Ψ d).1 ∧
    ((Ψ d).2.1 r, (fun i => (Ψ d).2.2.1 i r), fun i => (Ψ d).2.2.2 i r) ∈ A} with hBdef
  have hBm : MeasurableSet B := by
    refine (measurableSet_lt measurable_const (measurable_fst.comp hΨm)).inter (hA.preimage ?_)
    refine (((measurable_pi_apply r).comp measurable_snd.fst).comp hΨm).prodMk
      (((measurable_pi_iff.2 fun i => (measurable_pi_apply r).comp ((measurable_pi_apply i).comp
        measurable_snd.snd.fst))).comp hΨm |>.prodMk
      ((measurable_pi_iff.2 fun i => (measurable_pi_apply r).comp ((measurable_pi_apply i).comp
        measurable_snd.snd.snd)).comp hΨm))
  refine ⟨h ⁻¹' B, ⟨B, hBm, rfl⟩, ?_⟩
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [hΨ] with ω ⟨hz, hpath⟩
  simp only [mem_ofPred_eq, mem_preimage, hBdef, hz]
  constructor
  · rintro ⟨hr, hA⟩
    obtain ⟨e1, e2, e3⟩ := hpath r hr
    refine ⟨hr, ?_⟩
    have e2' : (fun i => (Ψ (h ω)).2.2.1 i r) = fun i => VL i r ω := funext e2
    have e3' : (fun i => (Ψ (h ω)).2.2.2 i r) = fun i => VR i r ω := funext e3
    rw [e1, e2', e3']
    exact hA
  · rintro ⟨hr, hA⟩
    obtain ⟨e1, e2, e3⟩ := hpath r hr
    refine ⟨hr, ?_⟩
    have e2' : (fun i => (Ψ (h ω)).2.2.1 i r) = fun i => VL i r ω := funext e2
    have e3' : (fun i => (Ψ (h ω)).2.2.2 i r) = fun i => VR i r ω := funext e3
    rw [e1, e2', e3'] at hA
    exact hA

/-- **The driving filtration is field-determined** (the usual augmentation adds null sets only). -/
theorem drivingFiltration_le_aeSigma (hdet : LP.IsFieldDeterminedHistory P h W VL VR ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    drivingFiltration P hX t ≤ aeSigma (MeasurableSpace.comap h inferInstance) P := by
  rw [drivingFiltration, Ito.usualAugmentation_apply]
  refine (iInf₂_le (t + 1) (lt_add_one t)).trans ?_
  rw [Ito.nullAugmented_apply]
  exact sup_le (killedDrivingSigma_le_aeSigma hdet (t + 1)) (nullSets_le_aeSigma _)

/-- **The σ-algebra of a finite stopping time of a filtration contained in `aeSigma G`** is contained in it. -/
theorem stopping_measurableSpace_le_aeSigma {𝓖 : Filtration ℝ≥0 mΩ} {G : MeasurableSpace Ω}
    (h𝓖 : ∀ t, 𝓖 t ≤ aeSigma G P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (hτt : ∀ ω, τ ω ≠ ⊤) :
    hτ.measurableSpace ≤ aeSigma G P := by
  intro S hS
  have e : S = ⋃ n : ℕ, (S ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    refine ⟨fun hω => ?_, fun ⟨_, hω, _⟩ => hω⟩
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 (hτt ω)
    obtain ⟨n, hn⟩ := exists_nat_ge x
    refine ⟨n, hω, ?_⟩
    rw [← hx]
    exact_mod_cast hn
  rw [e]
  exact MeasurableSet.iUnion fun n => h𝓖 n _ (((hτ.measurableSet S).1 hS).2 n)

end History

/-! ### Avoidance events -/

/-- **Avoidance of an open set through rational closed discs**: for `U` open, a set `K` avoids `U` iff it avoids every
closed disc with rational centre and radius contained in `U`. -/
theorem disjoint_iff_forall_ratDisc {K U : Set ℂ} (hU : IsOpen U) :
    Disjoint K U ↔ ∀ p : ℚ × ℚ × ℚ, closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U →
      Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ)) K := by
  constructor
  · intro hd p hp
    exact (hd.mono_right hp).symm
  · intro hall
    refine Set.disjoint_left.2 fun z hzK hzU => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hzU
    have hε3 : 0 < ε / 8 := by positivity
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 8 < z.re by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ε / 8 < z.im by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    set q : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hq
    have hqre : q.re = a := by simp [hq]
    have hqim : q.im = b := by simp [hq]
    have hdist : dist z q < ε / 4 := by
      rw [Complex.dist_eq]
      calc ‖z - q‖ ≤ |(z - q).re| + |(z - q).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < ε / 8 + ε / 8 := by
          refine add_lt_add ?_ ?_
          · rw [Complex.sub_re, hqre, abs_lt]; constructor <;> linarith
          · rw [Complex.sub_im, hqim, abs_lt]; constructor <;> linarith
        _ = ε / 4 := by ring
    have hsub : closedBall q (r : ℝ) ⊆ U := by
      intro w hw
      refine hεU ?_
      rw [mem_ball]
      calc dist w z ≤ dist w q + dist q z := dist_triangle _ _ _
        _ < (r : ℝ) + ε / 4 + ε / 4 := by
          rw [dist_comm q z]
          have := mem_closedBall.1 hw
          linarith
        _ ≤ ε := by linarith
    have hzq : z ∈ closedBall q (r : ℝ) := by
      rw [mem_closedBall]
      linarith
    exact Set.disjoint_left.1 (hall (a, b, r) hsub) hzq hzK

theorem avoid_negInv_iff {S U : Set ℂ} : Disjoint (WangWu.negInv '' S) U ↔ Disjoint S (WangWu.negInv '' U) := by
  constructor
  · intro hd
    refine Set.disjoint_left.2 fun z hzS ⟨w, hwU, hwz⟩ => ?_
    refine Set.disjoint_left.1 hd ⟨z, hzS, rfl⟩ ?_
    rw [← hwz]
    change -(-w⁻¹)⁻¹ ∈ U
    rw [inv_neg, inv_inv, neg_neg]
    exact hwU
  · intro hd
    refine Set.disjoint_left.2 fun z ⟨w, hwS, hwz⟩ hzU => ?_
    refine Set.disjoint_left.1 hd hwS ⟨z, hzU, ?_⟩
    rw [← hwz]
    change -(-w⁻¹)⁻¹ = w
    rw [inv_neg, inv_inv, neg_neg]


/-- **The avoidance events of the hull at a finite stopping time before the lifetime are field-determined**: if the
driving filtration is contained in `aeSigma G` (e.g. `drivingFiltration_le_aeSigma`), then for every open `U ⊆ ℍ`
the event `{K_τ ∩ U = ∅}` is an event of `aeSigma G`. -/
theorem avoid_hull_aeSigma {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : ℕ → Ω → ℝ≥0}
    (hσ : Coupling.IsAnnouncingSeq (drivingFiltration P hX) P ζ σ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) {Y : Type*} [MeasurableSpace Y] {g : Ω → Y}
    (hG : ∀ t, drivingFiltration P hX t ≤ aeSigma (MeasurableSpace.comap g inferInstance) P)
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[aeSigma (MeasurableSpace.comap g inferInstance) P]
      {ω | Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) U} := by
  have hst := stopping_measurableSpace_le_aeSigma hG hτ hτt
  have e : {ω | Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) U} =
      ⋂ p : ℚ × ℚ × ℚ, {ω | closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U →
        Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
          (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact disjoint_iff_forall_ratDisc hU
  rw [e]
  refine MeasurableSet.iInter fun p => ?_
  by_cases hp : closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U
  · obtain ⟨Gp, hGp, hGpe⟩ := WholeField.exists_measurableSet_ae_iff_disjoint hE hX hσ hτ hτζ
      (isCompact_closedBall _ _) (hp.trans hUH)
    obtain ⟨T, hT, hTe⟩ := hst Gp hGp
    refine ⟨T, hT, EventuallyEq.trans ?_ hTe⟩
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hGpe] with ω hω
    simp only [hp, true_imp_iff]
    exact hω.symm
  · have e' : {ω | closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U →
        Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
          (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact fun h => absurd h hp
    rw [e']
    exact MeasurableSet.univ

/-- **The hitting σ-algebra of a reflected hull at a stopping time is field-determined** (`A =ᵐ R(K_τ)`). -/
theorem hitting_reflect_hull_le_aeSigma {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : ℕ → Ω → ℝ≥0}
    (hσ : Coupling.IsAnnouncingSeq (drivingFiltration P hX) P ζ σ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) {Y : Type*} [MeasurableSpace Y] {g : Ω → Y}
    (hG : ∀ t, drivingFiltration P hX t ≤ aeSigma (MeasurableSpace.comap g inferInstance) P)
    {A : Ω → Set ℂ}
    (hAe : ∀ᵐ ω ∂P, A ω = WangWu.negInv '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    MeasurableSpace.comap A hittingSigma ≤ aeSigma (MeasurableSpace.comap g inferInstance) P := by
  refine Theorem14.WalkBdry.hitting_comap_le_aeSigma fun U hUH => ?_
  refine Theorem14.WalkBdry.avoid_aeSigma_congr (A := fun ω =>
    WangWu.negInv '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) hAe (fun V hVH => ?_) U hUH
  have e : {ω | Disjoint (WangWu.negInv '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
      (V : Set ℂ)} = {ω | Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
      (WangWu.negInv '' (V : Set ℂ))} := by
    ext ω
    exact avoid_negInv_iff
  rw [e]
  exact avoid_hull_aeSigma hE hX hσ hτ hτζ hτt hG (WangWu.isOpen_image_negInv V.isOpen hVH)
    (fun z ⟨w, hw, hwz⟩ => hwz ▸ WangWu.negInv_mem_H (hVH hw))

end InteractingSLE.Supp8.Q3Chain
