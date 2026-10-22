import HigherDimLQGMetric.Amplify.TrialLocal
import HigherDimLQGMetric.Amplify.LocalPlus
import LQGMetric.Meas.LocalEvent

/-!
# Trial locality for a Gaussian field plus a continuous perturbation

The fine field lives on a standard Borel white-noise sample space. On such a
space, the countable normalized metric code and Lusin separation show that the
trial event belongs, modulo null sets, to the shell field sigma algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric Topology LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private abbrev AmplifyShellCode :=
  ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞)) ×
    ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞))

private def amplify_shellCode (D Dt : DistRd d → ContMetric d)
    (ξ Q s : ℝ) (w : Rd d) (qJ qO : ℕ → Rd d) (g : DistRd d) :
    AmplifyShellCode :=
  ((fun p => ENNReal.ofReal ((sNorm ξ Q g s w)⁻¹) *
      (D g).chainInf (ann w (s / 2) (5 * s)) (qJ p.1) (qJ p.2),
    fun p => ENNReal.ofReal ((sNorm ξ Q g s w)⁻¹) *
      (Dt g).chainInf (ann w (s / 2) (5 * s)) (qJ p.1) (qJ p.2)),
   (fun p => ENNReal.ofReal ((sNorm ξ Q g s w)⁻¹) *
      (D g).chainInf (ann w (3 * s / 4) (3 * s)) (qO p.1) (qO p.2),
    fun p => ENNReal.ofReal ((sNorm ξ Q g s w)⁻¹) *
      (Dt g).chainInf (ann w (3 * s / 4) (3 * s)) (qO p.1) (qO p.2)))

private theorem amplify_measurable_shellCode
    {D Dt : DistRd d → ContMetric d} (hD : Measurable D) (hDt : Measurable Dt)
    (ξ Q s : ℝ) (w : Rd d) (qJ qO : ℕ → Rd d) :
    Measurable (amplify_shellCode D Dt ξ Q s w qJ qO) := by
  have hn : Measurable fun g : DistRd d => sNorm ξ Q g s w :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left s w)))
  have hcoord (A : DistRd d → ContMetric d) (hA : Measurable A)
      (V : Set (Rd d)) (q : ℕ → Rd d) :
      Measurable fun g : DistRd d => fun p : ℕ × ℕ =>
        ENNReal.ofReal ((sNorm ξ Q g s w)⁻¹) *
          (A g).chainInf V (q p.1) (q p.2) := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (ENNReal.measurable_ofReal.comp hn.inv).mul
      ((ContMetric.measurable_chainInf V).comp
        (hA.prodMk (measurable_const.prodMk measurable_const)))
  exact ((hcoord D hD _ qJ).prodMk (hcoord Dt hDt _ qJ)).prodMk
    ((hcoord D hD _ qO).prodMk (hcoord Dt hDt _ qO))

private theorem amplify_normInt_eq_of_dense
    {D : DistRd d → ContMetric d} {g₁ g₂ : DistRd d}
    (h₁ : (D g₁).IsLength) (h₂ : (D g₂).IsLength)
    (ξ Q s : ℝ) (w : Rd d) {V : Set (Rd d)} (hV : IsOpen V)
    {q : ℕ → Rd d} (hqV : ∀ n, q n ∈ V) (hq : V ⊆ closure (range q))
    (he : ∀ i j, normInt ξ Q D g₁ s w V (q i) (q j) =
      normInt ξ Q D g₂ s w V (q i) (q j)) :
    ∀ u ∈ V, ∀ v ∈ V,
      normInt ξ Q D g₁ s w V u v = normInt ξ Q D g₂ s w V u v := by
  have heq : EqOn (fun p : Rd d × Rd d => normInt ξ Q D g₁ s w V p.1 p.2)
      (fun p => normInt ξ Q D g₂ s w V p.1 p.2) (V ×ˢ V) := by
    refine EqOn.of_subset_closure (s := range (Prod.map q q)) ?_
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousOn.comp
        ((D g₁).continuousOn_internal h₁ hV) (mapsTo_univ _ _))
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousOn.comp
        ((D g₂).continuousOn_internal h₂ hV) (mapsTo_univ _ _)) ?_ ?_
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact he i j
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact ⟨hqV i, hqV j⟩
    · rw [range_prodMap, closure_prod_eq]
      exact prod_mono hq hq
  intro u hu v hv
  exact heq (show (u, v) ∈ V ×ˢ V from ⟨hu, hv⟩)

private theorem amplify_sphere_subset_outer {s : ℝ} (hs : 0 < s) (w : Rd d) :
    sphere w s ⊆ ann w (s / 2) (5 * s) := by
  intro x hx
  have he : ‖x - w‖ = s := mem_sphere_iff_norm.1 hx
  dsimp [ann]
  rw [he]
  constructor <;> linarith

private theorem amplify_sphere_subset_inner {s : ℝ} (hs : 0 < s) (w : Rd d) :
    sphere w s ⊆ ann w (3 * s / 4) (3 * s) := by
  intro x hx
  have he : ‖x - w‖ = s := mem_sphere_iff_norm.1 hx
  dsimp [ann]
  rw [he]
  constructor <;> linarith

private theorem amplify_inner_subset_outer {s : ℝ} (hs : 0 < s) (w : Rd d) :
    ann w (3 * s / 4) (3 * s) ⊆ ann w (s / 2) (5 * s) := by
  intro x hx
  dsimp [ann] at hx ⊢
  constructor <;> linarith

/-- D-LOC for the trial event under an LGF plus a continuous field on a
standard Borel sample space. This is the form used by the concrete white-noise
realization, whose sample space is `ℕ → ℝ`. -/
theorem amplify_aeEventIn_trialEvent_plus
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (cs c1 ℓ δ : ℝ) {s : ℝ} (hs : 0 < s) (w : Rd d) :
    AEEventIn P (fieldSigma0 h (ann w (s / 2) (5 * s)))
      (h ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w) := by
  have : NeZero d := ⟨by omega⟩
  let J : TopologicalSpace.Opens (Rd d) :=
    ⟨ann w (s / 2) (5 * s), isOpen_ann _ _ _⟩
  let O : TopologicalSpace.Opens (Rd d) :=
    ⟨ann w (3 * s / 4) (3 * s), isOpen_ann _ _ _⟩
  have hSJ : sphere w s ⊆ J := amplify_sphere_subset_outer hs w
  have hSO : sphere w s ⊆ O := amplify_sphere_subset_inner hs w
  have hOJ : O ≤ J := amplify_inner_subset_outer hs w
  have hsphere : (sphere w s).Nonempty := NormedSpace.sphere_nonempty.2 hs.le
  obtain ⟨x, hx⟩ := hsphere
  obtain ⟨qJ, hqJ, hqJd⟩ := exists_denseSeq_rd ⟨x, hSJ hx⟩
  obtain ⟨qO, hqO, hqOd⟩ := exists_denseSeq_rd ⟨x, hSO hx⟩
  let R : Ω → AmplifyShellCode := fun ω =>
    amplify_shellCode D Dt ξ Q s w qJ qO (h ω)
  have hRm : Measurable R :=
    (amplify_measurable_shellCode hD.measurable hDt.measurable ξ Q s w qJ qO).comp
      hh.measurable
  obtain ⟨FDJ, hFDJm, hFDJae⟩ :=
    amplify_exists_measurable_normInternal_all_plus hD hd hh J J le_rfl w hs hSJ
  obtain ⟨FDtJ, hFDtJm, hFDtJae⟩ :=
    amplify_exists_measurable_normInternal_all_plus hDt hd hh J J le_rfl w hs hSJ
  obtain ⟨FDO, hFDOm, hFDOae⟩ :=
    amplify_exists_measurable_normInternal_all_plus hD hd hh O J hOJ w hs hSJ
  obtain ⟨FDtO, hFDtOm, hFDtOae⟩ :=
    amplify_exists_measurable_normInternal_all_plus hDt hd hh O J hOJ w hs hSJ
  let F : Ω → AmplifyShellCode := fun ω =>
    ((fun p => FDJ ω (qJ p.1) (qJ p.2), fun p => FDtJ ω (qJ p.1) (qJ p.2)),
     (fun p => FDO ω (qO p.1) (qO p.2), fun p => FDtO ω (qO p.1) (qO p.2)))
  have hcoord (G : Ω → Rd d → Rd d → ℝ≥0∞)
      (hG : Measurable[fieldSigma0 h J] G) (q : ℕ → Rd d) :
      Measurable[fieldSigma0 h J]
        (fun ω (p : ℕ × ℕ) => G ω (q p.1) (q p.2)) := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun p => ?_
    exact (measurable_pi_apply (q p.2)).comp
      ((measurable_pi_apply (q p.1)).comp hG)
  have hFm : Measurable[fieldSigma0 h J] F :=
    ((hcoord FDJ hFDJm qJ).prodMk (hcoord FDtJ hFDtJm qJ)).prodMk
      ((hcoord FDO hFDOm qO).prodMk (hcoord FDtO hFDtOm qO))
  have hLenD := hD.length P h hh
  have hLenDt := hDt.length P h hh
  have hFR : ∀ᵐ ω ∂P, F ω = R ω := by
    filter_upwards [hFDJae, hFDtJae, hFDOae, hFDtOae, hLenD, hLenDt]
      with ω h₁ h₂ h₃ h₄ hlD hlDt
    apply Prod.ext
    · apply Prod.ext <;> funext p
      · exact (h₁ _ _).trans (congrArg _ ((D (h ω)).internal_eq_chainInf hlD J.isOpen _ _))
      · exact (h₂ _ _).trans (congrArg _ ((Dt (h ω)).internal_eq_chainInf hlDt J.isOpen _ _))
    · apply Prod.ext <;> funext p
      · exact (h₃ _ _).trans (congrArg _ ((D (h ω)).internal_eq_chainInf hlD O.isOpen _ _))
      · exact (h₄ _ _).trans (congrArg _ ((Dt (h ω)).internal_eq_chainInf hlDt O.isOpen _ _))
  have hbad : P {ω | ¬((D (h ω)).IsLength ∧ (Dt (h ω)).IsLength)} = 0 :=
    ae_iff.mp (hLenD.and hLenDt)
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  let W : Set Ω := Nᶜ
  have hWm : MeasurableSet W := hNm.compl
  have hWlen : ∀ ω ∈ W, (D (h ω)).IsLength ∧ (Dt (h ω)).IsLength := by
    intro ω hω
    by_contra hc
    exact hω (hsub hc)
  have hWh : ∀ᵐ ω ∂P, ω ∈ W := by
    rw [ae_iff]
    simpa [W] using hN0
  let E : Set Ω := h ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w
  have hE : NullMeasurableSet E P :=
    amplify_nullMeasurableSet_trialEvent P h hh hD hDt cs c1 ℓ δ s w
  have hsat : ∀ ω₁ ∈ W, ∀ ω₂ ∈ W, R ω₁ = R ω₂ → ω₁ ∈ E → ω₂ ∈ E := by
    intro ω₁ hω₁ ω₂ hω₂ he hmem
    obtain ⟨hD₁, hDt₁⟩ := hWlen ω₁ hω₁
    obtain ⟨hD₂, hDt₂⟩ := hWlen ω₂ hω₂
    apply amplify_trial_saturated D Dt ξ Q cs c1 ℓ δ hs w (h ω₁) (h ω₂)
    · apply amplify_normInt_eq_of_dense hD₁ hD₂ ξ Q s w J.isOpen hqJ hqJd
      intro i j
      rw [normInt, (D (h ω₁)).internal_eq_chainInf hD₁ J.isOpen,
        normInt, (D (h ω₂)).internal_eq_chainInf hD₂ J.isOpen]
      exact congrFun (congrArg (fun x : AmplifyShellCode => x.1.1) he) (i, j)
    · apply amplify_normInt_eq_of_dense hD₁ hD₂ ξ Q s w O.isOpen hqO hqOd
      intro i j
      rw [normInt, (D (h ω₁)).internal_eq_chainInf hD₁ O.isOpen,
        normInt, (D (h ω₂)).internal_eq_chainInf hD₂ O.isOpen]
      exact congrFun (congrArg (fun x : AmplifyShellCode => x.2.1) he) (i, j)
    · apply amplify_normInt_eq_of_dense hDt₁ hDt₂ ξ Q s w O.isOpen hqO hqOd
      intro i j
      rw [normInt, (Dt (h ω₁)).internal_eq_chainInf hDt₁ O.isOpen,
        normInt, (Dt (h ω₂)).internal_eq_chainInf hDt₂ O.isOpen]
      exact congrFun (congrArg (fun x : AmplifyShellCode => x.2.2) he) (i, j)
    · exact hmem
  exact LocalEvent.aeEventIn_of_saturated measurable_id hRm hFm hFR hWm
    (by simpa only [Measure.map_id] using hE) hWh hsat

end HigherDimLQGMetric
