import HigherDimLQGMetric.Events.RegMeas
import HigherDimLQGMetric.Sharp.CountableShell
import LQGMetric.Meas.LocalEvent

/-! A countable shell code for normalized internal metrics and its locality theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric Topology LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The sharp-normalized internal distance on a deterministic open domain. -/
def normInt (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) (z : Rd d) (V : Set (Rd d))
    (u v : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) * (D g).internal V u v

private theorem continuousOn_normInt {D : DistRd d → ContMetric d}
    {g : DistRd d} (hD : (D g).IsLength) (ξ Q r : ℝ) (z : Rd d)
    {V : Set (Rd d)} (hV : IsOpen V) :
    ContinuousOn (fun p : Rd d × Rd d => normInt ξ Q D g r z V p.1 p.2)
      (V ×ˢ V) := by
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousOn.comp
    ((D g).continuousOn_internal hD hV) (mapsTo_univ _ _)

private theorem normInt_eq_of_dense {D : DistRd d → ContMetric d}
    {g₁ g₂ : DistRd d} (h₁ : (D g₁).IsLength) (h₂ : (D g₂).IsLength)
    (ξ Q r : ℝ) (z : Rd d) {V : Set (Rd d)} (hV : IsOpen V)
    {q : ℕ → Rd d} (hqV : ∀ n, q n ∈ V) (hq : V ⊆ closure (range q))
    (he : ∀ i j, normInt ξ Q D g₁ r z V (q i) (q j) =
      normInt ξ Q D g₂ r z V (q i) (q j)) :
    ∀ u ∈ V, ∀ v ∈ V,
      normInt ξ Q D g₁ r z V u v = normInt ξ Q D g₂ r z V u v := by
  have heq : EqOn (fun p : Rd d × Rd d => normInt ξ Q D g₁ r z V p.1 p.2)
      (fun p => normInt ξ Q D g₂ r z V p.1 p.2) (V ×ˢ V) := by
    refine EqOn.of_subset_closure (s := range (Prod.map q q)) ?_
      (continuousOn_normInt h₁ ξ Q r z hV)
      (continuousOn_normInt h₂ ξ Q r z hV) ?_ ?_
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact he i j
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact ⟨hqV i, hqV j⟩
    · rw [range_prodMap, closure_prod_eq]
      exact prod_mono hq hq
  intro u hu v hv
  exact heq (show (u, v) ∈ V ×ˢ V from ⟨hu, hv⟩)

private theorem sphere_subset_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z r ⊆ ann z (r / 2) (5 * r) := by
  intro x hx
  have he : ‖x - z‖ = r := mem_sphere_iff_norm.1 hx
  dsimp [ann]
  rw [he]
  constructor <;> linarith

private theorem sphere_subset_inner {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z r ⊆ ann z (3 * r / 4) (3 * r) := by
  intro x hx
  have he : ‖x - z‖ = r := mem_sphere_iff_norm.1 hx
  dsimp [ann]
  rw [he]
  constructor <;> linarith

private theorem inner_subset_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ann z (3 * r / 4) (3 * r) ⊆ ann z (r / 2) (5 * r) := by
  intro x hx
  dsimp [ann] at hx ⊢
  constructor <;> linarith

private theorem measurable_normInt_chain {D : DistRd d → ContMetric d}
    (hD : Measurable D) (ξ Q r : ℝ) (z : Rd d) (V : Set (Rd d))
    (u v : Rd d) :
    Measurable fun g : DistRd d => ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
      (D g).chainInf V u v := by
  have hs : Measurable fun g : DistRd d => sNorm ξ Q g r z :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left r z)))
  exact (ENNReal.measurable_ofReal.comp hs.inv).mul
    ((ContMetric.measurable_chainInf V).comp
      (hD.prodMk (measurable_const.prodMk measurable_const)))

private abbrev ShellCode :=
  ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞)) ×
    ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞))

private def shellCode (A B : DistRd d → ContMetric d) (ξ Q r : ℝ) (z : Rd d)
    (qJ qO : ℕ → Rd d) (g : DistRd d) : ShellCode :=
  ((fun p => ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
      (A g).chainInf (ann z (r / 2) (5 * r)) (qJ p.1) (qJ p.2),
    fun p => ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
      (B g).chainInf (ann z (r / 2) (5 * r)) (qJ p.1) (qJ p.2)),
   (fun p => ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
      (A g).chainInf (ann z (3 * r / 4) (3 * r)) (qO p.1) (qO p.2),
    fun p => ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
      (B g).chainInf (ann z (3 * r / 4) (3 * r)) (qO p.1) (qO p.2)))

private theorem measurable_shellCode {A B : DistRd d → ContMetric d}
    (hA : Measurable A) (hB : Measurable B) (ξ Q r : ℝ) (z : Rd d)
    (qJ qO : ℕ → Rd d) : Measurable (shellCode A B ξ Q r z qJ qO) := by
  exact ((measurable_pi_iff.2 fun p =>
      measurable_normInt_chain hA ξ Q r z _ _ _).prodMk
    (measurable_pi_iff.2 fun p =>
      measurable_normInt_chain hB ξ Q r z _ _ _)).prodMk
    ((measurable_pi_iff.2 fun p =>
      measurable_normInt_chain hA ξ Q r z _ _ _).prodMk
    (measurable_pi_iff.2 fun p =>
      measurable_normInt_chain hB ξ Q r z _ _ _))

/-- D-LOC reduction: any null-measurable field event determined, on length
metrics, by the two sharp-normalized internal metrics on the trapping shells
is an event of the mean-zero field pairings on the outer shell modulo null sets. -/
theorem aeEventIn_of_normInternal_shell
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (E : Set (DistRd d)) (hE : NullMeasurableSet E (P.map h))
    (hsat : ∀ g₁ g₂ : DistRd d,
      (A g₁).IsLength → (B g₁).IsLength →
      (A g₂).IsLength → (B g₂).IsLength →
      (∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
        normInt ξ Q A g₁ r z (ann z (r / 2) (5 * r)) u v =
          normInt ξ Q A g₂ r z (ann z (r / 2) (5 * r)) u v) →
      (∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
        normInt ξ Q B g₁ r z (ann z (r / 2) (5 * r)) u v =
          normInt ξ Q B g₂ r z (ann z (r / 2) (5 * r)) u v) →
      (∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
        normInt ξ Q A g₁ r z (ann z (3 * r / 4) (3 * r)) u v =
          normInt ξ Q A g₂ r z (ann z (3 * r / 4) (3 * r)) u v) →
      (∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
        normInt ξ Q B g₁ r z (ann z (3 * r / 4) (3 * r)) u v =
          normInt ξ Q B g₂ r z (ann z (3 * r / 4) (3 * r)) u v) →
      g₁ ∈ E → g₂ ∈ E) :
    AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r))) (h ⁻¹' E) := by
  have : NeZero d := ⟨by omega⟩
  let J : TopologicalSpace.Opens (Rd d) :=
    ⟨ann z (r / 2) (5 * r), isOpen_ann _ _ _⟩
  let O : TopologicalSpace.Opens (Rd d) :=
    ⟨ann z (3 * r / 4) (3 * r), isOpen_ann _ _ _⟩
  have hSJ : sphere z r ⊆ J := sphere_subset_outer hr z
  have hSO : sphere z r ⊆ O := sphere_subset_inner hr z
  have hOJ : O ≤ J := inner_subset_outer hr z
  have hsphere : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.2 hr.le
  obtain ⟨x, hx⟩ := hsphere
  obtain ⟨qJ, hqJ, hqJd⟩ := exists_denseSeq_rd ⟨x, hSJ hx⟩
  obtain ⟨qO, hqO, hqOd⟩ := exists_denseSeq_rd ⟨x, hSO hx⟩
  let R : DistRd d → ShellCode := shellCode A B ξ Q r z qJ qO
  have hRm : Measurable R := measurable_shellCode hA.measurable hB.measurable ξ Q r z qJ qO
  obtain ⟨FAJ, hFAJm, hFAJae⟩ := hA.exists_measurable_normInternal_all hd hh J J le_rfl z hr hSJ
  obtain ⟨FBJ, hFBJm, hFBJae⟩ := hB.exists_measurable_normInternal_all hd hh J J le_rfl z hr hSJ
  obtain ⟨FAO, hFAOm, hFAOae⟩ := hA.exists_measurable_normInternal_all hd hh O J hOJ z hr hSJ
  obtain ⟨FBO, hFBOm, hFBOae⟩ := hB.exists_measurable_normInternal_all hd hh O J hOJ z hr hSJ
  let F : Ω → ShellCode := fun ω =>
    ((fun p => FAJ ω (qJ p.1) (qJ p.2), fun p => FBJ ω (qJ p.1) (qJ p.2)),
     (fun p => FAO ω (qO p.1) (qO p.2), fun p => FBO ω (qO p.1) (qO p.2)))
  have hcoord (G : Ω → Rd d → Rd d → ℝ≥0∞)
      (hG : Measurable[fieldSigma0 h J] G) (q : ℕ → Rd d) :
      Measurable[fieldSigma0 h J] (fun ω (p : ℕ × ℕ) => G ω (q p.1) (q p.2)) := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun p => ?_
    exact (measurable_pi_apply (q p.2)).comp
      ((measurable_pi_apply (q p.1)).comp hG)
  have hFm : Measurable[fieldSigma0 h J] F := by
    exact ((hcoord FAJ hFAJm qJ).prodMk (hcoord FBJ hFBJm qJ)).prodMk
      ((hcoord FAO hFAOm qO).prodMk (hcoord FBO hFBOm qO))
  have hLenA := hA.length P h hh.isLGFPlusCont
  have hLenB := hB.length P h hh.isLGFPlusCont
  have hFR : ∀ᵐ ω ∂P, F ω = R (h ω) := by
    filter_upwards [hFAJae, hFBJae, hFAOae, hFBOae, hLenA, hLenB]
      with ω h₁ h₂ h₃ h₄ hlA hlB
    apply Prod.ext
    · apply Prod.ext <;> funext p
      · exact (h₁ _ _).trans (congrArg _ ((A (h ω)).internal_eq_chainInf hlA J.isOpen _ _))
      · exact (h₂ _ _).trans (congrArg _ ((B (h ω)).internal_eq_chainInf hlB J.isOpen _ _))
    · apply Prod.ext <;> funext p
      · exact (h₃ _ _).trans (congrArg _ ((A (h ω)).internal_eq_chainInf hlA O.isOpen _ _))
      · exact (h₄ _ _).trans (congrArg _ ((B (h ω)).internal_eq_chainInf hlB O.isOpen _ _))
  have hLenLaw : ∀ᵐ g ∂(P.map h), (A g).IsLength ∧ (B g).IsLength :=
    (hA.length (P.map h) id hh.map_id.isLGFPlusCont).and
      (hB.length (P.map h) id hh.map_id.isLGFPlusCont)
  have hbad : (P.map h) {g : DistRd d | ¬((A g).IsLength ∧ (B g).IsLength)} = 0 :=
    ae_iff.mp hLenLaw
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  let W : Set (DistRd d) := Nᶜ
  have hWm : MeasurableSet W := hNm.compl
  have hWlen : ∀ g ∈ W, (A g).IsLength ∧ (B g).IsLength := by
    intro g hg
    by_contra hc
    exact hg (hsub hc)
  have hWh : ∀ᵐ ω ∂P, h ω ∈ W := by
    have hwLaw : ∀ᵐ g ∂(P.map h), g ∈ W := by
      rw [ae_iff]
      simpa [W] using hN0
    exact ae_of_ae_map hh.measurable.aemeasurable hwLaw
  have hRhsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he h₁
    obtain ⟨hA₁, hB₁⟩ := hWlen g₁ hg₁
    obtain ⟨hA₂, hB₂⟩ := hWlen g₂ hg₂
    apply hsat g₁ g₂ hA₁ hB₁ hA₂ hB₂
    · apply normInt_eq_of_dense hA₁ hA₂ ξ Q r z J.isOpen hqJ hqJd
      intro i j
      rw [normInt, (A g₁).internal_eq_chainInf hA₁ J.isOpen,
        normInt, (A g₂).internal_eq_chainInf hA₂ J.isOpen]
      exact congrFun (congrArg (fun x : ShellCode => x.1.1) he) (i, j)
    · apply normInt_eq_of_dense hB₁ hB₂ ξ Q r z J.isOpen hqJ hqJd
      intro i j
      rw [normInt, (B g₁).internal_eq_chainInf hB₁ J.isOpen,
        normInt, (B g₂).internal_eq_chainInf hB₂ J.isOpen]
      exact congrFun (congrArg (fun x : ShellCode => x.1.2) he) (i, j)
    · apply normInt_eq_of_dense hA₁ hA₂ ξ Q r z O.isOpen hqO hqOd
      intro i j
      rw [normInt, (A g₁).internal_eq_chainInf hA₁ O.isOpen,
        normInt, (A g₂).internal_eq_chainInf hA₂ O.isOpen]
      exact congrFun (congrArg (fun x : ShellCode => x.2.1) he) (i, j)
    · apply normInt_eq_of_dense hB₁ hB₂ ξ Q r z O.isOpen hqO hqOd
      intro i j
      rw [normInt, (B g₁).internal_eq_chainInf hB₁ O.isOpen,
        normInt, (B g₂).internal_eq_chainInf hB₂ O.isOpen]
      exact congrFun (congrArg (fun x : ShellCode => x.2.2) he) (i, j)
    · exact h₁
  exact LocalEvent.aeEventIn_of_saturated hh.measurable hRm hFm hFR hWm hE hWh hRhsat

end HigherDimLQGMetric
