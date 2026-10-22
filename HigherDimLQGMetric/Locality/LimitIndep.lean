import HigherDimLQGMetric.Locality.FiniteTransfer
import HigherDimLQGMetric.Locality.StageFiniteVersion

/-! Finite-stage independence survives the marked joint Skorokhod coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_second_limit_indep
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (V : TopologicalSpace.Opens (Rd d)) (z₀ : Rd d) (ρ : ℝ)
    (F : Ω → C(Rd d, ℝ))
    (Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ)) (hΨ : Measurable Ψ)
    (hΨeq : ∀ ω, Ψ (pairJ ⊤ (h ω)) =
      (sphereAvg (h ω) ρ z₀, F ω))
    (R : Ω → DistOn (extOpen V))
    (Φ : (CoordJ → ℝ) → C(Rd d, ℝ) × DistOn (extOpen V))
    (hΦ : Measurable Φ)
    (hΦeq : (fun ω => (F ω, R ω)) = Φ ∘
      (fun ω => pairJ ⊤ (h ω)))
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (hstage : ∀ n, Indep
      (fieldSigmaRd (fun ω => addConst (h ω)
          (-sphereAvg (h ω) ρ z₀)) V ⊔
        MeasurableSpace.comap
          (fun ω => l7a_stageArray hd κ hκ ξ (hεs n) S W hWc
            (addConst (h ω) (-sphereAvg (h ω) ρ z₀))) inferInstance)
      (MeasurableSpace.comap R inferInstance ⊔
        MeasurableSpace.comap
          (fun ω => l7a_stageArray hd κ hκ ξ (hεs n) T W' hW'c
            (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)))
          inferInstance) P)
    (ns : ℕ → ℕ)
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    [IsProbabilityMeasure Q]
    (Z : ℕ → E → L7aJointState S T W W')
    (Zlim : E → L7aJointState S T W W')
    (hZm : ∀ n, Measurable (Z n)) (hZlimm : Measurable Zlim)
    (hZlaw : ∀ n, Q.map (Z n) = P.map (fun ω =>
      (((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
        lfppSeq κ ξ εs (h ω) (ns n)),
       (l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀)),
        l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω))))))
    (hZc : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) :
    Indep
      (fieldSigmaRd (fun e => l7a_markedField₁ (Zlim e).1) V ⊔
        MeasurableSpace.comap (fun e => (Zlim e).2.1) inferInstance)
      (MeasurableSpace.comap
        (fun e => (Φ (Zlim e).1.1.1).2) inferInstance ⊔
        MeasurableSpace.comap (fun e => (Zlim e).2.2) inferInstance) Q := by
  letI : PolishSpace C(Rd d, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI (i : S) : LocallyCompactSpace (W i.1 : Set (Rd d)) :=
    (W i.1).isOpen.locallyCompactSpace
  letI (j : T) : LocallyCompactSpace (W' j.1 : Set (Rd d)) :=
    (W' j.1).isOpen.locallyCompactSpace
  letI : PolishSpace (L7aFiniteArray S W) :=
    l7a_polish_finite_internal_array S W
  letI : PolishSpace (L7aFiniteArray T W') :=
    l7a_polish_finite_internal_array T W'
  let Mark : Type := (CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))
  let X : Ω → Mark := fun ω =>
    (pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω)))
  let A : ℕ → Ω → L7aFiniteArray S W := fun n ω =>
    l7a_stageArray hd κ hκ ξ (hεs n) S W hWc
      (addConst (h ω) (-sphereAvg (h ω) ρ z₀))
  let B : ℕ → Ω → L7aFiniteArray T W' := fun n ω =>
    l7a_stageArray hd κ hκ ξ (hεs n) T W' hW'c
      (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω))
  let Cₙ : ℕ → Ω → C(Rd d × Rd d, ℝ) :=
    fun n ω => lfppSeq κ ξ εs (h ω) n
  have hX : Measurable X :=
    (((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
      (hΨ.comp ((measurable_pairJ ⊤).comp hh.1.measurable)))
  have hF : Measurable F := by
    have heq : F = fun ω => (Ψ (pairJ ⊤ (h ω))).2 := by
      funext ω
      exact (congrArg Prod.snd (hΨeq ω)).symm
    rw [heq]
    exact measurable_snd.comp (hΨ.comp
      ((measurable_pairJ ⊤).comp hh.1.measurable))
  have hg : Measurable (fun ω => addConst (h ω)
      (-sphereAvg (h ω) ρ z₀)) :=
    measurable_addConst.comp
      (hh.1.measurable.prodMk
        (((measurable_sphereAvg_left ρ z₀).comp hh.1.measurable).neg))
  have hA (n : ℕ) : Measurable (A n) :=
    (l7a_measurable_stageArray hd κ hκ ξ (hεs n) S W hWc).comp hg
  have hB (n : ℕ) : Measurable (B n) :=
    (l7a_measurable_stageArray hd κ hκ ξ (hεs n) T W' hW'c).comp
      (hg.sub (measurable_ofCont.comp hF))
  have hC (n : ℕ) : AEMeasurable (Cₙ n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  let mMark : MeasurableSpace Mark := inferInstance
  let Gmark : MeasurableSpace Mark :=
    MeasurableSpace.comap (fun q : Mark =>
      restrictTo V (addConst (pairJInv ⊤ q.1) (-q.2.1))) inferInstance
  let Hmark : MeasurableSpace Mark :=
    MeasurableSpace.comap (fun q : Mark => (Φ q.1).2) inferInstance
  letI : MeasurableSpace Mark := mMark
  have hGmark : Gmark ≤ (inferInstance : MeasurableSpace Mark) :=
    (show Measurable (fun q : Mark =>
      restrictTo V (addConst (pairJInv ⊤ q.1) (-q.2.1))) from
      (measurable_restrictTo V).comp
      (measurable_addConst.comp
        (((measurable_pairJInv ⊤).comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd).neg))).comap_le
  have hHmark : Hmark ≤ (inferInstance : MeasurableSpace Mark) :=
    (measurable_snd.comp (hΦ.comp measurable_fst)).comap_le
  have hGpull : Gmark.comap X = fieldSigmaRd
      (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V := by
    simp only [Gmark, fieldSigmaRd, MeasurableSpace.comap_comp]
    apply congrArg (fun f => MeasurableSpace.comap f inferInstance)
    funext ω
    change restrictTo V (addConst (pairJInv ⊤ (pairJ ⊤ (h ω)))
      (-(Ψ (pairJ ⊤ (h ω))).1)) =
      restrictTo V (addConst (h ω) (-sphereAvg (h ω) ρ z₀))
    rw [pairJInv_pairJ, congrArg Prod.fst (hΨeq ω)]
  have hHpull : Hmark.comap X = MeasurableSpace.comap R inferInstance := by
    simp only [Hmark, MeasurableSpace.comap_comp]
    apply congrArg (fun f => MeasurableSpace.comap f inferInstance)
    funext ω
    exact (congrArg Prod.snd (congrFun hΦeq ω)).symm
  have hInd (n : ℕ) : Indep
      (Gmark.comap X ⊔ MeasurableSpace.comap (A n) inferInstance)
      (Hmark.comap X ⊔ MeasurableSpace.comap (B n) inferInstance) P := by
    simpa only [hGpull, hHpull, A, B] using hstage n
  have hlimit := l7a_indep_of_joint_skorokhod P Q
    X A B Cₙ hX hA hB hC ns Z Zlim hZm hZlimm hZlaw hZc
    ⟨Gmark, hGmark⟩ ⟨Hmark, hHmark⟩ hInd
  simpa only [Gmark, Hmark, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp, Function.comp_def, fieldSigmaRd,
    l7a_markedField₁] using hlimit

end HigherDimLQGMetric
