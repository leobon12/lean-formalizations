import HigherDimLQGMetric.Locality.GraphTransport

/-! The internal arrays in the second coupling retain their exact
finite-stage graph over the marked field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l7a_markedField₁ {d : ℕ} (q : L7aMarkedBase d) : DistRd d :=
  addConst (pairJInv ⊤ q.1.1) (-q.1.2.1)

def l7a_markedField₂ {d : ℕ} (q : L7aMarkedBase d) : DistRd d :=
  l7a_markedField₁ q - ofCont q.1.2.2

theorem l7a_measurable_markedField₁ {d : ℕ} :
    Measurable (l7a_markedField₁ (d := d)) :=
  measurable_addConst.comp
    (((measurable_pairJInv ⊤).comp
      (measurable_fst.comp measurable_fst)).prodMk
      (((measurable_fst.comp measurable_snd).comp measurable_fst).neg))

theorem l7a_measurable_markedField₂ {d : ℕ} :
    Measurable (l7a_markedField₂ (d := d)) :=
  l7a_measurable_markedField₁.sub
    (measurable_ofCont.comp
      ((measurable_snd.comp measurable_snd).comp measurable_fst))

theorem l7a_ae_second_stage_arrays
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (ρ : ℝ) (z₀ : Rd d) (F : Ω → C(Rd d, ℝ))
    (Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ)) (hΨ : Measurable Ψ)
    (hΨeq : ∀ ω, Ψ (pairJ ⊤ (h ω)) =
      (sphereAvg (h ω) ρ z₀, F ω))
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (ns : ℕ → ℕ)
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    (Z : ℕ → E → L7aJointState S T W W')
    (hZm : ∀ n, Measurable (Z n))
    (hZlaw : ∀ n, Q.map (Z n) = P.map (fun ω =>
      (((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
        lfppSeq κ ξ εs (h ω) (ns n)),
       (l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀)),
        l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)))))) :
    (∀ᵐ e ∂Q, ∀ n,
      (Z n e).2.1 =
        l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
          (l7a_markedField₁ (Z n e).1)) ∧
    (∀ᵐ e ∂Q, ∀ n,
      (Z n e).2.2 =
        l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
          (l7a_markedField₂ (Z n e).1)) := by
  letI (i : S) : LocallyCompactSpace (W i.1 : Set (Rd d)) :=
    (W i.1).isOpen.locallyCompactSpace
  letI (i : S) : PolishSpace
      C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI (j : T) : LocallyCompactSpace (W' j.1 : Set (Rd d)) :=
    (W' j.1).isOpen.locallyCompactSpace
  letI (j : T) : PolishSpace
      C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace (L7aFiniteArray S W) :=
    l7a_polish_finite_internal_array S W
  letI : PolishSpace (L7aFiniteArray T W') :=
    l7a_polish_finite_internal_array T W'
  have hF : Measurable F := by
    have heq : F = fun ω => (Ψ (pairJ ⊤ (h ω))).2 := by
      funext ω
      exact (congrArg Prod.snd (hΨeq ω)).symm
    rw [heq]
    exact measurable_snd.comp
      (hΨ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))
  have hg₁ : Measurable (fun ω =>
      addConst (h ω) (-sphereAvg (h ω) ρ z₀)) :=
    measurable_addConst.comp (hh.1.measurable.prodMk
      (((measurable_sphereAvg_left ρ z₀).comp hh.1.measurable).neg))
  have hg₂ : Measurable (fun ω =>
      addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)) :=
    hg₁.sub (measurable_ofCont.comp hF)
  let X : ℕ → Ω → L7aJointState S T W W' := fun n ω =>
    (((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
      lfppSeq κ ξ εs (h ω) (ns n)),
     (l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀)),
      l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω))))
  have hXm (n : ℕ) : AEMeasurable (X n) P :=
    (((((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
      (hΨ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).aemeasurable).prodMk
      (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs (ns n)) P h
        hh.1.isLGFPlusBddCont)).prodMk
      (((l7a_measurable_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc).comp hg₁).prodMk
        ((l7a_measurable_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c).comp hg₂)).aemeasurable
  have hL₁ (ω : Ω) (n : ℕ) :
      l7a_markedField₁ (X n ω).1 =
        addConst (h ω) (-sphereAvg (h ω) ρ z₀) := by
    simp only [l7a_markedField₁, X, hΨeq ω, pairJInv_pairJ]
  have hL₂ (ω : Ω) (n : ℕ) :
      l7a_markedField₂ (X n ω).1 =
        addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω) := by
    rw [show l7a_markedField₂ (X n ω).1 =
      l7a_markedField₁ (X n ω).1 - ofCont (Ψ (pairJ ⊤ (h ω))).2 from rfl,
      hL₁ ω n, hΨeq ω]
  have h₁ (n : ℕ) : ∀ᵐ e ∂Q,
      (Z n e).2.1 =
        l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
          (l7a_markedField₁ (Z n e).1) := by
    apply l7a_ae_graph_of_equal_law P Q (X n) (Z n)
      (hXm n) (hZm n) (hZlaw n)
      (fun q => q.2.1)
      (fun q => l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
        (l7a_markedField₁ q.1))
      (measurable_fst.comp measurable_snd)
      ((l7a_measurable_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc).comp
        (l7a_measurable_markedField₁.comp measurable_fst))
    intro ω
    exact congrArg (l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc)
      (hL₁ ω n).symm
  have h₂ (n : ℕ) : ∀ᵐ e ∂Q,
      (Z n e).2.2 =
        l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
          (l7a_markedField₂ (Z n e).1) := by
    apply l7a_ae_graph_of_equal_law P Q (X n) (Z n)
      (hXm n) (hZm n) (hZlaw n)
      (fun q => q.2.2)
      (fun q => l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
        (l7a_markedField₂ q.1))
      (measurable_snd.comp measurable_snd)
      ((l7a_measurable_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c).comp
        (l7a_measurable_markedField₂.comp measurable_fst))
    intro ω
    exact congrArg (l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c)
      (hL₂ ω n).symm
  exact ⟨ae_all_iff.mpr h₁, ae_all_iff.mpr h₂⟩

end HigherDimLQGMetric
