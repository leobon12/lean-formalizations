import HigherDimLQGMetric.Locality.MarkedStageTight
import HigherDimLQGMetric.Locality.FiniteJointTight
import HigherDimLQGMetric.Locality.StageArrays

/-! The second coupling contains the marked field, full LFPP metric, and
finite inside/outside internal arrays. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

abbrev L7aMarkedBase (d : ℕ) :=
  ((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) × C(Rd d × Rd d, ℝ)

abbrev L7aJointState {d : ℕ} {ι κ' : Type}
    (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d)) :=
  L7aMarkedBase d × (L7aFiniteArray S W × L7aFiniteArray T W')

theorem l7a_exists_second_coupling
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ) (hL2c : L2c_trunc)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ q : ℝ, DGZ.DGZHyp d κ ξ q ∧
      DGZ.RealEpsAdapterShape d κ ξ q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    (ρ : ℝ) (z₀ : Rd d) (F : Ω → C(Rd d, ℝ))
    (Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ)) (hΨ : Measurable Ψ)
    (hΨeq : ∀ ω, Ψ (pairJ ⊤ (h ω)) =
      (sphereAvg (h ω) ρ z₀, F ω))
    (K : Set (Rd d)) (hK : IsCompact K)
    (hΨsupp : ∀ x z, z ∉ K → (Ψ x).2 z = 0)
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ (E : Type) (_ : MeasurableSpace E) (_ : StandardBorelSpace E)
        (Q : Measure E), IsProbabilityMeasure Q ∧
      ∃ (Z : ℕ → E → L7aJointState S T W W')
        (Zlim : E → L7aJointState S T W W'),
        (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
        (∀ n, Q.map (Z n) = P.map (fun ω =>
          (((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
            lfppSeq κ ξ εs (h ω) (ns n)),
           (l7a_stageArray hd κ hκ ξ (hεs (ns n)) S W hWc
              (addConst (h ω) (-sphereAvg (h ω) ρ z₀)),
            l7a_stageArray hd κ hκ ξ (hεs (ns n)) T W' hW'c
              (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)))))) ∧
        (∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) := by
  obtain ⟨ns₀, hns₀, hXT, hYT⟩ :=
    l7a_marked_stage_internal_tight hL6a hL2c hd ξ κ hκ hB2
      εs hεs hεt P h Dh hh hDh hstable ρ z₀ F Ψ hΨ hΨeq K hK hΨsupp
  let g₁ : Ω → DistRd d := fun ω =>
    addConst (h ω) (-sphereAvg (h ω) ρ z₀)
  let g₂ : Ω → DistRd d := fun ω => g₁ ω - ofCont (F ω)
  have hg₁ : Measurable g₁ :=
    measurable_addConst.comp
      (hh.1.measurable.prodMk
        (((measurable_sphereAvg_left ρ z₀).comp hh.1.measurable).neg))
  have hF : Measurable F := by
    have hFe : F = fun ω => (Ψ (pairJ ⊤ (h ω))).2 := by
      funext ω
      exact (congrArg Prod.snd (hΨeq ω)).symm
    rw [hFe]
    exact measurable_snd.comp (hΨ.comp
      ((measurable_pairJ ⊤).comp hh.1.measurable))
  have hg₂ : Measurable g₂ := hg₁.sub (measurable_ofCont.comp hF)
  let X : ℕ → Ω → L7aMarkedBase d := fun n ω =>
    ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
      lfppSeq κ ξ εs (h ω) (ns₀ n))
  let A : ℕ → Ω → L7aFiniteArray S W := fun n ω =>
    l7a_stageArray hd κ hκ ξ (hεs (ns₀ n)) S W hWc (g₁ ω)
  let B : ℕ → Ω → L7aFiniteArray T W' := fun n ω =>
    l7a_stageArray hd κ hκ ξ (hεs (ns₀ n)) T W' hW'c (g₂ ω)
  have hXm (n : ℕ) : AEMeasurable (X n) P :=
    ((((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
      (hΨ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).aemeasurable).prodMk
      (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs (ns₀ n))
        P h hh.1.isLGFPlusBddCont)
  have hAm (n : ℕ) : Measurable (A n) :=
    (l7a_measurable_stageArray hd κ hκ ξ (hεs (ns₀ n)) S W hWc).comp hg₁
  have hBm (n : ℕ) : Measurable (B n) :=
    (l7a_measurable_stageArray hd κ hκ ξ (hεs (ns₀ n)) T W' hW'c).comp hg₂
  have hAT (i : S) : IsTightMeasureSet
      {ν : Measure C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ) |
        ∃ n, ν = P.map (fun ω => A n ω i)} := by
    exact (hYT (W i.1).isOpen (hWc i.1 i.2)).1
  have hBT (j : T) : IsTightMeasureSet
      {ν : Measure C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ) |
        ∃ n, ν = P.map (fun ω => B n ω j)} := by
    exact (hYT (W' j.1).isOpen (hW'c j.1 j.2)).2
  letI : PolishSpace C(Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  obtain ⟨ns₁, hns₁, μ, E, mE, hsb, Q, hQ, Z, Zlim,
    hZm, hZlimm, hZlaw, _, hZc⟩ :=
    l7a_exists_finite_internal_joint_skorokhod S T W W' P X A B
      (fun n => (hXm n))
      (fun n i => (measurable_pi_apply i).comp (hAm n) |>.aemeasurable)
      (fun n j => (measurable_pi_apply j).comp (hBm n) |>.aemeasurable)
      hXT hAT hBT
  let ns : ℕ → ℕ := ns₀ ∘ ns₁
  refine ⟨ns, hns₀.comp hns₁, E, mE, hsb, Q, hQ, Z, Zlim,
    hZm, hZlimm, ?_, hZc⟩
  intro n
  simpa only [ns, Function.comp_def, X, A, B, g₁, g₂]
    using hZlaw n

end HigherDimLQGMetric
