import HigherDimLQGMetric.Locality.MarkedRepTrunc
import HigherDimLQGMetric.Locality.CoupledWeylTight
import HigherDimLQGMetric.Locality.TightLawTransfer
import HigherDimLQGMetric.Field.Measurable
import HigherDimLQGMetric.Locality.CoupledConvergentTight

/-! One marked coupling supplies a common subsequence on which every
connected-domain truncated internal coordinate has tight laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_marked_stage_internal_tight
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
    (hΨsupp : ∀ x z, z ∉ K → (Ψ x).2 z = 0) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      IsTightMeasureSet {ν : Measure
        (((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) × C(Rd d × Rd d, ℝ)) |
          ∃ n, ν = P.map (fun ω =>
            ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
              lfppSeq κ ξ εs (h ω) (ns n)))} ∧
      ∀ {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U),
        IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
          ∃ n, ν = P.map (fun ω => internalC
            (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n))
              (addConst (h ω) (-sphereAvg (h ω) ρ z₀)))
            (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n))
              (addConst (h ω) (-sphereAvg (h ω) ρ z₀))) hU hUc)} ∧
        IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
          ∃ n, ν = P.map (fun ω => internalC
            (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n))
              (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)))
            (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n))
              (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω))) hU hUc)} := by
  obtain ⟨E, mE, hsb, Q, hQ, Z, Zlim, hZm, hZlimm,
    hZlaw, hZlimlaw, hZc, hZgood⟩ :=
    l7a_exists_skorokhod_marks hL6a hd ξ κ hκ hB2 εs hεs hεt
      P h Dh hh hDh hstable Ψ hΨ
  letI : MeasurableSpace E := mE
  letI : StandardBorelSpace E := hsb
  letI : IsProbabilityMeasure Q := hQ
  obtain ⟨ns, hns, hballs₁, hballs₂⟩ :=
    l7a_ae_marked_rep_two_trunc_subseq hd κ hκ ξ hL2c εs hεs hεt
      P h Dh hh hDh Ψ hΨ K hK hΨsupp Q Z Zlim
      hZm hZlimm hZlaw hZlimlaw hZc hZgood
  let Xn : ℕ → E → DistRd d := fun n e =>
    pairJInv ⊤ (Z (ns n) e).1.1
  let cn : ℕ → E → ℝ := fun n e => (Z (ns n) e).1.2.1
  let Fn : ℕ → E → C(Rd d, ℝ) := fun n e => (Z (ns n) e).1.2.2
  let g₁ : ℕ → E → DistRd d := fun n e => addConst (Xn n e) (-cn n e)
  let g₂ : ℕ → E → DistRd d := fun n e => g₁ n e - ofCont (Fn n e)
  let D : E → ContMetric d := fun e => l7a_metricLift (Zlim e).2
  let c : E → ℝ := fun e => (Zlim e).1.2.1
  let F' : E → C(Rd d, ℝ) := fun e => (Zlim e).1.2.2
  let f₁ : E → C(Rd d, ℝ) := fun e => ContinuousMap.const _ (-c e)
  let f₂ : E → C(Rd d, ℝ) := fun e => f₁ e - F' e
  have hXn (n : ℕ) : Measurable (Xn n) :=
    (measurable_pairJInv ⊤).comp
      ((measurable_fst.comp measurable_fst).comp (hZm (ns n)))
  have hcn (n : ℕ) : Measurable (cn n) :=
    ((measurable_fst.comp measurable_snd).comp measurable_fst).comp (hZm (ns n))
  have hFn (n : ℕ) : Measurable (Fn n) :=
    ((measurable_snd.comp measurable_snd).comp measurable_fst).comp (hZm (ns n))
  have hg₁ (n : ℕ) : Measurable (g₁ n) :=
    measurable_addConst.comp ((hXn n).prodMk (hcn n).neg)
  have hg₂ (n : ℕ) : Measurable (g₂ n) :=
    (hg₁ n).sub (measurable_ofCont.comp (hFn n))
  have hD : ∀ᵐ e ∂Q, (D e).IsLength := by
    filter_upwards [hZgood] with e he
    exact l7a_metricLift_isLength he.1
  have hTQ₁ {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
      IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
        ∃ n, ν = Q.map (fun e => internalC
          (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n)) (g₁ n e))
          (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n)) (g₁ n e))
          hU hUc)} :=
    l7a_coupled_weyl_trunc_internal_tight hd κ hκ ξ
      (fun n => εs (ns n)) (fun n => hεs (ns n)) Q g₁ hg₁
      D f₁ hD hballs₁ hU hUc
  have hTQ₂ {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
      IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
        ∃ n, ν = Q.map (fun e => internalC
          (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n)) (g₂ n e))
          (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n)) (g₂ n e))
          hU hUc)} :=
    l7a_coupled_weyl_trunc_internal_tight hd κ hκ ξ
      (fun n => εs (ns n)) (fun n => hεs (ns n)) Q g₂ hg₂
      D f₂ hD hballs₂ hU hUc
  letI : PolishSpace C(Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  have hTQbase : IsTightMeasureSet {ν : Measure
      (((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) × C(Rd d × Rd d, ℝ)) |
        ∃ n, ν = Q.map (Z (ns n))} :=
    l7a_tight_of_ae_tendsto Q (fun n => Z (ns n)) Zlim
      (fun n => hZm (ns n))
      (Filter.Eventually.of_forall fun e => (hZc e).comp hns.tendsto_atTop)
  have hTPbase : IsTightMeasureSet {ν : Measure
      (((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) × C(Rd d × Rd d, ℝ)) |
        ∃ n, ν = P.map (fun ω =>
          ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
            lfppSeq κ ξ εs (h ω) (ns n)))} := by
    apply l7a_tight_of_equal_laws P Q
      (fun n ω => ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
        lfppSeq κ ξ εs (h ω) (ns n)))
      (fun n => Z (ns n))
    · intro n
      exact (hZlaw (ns n)).symm
    · exact hTQbase
  refine ⟨ns, hns, hTPbase, ?_⟩
  intro U hU hUc
  let M := ((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) × C(Rd d × Rd d, ℝ)
  let L₁ : M → DistRd d := fun q =>
    addConst (pairJInv ⊤ q.1.1) (-q.1.2.1)
  let L₂ : M → DistRd d := fun q => L₁ q - ofCont q.1.2.2
  have hL₁ : Measurable L₁ :=
    measurable_addConst.comp
      (((measurable_pairJInv ⊤).comp
        (measurable_fst.comp measurable_fst)).prodMk
        (((measurable_fst.comp measurable_snd).comp measurable_fst).neg))
  have hL₂ : Measurable L₂ := hL₁.sub
    (measurable_ofCont.comp
      ((measurable_snd.comp measurable_snd).comp measurable_fst))
  let Uo : TopologicalSpace.Opens (Rd d) := ⟨U, hU⟩
  let I₁ (n : ℕ) : M → C(U × U, ℝ) := fun q => internalC
    (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n)) (L₁ q))
    (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n)) (L₁ q))
    hU hUc
  let I₂ (n : ℕ) : M → C(U × U, ℝ) := fun q => internalC
    (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n)) (L₂ q))
    (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n)) (L₂ q))
    hU hUc
  have hI₁ (n : ℕ) : Measurable (I₁ n) :=
    (l7a_measurable_truncScaledInternal hd κ hκ ξ (hεs (ns n)) Uo hUc).comp hL₁
  have hI₂ (n : ℕ) : Measurable (I₂ n) :=
    (l7a_measurable_truncScaledInternal hd κ hκ ξ (hεs (ns n)) Uo hUc).comp hL₂
  let X (n : ℕ) : Ω → M := fun ω =>
    ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))), lfppSeq κ ξ εs (h ω) n)
  have hXm (n : ℕ) : AEMeasurable (X n) P :=
    ((((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
      (hΨ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).aemeasurable).prodMk
      (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
        hh.1.isLGFPlusBddCont)
  have heq₁ (n : ℕ) : P.map (I₁ n ∘ X (ns n)) =
      Q.map (I₁ n ∘ Z (ns n)) := by
    rw [← AEMeasurable.map_map_of_aemeasurable (hI₁ n).aemeasurable (hXm (ns n)),
      ← Measure.map_map (hI₁ n) (hZm (ns n)), ← hZlaw (ns n)]
  have heq₂ (n : ℕ) : P.map (I₂ n ∘ X (ns n)) =
      Q.map (I₂ n ∘ Z (ns n)) := by
    rw [← AEMeasurable.map_map_of_aemeasurable (hI₂ n).aemeasurable (hXm (ns n)),
      ← Measure.map_map (hI₂ n) (hZm (ns n)), ← hZlaw (ns n)]
  have hL₁X (ω : Ω) (n : ℕ) : L₁ (X n ω) =
      addConst (h ω) (-sphereAvg (h ω) ρ z₀) := by
    simp only [L₁, X, hΨeq ω, pairJInv_pairJ]
  have hL₂X (ω : Ω) (n : ℕ) : L₂ (X n ω) =
      addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω) := by
    rw [show L₂ (X n ω) = L₁ (X n ω) - ofCont (Ψ (pairJ ⊤ (h ω))).2 from rfl,
      hL₁X ω n, hΨeq ω]
  have hL₁Z (e : E) (n : ℕ) : L₁ (Z (ns n) e) = g₁ n e := rfl
  have hL₂Z (e : E) (n : ℕ) : L₂ (Z (ns n) e) = g₂ n e := rfl
  constructor
  · apply l7a_tight_of_equal_laws P Q
      (fun n ω => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n))
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀)))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n))
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀))) hU hUc)
      (fun n e => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n)) (g₁ n e))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n)) (g₁ n e)) hU hUc)
    · intro n
      simpa only [Function.comp_def, I₁, hL₁X, hL₁Z] using heq₁ n
    · exact hTQ₁ hU hUc
  · apply l7a_tight_of_equal_laws P Q
      (fun n ω => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n))
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n))
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω))) hU hUc)
      (fun n e => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (ns n)) (g₂ n e))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (ns n)) (g₂ n e)) hU hUc)
    · intro n
      simpa only [Function.comp_def, I₂, hL₂X, hL₂Z] using heq₂ n
    · exact hTQ₂ hU hUc

end HigherDimLQGMetric
