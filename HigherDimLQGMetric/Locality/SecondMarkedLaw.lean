import HigherDimLQGMetric.Locality.SecondBaseLaw
import HigherDimLQGMetric.Locality.StableAdjoinAE
import HigherDimLQGMetric.Locality.StableGood

/-! The full metric coordinate in the second coupling has the prescribed
stable law and is almost surely a proper length metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_second_marked_limit_law
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
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
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (ns : ℕ → ℕ) (hns : StrictMono ns)
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
    (∀ n, Q.map (fun e => (Z n e).1) = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
        lfppSeq κ ξ εs (h ω) (ns n)))) ∧
    Q.map (fun e => (Zlim e).1) = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))), (Dh ω).1)) ∧
    (∀ᵐ e ∂Q, IsContLengthFn (Zlim e).1.2 ∧
      IsProperFn (Zlim e).1.2) := by
  letI : PolishSpace C(Rd d, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let X : Ω → (CoordJ → ℝ) × (ℝ × C(Rd d, ℝ)) := fun ω =>
    (pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω)))
  let Y : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n ω =>
    lfppSeq κ ξ εs (h ω) n
  let Ylim : Ω → C(Rd d × Rd d, ℝ) := fun ω => (Dh ω).1
  let A : ℕ → Ω → L7aFiniteArray S W × L7aFiniteArray T W' :=
    fun n ω =>
      (l7a_stageArray hd κ hκ ξ (hεs n) S W hWc
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀)),
       l7a_stageArray hd κ hκ ξ (hεs n) T W' hW'c
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)))
  have hX : Measurable X :=
    ((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
      (hΨ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))
  have hY (n : ℕ) : AEMeasurable (Y n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hF : Measurable F := by
    have heq : F = fun ω => (Ψ (pairJ ⊤ (h ω))).2 := by
      funext ω
      exact (congrArg Prod.snd (hΨeq ω)).symm
    rw [heq]
    exact measurable_snd.comp (hΨ.comp
      ((measurable_pairJ ⊤).comp hh.1.measurable))
  have hg₁ : Measurable (fun ω =>
      addConst (h ω) (-sphereAvg (h ω) ρ z₀)) :=
    measurable_addConst.comp
      (hh.1.measurable.prodMk
        (((measurable_sphereAvg_left ρ z₀).comp hh.1.measurable).neg))
  have hg₂ : Measurable (fun ω =>
      addConst (h ω) (-sphereAvg (h ω) ρ z₀) - ofCont (F ω)) :=
    hg₁.sub (measurable_ofCont.comp hF)
  have hA (n : ℕ) : AEMeasurable (A n) P :=
    ((l7a_measurable_stageArray hd κ hκ ξ (hεs n) S W hWc).comp hg₁).prodMk
      ((l7a_measurable_stageArray hd κ hκ ξ (hεs n) T W' hW'c).comp hg₂)
      |>.aemeasurable
  have hstablelaw := l7a_stable_adjoin_field_ae P h hh.1.measurable
    Y Ylim hY (measurable_subtype_coe.comp hDh) hstable
    (fun x => (x, Ψ x)) (measurable_id.prodMk hΨ)
  have hbase := l7a_second_base_limit_law P Q X Y Ylim A hX hY hA
    hstablelaw ns hns Z Zlim hZm hZlimm hZlaw hZc
  have hstage (n : ℕ) : Q.map (fun e => (Z n e).1) =
      P.map (fun ω => (X ω, Y (ns n) ω)) := by
    calc
      Q.map (fun e => (Z n e).1) = (Q.map (Z n)).map Prod.fst :=
        (Measure.map_map measurable_fst (hZm n)).symm
      _ = (P.map (fun ω => ((X ω, Y (ns n) ω), A (ns n) ω))).map Prod.fst := by
        rw [hZlaw n]
      _ = P.map (fun ω => (X ω, Y (ns n) ω)) := by
        simpa only [Function.comp_def] using
          (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
            ((hX.aemeasurable.prodMk (hY (ns n))).prodMk (hA (ns n))))
  have hgoodlaw := l7a_stable_limit_law_good hL6a ξ κ hB2
    εs hεs hεt P h Dh hh hDh hstable
  have hYlaw : Q.map (fun e => (Zlim e).1.2) = P.map Ylim := by
    calc
      Q.map (fun e => (Zlim e).1.2) =
          (Q.map (fun e => (Zlim e).1)).map Prod.snd :=
        (Measure.map_map measurable_snd (measurable_fst.comp hZlimm)).symm
      _ = (P.map (fun ω => (X ω, Ylim ω))).map Prod.snd := by
        rw [hbase]
      _ = P.map Ylim := by
        simpa only [Function.comp_def] using
          (Measure.map_map measurable_snd
            (hX.prodMk (measurable_subtype_coe.comp hDh)))
  have hgood : ∀ᵐ e ∂Q, IsContLengthFn (Zlim e).1.2 ∧
      IsProperFn (Zlim e).1.2 := by
    have ht : ∀ᵐ D ∂Q.map (fun e => (Zlim e).1.2),
        IsContLengthFn D ∧ IsProperFn D := by
      rw [hYlaw]
      exact hgoodlaw
    exact ae_of_ae_map ((measurable_snd.comp measurable_fst).comp hZlimm).aemeasurable ht
  exact ⟨hstage, hbase, hgood⟩

end HigherDimLQGMetric
