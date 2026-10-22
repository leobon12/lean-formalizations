import HigherDimLQGMetric.Locality.SkorokhodMarks

/-! Exact field and LFPP graphs in a marked Skorokhod representation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_marked_stage_graph {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {M : Type} [MeasurableSpace M] [MeasurableEq M]
    (Φ : (CoordJ → ℝ) → M) (hΦ : Measurable Φ)
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    (Z : ℕ → E → ((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ))
    (hZm : ∀ n, Measurable (Z n))
    (hZlaw : ∀ n, Q.map (Z n) = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
        lfppSeq κ ξ εs (h ω) n))) :
    (∀ n, Q.map (fun e => pairJInv ⊤ (Z n e).1.1) = P.map h) ∧
    (∀ n, ∀ᵐ e ∂Q, (Z n e).1.2 = Φ (Z n e).1.1) ∧
    (∀ n, ∀ᵐ e ∂Q, (Z n e).2 =
      lfppSeq κ ξ εs (pairJInv ⊤ (Z n e).1.1) n) := by
  have hπ : Measurable
      (fun q : ((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ) =>
        (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hpairlaw (n : ℕ) :
      Q.map (fun e => ((Z n e).1.1, (Z n e).2)) =
        P.map (fun ω => (pairJ ⊤ (h ω), lfppSeq κ ξ εs (h ω) n)) := by
    calc
      Q.map (fun e => ((Z n e).1.1, (Z n e).2)) =
          (Q.map (Z n)).map (fun q => (q.1.1, q.2)) :=
        (Measure.map_map hπ (hZm n)).symm
      _ = (P.map (fun ω =>
          ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
            lfppSeq κ ξ εs (h ω) n))).map (fun q => (q.1.1, q.2)) := by
        rw [hZlaw n]
      _ = P.map (fun ω => (pairJ ⊤ (h ω), lfppSeq κ ξ εs (h ω) n)) := by
        have hm : AEMeasurable (fun ω =>
            ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
              lfppSeq κ ξ εs (h ω) n)) P := by
          exact ((((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
            (hΦ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).aemeasurable).prodMk
            (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
              hh.1.isLGFPlusBddCont)
        simpa only [Function.comp_def] using
          (AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable hm)
  have hfield (n : ℕ) :
      Q.map (fun e => pairJInv ⊤ (Z n e).1.1) = P.map h := by
    have hInv : Measurable (fun q : ((CoordJ → ℝ) × M) ×
        C(Rd d × Rd d, ℝ) => pairJInv (d := d) ⊤ q.1.1) :=
      (measurable_pairJInv (d := d) ⊤).comp
        (measurable_fst.comp measurable_fst)
    calc
      Q.map (fun e => pairJInv ⊤ (Z n e).1.1) =
          (Q.map (Z n)).map (fun q => pairJInv ⊤ q.1.1) :=
        (Measure.map_map hInv (hZm n)).symm
      _ = (P.map (fun ω =>
          ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
            lfppSeq κ ξ εs (h ω) n))).map
              (fun q => pairJInv ⊤ q.1.1) := by rw [hZlaw n]
      _ = P.map h := by
        have hm : AEMeasurable (fun ω =>
            ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
              lfppSeq κ ξ εs (h ω) n)) P :=
          (((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
            (hΦ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).aemeasurable.prodMk
            (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
              hh.1.isLGFPlusBddCont)
        simpa only [Function.comp_def, pairJInv_pairJ] using
          (AEMeasurable.map_map_of_aemeasurable hInv.aemeasurable hm)
  have hmark (n : ℕ) : ∀ᵐ e ∂Q, (Z n e).1.2 = Φ (Z n e).1.1 := by
    let A : Set (((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ)) :=
      {q | q.1.2 = Φ q.1.1}
    have hA : MeasurableSet A :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (hΦ.comp (measurable_fst.comp measurable_fst))
    have hμ : ∀ᵐ q ∂Q.map (Z n), q ∈ A := by
      rw [hZlaw n]
      have hm : AEMeasurable (fun ω =>
          ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
            lfppSeq κ ξ εs (h ω) n)) P :=
        ((((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
          (hΦ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).aemeasurable).prodMk
          (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
            hh.1.isLGFPlusBddCont)
      exact (ae_map_iff hm hA).2 (Filter.Eventually.of_forall fun ω => rfl)
    exact ae_of_ae_map (hZm n).aemeasurable hμ
  have hmetric (n : ℕ) : ∀ᵐ e ∂Q, (Z n e).2 =
      lfppSeq κ ξ εs (pairJInv ⊤ (Z n e).1.1) n := by
    exact l7a_ae_graph_of_joint_law hd κ hκ ξ εs hεs P h hh n Q
      (fun e => ((Z n e).1.1, (Z n e).2))
      (hπ.comp (hZm n)) (hpairlaw n)
  exact ⟨hfield, hmark, hmetric⟩

theorem l7a_marked_limit_graph {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistRd d) (hh : Measurable h)
    (D : Ω → ContMetric d) (hD : Measurable D)
    {M : Type} [MeasurableSpace M] [MeasurableEq M]
    (Φ : (CoordJ → ℝ) → M) (hΦ : Measurable Φ)
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    (Zlim : E → ((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ))
    (hZm : Measurable Zlim)
    (hZlaw : Q.map Zlim = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))), (D ω).1))) :
    Q.map (fun e => pairJInv ⊤ (Zlim e).1.1) = P.map h ∧
    (∀ᵐ e ∂Q, (Zlim e).1.2 = Φ (Zlim e).1.1) := by
  have hι : Measurable (fun q : ((CoordJ → ℝ) × M) ×
      C(Rd d × Rd d, ℝ) => pairJInv (d := d) ⊤ q.1.1) :=
    (measurable_pairJInv (d := d) ⊤).comp
      (measurable_fst.comp measurable_fst)
  have hFm : Measurable (fun ω =>
      ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))), (D ω).1)) :=
    (((measurable_pairJ ⊤).comp hh).prodMk
      (hΦ.comp ((measurable_pairJ ⊤).comp hh))).prodMk
      (measurable_subtype_coe.comp hD)
  have hfield : Q.map (fun e => pairJInv ⊤ (Zlim e).1.1) = P.map h := by
    calc
      Q.map (fun e => pairJInv ⊤ (Zlim e).1.1) =
          (Q.map Zlim).map (fun q => pairJInv ⊤ q.1.1) :=
        (Measure.map_map hι hZm).symm
      _ = (P.map (fun ω =>
          ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))), (D ω).1))).map
            (fun q => pairJInv ⊤ q.1.1) := by rw [hZlaw]
      _ = P.map h := by
        simpa only [Function.comp_def, pairJInv_pairJ] using
          (Measure.map_map hι hFm)
  have hmark : ∀ᵐ e ∂Q, (Zlim e).1.2 = Φ (Zlim e).1.1 := by
    let A : Set (((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ)) :=
      {q | q.1.2 = Φ q.1.1}
    have hA : MeasurableSet A :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (hΦ.comp (measurable_fst.comp measurable_fst))
    have hμ : ∀ᵐ q ∂Q.map Zlim, q ∈ A := by
      rw [hZlaw]
      exact (ae_map_iff hFm.aemeasurable hA).2
        (Filter.Eventually.of_forall fun ω => rfl)
    exact ae_of_ae_map hZm.aemeasurable hμ
  exact ⟨hfield, hmark⟩

end HigherDimLQGMetric
