import HigherDimLQGMetric.Determ.L7e
import HigherDimLQGMetric.Limits.TranslateStable
import HigherDimLQGMetric.Bilip.UniformFamily

/-! Translation invariance of a centered and scaled normalized LFPP law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private def determCenterX {d : ℕ} (κ : Rd d → ℝ) (ξ : ℝ)
    (εs : ℕ → ℝ) (c : ℝ → ℝ) (r : ℝ) (z : Rd d)
    (g : DistRd d) (n : ℕ) : C(Rd d × Rd d, ℝ) :=
  ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z)) •
    (lfppSeq κ ξ εs g n).comp
      ⟨fun p : Rd d × Rd d => (r • p.1 + z, r • p.2 + z), by fun_prop⟩

theorem determ_lfpp_centerLaw {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n) (c : ℝ → ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (r : ℝ) (hr : 0 < r) (z : Rd d) (n : ℕ) :
    P.map (fun ω => determCenterX κ ξ εs c r z (h ω) n) =
      P.map (fun ω => determCenterX κ ξ εs c r 0 (h ω) n) := by
  let k : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  let g : Ω → DistRd d := fun ω => addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp one_pos z
  have hgm : Measurable g :=
    measurable_addConst.comp
      ((hk.measurable).prodMk ((measurable_sphereAvg_left 1 0).comp hk.measurable).neg)
  have hglaw : P.map g = P.map h :=
    l6c_map_normalizedTranslate_eq hd P h hh z
  have hkr := hk.ae_exists_tendsto_sphereAvgSeq hd hr 0
  have hsr := hh.1.ae_sphereAvg_affineComp hd one_pos z hr 0
  have hs1 := hh.1.ae_sphereAvg_affineComp hd one_pos z one_pos 0
  have hrel : ∀ᵐ ω ∂P,
      sphereAvg (g ω) r 0 = sphereAvg (h ω) r z - sphereAvg (h ω) 1 z := by
    filter_upwards [hkr, hsr, hs1] with ω ⟨a, ha⟩ hsrω hs1ω
    dsimp [g]
    rw [sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) ha,
      hsrω, hs1ω]
    simp only [one_mul, one_smul, zero_add]
    ring
  have hpoint : ∀ᵐ ω ∂P,
      determCenterX κ ξ εs c r z (h ω) n =
        determCenterX κ ξ εs c r 0 (g ω) n := by
    filter_upwards [hrel,
      l6c_ae_lfppSeq_translate hd κ hκ ξ εs hεs P h hh z] with ω hrelω ht
    apply ContinuousMap.ext
    rintro ⟨u, v⟩
    simp only [determCenterX, ContinuousMap.smul_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul, add_zero]
    have ht' := ht n (r • u) (r • v)
    rw [show r • u + z = z + r • u from add_comm _ _,
      show r • v + z = z + r • v from add_comm _ _, ht', hrelω]
    have he : -ξ * sphereAvg (h ω) r z + ξ * sphereAvg (h ω) 1 z =
        -ξ * (sphereAvg (h ω) r z - sphereAvg (h ω) 1 z) := by ring
    calc
      _ = (c r)⁻¹ * (Real.exp (-ξ * sphereAvg (h ω) r z) *
          Real.exp (ξ * sphereAvg (h ω) 1 z)) *
          lfppSeq κ ξ εs (g ω) n (r • u, r • v) := by ring
      _ = _ := by rw [← Real.exp_add, he]
  have hnorm : IsNormalizedLGF id (P.map h) := hh.map_id
  let F : DistRd d → C(Rd d × Rd d, ℝ) := fun x => determCenterX κ ξ εs c r 0 x n
  have hF : AEMeasurable F (P.map h) := by
    have hX : AEMeasurable (fun x : DistRd d => lfppSeq κ ξ εs x n) (P.map h) :=
      l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) (P.map h) id
        hnorm.1.isLGFPlusBddCont
    have hs : Measurable (fun x : DistRd d =>
        (c r)⁻¹ * Real.exp (-ξ * sphereAvg x r 0)) :=
      measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (measurable_sphereAvg_left r 0)))
    exact hs.aemeasurable.smul
      ((ContinuousMap.continuous_precomp _).measurable.comp_aemeasurable hX)
  calc
    P.map (fun ω => determCenterX κ ξ εs c r z (h ω) n) = P.map (F ∘ g) :=
      Measure.map_congr hpoint
    _ = (P.map g).map F :=
      (AEMeasurable.map_map_of_aemeasurable (hglaw ▸ hF) hgm.aemeasurable).symm
    _ = (P.map h).map F := by rw [hglaw]
    _ = P.map (F ∘ h) :=
      AEMeasurable.map_map_of_aemeasurable hF hh.1.measurable.aemeasurable

/-- A stable LFPP limit has the same centered, scaled metric law at every centre. -/
theorem determ_limit_centerLaw {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    (c : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (z : Rd d) :
    P.map (fun ω => scaledField ξ (fun _ => Dh ω) c r z (h ω)) =
      P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
  let X : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n ω => lfppSeq κ ξ εs (h ω) n
  let Y : Ω → C(Rd d × Rd d, ℝ) := fun ω => (Dh ω).1
  have hX (n : ℕ) : AEMeasurable (X n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hY : AEMeasurable Y P :=
    (measurable_subtype_coe.comp hDh).aemeasurable
  let Z : Rd d → ℕ → Ω → C(Rd d × Rd d, ℝ) := fun w n ω =>
    determCenterX κ ξ εs c r w (h ω) n
  let Zlim : Rd d → Ω → C(Rd d × Rd d, ℝ) := fun w ω =>
    ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r w)) •
      (Dh ω).1.comp
        ⟨fun p : Rd d × Rd d => (r • p.1 + w, r • p.2 + w), by fun_prop⟩
  have hZ (w : Rd d) : TendstoInDistribution (Z w) atTop (Zlim w)
      (fun _ => P) P := by
    have ha : Measurable (fun g : DistRd d => sphereAvg g r w) :=
      measurable_sphereAvg_left r w
    have hpair := l6c_stable_adjoin_scalar P h hh.1.measurable X Y hX hY
      hstable (fun g => sphereAvg g r w) ha
    let T : ℝ × C(Rd d × Rd d, ℝ) → C(Rd d × Rd d, ℝ) := fun q =>
      ((c r)⁻¹ * Real.exp (-ξ * q.1)) • q.2.comp
        ⟨fun p : Rd d × Rd d => (r • p.1 + w, r • p.2 + w), by fun_prop⟩
    have hT : Continuous T :=
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_fst))).smul
        ((ContinuousMap.continuous_precomp _).comp continuous_snd)
    exact hpair.continuous_comp hT
  let ν : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) := fun n =>
    ⟨P.map (Z 0 n), (Measure.isProbabilityMeasure_map_iff
      ((hZ 0).forall_aemeasurable n)).mpr inferInstance⟩
  have hE (n : ℕ) :
      (⟨P.map (Z z n), inferInstance⟩ : ProbabilityMeasure C(Rd d × Rd d, ℝ)) = ν n := by
    exact Subtype.ext (determ_lfpp_centerLaw hd κ hκ ξ εs hεs c P h hh r hr z n)
  have ht0 : Tendsto ν atTop
      (𝓝 (⟨P.map (Zlim 0), inferInstance⟩ : ProbabilityMeasure C(Rd d × Rd d, ℝ))) :=
    (hZ 0).tendsto
  have htz : Tendsto ν atTop
      (𝓝 (⟨P.map (Zlim z), inferInstance⟩ : ProbabilityMeasure C(Rd d × Rd d, ℝ))) := by
    simpa only [ν, hE] using (hZ z).tendsto
  have heq := congrArg (fun μ : ProbabilityMeasure C(Rd d × Rd d, ℝ) =>
    (μ : Measure C(Rd d × Rd d, ℝ))) (tendsto_nhds_unique htz ht0)
  have hleft : (fun ω => scaledField ξ (fun _ => Dh ω) c r z (h ω)) = Zlim z := rfl
  have hright : (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) = Zlim 0 := by
    funext ω
    exact (scaledField_zero ξ (fun _ => Dh ω) c r (h ω)).symm
  rw [hleft, hright]
  simpa only [ProbabilityMeasure.coe_mk] using heq

end HigherDimLQGMetric
