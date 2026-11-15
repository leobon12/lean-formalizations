/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aMeanIdentGreen
import InteractingSLE.Spec.Supplement.RLCG7aMeanIdentAssembly

/-!
# G7a's pocket mean identity from active-domain Green regularity

Packet PROVE-G7A-MEANIDENT. The deterministic identity is reduced to the
explicit analytic input `AliveGreenRegularityStatement`. All finite-word,
boundary geometry, harmonic uniqueness and integration steps are proved here
and in the two boundary modules. The Gaussian hull-limit input is discharged.
No unconditional pocket mean identity or G7a theorem is claimed in this file.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap greenH)
open scoped NNReal

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The restricted Cameron–Martin source is minus the active Laplacian density. -/
theorem indicator_src_eq_neg_density (F : CMCut) (K : Set ℂ) (z : ℂ) :
    (H \ K).indicator F.src z =
      -((H \ K).indicator (QuantumZipper.K3.greenDensity F.f) z) := by
  by_cases hz : z ∈ H \ K
  · rw [indicator_of_mem hz, indicator_of_mem hz, F.src_of_mem hz.1]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, neg_zero]

/-- The exact unchanged pocket mean identity, conditional only on the isolated
active-domain Green regularity obligation. -/
theorem pocketMeanIdentStatement_of_greenRegularity (hreg : AliveGreenRegularityStatement) :
    PocketMeanIdentStatement := by
  classical
  intro κ hκ b bR J Ĵ hb hbR O hO hbO y hy θ F q hq N hNo _hNO hFq _hFΔ hyN
    w' hw' hw0 t ht η hηc hfill hηN uR u huR hu φ hφ
  set w : ℝ → ℝ := Ito.rpath w' with hwdef
  have hw : Continuous w := hw'.comp continuous_real_toNNReal
  have hw00 : w 0 = 0 := by simp only [hwdef, Ito.rpath, Real.toNNReal_zero, hw0]
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  set N' : Set ℂ := (fun z => z + (y : ℂ)) ⁻¹' N with hNdef
  have hN'o : IsOpen N' := hNo.preimage (continuous_id.add continuous_const)
  have h0N' : (0 : ℂ) ∈ N' := by simpa only [hNdef, mem_preimage, zero_add] using hyN
  have hp : ∀ j : ↥(offMarks J Ĵ O), chartP J Ĵ O y j ≠ 0 := by
    intro j he
    have hjy : (j : ℝ) = y := sub_eq_zero.1 he
    exact (Finset.mem_filter.1 j.2).2 (hjy ▸ hy)
  have hqa : EqOn (fun z => q (z + y))
      (GB7a.argSum0 (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y)) H := by
    intro z hz
    have he := argSum0_shift (argP J Ĵ O) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) y z
    rw [show (fun j => argP J Ĵ O j - y) = chartP J Ĵ O y from rfl] at he
    rw [he, argSum0_eq hb hbR hO hbO hq hy (Exist.add_real_mem_H hz y)]
  have hqh : InnerProductSpace.HarmonicOnNhd (fun z => q (z + y)) H :=
    fun z hz => Exist.harmonicAt_comp_add_const (hq.1 _ (Exist.add_real_mem_H hz y))
  obtain ⟨Cq, hCq⟩ := hq.2.1
  have hqb : Bornology.IsBounded ((fun z => q (z + y)) '' H) := by
    refine isBounded_iff_forall_norm_le.2 ⟨Cq, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Real.norm_eq_abs]
    exact hCq _ (Exist.add_real_mem_H hz y)
  have hseed : argC₀ b bR J Ĵ O y + Real.pi *
      ∑ j ∈ Finset.univ.filter (fun j => 0 < chartP J Ĵ O y j), argC b bR J Ĵ O j = 0 := by
    rw [argC₀, Finset.sum_filter, Finset.mul_sum,
      ← Finset.sum_coe_sort (offMarks J Ĵ O), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [chartP, argC, sub_pos]
    split_ifs <;> field_simp <;> ring
  have harg : ∀ ξ : ℂ,
      GB7a.argSum0 (fun j => geomImage w t (chartP J Ĵ O y j))
          (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) ξ =
        ∑ p ∈ offMarks J Ĵ O, ((jmp bR p - jmp b p) * (if y < p then 1 else 0) -
          (jmp bR p - jmp b p) / Real.pi *
            Complex.arg (ξ - ((if p < y then geomL w t (p - y) else geomR w t (p - y)) : ℝ))) := by
    intro ξ
    rw [GB7a.argSum0, argC₀, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_coe_sort (offMarks J Ĵ O)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [argC, chartP, geomImage, sub_neg]
    ring
  have hha : EqOn (fun ξ => uR ξ - u ξ)
      (GB7a.argSum0 (fun j => geomImage w t (chartP J Ĵ O y j))
        (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y)) H := by
    intro ξ hξ
    rw [harg]
    dsimp only
    rw [Ito.eqOn_meanHarmonic (fun _ => geomL_nonpos hw t.coe_nonneg _)
      (fun _ => geomR_nonneg hw t.coe_nonneg _) huR hξ,
      Ito.eqOn_meanHarmonic (fun _ => geomL_nonpos hw t.coe_nonneg _)
        (fun _ => geomR_nonneg hw t.coe_nonneg _) hu hξ]
    exact meanHarmonic_flowLine_sub hκ hb hbR hO hbO hy θ (geomL w t) (geomR w t) ξ
  obtain ⟨CR, hCR⟩ := huR.2.1
  obtain ⟨CB, hCB⟩ := hu.2.1
  have hhb : Bornology.IsBounded ((fun ξ => uR ξ - u ξ) '' H) := by
    refine isBounded_iff_forall_norm_le.2 ⟨CR + CB, ?_⟩
    rintro _ ⟨ξ, hξ, rfl⟩
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hCR ξ hξ) (hCB ξ hξ))
  have hpoint : ∀ z ∈ H \ fwdHull w t,
      couplingMean κ w t uR z = couplingMean κ w t u z + aliveGreenPot (F.shift y) w t z +
        q (z + y) - (F.shift y).f z := by
    intro z hz
    have he := geomArgSum_ident_of_greenRegularity hreg hw hw00 htr hηc (hfill t ⟨htr, le_rfl⟩)
      (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) hp hseed
      hN'o h0N' hηN (F.shift y) hqh hqb hqa (huR.1.sub hu.1) hhb hha
      (fun z hz hzH => hFq _ hz (Exist.add_real_mem_H hzH y)) hz
    simp only [Pi.sub_apply] at he
    simp only [couplingMean]
    linarith
  set G : ℂ → ℝ := aliveGreenPot (F.shift y) w t with hGdef
  have hφH : ∀ z, φ z ≠ 0 → z ∈ H \ fwdHull w t := fun z hz =>
    ⟨φ.tsupport_subset (subset_tsupport _ hz), fun hK =>
      disjoint_left.1 hφ (subset_tsupport _ hz) hK⟩
  have hpt : ∀ z, couplingMean κ w t uR z * φ z =
      couplingMean κ w t u z * φ z + G z * φ z +
        φ z * (q (z + y) - (F.shift y).f z) := by
    intro z
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero, zero_mul, add_zero]
    · rw [hpoint z (hφH z hz)]
      ring
  have iR := LocalExt.integrable_couplingMean_mul (κ := κ) hw.continuousOn huR.1 hφ
  have iB := LocalExt.integrable_couplingMean_mul (κ := κ) hw.continuousOn hu.1 hφ
  have hqyc : ContinuousOn (fun z => q (z + y) - (F.shift y).f z) H := by
    have hqc : ContinuousOn q H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
    exact (hqc.comp (continuousOn_id.add continuousOn_const)
      (fun z hz => Exist.add_real_mem_H hz y)).sub (F.shift y).smooth.continuous.continuousOn
  have iT : Integrable fun z => φ z * (q (z + y) - (F.shift y).f z) :=
    (LocalExt.integrable_mul_testOn hqyc φ).congr (ae_of_all _ fun z => mul_comm _ _)
  have iG : Integrable fun z => G z * φ z := by
    refine ((iR.sub iB).sub iT).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply]
    rw [hpt z]
    ring
  have hcross : LocalExt.greenCross w t φ ((H \ fwdHull w t).indicator (F.shift y).src) =
      -∫ z, G z * φ z := by
    unfold LocalExt.greenCross
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have he : (fun z => φ x * greenH (fwdMap w t x) (fwdMap w t z) *
        (H \ fwdHull w t).indicator (F.shift y).src z) =
        fun z => -(φ x * (greenH (fwdMap w t x) (fwdMap w t z) *
          (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity (F.shift y).f) z)) := by
      funext z
      rw [indicator_src_eq_neg_density]
      ring
    simp only at he ⊢
    rw [he, integral_neg, integral_const_mul]
    simp only [hGdef, aliveGreenPot, GB7a.greenPot]
    ring
  have hT : chartShift F q y φ = ∫ z, φ z * (q (z + y) - (F.shift y).f z) :=
    SupercriticalConformalCovariance.GM24.smoothDist_apply hqyc φ
  have iBG : Integrable fun z => couplingMean κ w t u z * φ z + G z * φ z := iB.add iG
  rw [hcross, hT, sub_neg_eq_add, ← integral_add iB iG, ← integral_add iBG iT]
  exact integral_congr_ae (ae_of_all _ fun z => (hpt z).symm)

end InteractingSLE.Restart.FlowLocalityGen

namespace InteractingSLE.RLC

/-- G7a reduced to the active Green Dirichlet theorem and its pre-existing WFS
and Theorems 1.2/1.3 prerequisites. There is no Gaussian hull-limit input. -/
theorem g7aChartStatement_of_greenRegularity
    (hreg : Restart.FlowLocalityGen.AliveGreenRegularityStatement)
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) : G7aChartStatement.{0} :=
  g7aChartStatement_of_pocketMeanIdent
    (Restart.FlowLocalityGen.pocketMeanIdentStatement_of_greenRegularity hreg) hT h12p h13

end InteractingSLE.RLC
