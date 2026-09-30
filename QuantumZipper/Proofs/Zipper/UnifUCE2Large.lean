import QuantumZipper.Proofs.Zipper.UnifUCE2Scale
import QuantumZipper.Proofs.Zipper.UnifUC1Stab

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-E2 (decision D33), step 4: the time modulus at radii `ρ ≥ r₀`

* `energy_nuT_pair_le`: for one pair of pushed circles with different centres **and** different
  times, `E(νT W w ρ u − νT W w' ρ u') ≤ 2·timeK·δ^{a/12} + 2·spaceK·D^{1/12}` when `|u − u'| ≤ δ`,
  `‖w − w'‖ ≤ D` (triangle inequality for the energy through `νT W w ρ u'`, then the JointMod time
  and space moduli `abs_kernelCov2_νT_time_unif`, `abs_kernelCov2_νT_space_unif`).
* `energyPar_large_le`: for `p, p' ∈ tri T` with `dist p p' ≤ 1/2`, `ρ ≥ r₀ > 0`, `τ ∈ (0,1]`,
  `E(μ_{p,ρ} − μ_{p',ρ}) ≤ 2 Kb + 2 Ks (18 √(τ / 2^{-k}))²`, where `Kb` is the per-circle bound above
  the strip `{Im z < τ}` (centre displacement from RSTAB `norm_RUS_sub_le_holder`) and `Ks` the
  crude per-circle bound in the strip (centre displacement `≤ 2·revBound`). The mixture step is
  `UnifUCE2Basic.energy_mixFc_le_strip`, the strip mass `TwoPoint.foldedCircle_strip_le`.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (energy of circle-average mixtures);
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through the JointMod moduli). The
strip cut and the bookkeeping are an own elementary argument (plan D33, item 5).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist B2

variable {W : ℝ → ℝ}

theorem timeK_nonneg_E2 {M T r₀ R CH : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀)
    (hCH : 0 ≤ CH) : 0 ≤ timeK M T r₀ R CH := by
  have h1 := timeConst_nonneg (R := R) hM hT hr₀
  have h2 := potC_nonneg (R := R) hM hT hr₀
  have h3 : (0 : ℝ) ≤ (CH + 1) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by linarith) _
  unfold timeK; positivity

theorem spaceK_nonneg_E2 {M T r₀ R : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀) :
    0 ≤ spaceK M T r₀ R := by
  have h1 := spaceConst_nonneg (R := R) hM hT hr₀
  have h2 := potC_nonneg (R := R) hM hT hr₀
  unfold spaceK; positivity

/-- One pair of pushed circles: different centres and different times. -/
theorem energy_nuT_pair_le (hW : Continuous W) (hW0 : W 0 = 0) {T Mw r₀ R a CH : ℝ}
    (hr₀ : 0 < r₀) (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (ha : 0 < a) (ha1 : a ≤ 1)
    (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {w w' : ℂ} {ρ : ℝ} (hρ : r₀ ≤ ρ) (hwR : ‖w‖ + ρ ≤ R) (hwR' : ‖w'‖ + ρ ≤ R)
    {u u' δ D : ℝ} (hu : u ∈ Icc (0 : ℝ) T) (hu' : u' ∈ Icc (0 : ℝ) T) (hδ : |u - u'| ≤ δ)
    (hD : ‖w - w'‖ ≤ D) :
    kernelCov2 neumannH (νT W w ρ u, νT W w' ρ u') (νT W w ρ u, νT W w' ρ u') ≤
      2 * (timeK Mw T r₀ R CH * δ ^ (a / 12)) + 2 * (spaceK Mw T r₀ R * D ^ (1 / 12 : ℝ)) := by
  have hT : 0 ≤ T := hu.1.trans hu.2
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  obtain ⟨e1, g1⟩ := goodM_pushed_circle hW hW0 hMw hu hr₀ hρ hwR
  obtain ⟨e2, g2⟩ := goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ hwR
  obtain ⟨e3, g3⟩ := goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ hwR'
  rw [← e1] at g1
  rw [← e2] at g2
  rw [← e3] at g3
  have htri := kernelCov2_self_triangle (g1.admissible (by norm_num))
    (g2.admissible (by norm_num)) (g3.admissible (by norm_num)) (g1.univ_eq g2) (g2.univ_eq g3)
  have ht := abs_kernelCov2_νT_time_unif hW hW0 hr₀ hMw ha ha1 hCH hH hρ hwR hu hu'
  have hs := abs_kernelCov2_νT_space_unif hW hW0 hr₀ hMw (β := 1 / 12) (by norm_num) le_rfl hu'
    hρ hρ hwR hwR'
  rw [sub_self, abs_zero, add_zero] at hs
  have htK := timeK_nonneg_E2 (R := R) hM0 hT hr₀ hCH
  have hsK := spaceK_nonneg_E2 (R := R) hM0 hT hr₀
  have h1 : |u - u'| ^ (a / 12) ≤ δ ^ (a / 12) :=
    Real.rpow_le_rpow (abs_nonneg _) hδ (by positivity)
  have h2 : ‖w - w'‖ ^ (1 / 12 : ℝ) ≤ D ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hD (by norm_num)
  have a1 := (le_abs_self _).trans (ht.trans (mul_le_mul_of_nonneg_left h1 htK))
  have a2 := (le_abs_self _).trans (hs.trans (mul_le_mul_of_nonneg_left h2 hsK))
  linarith

/-- **The time modulus at radii `ρ ≥ r₀`** (strip form). -/
theorem energyPar_large_le {T a CH : ℝ} (hWH : HolderDrv W T a CH) {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) {Ra : ℝ}
    (hRa : Ra = revBound (2 * Mw) T (‖d‖ + radius k)) {p p' : ℝ × ℝ} (hp : p ∈ tri T)
    (hp' : p' ∈ tri T) (hpp : dist p p' ≤ 1 / 2) {r₀ ρ τ : ℝ} (hr₀ : 0 < r₀) (hρ : r₀ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p' ρ) (muUS W d k p ρ, muUS W d k p' ρ) ≤
      2 * (2 * (timeK Mw T r₀ (Ra + 1) CH * dist p p' ^ (a / 12)) +
          2 * (spaceK Mw T r₀ (Ra + 1) *
            (4 * (CH + 2) * (1 + Real.sqrt ((‖d‖ + radius k) ^ 2 + 8 * T)) * dist p p' ^ a /
              τ ^ 2) ^ (1 / 12 : ℝ))) +
        2 * ((2 * (timeK Mw T r₀ (Ra + 1) CH * dist p p' ^ (a / 12)) +
            2 * (spaceK Mw T r₀ (Ra + 1) * (2 * Ra) ^ (1 / 12 : ℝ))) *
          (18 * Real.sqrt (τ / radius k)) ^ 2) := by
  have hWH' := hWH
  obtain ⟨hW, hW0, ha, ha1, hCH, hH⟩ := hWH'
  have hT : 0 ≤ T := hp.1.trans (by linarith [hp.2.1, hp.2.2])
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  have hu : p.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
  have hu' : p'.1 ∈ Icc (0 : ℝ) T := ⟨hp'.1, by linarith [hp'.2.1, hp'.2.2]⟩
  have hρ0 : 0 < ρ := hr₀.trans_le hρ
  have hδu : |p.1 - p'.1| ≤ dist p p' := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
  rw [muUS_eq_map hW hW0 hMw d k hp hρ0, muUS_eq_map hW hW0 hMw d k hp' hρ0]
  unfold alphaUS
  have hwm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2)) hp.2.1
  have hwm' := TwoPoint.measurable_revMap (continuous_vrev hW (p'.1 + p'.2)) hp'.2.1
  have hψ := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  have hψ' := TwoPoint.measurable_revMap (continuous_vrev hW p'.1) hp'.1
  have hf := alphaUS_ae_facts hW hMw d k hp
  have hf' := alphaUS_ae_facts hW hMw d k hp'
  rw [← hRa] at hf hf'
  set R := Ra + 1 with hR
  have htK := timeK_nonneg_E2 (R := R) hM0 hT hr₀ hCH
  have hsK := spaceK_nonneg_E2 (R := R) hM0 hT hr₀
  have hRa0 : 0 ≤ Ra := by rw [hRa]; exact revBound_nonneg (by linarith) hT
  set Kb := 2 * (timeK Mw T r₀ R CH * dist p p' ^ (a / 12)) +
    2 * (spaceK Mw T r₀ R *
      (4 * (CH + 2) * (1 + Real.sqrt ((‖d‖ + radius k) ^ 2 + 8 * T)) * dist p p' ^ a /
        τ ^ 2) ^ (1 / 12 : ℝ)) with hKb
  set Ks := 2 * (timeK Mw T r₀ R CH * dist p p' ^ (a / 12)) +
    2 * (spaceK Mw T r₀ R * (2 * Ra) ^ (1 / 12 : ℝ)) with hKs
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  have key := energy_mixFc_le_strip (A := foldedCircle d (radius k)) hwm hwm' hψ hψ'
    (ρ := ρ) (ρ' := ρ) (α := 1 / 3) (C := frostC T r₀ R) (B := revBound (2 * Mw) T R)
    (by norm_num) (by unfold frostC; positivity) (revBound_nonneg (by linarith) hT)
    (by
      filter_upwards [hf, hf'] with z hz hz'
      exact ⟨(goodM_pushed_circle hW hW0 hMw hu hr₀ hρ (R := R) (by linarith [hz.2.2.2.2])).2,
        (goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ (R := R) (by linarith [hz'.2.2.2.2])).2⟩)
    (Kb := Kb) (Ks := Ks) (τ := τ) hKb0 hKs0
    (by
      filter_upwards [hf, hf'] with z hz hz' hzτ
      have hzR : ‖revMap (vrev W (p.1 + p.2)) p.2 z‖ + ρ ≤ R := by linarith [hz.2.2.2.2]
      have hzR' : ‖revMap (vrev W (p'.1 + p'.2)) p'.2 z‖ + ρ ≤ R := by linarith [hz'.2.2.2.2]
      rw [← (goodM_pushed_circle hW hW0 hMw hu hr₀ hρ hzR).1,
        ← (goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ hzR').1]
      exact energy_nuT_pair_le hW hW0 hr₀ hMw ha ha1 hCH hH hρ hzR hzR' hu hu' hδu
        (norm_RUS_sub_le_holder hWH hT hτ hτ1 hp hp' hpp hz.1 hzτ hz.2.1))
    (by
      filter_upwards [hf, hf'] with z hz hz' _
      have hzR : ‖revMap (vrev W (p.1 + p.2)) p.2 z‖ + ρ ≤ R := by linarith [hz.2.2.2.2]
      have hzR' : ‖revMap (vrev W (p'.1 + p'.2)) p'.2 z‖ + ρ ≤ R := by linarith [hz'.2.2.2.2]
      rw [← (goodM_pushed_circle hW hW0 hMw hu hr₀ hρ hzR).1,
        ← (goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ hzR').1]
      refine energy_nuT_pair_le hW hW0 hr₀ hMw ha ha1 hCH hH hρ hzR hzR' hu hu' hδu ?_
      refine (norm_sub_le _ _).trans ?_
      linarith [hz.2.2.2.2, hz'.2.2.2.2])
  refine key.trans ?_
  -- the strip mass
  set m := (foldedCircle d (radius k) {z : ℂ | z.im < τ}).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hm1 : m ≤ 18 * Real.sqrt (τ / radius k) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine le_trans (measure_mono_ae ?_) (foldedCircle_strip_le d (radius_pos k) hτ)
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d (radius_pos k)] with z hz
    exact fun (hzτ : z.im < τ) => show |z.im| < τ by
      rw [abs_of_pos (show 0 < z.im from hz)]; exact hzτ
  have hm2 : m ^ 2 ≤ (18 * Real.sqrt (τ / radius k)) ^ 2 := pow_le_pow_left₀ hm0 hm1 2
  have e1 := Real.sq_sqrt hKb0
  have e2 := Real.sq_sqrt hKs0
  have h3 : (Real.sqrt Kb + Real.sqrt Ks * m) ^ 2 ≤
      2 * Real.sqrt Kb ^ 2 + 2 * (Real.sqrt Ks ^ 2 * m ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt Kb - Real.sqrt Ks * m)]
  rw [e1, e2] at h3
  have h4 := mul_le_mul_of_nonneg_left hm2 hKs0
  linarith

end RegUnif
end QuantumZipper
