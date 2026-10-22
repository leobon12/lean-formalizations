import HigherDimLQGMetric.Sphere.Cov
import HigherDimLQGMetric.LGF.Normalized
import LQGMetric.Field.CircleAvgAffine

/-!
# Scaling and translation of sphere averages of the LGF; invariance of laws

Packet F3 (Phase A, block A1), target 5. Ruling M17 (the identity
`sphereAvg (affineComp ρ z h) r w = sphereAvg h (ρr) (ρw + z)` holds deterministically only for
dyadic `ρ`; for the LGF it holds almost surely for every `ρ > 0`); port of LQGMetric's
`ae_circleAvg_affineComp` and `map_affine_sub_circleAvg` (`Field/CircleAvgAffine.lean`); blueprint
Lemma `r1:lem:var` (b).

* `smul_testAffinePull_sphMol`: `ρ^{-d} (σ_{r,w} * ψ_ε)((· - z)/ρ) = σ_{ρr, ρw+z} * ψ_{ρε}`, hence
  `⟨h(ρ· + z), sphMol ε w r⟩ = ⟨h, sphMol (ρε) (ρw + z) (ρr)⟩` (`affineComp_apply_sphMol`);
* `IsWholeSpaceLGF.ae_sphereAvg_affineComp`, `IsLGFPlusCont.ae_sphereAvg_affineComp` (`d ≥ 2`,
  `ρ, r > 0`): almost surely `sphereAvg (affineComp ρ z (h ω)) r w = sphereAvg (h ω) (ρr) (ρw + z)`.
  Proof: the two defining sequences differ by `⟨h, sphMol (ρ 2^{-n}) x s - sphMol 2^{-n} x s⟩`
  (`x = ρw + z`, `s = ρr`), whose second moment is `≤ C |ρ - 1| 2^{-n} / (ρr)` (transport bound),
  so the difference tends to `0` a.s. (Borel–Cantelli, LQGMetric's `ae_tendsto_zero_of_sq_le`);
  both sequences converge a.s. (target 1, applied to `h` and to the LGF `h(ρ· + z)`);
* `IsWholeSpaceLGF.map_recSph_eq`: the law of the recentred sphere-average process
  `p ↦ h_{p.r}(p.z) - h_1(0)` (indexed by `p = (r, z)`, `r > 0`) is the same for all LGFs (it is a
  `sigma0`-measurable functional of the field, a.s. coordinatewise; F2's `map_comp_eq_of_sigma0`);
* `IsWholeSpaceLGF.map_sphereAvg_affine_sub` (blueprint `r1:lem:var` (b)): the process
  `(s, u) ↦ h_{ρs}(ρu + w) - h_ρ(w)` has the law of `(s, u) ↦ h_s(u) - h_1(0)`;
* `IsNormalizedLGF.map_affineComp_sub_sphereAvg` (GM's form, port of `map_affine_sub_circleAvg`):
  for a normalized LGF, `h(ρ· + w) - h_ρ(w)` has the law of `h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Affine images of mollified sphere bumps -/

/-- `ρ^{-d} (sphMol ε w r)((· - z)/ρ) = sphMol (ρε) (ρw + z) (ρr)` (`ρ, ε > 0`). -/
theorem smul_testAffinePull_sphMol {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (z w : Rd d) (r : ℝ) :
    ((ρ ^ d)⁻¹) • testAffinePull ρ z (sphMol ε w r) = sphMol (ρ * ε) (ρ • w + z) (ρ * r) := by
  ext y
  rw [smul_apply, smul_eq_mul, testAffinePull_apply hρ.ne', sphMol_apply hε.ne',
    sphMol_apply (mul_pos hρ hε).ne', ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  have harg : ε⁻¹ • (ρ⁻¹ • (y - z) - (w + r • u)) =
      (ρ * ε)⁻¹ • (y - (ρ • w + z + (ρ * r) • u)) := by
    have e1 : y - (ρ • w + z + (ρ * r) • u) = (y - z) - ρ • (w + r • u) := by
      rw [smul_add, smul_smul]; abel
    rw [e1, mul_inv, mul_comm ρ⁻¹ ε⁻¹, mul_smul, smul_sub ρ⁻¹ (y - z) (ρ • (w + r • u)),
      smul_smul ρ⁻¹ ρ, inv_mul_cancel₀ hρ.ne', one_smul]
  rw [harg]
  ring

/-- `⟨h(ρ· + z), sphMol ε w r⟩ = ⟨h, sphMol (ρε) (ρw + z) (ρr)⟩` (`ρ, ε > 0`). -/
theorem affineComp_apply_sphMol {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (z w : Rd d) (r : ℝ)
    (g : DistRd d) :
    affineComp ρ z g (sphMol ε w r) = g (sphMol (ρ * ε) (ρ • w + z) (ρ * r)) := by
  rw [affineComp_apply_eq_apply_smul, smul_testAffinePull_sphMol hρ hε]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-! ### The a.s. scaling identity (ruling M17) -/

/-- **Ruling M17 for the LGF** (`d ≥ 2`, `ρ, r > 0`): almost surely
`sphereAvg (h(ρ· + z)) r w = sphereAvg h (ρr) (ρw + z)`. -/
theorem IsWholeSpaceLGF.ae_sphereAvg_affineComp (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ρ : ℝ} (hρ : 0 < ρ) (z : Rd d) {r : ℝ} (hr : 0 < r) (w : Rd d) :
    ∀ᵐ ω ∂P, sphereAvg (HigherDimLQGMetric.affineComp ρ z (h ω)) r w =
      sphereAvg (h ω) (ρ * r) (ρ • w + z) := by
  have := hh.gaussian.isProbabilityMeasure
  have hg := hh.affineComp hρ z
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphMol_sub_le hd
  set x : Rd d := ρ • w + z with hx
  set s : ℝ := ρ * r with hs
  have hs0 : 0 < s := mul_pos hρ hr
  set D : ℕ → Ω → ℝ := fun n ω =>
    h ω (sphMol (ρ * ((2 : ℝ) ^ n)⁻¹) x s) - h ω (sphMol ((2 : ℝ) ^ n)⁻¹ x s) with hD
  have hDeq : ∀ n ω, D n ω = sphereAvgSeq (HigherDimLQGMetric.affineComp ρ z (h ω)) r w n -
      sphereAvgSeq (h ω) s x n := by
    intro n ω
    rw [sphereAvgSeq_eq_apply_sphMol, sphereAvgSeq_eq_apply_sphMol,
      affineComp_apply_sphMol hρ (by positivity)]
  have hbound : ∀ n : ℕ, Integrable (fun ω => D n ω ^ 2) P ∧
      ∫ ω, D n ω ^ 2 ∂P ≤ C * |ρ - 1| / s * (1 / 2) ^ n := by
    intro n
    obtain ⟨hi, -, hb⟩ := hC hh (ε := ρ * ((2 : ℝ) ^ n)⁻¹) (ε' := ((2 : ℝ) ^ n)⁻¹)
      (by positivity) (by positivity) hs0 hs0 x x
    refine ⟨hi, hb.trans (le_of_eq ?_)⟩
    rw [sub_self, norm_zero, sub_self, abs_zero, zero_add, zero_add, min_self,
      show ρ * ((2 : ℝ) ^ n)⁻¹ - ((2 : ℝ) ^ n)⁻¹ = (ρ - 1) * ((2 : ℝ) ^ n)⁻¹ by ring, abs_mul,
      abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 ^ n)), one_div, inv_pow]
    ring
  have hD0 : ∀ᵐ ω ∂P, Tendsto (fun n => D n ω) atTop (𝓝 0) :=
    LQGMetric.CircleAvg.ae_tendsto_zero_of_sq_le (fun n => (hbound n).1) (by norm_num)
      (by norm_num) fun n => (hbound n).2
  filter_upwards [hD0, hg.ae_exists_tendsto_sphereAvgSeq hd hr w,
    hh.ae_exists_tendsto_sphereAvgSeq hd hs0 x] with ω h0 ha hb
  have h1 := tendsto_sphereAvgSeq_sphereAvg ha
  have h2 := tendsto_sphereAvgSeq_sphereAvg hb
  have h3 : Tendsto (fun n => D n ω) atTop
      (𝓝 (sphereAvg (HigherDimLQGMetric.affineComp ρ z (h ω)) r w - sphereAvg (h ω) s x)) :=
    (h1.sub h2).congr fun n => (hDeq n ω).symm
  have := tendsto_nhds_unique h3 h0
  linarith

/-- **Ruling M17 for an LGF plus a continuous function** (`d ≥ 2`, `ρ, r > 0`): almost surely
`sphereAvg (h(ρ· + z)) r w = sphereAvg h (ρr) (ρw + z)`. -/
theorem IsLGFPlusCont.ae_sphereAvg_affineComp (hd : 2 ≤ d) (hh : IsLGFPlusCont h P)
    {ρ : ℝ} (hρ : 0 < ρ) (z : Rd d) {r : ℝ} (hr : 0 < r) (w : Rd d) :
    ∀ᵐ ω ∂P, sphereAvg (HigherDimLQGMetric.affineComp ρ z (h ω)) r w =
      sphereAvg (h ω) (ρ * r) (ρ • w + z) := by
  obtain ⟨-, f, -, hlgf⟩ := hh
  have hg := hlgf.affineComp hρ z
  filter_upwards [hlgf.ae_sphereAvg_affineComp hd hρ z hr w,
    hg.ae_exists_tendsto_sphereAvgSeq hd hr w,
    hlgf.ae_exists_tendsto_sphereAvgSeq hd (mul_pos hρ hr) (ρ • w + z)] with ω hω ⟨a, ha⟩ ⟨b, hb⟩
  set g := h ω - ofCont (f ω) with hgdef
  have e : h ω = HigherDimLQGMetric.addFun g (f ω) := by
    rw [addFun_def, hgdef, sub_add_cancel]
  rw [e, affineComp_addFun hρ, sphereAvg_addFun_of_tendsto ha, sphereAvg_addFun_of_tendsto hb, hω]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [ContinuousMap.comp_apply, affinePt_apply]
  congr 1
  rw [smul_add, smul_smul]
  abel

/-! ### Invariance of laws -/

/-- The law of a real process is determined by the coordinatewise a.s. classes. -/
theorem map_eq_of_forall_ae_eq {T : Type*} [IsFiniteMeasure P] {X Y : Ω → T → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : ∀ t, ∀ᵐ ω ∂P, X ω t = Y ω t) :
    P.map X = P.map Y := by
  have h1 := ProbabilityTheory.isProjectiveLimit_map (P := P) (X := fun t ω => X ω t)
    hX.aemeasurable
  have h2 := ProbabilityTheory.isProjectiveLimit_map (P := P) (X := fun t ω => Y ω t)
    hY.aemeasurable
  refine h1.unique fun I => ?_
  rw [h2 I]
  refine Measure.map_congr ?_
  have hall : ∀ᵐ ω ∂P, ∀ i : I, X ω i = Y ω i := by
    rw [ae_all_iff]; exact fun i => hXY i
  filter_upwards [hall] with ω hω
  funext i
  exact (hω i).symm

/-- Sphere indices `(r, z)` with `r > 0`. -/
abbrev SphIdx (d : ℕ) : Type := {p : ℝ × Rd d // 0 < p.1}

/-- The recentred sphere-average process `p ↦ g_{p.r}(p.z) - g_1(0)`. -/
def recSph (g : DistRd d) (p : SphIdx d) : ℝ := sphereAvg g p.1.1 p.1.2 - sphereAvg g 1 0

theorem measurable_recSph : Measurable (recSph (d := d)) :=
  measurable_pi_iff.2 fun _ => (measurable_sphereAvg_left _ _).sub (measurable_sphereAvg_left _ _)

/-- The limit of the mean-zero pairings behind `recSph`. -/
def recSphLim (g : DistRd d) (p : SphIdx d) : ℝ :=
  limUnder atTop fun n => g (sphDiff n p.1.2 p.1.1 n 0 1)

theorem measurable_recSphLim_sigma0 (hd : 1 ≤ d) :
    Measurable[sigma0 d] (recSphLim (d := d)) := by
  refine @measurable_pi_iff _ _ _ (sigma0 d) _ _ |>.2 fun p => ?_
  have hn : ∀ n : ℕ, StronglyMeasurable[sigma0 d]
      fun g : DistRd d => g (sphDiff n p.1.2 p.1.1 n 0 1) := fun n =>
    Measurable.stronglyMeasurable (mα := sigma0 d)
      ((measurable_pi_apply (sphDiff0 hd n p.1.2 p.1.1 n 0 1)).comp measurable_ev0_sigma0)
  exact (@StronglyMeasurable.limUnder ℕ (DistRd d) ℝ (sigma0 d) _ _ atTop _
    (fun n g => g (sphDiff n p.1.2 p.1.1 n 0 1)) _ _ hn).measurable

theorem IsWholeSpaceLGF.ae_recSph_eq (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) (p : SphIdx d) :
    ∀ᵐ ω ∂P, recSph (h ω) p = recSphLim (h ω) p := by
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd p.2 p.1.2,
    hh.ae_exists_tendsto_sphereAvgSeq hd one_pos 0] with ω h1 h2
  have := ((tendsto_sphereAvgSeq_sphereAvg h1).sub (tendsto_sphereAvgSeq_sphereAvg h2)).congr
    fun n => sphereAvgSeq_sub_eq_apply_sphDiff (h ω) n p.1.2 p.1.1 n 0 1
  exact this.limUnder_eq.symm

/-- **The law of the recentred sphere-average process is the same for all LGFs** (`d ≥ 2`). -/
theorem IsWholeSpaceLGF.map_recSph_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistRd d} (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P') :
    P.map (fun ω => recSph (h ω)) = P'.map (fun ω => recSph (h' ω)) := by
  have := hh.gaussian.isProbabilityMeasure
  have := hh'.gaussian.isProbabilityMeasure
  have hF := measurable_recSphLim_sigma0 (d := d) (by omega)
  have hFm : Measurable (recSphLim (d := d)) := hF.mono sigma0_le le_rfl
  have e1 : P.map (fun ω => recSph (h ω)) = P.map (recSphLim ∘ h) :=
    map_eq_of_forall_ae_eq (measurable_recSph.comp hh.measurable) (hFm.comp hh.measurable)
      fun p => hh.ae_recSph_eq hd p
  have e2 : P'.map (fun ω => recSph (h' ω)) = P'.map (recSphLim ∘ h') :=
    map_eq_of_forall_ae_eq (measurable_recSph.comp hh'.measurable) (hFm.comp hh'.measurable)
      fun p => hh'.ae_recSph_eq hd p
  rw [e1, e2]
  exact map_comp_eq_of_sigma0 hF hh hh'

/-- **Scale and translation invariance of the recentred sphere-average process** (`d ≥ 2`,
blueprint `r1:lem:var` (b)): `(s, u) ↦ h_{ρs}(ρu + w) - h_ρ(w)` has the law of
`(s, u) ↦ h_s(u) - h_1(0)`. -/
theorem IsWholeSpaceLGF.map_sphereAvg_affine_sub (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ρ : ℝ} (hρ : 0 < ρ) (w : Rd d) :
    P.map (fun ω (p : SphIdx d) =>
        sphereAvg (h ω) (ρ * p.1.1) (ρ • p.1.2 + w) - sphereAvg (h ω) ρ w) =
      P.map (fun ω => recSph (h ω)) := by
  have := hh.gaussian.isProbabilityMeasure
  have hg := hh.affineComp hρ w
  rw [← hg.map_recSph_eq hd hh]
  refine map_eq_of_forall_ae_eq ?_ (measurable_recSph.comp hg.measurable) fun p => ?_
  · exact measurable_pi_iff.2 fun p =>
      ((measurable_sphereAvg_left _ _).comp hh.measurable).sub
        ((measurable_sphereAvg_left _ _).comp hh.measurable)
  · filter_upwards [hh.ae_sphereAvg_affineComp hd hρ w p.2 p.1.2,
      hh.ae_sphereAvg_affineComp hd hρ w one_pos 0] with ω h1 h2
    simp only [recSph]
    rw [h1, h2, mul_one, smul_zero, zero_add]

/-- **GM's form of the invariance** (`d ≥ 2`): for a normalized LGF, `h(ρ· + w) - h_ρ(w)` has the
law of `h`. -/
theorem IsNormalizedLGF.map_affineComp_sub_sphereAvg (hd : 2 ≤ d) (hh : IsNormalizedLGF h P)
    {ρ : ℝ} (hρ : 0 < ρ) (w : Rd d) :
    P.map (fun ω => HigherDimLQGMetric.addConst (HigherDimLQGMetric.affineComp ρ w (h ω))
      (-sphereAvg (h ω) ρ w)) = P.map h := by
  have hd1 : 1 ≤ d := by omega
  have hg := hh.1.affineComp hρ w
  have hN : ∀ {k : Ω → DistRd d},
      IsWholeSpaceLGF k P → ∀ᵐ ω ∂P, ∀ c, sphereAvg (HigherDimLQGMetric.addConst (k ω) c) 1 0 =
        sphereAvg (k ω) 1 0 + c := by
    intro k hk
    filter_upwards [hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0] with ω hω c
    exact sphereAvg_addConst_of_mem_convSet hd1 hω c
  have hmain := map_affine_normalized_ae (integral_bumpTest_zero (d := d))
    (measurable_sphereAvg_left 1 0) hh.1 (hN hh.1) hh.2 hρ w (hN hg)
  rw [← hmain]
  refine Measure.map_congr ?_
  filter_upwards [hh.1.ae_sphereAvg_affineComp hd hρ w one_pos 0] with ω hω
  rw [hω, mul_one, smul_zero, zero_add]

end HigherDimLQGMetric
