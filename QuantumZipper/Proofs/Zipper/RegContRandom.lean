import QuantumZipper.Proofs.Zipper.RegContMain
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.RS.BMModulus

/-!
# REG-CONT: the zipped field is almost surely continuous in time

Blueprint `E_BRANCH_BLUEPRINT.md` §3, node REG-CONT. Standing setup: `B` a Brownian motion,
`X` a free-boundary GFF modulo constants, `pathOf B ⟂ X`, `W = drive κ B`. Main result:

```
theorem ae_continuousOn_unzippedField (κ γ : ℝ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {T : ℝ} (hT : 0 < T)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ContinuousOn (fun s => unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) s
      (foldedCircle w r)) (Icc 0 T)
```

and its countable form for all dyadic folded circles, in the zipping time `t ↦ Y_t =
unzippedField γ 𝒵 (T − t)` (`ae_continuousOn_Y_dyadic`). No hypothesis `0 ∉ supp μ` is needed.

Proof: condition on the driver. For a fixed locally Hölder driver `W` the averages `Ψ_k` are
a.s. uniformly Cauchy over rational times (`ae_UCq`, Kolmogorov); this event is measurable in
`(path, field)` once `Ψ_k` is written through the jointly measurable reverse map `CharFun.Fm` of
the time-reversed path (`PsiKm`), so independence transfers it to the random driver
(`CharFun.ae_indep`); Brownian paths are locally `1/3`-Hölder (`RS.bm_holder`). The
deterministic step `continuousOn_coordChange_of_uc` concludes.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegCont

open CharFun TwoPoint UnzipInvariance

/-! ## Congruence in the driver -/

theorem fwdMapInv_congr {W W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hW' : Continuous W')
    (hW'0 : W' 0 = 0) {T : ℝ} (hEq : EqOn W W' (Icc 0 T)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    EqOn (fwdMapInv W s) (fwdMapInv W' s) H := by
  intro u hu
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hs.1 hu, fwdMapInv_eq_revMap_timeRev W' hW' hW'0 hs.1 hu]
  refine ReverseFlow.revMap_congr_drive u fun q hq => ?_
  rw [hEq ⟨by linarith [hq.2], by linarith [hq.1, hs.2]⟩, hEq hs]

/-! ## A jointly measurable form of `Ψ_k` -/

variable {T : ℝ} (hT : 0 ≤ T)

/-- The time-reversed path at time `s`, as a continuous path on `[0,s]`. -/
def revPath (s : ℝ) (hs : 0 ≤ s) (f : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) s, ℝ) :=
  ⟨fun q => f (projIcc 0 T hT (s - q)) - f (projIcc 0 T hT s),
    (f.continuous.comp (continuous_projIcc.comp (continuous_const.sub continuous_subtype_val))).sub
      continuous_const⟩

theorem measurable_revPath (s : ℝ) (hs : 0 ≤ s) : Measurable (revPath hT s hs) :=
  ContinuousMap.measurable_iff_eval.2 fun _ =>
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable

theorem Wof_revPath_eqOn (κ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    EqOn (Wof κ s hs.1 (revPath hT s hs.1 f)) (vRev (Wof κ T hT f) s) (Icc 0 s) := by
  intro q hq
  simp only [Wof, revPath, ContinuousMap.coe_mk, projIcc_of_mem hs.1 hq, vRev]
  ring

/-- `Ψ_k` written with the jointly measurable reverse map. -/
def PsiKm (κ : ℝ) (w : ℂ) (r s : ℝ) (hs : 0 ≤ s) (k : ℕ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) :
    ℝ :=
  ∫ u, avgReg p.2 k (Fm κ s hs (revPath hT s hs p.1, u)) ∂foldedCircle w r

theorem measurable_PsiKm (κ : ℝ) (w : ℂ) (r s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    Measurable (PsiKm hT κ w r s hs k) := by
  have hm : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg q.1.2 k (Fm κ s hs (revPath hT s hs q.1.1, q.2)) :=
    (measurable_avgReg k).comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_Fm κ s hs).comp
        (((measurable_revPath hT s hs).comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem PsiKm_eq (κ : ℝ) (w : ℂ) {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (k : ℕ)
    (f : C(Icc (0 : ℝ) T, ℝ)) (hf0 : Wof κ T hT f 0 = 0) (x : FieldSample) :
    PsiKm hT κ w r s hs.1 k (f, x) = PsiK (Wof κ T hT f) w r s k x := by
  have hW := continuous_Wof κ T hT f
  unfold PsiK PsiKm
  simp only [νT]
  rw [integral_map (aemeasurable_fwdMapInv hW hf0 hs.1 w hr)
    (RegClosure.measurable_avgReg_slice x k).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [foldedCircle_ae_mem_H w hr] with u hu
  rw [fwdMapInv_eq_revMap_timeRev _ hW hf0 hs.1 hu]
  congr 1
  exact ReverseFlow.revMap_congr_drive u (Wof_revPath_eqOn hT κ hs f)

/-! ## The measurable event -/

/-- Paths vanishing at `0` and locally `a`-Hölder on `[0,T]`. -/
def GoodP (a : ℝ) : Set C(Icc (0 : ℝ) T, ℝ) :=
  {f | f ⟨0, le_rfl, hT⟩ = 0 ∧ ∃ C : ℕ, ∀ t t' : Icc (0 : ℝ) T, |(t : ℝ) - t'| ≤ 1 / 2 →
    |f t - f t'| ≤ C * |(t : ℝ) - t'| ^ a}

theorem measurableSet_GoodP (a : ℝ) : MeasurableSet (GoodP hT a) := by
  have e : GoodP hT a = {f : C(Icc (0 : ℝ) T, ℝ) | f ⟨0, le_rfl, hT⟩ = 0} ∩
      ⋃ C : ℕ, ⋂ t : Icc (0 : ℝ) T, ⋂ t' : Icc (0 : ℝ) T, ⋂ (_ : |(t : ℝ) - t'| ≤ 1 / 2),
        {f : C(Icc (0 : ℝ) T, ℝ) | |f t - f t'| ≤ C * |(t : ℝ) - t'| ^ a} := by
    ext f
    simp only [GoodP, mem_inter_iff, mem_setOf_eq, mem_iUnion, mem_iInter]
  rw [e]
  refine (isClosed_eq (continuous_eval_const _) continuous_const).measurableSet.inter ?_
  refine MeasurableSet.iUnion fun C => IsClosed.measurableSet ?_
  exact isClosed_iInter fun t => isClosed_iInter fun t' => isClosed_iInter fun _ =>
    isClosed_le ((continuous_eval_const t).sub (continuous_eval_const t')).abs continuous_const

/-- The measurable form of `UCq`. -/
def UCm (κ : ℝ) (w : ℂ) (r : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ q : ℚ, ∀ hq : (q : ℝ) ∈ Icc (0 : ℝ) T,
    |PsiKm hT κ w r q hq.1 k p - PsiKm hT κ w r q hq.1 k' p| ≤ 1 / ((n : ℝ) + 1)

theorem measurableSet_UCm (κ : ℝ) (w : ℂ) (r : ℝ) : MeasurableSet {p | UCm hT κ w r p} := by
  have e : {p | UCm hT κ w r p} = ⋂ n : ℕ, ⋃ N : ℕ, ⋂ k : ℕ, ⋂ (_ : N ≤ k), ⋂ k' : ℕ,
      ⋂ (_ : N ≤ k'), ⋂ q : ℚ, ⋂ (hq : (q : ℝ) ∈ Icc (0 : ℝ) T),
        {p | |PsiKm hT κ w r q hq.1 k p - PsiKm hT κ w r q hq.1 k' p| ≤ 1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [UCm, mem_setOf_eq, mem_iInter, mem_iUnion]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun k' => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_
  exact measurableSet_le (continuous_abs.measurable.comp ((measurable_PsiKm hT κ w r q hq.1 k).sub
    (measurable_PsiKm hT κ w r q hq.1 k'))) measurable_const

theorem UCm_iff (κ : ℝ) (w : ℂ) {r : ℝ} (hr : 0 < r) (f : C(Icc (0 : ℝ) T, ℝ))
    (hf0 : Wof κ T hT f 0 = 0) (x : FieldSample) :
    UCm hT κ w r (f, x) ↔ UCq (Wof κ T hT f) w r T x := by
  unfold UCm UCq
  constructor
  · intro h n
    obtain ⟨N, hN⟩ := h n
    refine ⟨N, fun k hk k' hk' q hq => ?_⟩
    rw [← PsiKm_eq hT κ w hr hq k f hf0 x, ← PsiKm_eq hT κ w hr hq k' f hf0 x]
    exact hN k hk k' hk' q hq
  · intro h n
    obtain ⟨N, hN⟩ := h n
    refine ⟨N, fun k hk k' hk' q hq => ?_⟩
    rw [PsiKm_eq hT κ w hr hq k f hf0 x, PsiKm_eq hT κ w hr hq k' f hf0 x]
    exact hN k hk k' hk' q hq

theorem Wof_holder (κ : ℝ) {a : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} {C : ℕ}
    (hC : ∀ t t' : Icc (0 : ℝ) T, |(t : ℝ) - t'| ≤ 1 / 2 → |f t - f t'| ≤ C * |(t : ℝ) - t'| ^ a) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |Wof κ T hT f t - Wof κ T hT f t'| ≤ Real.sqrt κ * C * |t - t'| ^ a := by
  intro t ht t' ht' htt
  simp only [Wof, projIcc_of_mem hT ht, projIcc_of_mem hT ht']
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC ⟨t, ht⟩ ⟨t', ht'⟩ htt) (Real.sqrt_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

omit [MeasurableSpace Ω] in
theorem Wof_zero_of_GoodP (κ : ℝ) {a : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT a) :
    Wof κ T hT f 0 = 0 := by
  simp only [Wof]
  rw [show projIcc (0 : ℝ) T hT 0 = ⟨0, le_rfl, hT⟩ from projIcc_of_mem hT ⟨le_rfl, hT⟩, hf.1,
    mul_zero]

/-- **The fibre statement.** For every path, almost surely in the field, either the path is
not good or `UCm` holds. -/
theorem ae_fibre (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (hT : 0 < T) (κ : ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (w : ℂ) {r : ℝ} (hr : 0 < r) (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∀ᵐ ω ∂P, (f, X ω) ∈ {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      p.1 ∉ GoodP hT.le a ∨ UCm hT.le κ w r p} := by
  by_cases hf : f ∈ GoodP hT.le a
  · have hf0 := Wof_zero_of_GoodP hT.le κ hf
    obtain ⟨C, hC⟩ := hf.2
    filter_upwards [ae_UCq hX (continuous_Wof κ T hT.le f) hf0 hT ha ha1
      (by positivity : 0 ≤ Real.sqrt κ * C) (Wof_holder hT.le κ hC) w hr] with ω hω
    exact Or.inr ((UCm_iff hT.le κ w hr f hf0 (X ω)).2 hω)
  · exact ae_of_all _ fun ω => Or.inl hf

/-! ## Brownian paths are good -/

omit [MeasurableSpace Ω] in
theorem pathC_mem_GoodP {B : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => B t ω) {ω : Ω}
    (h0 : B 0 ω = 0) {a : ℝ}
    (hH : ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ T.toNNReal → ∀ s : ℝ≥0, 0 < s → s ≤ 1 / 2 →
      |B (t + s) ω - B t ω| ≤ C * (s : ℝ) ^ a) :
    pathC T B hc ω ∈ GoodP hT a := by
  refine ⟨by simpa [pathC] using h0, ?_⟩
  obtain ⟨C, hC⟩ := hH
  refine ⟨⌈|C|⌉₊, ?_⟩
  have key : ∀ t t' : Icc (0 : ℝ) T, (t : ℝ) ≤ t' → (t' : ℝ) - t ≤ 1 / 2 →
      |pathC T B hc ω t' - pathC T B hc ω t| ≤ ⌈|C|⌉₊ * ((t' : ℝ) - t) ^ a := by
    intro t t' htt h12
    rcases eq_or_lt_of_le htt with he | hlt
    · have : t = t' := Subtype.ext he
      subst this; simp only [sub_self, abs_zero]
      positivity
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    set s : ℝ≥0 := ((t' : ℝ) - t).toNNReal with hs
    have hs0 : 0 < s := by rw [hs]; exact Real.toNNReal_pos.2 (by linarith)
    have hs12 : s ≤ 1 / 2 := by
      rw [hs, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith)]; push_cast; linarith
    have htN : (t : ℝ).toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal t.2.2
    have hsum : (t : ℝ).toNNReal + s = (t' : ℝ).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_add, hs, Real.coe_toNNReal _ ht0, Real.coe_toNNReal _ (by linarith),
        Real.coe_toNNReal _ (by linarith [t'.2.1])]
      ring
    have hb := hC _ htN s hs0 hs12
    rw [hsum] at hb
    have hsr : (s : ℝ) = (t' : ℝ) - t := by rw [hs, Real.coe_toNNReal _ (by linarith)]
    rw [hsr] at hb
    simp only [pathC, ContinuousMap.coe_mk]
    refine hb.trans (mul_le_mul_of_nonneg_right ((le_abs_self C).trans (Nat.le_ceil _))
      (Real.rpow_nonneg (by linarith) _))
  intro t t' h12
  rcases le_total (t : ℝ) t' with htt | htt
  · rw [abs_sub_comm (t : ℝ), abs_of_nonneg (sub_nonneg.2 htt)] at h12
    rw [abs_sub_comm, abs_sub_comm (t : ℝ), abs_of_nonneg (sub_nonneg.2 htt)]
    exact key t t' htt h12
  · rw [abs_of_nonneg (sub_nonneg.2 htt)] at h12
    rw [abs_of_nonneg (sub_nonneg.2 htt)]
    exact key t' t htt h12

/-! ## Main theorem -/

/-- **REG-CONT.** Almost surely `s ↦ Y μ` along the unzipping, `μ = fc(w,r)`, is continuous on
`[0,T]`. -/
theorem ae_continuousOn_unzippedField [IsProbabilityMeasure P] (κ γ : ℝ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 < T) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ContinuousOn (fun s => unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) s
      (foldedCircle w r)) (Icc 0 T) := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  set a : ℝ := 1 / 3
  have hE := ae_indep (measurable_pathC T hB'm hB'c) hXm hind'
    ((measurableSet_GoodP hT.le a).compl.prod MeasurableSet.univ |>.union
      (measurableSet_UCm hT.le κ w r)) (fun f => by
        filter_upwards [ae_fibre hX hT κ (a := a) (by norm_num) (by norm_num) w hr f] with ω h
        rcases h with h | h
        · exact Or.inl ⟨h, trivial⟩
        · exact Or.inr h)
  have hgood : ∀ᵐ ω ∂P, pathC T B' hB'c ω ∈ GoodP hT.le a := by
    filter_upwards [RS.bm_holder hB (a := a) (by norm_num), hB.eval_zero_ae_eq_zero, hB'eq]
      with ω hH h0 heq
    refine pathC_mem_GoodP hT.le hB'c (by rw [heq]; exact h0) ?_
    obtain ⟨C, hC⟩ := hH T.toNNReal
    exact ⟨C, fun t ht s hs0 hs1 => by rw [heq, heq]; exact hC t ht s hs0 hs1⟩
  have hreg : ∀ᵐ ω ∂P, RegAvgGood (X ω) := by
    exact ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hX k
  filter_upwards [hE, hgood, hreg, hB'eq] with ω hE hgood hreg heq
  set f := pathC T B' hB'c ω
  have hf0 := Wof_zero_of_GoodP hT.le κ hgood
  have huc : UCq (Wof κ T hT.le f) w r T (X ω) := by
    rcases hE with h | h
    · exact absurd hgood h.1
    · exact (UCm_iff hT.le κ w hr f hf0 (X ω)).1 h
  have hc := continuousOn_coordChange_of_uc (continuous_Wof κ T hT.le f) hf0 hT w hr κ (Qc γ)
    hreg huc
  -- the driver `drive κ B ω` agrees with `Wof κ T f` on `[0,T]`
  have hdrive : drive κ B ω = drive κ B' ω := funext fun t => by simp [drive, heq]
  have hdc : Continuous (drive κ B ω) := by
    rw [hdrive]; exact continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)
  have hEq : EqOn (drive κ B ω) (Wof κ T hT.le f) (Icc 0 T) := by
    intro t ht
    rw [hdrive]
    simp only [drive, Wof, f, pathC, ContinuousMap.coe_mk, projIcc_of_mem hT.le ht]
  have hd0 : drive κ B ω 0 = 0 := (hEq ⟨le_rfl, hT.le⟩).trans hf0
  have hH : (foldedCircle w r) Hᶜ = 0 := ae_iff.1 (foldedCircle_ae_mem_H w hr)
  refine hc.congr fun s hs => ?_
  simp only [unzippedField]
  exact coordChange_congr_of_eqOn (fwdMapInv_congr hdc hd0 (continuous_Wof κ T hT.le f) hf0 hEq hs)
    hH _ _

end RegCont
end QuantumZipper
