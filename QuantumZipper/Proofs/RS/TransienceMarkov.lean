import QuantumZipper.Proofs.RS.TransienceBase
import QuantumZipper.Proofs.RS.TransienceKR
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Loewner.CaraR8

/-!
# EXT-RS node TRANS, Markov step: `0 ∉ closure η[1,∞)` almost surely (κ ≤ 4)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **TRANS**.

`ae_zero_not_mem_closure_Ici_one`: for a Brownian motion `B` and `0 < κ ≤ 4`, almost surely
`0 ∉ closure (η '' [1,∞))`, `η = sleTrace κ B ω`.

Proof (Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), proof of Thm 7.1, p. 34:
"a.s. there are two limit points `x₀, x₁` for `g₁(z)` as `z → 0` in `H₁`. Note that `g₁(γ[1,∞))`
has the same distribution as `γ[0,∞)` translated by `ξ(1)`. Consequently, Lemma 7.2 shows that
a.s. `x₀` and `x₁` are not in the closure of `g₁(γ[1,∞))`"):
* BASE (`base_cluster`): accumulation at `0` forces the shifted trace `η¹` to accumulate at
  `0₋` or `0₊` (the two preimages of the base under the Carathéodory extension at time `1`);
* `0₋, 0₊` are Borel functions of the driver on `[0,1]` (`Thm14WeldingData.zmSeq`, and `zpSeq`
  below), hence independent of the shifted motion (weak Markov property);
* for every fixed `x ≠ 0`, a.s. `x ∉ closure (η¹ '' [0,∞))` (RS Lemma 7.2, node KR,
  `ae_not_mem_closure_sleTrace`); Fubini (`CharFun.ae_indep`) on the canonical path space
  `CPath` with the measurable trace TR6 handles the random points.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

open Thm14WeldingData

section ZeroPlus

variable {T : ℝ} (hT : 0 ≤ T)

/-- Borel version of `0₊`: the infimum of the positive rationals with real boundary value. -/
def zpSeq (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ :=
  sInf (((↑) : ℚ → ℝ) '' {q : ℚ | 0 < (q : ℝ) ∧ (bdrySeq hT f q).im = 0})

theorem measurable_zpSeq : Measurable (zpSeq hT) :=
  measurable_sInf_rat _
    (fun q => measurableSet_setOfPred.2 (measurable_const.and (measurableSet_setOfPred.1
      (measurableSet_eq_fun (Complex.measurable_im.comp (measurable_bdrySeq hT q))
        measurable_const))))
    (fun _ => ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact hq.1.le⟩)

theorem zpSeq_eq_of_car {f : C(Icc (0 : ℝ) T, ℝ)} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (extIccPath hT f) T F) :
    zpSeq hT f = zeroPlus (extIccPath hT f) T := by
  have ha := WeldingUniqueness.zeroMinus_nonpos (extIccPath hT f) T
  have hb := zeroPlus_nonneg (extIccPath hT f) T
  have hset : {q : ℚ | 0 < (q : ℝ) ∧ (bdrySeq hT f q).im = 0} =
      {q : ℚ | 0 < (q : ℝ) ∧ zeroPlus (extIccPath hT f) T ≤ (q : ℝ)} := by
    ext q
    simp only [mem_ofPred_eq, bdrySeq_eq_of_car hT hF]
    constructor
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rcases (hF.2.2.2.2.2.1 q).1 h with h' | h'
      · linarith
      · exact h'
    · rintro ⟨hq, h⟩
      exact ⟨hq, (hF.2.2.2.2.2.1 q).2 (Or.inr h)⟩
  unfold zpSeq
  rw [hset]
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt (zeroPlus (extIccPath hT f) T + 1)
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    ⟨_, q₀, ⟨by linarith, by linarith⟩, rfl⟩ ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hq.2
  · intro c hc
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc
    exact ⟨_, ⟨q, ⟨by linarith, hq1.le⟩, rfl⟩, hq2⟩

end ZeroPlus

theorem pathC_apply_of_continuous {T : ℝ} {W : ℝ → ℝ} (hW : Continuous W) (x : Icc (0 : ℝ) T) :
    Thm14WeldingData.pathC T W x = W x := by
  simp [Thm14WeldingData.pathC, hW]

section Markov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A function of the past `(B r)_{r ≤ 1}` is independent of the shifted path in `CPath`. -/
theorem indepFun_toCPath_shift {B₀ : ℝ≥0 → Ω → ℝ} {α : Type*} [MeasurableSpace α]
    (hind0 : IndepFun (fun ω u => B₀ (1 + u) ω - B₀ 1 ω)
      (fun ω (r : Set.Iic (1 : ℝ≥0)) => B₀ r ω) P)
    {g : Ω → α}
    (hg : Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic (1 : ℝ≥0)) => B₀ r ω)
      MeasurableSpace.pi] g)
    (hc : ∀ ω, Continuous fun u => B₀ (1 + u) ω - B₀ 1 ω) :
    IndepFun g (toCPath (fun u ω => B₀ (1 + u) ω - B₀ 1 ω) hc) P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind0 ⊢
  intro A C hA hC
  obtain ⟨A', hA', e1⟩ := MeasurableSpace.measurableSet_comap.1 (hg hA)
  obtain ⟨C', hC', e2⟩ := MeasurableSpace.measurableSet_comap.1 hC
  have e3 : toCPath (fun u ω => B₀ (1 + u) ω - B₀ 1 ω) hc ⁻¹' C =
      (fun ω u => B₀ (1 + u) ω - B₀ 1 ω) ⁻¹' C' := by rw [← e2]; rfl
  rw [← e1, e3, inter_comm, hind0 C' A' hC' hA', mul_comm]

/-- If `‖x − γ q‖ ≥ c > 0` at all rational `q ≥ 0` and `γ` is continuous on `[0,∞)`, then
`x ∉ closure (γ '' [0,∞))`. -/
theorem not_mem_closure_of_rat_bound {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) {x : ℂ} {c : ℝ}
    (hc : 0 < c) (h : ∀ q : ℚ, 0 ≤ (q : ℝ) → c ≤ ‖x - γ q‖) :
    x ∉ closure (γ '' Ici 0) := by
  have hall : ∀ s ∈ Ici (0 : ℝ), c ≤ ‖x - γ s‖ := by
    intro s hs
    have hseq : ∀ k : ℕ, ∃ q : ℚ, s < q ∧ (q : ℝ) < s + 1 / ((k : ℝ) + 1) := fun k =>
      exists_rat_btwn (lt_add_of_pos_right s (by positivity))
    choose q hq1 hq2 using hseq
    have hlim : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[Ici 0] s) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k =>
        (show (0 : ℝ) ≤ q k by linarith [hq1 k, mem_Ici.1 hs])⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun k => (hq1 k).le) (fun k => (hq2 k).le)
      have := (tendsto_const_nhds (x := s)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    have hcont : Continuous fun z : ℂ => ‖x - z‖ := (continuous_const.sub continuous_id).norm
    have ht := (hcont.tendsto (γ s)).comp ((hγ s hs).tendsto.comp hlim)
    have hs0 : (0 : ℝ) ≤ s := hs
    exact ge_of_tendsto ht (Eventually.of_forall fun k => h (q k) (by linarith [hq1 k]))
  have hsub : γ '' Ici 0 ⊆ {z | c ≤ ‖x - z‖} := by
    rintro _ ⟨s, hs, rfl⟩; exact hall s hs
  have hcl : IsClosed {z : ℂ | c ≤ ‖x - z‖} :=
    isClosed_le continuous_const (continuous_const.sub continuous_id).norm
  intro hx
  have := closure_minimal hsub hcl hx
  simp only [mem_ofPred_eq, sub_self, norm_zero] at this
  linarith

end Markov

section MarkovMain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **TRANS, Markov step.** For `0 < κ ≤ 4`, almost surely `0 ∉ closure (η '' [1,∞))`.
Rohde–Schramm, *Basic properties of SLE*, proof of Thm 7.1, p. 34. -/
theorem ae_zero_not_mem_closure_Ici_one {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, (0 : ℂ) ∉ closure (sleTrace κ B ω '' Ici 1) := by
  obtain ⟨B₀, hm, hc, h0, hB₀, hae⟩ := exists_good_version0 hB
  suffices h : ∀ᵐ ω ∂P, (0 : ℂ) ∉ closure (sleTrace κ B₀ ω '' Ici 1) by
    filter_upwards [h, hae] with ω h h'
    rwa [sleTrace_congr_of_eq h'] at h
  -- the shifted motion and its law on `CPath`
  have hB₁c : ∀ ω, Continuous fun u => B₀ (1 + u) ω - B₀ 1 ω := fun ω =>
    ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hB₁ : IsBrownianReal (fun u ω => B₀ (1 + u) ω - B₀ 1 ω) P := hB₀.shift 1
  have hB₁m : ∀ t, Measurable fun ω => B₀ (1 + t) ω - B₀ 1 ω := fun t => (hm _).sub (hm _)
  set Y : Ω → CPath := toCPath (fun u ω => B₀ (1 + u) ω - B₀ 1 ω) hB₁c with hYdef
  have hYm : Measurable Y := measurable_toCPath hB₁m hB₁c
  have hμ : IsBrownianReal canonBM (P.map Y) :=
    isBrownianReal_canonBM hB₁.toIsPreBrownianReal hB₁m hB₁c
  obtain ⟨η, -, hηm, -, hηeq⟩ := exists_measurable_sleTrace hμ hκ (by linarith)
  -- the event `E`
  set E : Set (ℝ × CPath) := {p | p.1 = 0 ∨ ∃ n : ℕ, ∀ q : ℚ, 0 ≤ (q : ℝ) →
    1 / ((n : ℝ) + 1) ≤ ‖(p.1 : ℂ) - η p.2 q‖} with hEdef
  have hE : MeasurableSet E := by
    have : E = {p : ℝ × CPath | p.1 = 0} ∪ ⋃ n : ℕ, ⋂ q : ℚ, {p : ℝ × CPath | 0 ≤ (q : ℝ) →
        1 / ((n : ℝ) + 1) ≤ ‖(p.1 : ℂ) - η p.2 q‖} := by
      ext p; simp [hEdef]
    rw [this]
    refine (measurableSet_eq_fun measurable_fst measurable_const).union
      (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => ?_)
    by_cases hq : 0 ≤ (q : ℝ)
    · simp only [hq, true_implies]
      exact measurableSet_le measurable_const ((Complex.measurable_ofReal.comp
        measurable_fst).sub ((measurable_pi_apply _).comp (hηm.comp measurable_snd))).norm
    · simp [hq]
  have hfix : ∀ a : ℝ, ∀ᵐ ω ∂P, (a, Y ω) ∈ E := by
    intro a
    by_cases ha : a = 0
    · exact ae_of_all _ fun ω => Or.inl ha
    have h2 : ∀ᵐ f ∂(P.map Y), (a, f) ∈ E := by
      filter_upwards [ae_not_mem_closure_sleTrace hμ hκ hκ4 ha, hηeq] with f hf heq
      right
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
        (isClosed_closure.isOpen_compl.mem_nhds hf)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine ⟨n, fun q hq => ?_⟩
      by_contra hlt
      push Not at hlt
      have hmem : η f q ∈ Metric.ball (a : ℂ) ε := by
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; linarith
      exact hball hmem (subset_closure ⟨q, hq, (heq hq).symm⟩)
    exact ae_of_ae_map hYm.aemeasurable h2
  -- the random base points, Borel functions of the past
  set W : Ω → ℝ → ℝ := fun ω => drive κ B₀ ω with hWdef
  have hWc : ∀ ω, Continuous (W ω) := fun ω => continuous_drive_path (hc ω)
  have htc : ∀ ω, Continuous (trev1 (W ω)) := fun ω => by
    have := hWc ω; unfold trev1; fun_prop
  set pth : Ω → C(Icc (0 : ℝ) 1, ℝ) := fun ω => Thm14WeldingData.pathC 1 (trev1 (W ω))
  set past : Ω → Set.Iic (1 : ℝ≥0) → ℝ := fun ω r => B₀ r ω
  have hpth : Measurable[MeasurableSpace.comap past MeasurableSpace.pi] pth := by
    let _ : MeasurableSpace Ω := MeasurableSpace.comap past MeasurableSpace.pi
    refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
    have hx : (1 - (x : ℝ)).toNNReal ≤ 1 := by
      rw [Real.toNNReal_le_one]; linarith [x.2.1]
    have e : (fun ω => pth ω x) = (fun p : Set.Iic (1 : ℝ≥0) → ℝ =>
        √κ * p ⟨(1 - (x : ℝ)).toNNReal, hx⟩ - √κ * p ⟨1, le_refl (1 : ℝ≥0)⟩) ∘ past := by
      funext ω
      show Thm14WeldingData.pathC 1 (trev1 (W ω)) x = _
      rw [pathC_apply_of_continuous (htc ω)]
      simp [trev1, hWdef, drive, past]
    rw [e]
    refine Measurable.comp ?_ (comap_measurable past)
    fun_prop
  have hpast_le : MeasurableSpace.comap past MeasurableSpace.pi ≤ ‹MeasurableSpace Ω› :=
    (show Measurable past from measurable_pi_iff.2 fun r => hm r).comap_le
  have hind0 := (isBrownianReal_shift_indep hB₀ κ 1).2.1
  have hg : ∀ G : C(Icc (0 : ℝ) 1, ℝ) → ℝ, Measurable G → ∀ᵐ ω ∂P, (G (pth ω), Y ω) ∈ E :=
    fun G hG => CharFun.ae_indep ((hG.comp hpth).mono hpast_le le_rfl) hYm
      (indepFun_toCPath_shift hind0 (hG.comp hpth) hB₁c) hE hfix
  have hηY : ∀ᵐ ω ∂P, EqOn (η (Y ω)) (sleTrace κ canonBM (Y ω)) (Ici 0) :=
    ae_of_ae_map hYm.aemeasurable hηeq
  have hsh1 : ∀ᵐ ω ∂P, ∀ t > (0 : ℝ),
      sleTrace κ (fun u ω => B₀ (1 + u) ω - B₀ 1 ω) ω t ≠ 0 := ae_sleTrace_ne_zero hB₁ hκ hκ4
  filter_upwards [hg _ (measurable_zmSeq zero_le_one), hg _ (measurable_zpSeq zero_le_one), hηY,
    hsh1, ae_radialGood_drive hB₀ hκ (by linarith), ae_sleTrace_simple_of_le_four hB₀ hκ hκ4,
    ae_fwdHull_eq_sleTrace_image_of_le_four hB₀ hκ hκ4, ae_shift_good hB₀ hκ hκ4 1]
    with ω hEm hEp hηω htip1 hgood hsimp hhull hshift
  intro hz
  simp only [NNReal.coe_one] at hshift
  have hsh : ∀ u : ℝ, 0 ≤ u →
      sleTrace κ canonBM (Y ω) u = trace (shiftDrive (W ω) 1) u := fun u hu => by
    rw [hYdef, sleTrace_toCPath]
    have := sleTrace_shift_eq κ (1 : ℝ≥0) (hc ω) hu
    simpa using this
  have hH1 : ∀ s > (0 : ℝ), trace (shiftDrive (W ω) 1) s ∈ H := fun s hs =>
    trace_mem_H_of_good hshift.1 hshift.2 (fun t ht => by rw [← hsh t ht.le]; exact htip1 t ht) hs
  -- Carathéodory at time 1
  set V := extIccPath zero_le_one (pth ω)
  have hVeq : EqOn (trev1 (W ω)) V (Icc 0 1) := fun r hr =>
    (extIccPath_pathC zero_le_one (htc ω) hr).symm
  have hVc : Continuous V := continuous_extIccPath _ _
  have hV0 : V 0 = 0 := by rw [← hVeq ⟨le_rfl, zero_le_one⟩]; simp [trev1]
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V hVc hV0 1 one_pos
    (isSimpleCurveHull_revHull_of_good hgood hsimp.1 hsimp.2 (hhull 1 zero_le_one) hVeq)
  have htip : trace (W ω) 1 ≠ 0 := fun h => by
    have := hsimp.2 1 one_pos; simp only [sleTrace] at this; rw [h] at this
    exact (lt_irrefl (0 : ℝ)) (by simp [H] at this)
  have hmne := zeroMinus_ne_zero_of_car hgood htip hVeq hF
  have hpne := zeroPlus_ne_zero_of_car hgood htip hVeq hF
  -- the base points avoid the shifted trace
  have havoid : ∀ a : ℝ, a ≠ 0 → (a, Y ω) ∈ E →
      (a : ℂ) ∉ closure (trace (shiftDrive (W ω) 1) '' Ici 0) := by
    rintro a ha (h | ⟨n, hn⟩)
    · exact absurd h ha
    refine not_mem_closure_of_rat_bound hshift.1.2.2.2.1 (c := 1 / ((n : ℝ) + 1))
      (by positivity) fun q hq => ?_
    have := hn q hq
    rwa [hηω hq, hsh _ hq] at this
  have hzm : zmSeq zero_le_one (pth ω) = zeroMinus V 1 := zmSeq_eq_of_car zero_le_one hF
  have hzp : zpSeq zero_le_one (pth ω) = zeroPlus V 1 := zpSeq_eq_of_car zero_le_one hF
  rw [hzm] at hEm
  rw [hzp] at hEp
  rcases base_cluster hgood hshift.1 hH1 hVc hVeq hF hz with h | h
  · exact havoid _ hmne hEm h
  · exact havoid _ hpne hEp h

end MarkovMain

end RS
end QuantumZipper
