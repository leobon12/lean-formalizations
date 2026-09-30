import QuantumZipper.Proofs.Zipper.T13Hard4TransBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD4: uniform translation smoothness of first passage laws (`HitTransUnifStmt`)

Markov property at the deterministic time `x`: on the event that the path has not reached `0`
before `x` and stays in a bounded window, `T_L = x + T_{L+Z}(W')` with `W' = W (x + ·) − W x` a
Brownian motion independent of `Z = √2 W x − ν x`. Hence the law of `T_L` is, up to small
probabilities, the `Z`-mixture of the laws of `x + T_{L+z}`, and the hitting-level spread bound
`T13Hit.tv_good_le_hit` (Cameron–Martin shift coupling, `T13Hard3Hit.lean`) makes each
`law T_{L+z}` close to `law T_L`, uniformly in `|z| ≤ C`. Own argument (the textbook route is the
inverse-Gaussian density, Karatzas–Shreve §3.5.C, which needs the reflection principle and
Girsanov, absent from the repository).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace T13Trans

open Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → ℝ}

/-- A good Brownian motion reaches every level: a.s. `Xc_c` eventually drops below `0`. -/
theorem ae_hit (hb : GoodBM W P) (hW : IsBrownianReal W P) {α Q : ℝ} (hQ : α < Q) (c : ℝ) :
    ∀ᵐ ω ∂P, ∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q c W ω v ≤ 0 := by
  rw [ae_iff]
  set ν := Q - α with hνdef
  have hν : 0 < ν := by rw [hνdef]; linarith
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun δ' hδ' _ => ?_
  have hδ : (0 : ℝ) < δ' := hδ'
  set m : ℝ := 2 * |c| / ν + 64 / (ν ^ 2 * δ') + 1 with hm
  obtain ⟨hcm, hx⟩ := D3Plus.horizon_ok (c := |c|) (m := m) hν hδ (abs_nonneg c) (by linarith)
  have hm0 : 0 < m := by
    have : 0 ≤ 2 * |c| / ν := by positivity
    have : 0 < 64 / (ν ^ 2 * δ') := by positivity
    linarith
  set H : ℝ≥0 := ⟨m, hm0.le⟩ with hH
  have hHv : (H : ℝ) = m := rfl
  have hsub : {ω | ¬∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q c W ω v ≤ 0} ⊆
      {ω | (ν * m - |c|) / 2 < bmOsc W 0 H ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_exists, not_and, not_le] at hω ⊢
    by_contra hle
    push Not at hle
    have habs := T13Path.abs_le_bmOsc0 (B := W) (hb.cont ω) (hb.zero ω) (le_refl H)
    have h1 := (abs_le.1 (habs.trans hle)).2
    have h0 := hω m hm0.le
    have hs2 : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h4 : 0 ≤ (ν * m - |c|) / 2 := by linarith
    have h3 : Real.sqrt 2 * W H ω ≤ Real.sqrt 2 * ((ν * m - |c|) / 2) :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
    have h5 : Real.sqrt 2 * ((ν * m - |c|) / 2) ≤ 2 * ((ν * m - |c|) / 2) :=
      mul_le_mul_of_nonneg_right hs2.le h4
    have hcabs : c ≤ |c| := le_abs_self c
    have hmH : m.toNNReal = H := by
      apply NNReal.coe_injective; rw [Real.coe_toNNReal _ hm0.le]; rfl
    simp only [ZoomRadial.Xc, hmH] at h0
    rw [hνdef] at h3 h5 h4
    nlinarith
  have htail := BMOsc.bmOsc_tail hb.pre hb.meas hb.cont 0 H (by rw [← NNReal.coe_pos, hHv]; exact hm0)
    (by linarith : (0 : ℝ) < (ν * m - |c|) / 2)
  rw [zero_add]
  refine (measure_mono hsub).trans (htail.trans ?_)
  rw [hHv]
  have := D3Plus.tail_small_path hδ hm0 hx
  rwa [ENNReal.ofReal_coe_nnreal] at this

/-- The level-shift bound, uniformly for `|z| ≤ C`. -/
theorem tv_level_shift_le (hW : IsBrownianReal W P) (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {α Q L C z : ℝ}
    (hQ : α < Q) (hLC : 2 * C < L) (hz : |z| ≤ C) :
    TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q (L + z) W ω)
      (P.map fun ω => ZoomRadial.Tc α Q L W ω) ≤
    ENNReal.ofReal (Real.sqrt (Real.exp (C ^ 2 * (Q - α) / (L - C)) - 1)) +
      ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * (L - C)))) := by
  have hν : 0 < Q - α := by linarith
  have hC0 : 0 ≤ C := (abs_nonneg z).trans hz
  have hLC0 : 0 < L - C := by linarith
  have hz2 : z ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  have hmono : ∀ {c L' : ℝ}, 0 < L' → L - C ≤ L' → c ^ 2 ≤ C ^ 2 →
      ENNReal.ofReal (Real.sqrt (Real.exp (c ^ 2 * (Q - α) / L') - 1)) +
        ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * L'))) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (C ^ 2 * (Q - α) / (L - C)) - 1)) +
        ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * (L - C)))) := by
    intro c L' hL' hLL hc2
    refine add_le_add (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
      (ENNReal.ofReal_le_ofReal ?_)
    · have : c ^ 2 * (Q - α) / L' ≤ C ^ 2 * (Q - α) / (L - C) := by
        calc c ^ 2 * (Q - α) / L' ≤ C ^ 2 * (Q - α) / L' :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hν.le) hL'.le
          _ ≤ C ^ 2 * (Q - α) / (L - C) :=
              div_le_div_of_nonneg_left (by positivity) hLC0 hLL
      linarith [Real.exp_le_exp.2 this]
    · have : -((Q - α) / 16 * L') ≤ -((Q - α) / 16 * (L - C)) := by
        have := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ (Q - α) / 16)
        linarith
      linarith [Real.exp_le_exp.2 this]
  rcases le_or_gt 0 z with hz0 | hz0
  · rw [TV.tvDist_comm]
    refine (T13Hit.tv_good_le_hit hW hWm hWc hW0 hQ hz0 (by linarith)).trans ?_
    exact hmono (by linarith) (by linarith) hz2
  · have hL' : 0 < L + z := by
      have := neg_abs_le z; linarith
    have h := T13Hit.tv_good_le_hit (P := P) hW hWm hWc hW0 (L := L + z) (c := -z) hQ
      (by linarith) hL'
    rw [show L + z + -z = L by ring] at h
    refine h.trans (hmono hL' ?_ (by rw [neg_sq]; exact hz2))
    have := neg_abs_le z; linarith

/-- **Per-translation bound.** -/
theorem tv_trans_perx (hb : GoodBM W P) (hW : IsBrownianReal W P) {α Q L x C0 C : ℝ}
    {N' : ℝ≥0} (hQ : α < Q) (hx0 : 0 ≤ x) (hxN : x ≤ N') (hN' : 0 < N') (hC0 : 0 < C0)
    (hC : Real.sqrt 2 * C0 + (Q - α) * N' ≤ C) (hLC : 2 * C < L) :
    TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L W ω)
      ((P.map fun ω => ZoomRadial.Tc α Q L W ω).map fun t => t + x) ≤
    2 * ENNReal.ofReal (2 * Real.exp (-(C0 ^ 2) / (2 * (N' : ℝ)))) +
      (ENNReal.ofReal (Real.sqrt (Real.exp (C ^ 2 * (Q - α) / (L - C)) - 1)) +
        ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * (L - C))))) := by
  have hν : 0 < Q - α := by linarith
  have hs2p : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hC0' : 0 ≤ C := le_trans (by positivity) hC
  set τ : ℝ≥0 := x.toNNReal with hτ
  have hτv : (τ : ℝ) = x := Real.coe_toNNReal x hx0
  have hτN : τ ≤ N' := by rw [← NNReal.coe_le_coe, hτv]; exact hxN
  have hind0 : ∀ t, Indep ((pastFilt W hb.meas) t)
      (MeasurableSpace.comap (StrongMarkov.smPath W (fun _ => t)) MeasurableSpace.pi) P :=
    fun t => StrongMarkov.indep_shift_of_le_past hb.pre (fun t => le_rfl) t
  have hstop : IsStoppingTime (pastFilt W hb.meas) (fun _ : Ω => ((τ : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_const _ _
  set W' : ℝ≥0 → Ω → ℝ := StrongMarkov.smShift W (fun _ => τ) with hW'
  have hW'BM : IsBrownianReal W' P :=
    StrongMarkov.isBrownianReal_smShift hb.pre hb.cont hb.meas hind0 hstop
  have hW'c : ∀ ω, Continuous fun s => W' s ω := fun ω =>
    ((hb.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hW'm : ∀ s, Measurable (W' s) := fun s =>
    StrongMarkov.measurable_smShift hb.cont hb.meas measurable_const s
  have hW'0 : ∀ ω, W' 0 ω = 0 := fun ω => by
    simp only [hW', StrongMarkov.smShift, add_zero, sub_self]
  have hgood' : GoodBM W' P := ⟨hW'BM.toIsPreBrownianReal, hW'm, hW'c, hW'0⟩
  set Z : Ω → ℝ := fun ω => Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ) with hZ
  -- independence of `Z` and the restarted path
  have hZpast : Measurable[(pastFilt W hb.meas) τ] Z :=
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic τ) => W r ω)
      ⟨τ, Set.mem_Iic.2 le_rfl⟩).const_mul _).add_const _
  have hZm : Measurable Z := hZpast.mono ((pastFilt W hb.meas).le τ) le_rfl
  have hpCm : Measurable (pathC W' hW'c) := measurable_pathC hW'c hW'm
  have hindZ : IndepFun Z (pathC W' hW'c) P := by
    have hCm' : Measurable[MeasurableSpace.comap (StrongMarkov.smPath W (fun _ => τ))
        MeasurableSpace.pi] (pathC W' hW'c) := by
      letI m' : MeasurableSpace Ω := MeasurableSpace.comap
        (StrongMarkov.smPath W (fun _ => τ)) MeasurableSpace.pi
      have hm' : ∀ s, Measurable[m'] (W' s) := fun s =>
        (measurable_pi_apply s).comp (comap_measurable (StrongMarkov.smPath W (fun _ => τ)))
      exact @measurable_pathC Ω m' W' hW'c hm'
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (hind0 τ) hZpast.comap_le)
      hCm'.comap_le
  have hjoint : P.map (fun ω => (Z ω, pathC W' hW'c ω)) =
      (P.map Z).prod (P.map (pathC W' hW'c)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hpCm.aemeasurable).1 hindZ
  -- the bad events
  set B : Set Ω := {ω | C0 < bmOsc W 0 N' ω} with hB
  set Nh : Set Ω := {ω | ¬∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q (L + C) W' ω v ≤ 0} with hNh
  have hNh0 : P Nh = 0 := by
    have h := ae_hit hgood' hW'BM hQ (L + C)
    rwa [ae_iff] at h
  have hoffB : ∀ ω, ω ∉ B → ∀ t : ℝ≥0, t ≤ N' → |W t ω| ≤ C0 := by
    intro ω hω t ht
    simp only [hB, mem_ofPred_eq, not_lt] at hω
    exact (T13Path.abs_le_bmOsc0 (B := W) (hb.cont ω) (hb.zero ω) ht).trans hω
  have hZC : ∀ ω, ω ∉ B → |Z ω| ≤ C := by
    intro ω hω
    have h1 := hoffB ω hω τ hτN
    have h2 : |Real.sqrt 2 * W τ ω| ≤ Real.sqrt 2 * C0 := by
      rw [abs_mul, abs_of_nonneg hs2p]; exact mul_le_mul_of_nonneg_left h1 hs2p
    have h3 : |(α - Q) * (τ : ℝ)| ≤ (Q - α) * N' := by
      rw [hτv, abs_mul, abs_of_nonneg hx0, abs_of_neg (by linarith : α - Q < 0)]
      have : (Q - α) * x ≤ (Q - α) * N' := mul_le_mul_of_nonneg_left hxN hν.le
      linarith
    calc |Z ω| ≤ |Real.sqrt 2 * W τ ω| + |(α - Q) * (τ : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hsplit : ∀ ω, ω ∉ B ∪ Nh →
      ZoomRadial.Tc α Q L W ω = ZoomRadial.Tc α Q (L + Z ω) W' ω + x := by
    intro ω hω
    simp only [mem_union, not_or] at hω
    obtain ⟨hωB, hωN⟩ := hω
    have hpos : ∀ t : ℝ, 0 ≤ t → t < τ → 0 < ZoomRadial.Xc α Q L W ω t := by
      intro t ht0 htτ
      have htN : t.toNNReal ≤ N' := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal t ht0]; rw [hτv] at htτ; linarith
      have h1 := (abs_le.1 (hoffB ω hωB _ htN)).1
      have h2 : Real.sqrt 2 * (-C0) ≤ Real.sqrt 2 * W t.toNNReal ω :=
        mul_le_mul_of_nonneg_left h1 hs2p
      have h3 : (Q - α) * t ≤ (Q - α) * N' := by
        rw [hτv] at htτ; exact mul_le_mul_of_nonneg_left (by linarith) hν.le
      simp only [ZoomRadial.Xc]
      nlinarith
    have hhit : ∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q (L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ)))
        W' ω v ≤ 0 := by
      simp only [hNh, mem_ofPred_eq, not_not] at hωN
      obtain ⟨v, hv0, hv⟩ := hωN
      refine ⟨v, hv0, ?_⟩
      have := (abs_le.1 (hZC ω hωB)).2
      simp only [ZoomRadial.Xc] at hv ⊢
      simp only [hZ] at this
      linarith
    have h := Tc_split' (τ := τ) (W' := W') (fun s => rfl) (hW'c ω) hpos hhit
    rw [h, add_comm]; exact congrArg₂ (· + ·) rfl hτv
  -- A1: coupling
  have hTm : Measurable fun ω => ZoomRadial.Tc α Q L W ω :=
    D3Plus.measurable_Tc_of_cont (fun ω => hb.cont ω) (fun t => hb.meas _) α Q L
  have hF : Measurable fun ω => PhiC2 α Q L (Z ω, pathC W' hW'c ω) :=
    (measurable_PhiC2 α Q L).comp (hZm.prodMk hpCm)
  have hA1 : TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L W ω)
      (P.map fun ω => PhiC2 α Q L (Z ω, pathC W' hW'c ω) + x) ≤ P B := by
    refine (D3Plus.tvDist_map_le_of_ae_eq_off hTm.aemeasurable (hF.add_const x).aemeasurable
      (B ∪ Nh) (ae_of_all _ fun ω hω => hsplit ω hω)).trans ?_
    exact (measure_union_le _ _).trans (by rw [hNh0, add_zero])
  -- A2: mixture
  set μZ := P.map Z with hμZ
  set μC := P.map (pathC W' hW'c) with hμC
  have hμT : (P.map fun ω => ZoomRadial.Tc α Q L W ω) = μC.map (PhiC α Q L) := by
    have e : (P.map fun ω => ZoomRadial.Tc α Q L W ω) =
        (P.map (pathC W fun ω => hb.cont ω)).map (PhiC α Q L) := by
      rw [Measure.map_map (measurable_PhiC α Q L) (measurable_pathC (fun ω => hb.cont ω) hb.meas)]
      rfl
    rw [e, hμC, map_pathC_eq hb.pre hgood'.pre hb.meas hW'm (fun ω => hb.cont ω) hW'c]
  have hμT' : μC.map (PhiC α Q L) = (μZ.prod μC).map fun p => PhiC α Q L p.2 := by
    rw [show (fun p : ℝ × CPathT => PhiC α Q L p.2) = PhiC α Q L ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_PhiC α Q L) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]
  have hmix : (P.map fun ω => PhiC2 α Q L (Z ω, pathC W' hW'c ω) + x) =
      ((μZ.prod μC).map (PhiC2 α Q L)).map fun t => t + x := by
    rw [hμZ, hμC, ← hjoint, Measure.map_map (measurable_PhiC2 α Q L) (hZm.prodMk hpCm),
      Measure.map_map (measurable_add_const x) ((measurable_PhiC2 α Q L).comp
        (hZm.prodMk hpCm))]
    rfl
  set β := ENNReal.ofReal (Real.sqrt (Real.exp (C ^ 2 * (Q - α) / (L - C)) - 1)) +
    ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * (L - C)))) with hβ
  set Aset : Set ℝ := {z | C < |z|} with hAset
  have hAm : MeasurableSet Aset := measurableSet_lt measurable_const continuous_abs.measurable
  have hsec : ∀ z : ℝ, TV.tvDist (μC.map fun w => PhiC2 α Q L (z, w))
      (μC.map fun w => PhiC α Q L (z, w).2) ≤ β + Aset.indicator 1 z := by
    intro z
    have e1 : (μC.map fun w => PhiC2 α Q L (z, w)) =
        P.map fun ω => ZoomRadial.Tc α Q (L + z) W' ω := by
      rw [show (fun w => PhiC2 α Q L (z, w)) = PhiC2 α Q L ∘ Prod.mk z from rfl, hμC,
        Measure.map_map ((measurable_PhiC2 α Q L).comp measurable_prodMk_left) hpCm]
      rfl
    have e2 : (μC.map fun w => PhiC α Q L (z, w).2) = P.map fun ω => ZoomRadial.Tc α Q L W' ω := by
      rw [show (fun w => PhiC α Q L (z, w).2) = PhiC α Q L from rfl, hμC,
        Measure.map_map (measurable_PhiC α Q L) hpCm]
      rfl
    rw [e1, e2]
    by_cases hz : C < |z|
    · have : Aset.indicator (1 : ℝ → ℝ≥0∞) z = 1 := by
        simp [hAset, Set.indicator_of_mem, hz]
      rw [this]; exact TV.tvDist_le_one.trans le_add_self
    · push Not at hz
      exact (tv_level_shift_le hW'BM hW'm hW'c hW'0 hQ hLC hz).trans le_self_add
  have hA2 : TV.tvDist (((μZ.prod μC).map (PhiC2 α Q L)).map fun t => t + x)
      ((P.map fun ω => ZoomRadial.Tc α Q L W ω).map fun t => t + x) ≤ β + P B := by
    rw [hμT, hμT']
    refine (TV.tvDist_map_le (measurable_add_const x)).trans ?_
    refine (tv_map_prod_le_gen μZ μC (measurable_PhiC2 α Q L)
      ((measurable_PhiC α Q L).comp measurable_snd)).trans ?_
    refine (lintegral_mono hsec).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_indicator_one hAm]
    refine add_le_add le_rfl ?_
    rw [hμZ, Measure.map_apply hZm hAm]
    refine measure_mono fun ω hω => ?_
    by_contra hωB
    exact absurd hω (not_lt.2 (hZC ω hωB))
  have htail : P B ≤ ENNReal.ofReal (2 * Real.exp (-(C0 ^ 2) / (2 * (N' : ℝ)))) :=
    BMOsc.bmOsc_tail hb.pre hb.meas hb.cont 0 N' hN' hC0
  calc _ ≤ TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L W ω)
        (P.map fun ω => PhiC2 α Q L (Z ω, pathC W' hW'c ω) + x) +
      TV.tvDist (P.map fun ω => PhiC2 α Q L (Z ω, pathC W' hW'c ω) + x)
        ((P.map fun ω => ZoomRadial.Tc α Q L W ω).map fun t => t + x) := TV.tvDist_triangle
    _ ≤ P B + (β + P B) := add_le_add hA1 (by rw [hmix]; exact hA2)
    _ ≤ _ := by
      calc P B + (β + P B) = 2 * P B + β := by ring
        _ ≤ _ := add_le_add (mul_le_mul_right htail 2) le_rfl

end T13Trans

namespace D3Plus

open T13Trans

/-- **`HitTransUnifStmt` holds**: the first passage law is asymptotically translation invariant
in total variation, uniformly on compact sets of translations. -/
theorem hitTransUnifStmt_holds : HitTransUnifStmt := by
  intro α Q Ω _ P _ b hb hQ N
  obtain ⟨W, hWm, hWc, hW0, hW, hWb⟩ := RS.exists_good_version0 hb
  have hgood : Williams.GoodBM W P := ⟨hW.toIsPreBrownianReal, hWm, hWc, hW0⟩
  have hmap : ∀ L, (P.map fun ω => ZoomRadial.Tc α Q L b ω) =
      P.map fun ω => ZoomRadial.Tc α Q L W ω := fun L =>
    Measure.map_congr (hWb.mono fun ω h => D3Plus.Tc_congr fun t => (h t).symm)
  simp only [hmap]
  set ν := Q - α with hνdef
  have hν : 0 < ν := by rw [hνdef]; linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ 3 * ENNReal.ofReal δ ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · have hε0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      refine ⟨ε.toReal / 3, by positivity, le_of_eq ?_⟩
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal htop]
      rw [show ENNReal.ofReal 3 = (3 : ℝ≥0∞) by norm_num]
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  set N' : ℝ≥0 := ⟨max N 0 + 1, by positivity⟩ with hN'
  have hN'v : (N' : ℝ) = max N 0 + 1 := rfl
  have hN'p : 0 < N' := by rw [← NNReal.coe_pos, hN'v]; positivity
  set C0 : ℝ := Real.sqrt (4 * (N' : ℝ) / δ) + 1 with hC0
  have hC0p : 0 < C0 := by positivity
  have htail : ENNReal.ofReal (2 * Real.exp (-(C0 ^ 2) / (2 * (N' : ℝ)))) ≤ ENNReal.ofReal δ := by
    refine tail_small_path hδ (by exact_mod_cast hN'p) ?_
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * (N' : ℝ) / δ)
    have hs0 := Real.sqrt_nonneg (4 * (N' : ℝ) / δ)
    have e : 2 / δ * (2 * (N' : ℝ)) = 4 * (N' : ℝ) / δ := by ring
    rw [e]; nlinarith
  set C : ℝ := Real.sqrt 2 * C0 + ν * N' with hC
  -- the level-shift error term tends to `0`
  have h1 : Tendsto (fun L : ℝ => L - C) atTop atTop := by
    simp only [sub_eq_add_neg]; exact tendsto_atTop_add_const_right _ _ tendsto_id
  have h2 : Tendsto (fun L : ℝ => C ^ 2 * ν / (L - C)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have h3 : Tendsto (fun L : ℝ => Real.sqrt (Real.exp (C ^ 2 * ν / (L - C)) - 1)) atTop
      (𝓝 0) := by
    have hc : Continuous fun y : ℝ => Real.sqrt (Real.exp y - 1) :=
      Real.continuous_sqrt.comp (Real.continuous_exp.sub continuous_const)
    have := (hc.tendsto 0).comp h2
    simp only [Real.exp_zero, sub_self, Real.sqrt_zero] at this
    exact this
  have h4 : Tendsto (fun L : ℝ => 2 * Real.exp (-(ν / 16 * (L - C)))) atTop (𝓝 0) := by
    have h5 : Tendsto (fun L : ℝ => ν / 16 * (L - C)) atTop atTop :=
      h1.const_mul_atTop (by positivity)
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h5).const_mul 2
    simpa using this
  have hβ : Tendsto (fun L : ℝ =>
      ENNReal.ofReal (Real.sqrt (Real.exp (C ^ 2 * ν / (L - C)) - 1)) +
        ENNReal.ofReal (2 * Real.exp (-(ν / 16 * (L - C))))) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal h3).add (ENNReal.tendsto_ofReal h4)
    simpa using this
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hβ _ (ENNReal.ofReal_pos.2 hδ),
    eventually_gt_atTop (2 * C)] with L hL hLC
  refine iSup₂_le fun x hx => ?_
  have hxN : x ≤ (N' : ℝ) := by rw [hN'v]; have := le_max_left N 0; linarith [hx.2]
  refine (tv_trans_perx hgood hW hQ hx.1 hxN hN'p hC0p le_rfl hLC).trans ?_
  calc 2 * ENNReal.ofReal (2 * Real.exp (-(C0 ^ 2) / (2 * (N' : ℝ)))) +
        (ENNReal.ofReal (Real.sqrt (Real.exp (C ^ 2 * (Q - α) / (L - C)) - 1)) +
          ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * (L - C)))))
      ≤ 2 * ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add (mul_le_mul_right htail 2) hL
    _ = 3 * ENNReal.ofReal δ := by ring
    _ ≤ ε := hδε

/-- **`HitPathIndStmt` holds.** -/
theorem hitPathIndStmt_holds : HitPathIndStmt :=
  hitPathInd_of_transUnif hitTransUnifStmt_holds

end D3Plus
end QuantumZipper
