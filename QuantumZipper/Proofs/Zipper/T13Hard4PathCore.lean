import QuantumZipper.Proofs.Zipper.T13Hard4PathDet
import QuantumZipper.Proofs.Zipper.T13Hard3PathTV
import QuantumZipper.Proofs.Zipper.T13Hard3Hit
import QuantumZipper.Proofs.Probability.Williams.MarkovHit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD4 (`HitPathIndStmt`), part 2: the strong Markov step at an intermediate level

Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.7 (p. 78): at the first time `τ`
the drift path `Y = √2 W + (α − Q)·` reaches `M − L`, the restarted path `W' = W (τ + ·) − W τ` is
a Brownian motion independent of `𝓕_τ` (strong Markov property, `StrongMarkov.indep_smPath`,
Le Gall GTM 274 Thm 2.20). The first passage of `Xc_L` is `τ + G` with `G` the first passage of
`Xc_M` along `W'`, and the re-centred path is read off `W'` (`T13Hard4PathDet.lean`). Hence
`(ρ_L, T_L) = (R, τ + G)` off small oscillation events, with `τ ⟂ (R, G)`, and
`D3Plus.tv_pair_indep_le` bounds the independence defect by these events and by the translation
defect of the law of `τ ≈ T_{L−M}` (`tv_perL`). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace T13Path

open Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → ℝ}

/-- The capped first visit of the drift path to a level is a stopping time of the past of `W`. -/
theorem isStoppingTime_hit (hb : GoodBM W P) (σ μ a : ℝ) (n : ℝ≥0) :
    IsStoppingTime (pastFilt W hb.meas)
      (fun ω => ((hittingBtwn (fun t ω => dpath σ μ W ω t) {a} 0 n ω : ℝ≥0) : WithTop ℝ≥0)) := by
  have hAd : Adapted (pastFilt W hb.meas) (fun t ω => dpath σ μ W ω t) := fun t =>
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => W r ω)
      ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
  exact ItoLite.isStoppingTime_hittingBtwn_of_isClosed hAd (continuous_dpath hb σ μ)
    isClosed_singleton n

/-- The first passage of `Xc_c` below `0` is the first visit of the drift path to `−c`. -/
theorem Tc_eq_first {α Q c : ℝ} {ω : Ω} {τ : ℝ≥0}
    (hτ : Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ) = -c)
    (habove : ∀ t < τ, -c < Real.sqrt 2 * W t ω + (α - Q) * (t : ℝ)) :
    ZoomRadial.Tc α Q c W ω = τ := by
  have hin : (τ : ℝ) ∈ {t : ℝ | 0 ≤ t ∧ ZoomRadial.Xc α Q c W ω t ≤ 0} := by
    refine ⟨τ.2, ?_⟩
    simp only [ZoomRadial.Xc, Real.toNNReal_coe]
    linarith
  refine le_antisymm (csInf_le ⟨0, fun s hs => hs.1⟩ hin) ?_
  refine le_csInf ⟨_, hin⟩ fun t ht => ?_
  by_contra hlt
  push Not at hlt
  have hlt' : t.toNNReal < τ := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht.1]; exact hlt
  have h := habove _ hlt'
  rw [Real.coe_toNNReal t ht.1] at h
  have h2 := ht.2
  simp only [ZoomRadial.Xc] at h2
  linarith

/-- `|B r| ≤ bmOsc B 0 s` for `r ≤ s`, for a path started at `0`. -/
theorem abs_le_bmOsc0 {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω = 0)
    {s r : ℝ≥0} (hr : r ≤ s) : |B r ω| ≤ bmOsc B 0 s ω := by
  have h := T13Hit.abs_sub_le_bmOsc_hit (B := B) hc (t := 0) (s := s) (r := r)
    ⟨zero_le, by simpa using hr⟩
  rwa [h0, sub_zero] at h

/-- **Per-level bound** for the independence defect of `(ρ_L, T_L)`. -/
theorem tv_perL (hb : GoodBM W P) {α Q : ℝ} (hQ : α < Q) {S M L : ℝ} {S1 N : ℝ≥0} (n : ℕ)
    (hS1 : S ≤ S1) (hS1p : 0 < S1) (hMS : (Q - α) * S < M) (hM0 : 0 < M)
    (hNM : M < (Q - α) * N) (hLM : M < L) (hn : L - M < (Q - α) * n) :
    TV.tvDist (P.map fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω),
        ZoomRadial.Tc α Q L W ω))
      ((P.map fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω)).prod
        (P.map fun ω => ZoomRadial.Tc α Q L W ω)) ≤
    5 * ENNReal.ofReal (2 * Real.exp (-(((Q - α) * n - (L - M)) / 2) ^ 2 /
        (2 * ((n : ℝ≥0) : ℝ)))) +
    3 * ENNReal.ofReal (2 * Real.exp (-((M - (Q - α) * S) / 2) ^ 2 / (2 * (S1 : ℝ)))) +
    5 * ENNReal.ofReal (2 * Real.exp (-(((Q - α) * N - M) / 2) ^ 2 / (2 * (N : ℝ)))) +
    2 * ⨆ x ∈ Icc (0 : ℝ) N, TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q (L - M) W ω)
      ((P.map fun ω => ZoomRadial.Tc α Q (L - M) W ω).map fun t => t + x) := by
  have hν0 : 0 < Q - α := by linarith
  have hs2 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2p : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hnpos : (0 : ℝ) < n := by
    have : 0 < (Q - α) * n := by linarith
    exact pos_of_mul_pos_right this hν0.le
  have hNpos : (0 : ℝ) < N := by
    have : 0 < (Q - α) * N := by linarith
    exact pos_of_mul_pos_right this hν0.le
  set a : ℝ := M - L with ha
  have ha0 : a < 0 := by rw [ha]; linarith
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => dpath (Real.sqrt 2) (α - Q) W ω t with hY
  have hYc : ∀ ω, Continuous (Y · ω) := continuous_dpath hb (Real.sqrt 2) (α - Q)
  have hYapp : ∀ t ω, Y t ω = Real.sqrt 2 * W t ω + (α - Q) * (t : ℝ) := fun _ _ => rfl
  set τ : Ω → ℝ≥0 := fun ω => hittingBtwn Y {a} 0 (n : ℝ≥0) ω with hτ
  have hstop : IsStoppingTime (pastFilt W hb.meas) (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_hit hb (Real.sqrt 2) (α - Q) a n
  have hτm : Measurable τ := StrongMarkov.measurable_of_isStoppingTime hstop
  have hind0 : ∀ t, Indep ((pastFilt W hb.meas) t)
      (MeasurableSpace.comap (StrongMarkov.smPath W (fun _ => t)) MeasurableSpace.pi) P :=
    fun t => StrongMarkov.indep_shift_of_le_past hb.pre (fun t => le_rfl) t
  set W' : ℝ≥0 → Ω → ℝ := StrongMarkov.smShift W τ with hW'
  have hW'BM : IsBrownianReal W' P :=
    StrongMarkov.isBrownianReal_smShift hb.pre hb.cont hb.meas hind0 hstop
  have hW'c : ∀ ω, Continuous fun s => W' s ω := fun ω =>
    ((hb.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hW'm : ∀ s, Measurable (W' s) := fun s =>
    StrongMarkov.measurable_smShift hb.cont hb.meas hτm s
  have hW'0 : ∀ ω, W' 0 ω = 0 := fun ω => by
    simp only [hW', StrongMarkov.smShift, add_zero, sub_self]
  have hW'app : ∀ ω s, W' s ω = W (τ ω + s) ω - W (τ ω) ω := fun _ _ => rfl
  -- the bad events
  set On : Set Ω := {ω | ((Q - α) * n - (L - M)) / 2 < bmOsc W 0 (n : ℝ≥0) ω} with hOn
  set OS : Set Ω := {ω | (M - (Q - α) * S) / 2 < bmOsc W' 0 S1 ω} with hOS
  set ON : Set Ω := {ω | ((Q - α) * N - M) / 2 < bmOsc W' 0 N ω} with hON
  -- (F1) off `On`, the level `a` is reached before `n`
  have hEn : ∀ ω, ω ∉ On → Y (τ ω) ω = a := by
    intro ω hω
    simp only [hOn, mem_ofPred_eq, not_lt] at hω
    have habs := abs_le_bmOsc0 (B := W) (hb.cont ω) (hb.zero ω) (le_refl (n : ℝ≥0))
    have hle : Y (n : ℝ≥0) ω ≤ a := by
      rw [hYapp]
      have h1 := (abs_le.1 (habs.trans hω)).2
      have h3 : Real.sqrt 2 * W (n : ℝ≥0) ω ≤ Real.sqrt 2 *
          (((Q - α) * n - (L - M)) / 2) := mul_le_mul_of_nonneg_left h1 hs2p
      have h4 : 0 ≤ ((Q - α) * n - (L - M)) / 2 := by linarith
      have h5 : Real.sqrt 2 * (((Q - α) * n - (L - M)) / 2) ≤
          2 * (((Q - α) * n - (L - M)) / 2) := mul_le_mul_of_nonneg_right hs2.le h4
      push_cast
      rw [ha]; nlinarith
    have hY0 : Y 0 ω = 0 := by rw [hYapp, hb.zero ω]; simp
    obtain ⟨j, hj, hja⟩ := intermediate_value_Icc' (zero_le (a := (n : ℝ≥0)))
      (hYc ω).continuousOn ⟨hle, by rw [hY0]; exact ha0.le⟩
    have hex : ∃ j ∈ Set.Icc (0 : ℝ≥0) (n : ℝ≥0), Y j ω ∈ ({a} : Set ℝ) := ⟨j, hj, hja⟩
    exact mem_hittingBtwn_of_isClosed hYc isClosed_singleton hex
  -- (F3) before `τ`, `Y > a`
  have habove : ∀ ω t, t < τ ω → a < Y t ω := by
    intro ω
    refine lt_of_lt_first_visit (hYc ω) ?_ fun t ht => ?_
    · rw [hYapp, hb.zero ω]; simp; exact ha0
    · have h := notMem_of_lt_hittingBtwn (u := Y) (s := ({a} : Set ℝ)) (n := (0 : ℝ≥0))
        (m := (n : ℝ≥0)) (ω := ω) ht zero_le
      exact fun heq => h (by rw [heq]; rfl)
  -- (F4) off `ON`, `Xc_M` along `W'` is `≤ 0` at time `N`
  have hhitN : ∀ ω, ω ∉ ON → ZoomRadial.Xc α Q M W' ω (N : ℝ) ≤ 0 := by
    intro ω hω
    simp only [hON, mem_ofPred_eq, not_lt] at hω
    have habs := abs_le_bmOsc0 (B := W') (hW'c ω) (hW'0 ω) (le_refl N)
    have h1 := (abs_le.1 (habs.trans hω)).2
    have h4 : 0 ≤ ((Q - α) * N - M) / 2 := by linarith
    have h3 : Real.sqrt 2 * W' N ω ≤ Real.sqrt 2 * (((Q - α) * N - M) / 2) :=
      mul_le_mul_of_nonneg_left h1 hs2p
    have h5 : Real.sqrt 2 * (((Q - α) * N - M) / 2) ≤ 2 * (((Q - α) * N - M) / 2) :=
      mul_le_mul_of_nonneg_right hs2.le h4
    simp only [ZoomRadial.Xc, Real.toNNReal_coe]
    nlinarith
  -- (F5) off `OS`, `Xc_M` along `W'` stays positive on `[0, S]`
  have hposS : ∀ ω, ω ∉ OS → ∀ v : ℝ, 0 ≤ v → v ≤ S → 0 < ZoomRadial.Xc α Q M W' ω v := by
    intro ω hω v hv0 hvS
    simp only [hOS, mem_ofPred_eq, not_lt] at hω
    have hvS1 : v.toNNReal ≤ S1 := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hvS.trans hS1
    have habs := abs_le_bmOsc0 (B := W') (hW'c ω) (hW'0 ω) hvS1
    have h1 := (abs_le.1 (habs.trans hω)).1
    have h4 : 0 < (M - (Q - α) * S) / 2 := by linarith
    have h3 : Real.sqrt 2 * (-((M - (Q - α) * S) / 2)) ≤ Real.sqrt 2 * W' v.toNNReal ω :=
      mul_le_mul_of_nonneg_left h1 hs2p
    have h5 : Real.sqrt 2 * ((M - (Q - α) * S) / 2) < 2 * ((M - (Q - α) * S) / 2) :=
      mul_lt_mul_of_pos_right hs2 h4
    have h6 : (Q - α) * v ≤ (Q - α) * S := mul_le_mul_of_nonneg_left hvS hν0.le
    simp only [ZoomRadial.Xc]
    nlinarith
  -- the good event
  have hgood : ∀ ω, ω ∉ On ∪ OS ∪ ON →
      (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω) =
          ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W' M ω) ∧
        ZoomRadial.Tc α Q L W ω = (τ ω : ℝ) + ZoomRadial.Tc α Q M W' ω) := by
    intro ω hω
    simp only [mem_union, not_or] at hω
    obtain ⟨⟨hωn, hωS⟩, hωN⟩ := hω
    have hE := hEn ω hωn
    have hM : M = L + (Real.sqrt 2 * W (τ ω) ω + (α - Q) * (τ ω : ℝ)) := by
      rw [← hYapp, hE, ha]; ring
    have hab : ∀ t < τ ω, M - L < Real.sqrt 2 * W t ω + (α - Q) * (t : ℝ) := by
      intro t ht; rw [← hYapp]; exact habove ω t ht
    have hhit : ∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q M W' ω v ≤ 0 :=
      ⟨N, N.2, hhitN ω hωN⟩
    have hT := Tc_split (hW'app ω) (hW'c ω) hM hM0 hab hhit
    have hSG : S ≤ ZoomRadial.Tc α Q M W' ω := by
      refine le_csInf hhit fun v hv => ?_
      by_contra hlt
      push Not at hlt
      exact absurd hv.2 (not_le.2 (hposS ω hωS v hv.1 hlt.le))
    exact ⟨trunc_split (hW'app ω) hM hT hSG, hT⟩
  -- measurability
  have hpairW := measurable_truncTc (fun ω => hb.cont ω) hb.meas α Q L S
  have hpairW' := measurable_truncTc hW'c hW'm α Q M S
  have hσm : Measurable fun ω => (τ ω : ℝ) := measurable_coe_nnreal_real.comp hτm
  -- independence of `τ` and the restarted data
  have hind : IndepFun (fun ω => (τ ω : ℝ)) (fun ω =>
      (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W' M ω), ZoomRadial.Tc α Q M W' ω)) P := by
    have hI := StrongMarkov.indep_smPath hb.pre hb.cont hb.meas hind0 hstop
    have hσT : Measurable[hstop.measurableSpace] (fun ω => (τ ω : ℝ)) :=
      measurable_coe_nnreal_real.comp ((WithTop.measurable_untopA).comp hstop.measurable)
    have hRGm : Measurable[MeasurableSpace.comap (StrongMarkov.smPath W τ) MeasurableSpace.pi]
        (fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W' M ω),
          ZoomRadial.Tc α Q M W' ω)) := by
      letI m' : MeasurableSpace Ω := MeasurableSpace.comap (StrongMarkov.smPath W τ)
        MeasurableSpace.pi
      have hm' : ∀ s, Measurable[m'] (W' s) := fun s =>
        (measurable_pi_apply s).comp (comap_measurable (StrongMarkov.smPath W τ))
      exact @measurable_truncTc Ω m' W' hW'c hm' α Q M S
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hI hσT.comap_le)
      hRGm.comap_le
  -- the abstract bound
  have hmain := D3Plus.tv_pair_indep_le P
    (ρ := fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω))
    (T := fun ω => ZoomRadial.Tc α Q L W ω) (σ := fun ω => (τ ω : ℝ))
    (G := fun ω => ZoomRadial.Tc α Q M W' ω)
    (R := fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W' M ω))
    hpairW.fst.aemeasurable hpairW.snd.aemeasurable hσm hpairW'.fst hpairW'.snd
    (fun ω => ZoomRadial.Tc_nonneg α Q M W' ω) hind (On ∪ OS ∪ ON)
    (ae_of_all _ fun ω hω => hgood ω hω)
  -- the tails
  have htn : P On ≤ ENNReal.ofReal (2 * Real.exp (-(((Q - α) * n - (L - M)) / 2) ^ 2 /
      (2 * ((n : ℝ≥0) : ℝ)))) :=
    BMOsc.bmOsc_tail hb.pre hb.meas hb.cont 0 (n : ℝ≥0) (by exact_mod_cast hnpos)
      (by linarith)
  have htS : P OS ≤ ENNReal.ofReal (2 * Real.exp (-((M - (Q - α) * S) / 2) ^ 2 /
      (2 * (S1 : ℝ)))) :=
    BMOsc.bmOsc_tail hW'BM.toIsPreBrownianReal hW'm hW'c 0 S1 hS1p (by linarith)
  have htN : P ON ≤ ENNReal.ofReal (2 * Real.exp (-(((Q - α) * N - M) / 2) ^ 2 /
      (2 * (N : ℝ)))) :=
    BMOsc.bmOsc_tail hW'BM.toIsPreBrownianReal hW'm hW'c 0 N (by exact_mod_cast hNpos)
      (by linarith)
  have hPD : P (On ∪ OS ∪ ON) ≤ P On + P OS + P ON :=
    (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  -- the translation term
  set μσ := P.map fun ω => (τ ω : ℝ) with hμσ
  set μT := P.map fun ω => ZoomRadial.Tc α Q (L - M) W ω with hμT
  set Sup := ⨆ x ∈ Icc (0 : ℝ) N, TV.tvDist μT (μT.map fun t => t + x) with hSup
  have hTm' : Measurable fun ω => ZoomRadial.Tc α Q (L - M) W ω :=
    D3Plus.measurable_Tc_of_cont (fun ω => hb.cont ω) (fun t => hb.meas _) α Q (L - M)
  have hc : TV.tvDist μσ μT ≤ P On := by
    refine D3Plus.tvDist_map_le_of_ae_eq_off hσm.aemeasurable hTm'.aemeasurable On
      (ae_of_all _ fun ω hω => ?_)
    have hE := hEn ω hω
    refine (Tc_eq_first (c := L - M) ?_ ?_).symm
    · rw [← hYapp, hE, ha]; ring
    · intro t ht; rw [← hYapp]; have := habove ω t ht; rw [ha] at this; linarith
  set Gset : Set ((ℝ → ℝ) × ℝ) := {p | (N : ℝ) < p.2} with hGset
  have hGsetm : MeasurableSet Gset := measurableSet_lt measurable_const measurable_snd
  have hh : ∀ g : ℝ, TV.tvDist (μT.map fun t => t + max g 0) μT ≤
      Sup + Gset.indicator 1 ((fun _ => 0 : ℝ → ℝ → ℝ) 0, g) := by
    intro g
    by_cases hg : (N : ℝ) < g
    · have : Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) ((fun _ => 0 : ℝ → ℝ → ℝ) 0, g) = 1 := by
        simp [hGset, Set.indicator_of_mem, hg]
      rw [this]
      exact TV.tvDist_le_one.trans le_add_self
    · push Not at hg
      refine le_add_right ?_
      rw [TV.tvDist_comm]
      exact le_iSup₂ (f := fun x (_ : x ∈ Icc (0 : ℝ) N) => TV.tvDist μT (μT.map fun t => t + x))
        (max g 0) ⟨le_max_right _ _, max_le hg N.2⟩
  have htrans : ∀ q : ((ℝ → ℝ) × ℝ) × ((ℝ → ℝ) × ℝ), D3Plus.transTV μσ q.1.2 q.2.2 ≤
      (P On + P On) + ((Sup + Gset.indicator 1 q.1) + (Sup + Gset.indicator 1 q.2)) := by
    intro q
    have hf : ∀ g : ℝ, Measurable fun t : ℝ => t + max g 0 := fun g => measurable_add_const _
    have e1 : TV.tvDist (μσ.map fun t => t + max q.1.2 0) (μT.map fun t => t + max q.1.2 0)
        ≤ P On := (TV.tvDist_map_le (hf _)).trans hc
    have e4 : TV.tvDist (μT.map fun t => t + max q.2.2 0) (μσ.map fun t => t + max q.2.2 0)
        ≤ P On := (TV.tvDist_map_le (hf _)).trans (TV.tvDist_comm.le.trans hc)
    have i1 : Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) ((fun _ => 0 : ℝ → ℝ → ℝ) 0, q.1.2) =
        Gset.indicator 1 q.1 := by simp [hGset, Set.indicator_apply]
    have i2 : Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) ((fun _ => 0 : ℝ → ℝ → ℝ) 0, q.2.2) =
        Gset.indicator 1 q.2 := by simp [hGset, Set.indicator_apply]
    have e2 := hh q.1.2
    have e3 : TV.tvDist μT (μT.map fun t => t + max q.2.2 0) ≤
        Sup + Gset.indicator 1 ((fun _ => 0 : ℝ → ℝ → ℝ) 0, q.2.2) :=
      TV.tvDist_comm.le.trans (hh q.2.2)
    rw [i1] at e2
    rw [i2] at e3
    unfold D3Plus.transTV
    calc _ ≤ TV.tvDist (μσ.map fun t => t + max q.1.2 0) (μT.map fun t => t + max q.1.2 0) +
          (TV.tvDist (μT.map fun t => t + max q.1.2 0) μT +
            (TV.tvDist μT (μT.map fun t => t + max q.2.2 0) +
              TV.tvDist (μT.map fun t => t + max q.2.2 0)
                (μσ.map fun t => t + max q.2.2 0))) :=
          TV.tvDist_triangle.trans (add_le_add le_rfl (TV.tvDist_triangle.trans
            (add_le_add le_rfl TV.tvDist_triangle)))
      _ ≤ P On + ((Sup + Gset.indicator 1 q.1) + ((Sup + Gset.indicator 1 q.2) + P On)) :=
          add_le_add e1 (add_le_add e2 (add_le_add e3 e4))
      _ = _ := by ring
  set ν := P.map fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W' M ω),
    ZoomRadial.Tc α Q M W' ω) with hνdef
  have hνG : ν Gset ≤ P ON := by
    rw [hνdef, Measure.map_apply hpairW' hGsetm]
    refine measure_mono fun ω hω => ?_
    by_contra hωN
    have hle : ZoomRadial.Tc α Q M W' ω ≤ N :=
      csInf_le ⟨0, fun s hs => hs.1⟩ ⟨N.2, hhitN ω hωN⟩
    exact absurd hω (not_lt.2 hle)
  have hind1 : Measurable (Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞)) :=
    measurable_const.indicator hGsetm
  have hfst : ∫⁻ q, Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.1 ∂(ν.prod ν) = ν Gset := by
    rw [← lintegral_map hind1 measurable_fst, Measure.map_fst_prod, measure_univ, one_smul,
      lintegral_indicator_one hGsetm]
  have hsnd : ∫⁻ q, Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.2 ∂(ν.prod ν) = ν Gset := by
    rw [← lintegral_map hind1 measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
      lintegral_indicator_one hGsetm]
  have hm1 : Measurable fun q : ((ℝ → ℝ) × ℝ) × ((ℝ → ℝ) × ℝ) =>
      Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.1 := hind1.comp measurable_fst
  have hm2 : Measurable fun q : ((ℝ → ℝ) × ℝ) × ((ℝ → ℝ) × ℝ) =>
      Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.2 := hind1.comp measurable_snd
  have hI : ∫⁻ q, D3Plus.transTV μσ q.1.2 q.2.2 ∂(ν.prod ν) ≤
      (P On + P On) + ((Sup + P ON) + (Sup + P ON)) := by
    calc ∫⁻ q, D3Plus.transTV μσ q.1.2 q.2.2 ∂(ν.prod ν)
        ≤ ∫⁻ q, ((P On + P On) + ((Sup + Gset.indicator 1 q.1) +
            (Sup + Gset.indicator 1 q.2))) ∂(ν.prod ν) := lintegral_mono htrans
      _ = (P On + P On) + ((Sup + ν Gset) + (Sup + ν Gset)) := by
          have hca : ∀ (c : ℝ≥0∞) (f : ((ℝ → ℝ) × ℝ) × ((ℝ → ℝ) × ℝ) → ℝ≥0∞),
              ∫⁻ q, c + f q ∂(ν.prod ν) = c + ∫⁻ q, f q ∂(ν.prod ν) := by
            intro c f
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          have hsplit : ∫⁻ q, (Sup + Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.1) +
              (Sup + Gset.indicator 1 q.2) ∂(ν.prod ν) =
              ∫⁻ q, (Sup + Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.1) ∂(ν.prod ν) +
              ∫⁻ q, (Sup + Gset.indicator (1 : (ℝ → ℝ) × ℝ → ℝ≥0∞) q.2) ∂(ν.prod ν) :=
            lintegral_add_left (measurable_const.add hm1) _
          rw [hca, hsplit, hca, hca, hfst, hsnd]
      _ ≤ _ := by gcongr
  calc _ ≤ 3 * P (On ∪ OS ∪ ON) + ∫⁻ q, D3Plus.transTV μσ q.1.2 q.2.2 ∂(ν.prod ν) := hmain
    _ ≤ 3 * (ENNReal.ofReal (2 * Real.exp (-(((Q - α) * n - (L - M)) / 2) ^ 2 /
            (2 * ((n : ℝ≥0) : ℝ)))) +
          ENNReal.ofReal (2 * Real.exp (-((M - (Q - α) * S) / 2) ^ 2 / (2 * (S1 : ℝ)))) +
          ENNReal.ofReal (2 * Real.exp (-(((Q - α) * N - M) / 2) ^ 2 / (2 * (N : ℝ))))) +
        ((ENNReal.ofReal (2 * Real.exp (-(((Q - α) * n - (L - M)) / 2) ^ 2 /
            (2 * ((n : ℝ≥0) : ℝ)))) +
          ENNReal.ofReal (2 * Real.exp (-(((Q - α) * n - (L - M)) / 2) ^ 2 /
            (2 * ((n : ℝ≥0) : ℝ))))) +
          ((Sup + ENNReal.ofReal (2 * Real.exp (-(((Q - α) * N - M) / 2) ^ 2 / (2 * (N : ℝ))))) +
            (Sup + ENNReal.ofReal (2 * Real.exp (-(((Q - α) * N - M) / 2) ^ 2 /
              (2 * (N : ℝ))))))) := by
        refine add_le_add (mul_le_mul_right (hPD.trans (add_le_add (add_le_add htn htS) htN)) 3)
          (hI.trans ?_)
        gcongr
    _ = _ := by ring

end T13Path
end QuantumZipper
