/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoClusterCode

/-!
# Lemma 3.4: recurrence of the gap ratio for every separated two-force law

Packet PROVE-ZHAN-GT4-B2. Source: Astra, *Follow-up proofs*, §B.3 (E11)–(E13), L1210–L1213 and L1265–L1273
(ruling R38); additional note Lemma 3.4, L1486–L1488: "`X` returns to its original value `x` after every finite
stopping time". In chordal coordinates the strip gap `X = Re ψ(p) − ξ` of the upper mark is `log(R/L)`
(`L = W − V_L`, `R = V_R − W`), so this is the recurrence of the gap ratio `R/L` after every time.

PROVE-ZHAN-GT4-B proved it for the two-seed law (`twoSeedRatioRecurrenceStatement`, from the Jacobi martingale problem
of the log-clock angle). It transfers to every separated law exactly as two-seed transience did
(`codeLaw_nt_eq_zero_of_ratio`): restart the two-seed law when `R = rL`; the future is a separated law on the ray of
words `(−L, rL)`; the canonical probability of non-recurrence is dilation invariant along the ray and vanishes for the
future. The recurrence event reads the force points of the future, so this file first exposes them in the restart
kernel (`restart_core_state`, a copy of `Sec7.RandRestart.restart_core` with two more conclusions).

## Main results

* `restart_core_state`, `measure_restart_stateEvent`, `measure_eventOf_eq_codeLaw_state`: code events of the whole
  restarted state `(w, v_L, v_R, ζ)`.
* `RecEvent`, `recCodeSet`, `RealRec`: the recurrence event (sign changes of `R − rL` at arbitrarily late times).
* `ae_realRec_twoSeed`: two-seed recurrence after every time.
* `IsIntegratedSLEEvolution.ae_realRec_sep`: **recurrence for every separated two-force law** with weights
  `≥ κ/2 − 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper.StrongMarkov

/-! ### The restart kernel for state events -/

section StateCode

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restart at a stopping time, in code form, with the force points** (`Sec7.RandRestart.restart_core`, whose
proof is copied, with the decoded force points of the restarted code added to the conclusion). -/
theorem restart_core_state (ha : 0 < a) (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j)) :
    ∃ (st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (g : Ω → ℝ≥0 → ℝ) (c : Ω → XCode nL nR),
      Measurable st ∧ Measurable g ∧
      (∀ E : Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet E →
        P (A ∩ (fun ω => (st ω, g ω)) ⁻¹' E) = ∫⁻ ω in A, wienerPath (Prod.mk (st ω) ⁻¹' E) ∂P) ∧
      ∀ᵐ ω ∂P, ω ∈ A → st ω = wordAt W VL VR T ω ∧ SepStart (st ω) ∧
        c ω ∈ CRel a (st ω).1 (st ω).2 ρL ρR ∧ (c ω).1 = enc (g ω) ∧ cζ (c ω) = ζ ω - T ω ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω → cw (c ω) t = W (T ω + t) ω - W (T ω) ω) ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω → ∀ i, cvL (c ω) i t = VL i (T ω + t) ω - W (T ω) ω) ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω → ∀ j, cvR (c ω) j t = VR j (T ω + t) ω - W (T ω) ω) ∧
        HasLimW (c ω) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlimE := hE.ae_tendsto_threshold ha
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨Bv, hBvm, hBvc, hBvF, hBvae⟩ := exists_continuous_version hBF
  have h𝓕𝓖 : 𝓕 ≤ usualAugmentation 𝓕 P := Ito.le_usualAugmentation 𝓕 P
  have hT𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T ω : WithTop ℝ≥0) :=
    fun u => h𝓕𝓖 u _ (hT u)
  have hle𝓖 : hT.measurableSpace ≤ hT𝓖.measurableSpace :=
    Ito.measurableSpace_le_of_filtration_le h𝓕𝓖 hT hT𝓖
  -- the state at `T`, through the progressive versions
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    ((fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω),
      fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω) with hst
  have hstT : Measurable[hT.measurableSpace] st :=
    @measurable_start_aux nL nR Ω hT.measurableSpace _ _ _
      (measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT)
      (fun i => measurable_eval_stop (isStronglyProgressive_progVersion (hVLad i)) hT)
      (fun j => measurable_eval_stop (isStronglyProgressive_progVersion (hVRad j)) hT)
  have hstm : Measurable st := hstT.mono (hT.measurableSpace_le) le_rfl
  -- the restarted Brownian path: Wiener law, independent of `𝓖_T`
  set g : Ω → ℝ≥0 → ℝ := smPath Bv T with hg
  have hgm : Measurable g := measurable_smPath hBvc hBvm (measurable_of_isStoppingTime hT)
  have hind := indep_future hBvF
  have hlaw : P.map g = wienerPath :=
    map_path_eq_wienerPath
      (isBrownianReal_smShift hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖).toIsPreBrownianReal
      hgm
  have hindT := indep_smPath hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖
  have hpair : Measurable fun ω => (st ω, g ω) := hstm.prodMk hgm
  have hjoint : (P.restrict A).map (fun ω => (st ω, g ω)) =
      ((P.restrict A).map st).prod wienerPath := by
    refine (Measure.prod_eq fun D F hD hF => ?_).symm
    rw [Measure.map_apply hpair (hD.prod hF), Measure.map_apply hstm hD, ← hlaw,
      Measure.map_apply hgm hF, Measure.restrict_apply (hpair (hD.prod hF)),
      Measure.restrict_apply (hstm hD)]
    have hDA : MeasurableSet[hT𝓖.measurableSpace] (st ⁻¹' D ∩ A) :=
      hle𝓖 _ ((hstT hD).inter hA)
    have e : (fun ω => (st ω, g ω)) ⁻¹' (D ×ˢ F) ∩ A = (st ⁻¹' D ∩ A) ∩ g ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [e]
    exact (Indep_iff _ _ _).1 hindT _ _ hDA ⟨F, hF, rfl⟩
  refine ⟨st, g, fun ω => codeOf (wordAt W VL VR T ω).1 (wordAt W VL VR T ω).2 (smShift Bv T)
      (fun t ω' => W (T ω' + t) ω' - W (T ω') ω') (fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω') (fun ω' => ζ ω' - T ω') ω,
    hstm, hgm, fun E hEm => ?_, ?_⟩
  · rw [inter_comm, ← Measure.restrict_apply (hpair hEm), ← Measure.map_apply hpair hEm, hjoint,
      Measure.prod_apply hEm]
    rw [lintegral_map (measurable_measure_prodMk_left hEm) hstm]
  · filter_upwards [hpath, hBvae, hlimE] with ω hp hb hl hωA
    obtain ⟨hTζ, hT0⟩ := hAT ω hωA
    have h0 := restart_values hp hTζ
    have hst_eq : st ω = wordAt W VL VR T ω := by
      simp only [hst, wordAt, h0.1, h0.2.1, h0.2.2]
    have hr := hp.restart hTζ
    have hb' : (fun t => B (T ω + t) ω - B (T ω) ω) = fun t => smShift Bv T t ω := by
      funext t; simp only [smShift, hb]
    rw [hb'] at hr
    have hsep : SepStart (wordAt W VL VR T ω) := by
      rcases hT0 with hT0 | hsx
      · exact sepStart_restart hp hT0 hTζ
      · exact sepStart_restart_of_sep hp hsx hTζ
    have hrl := restart_tendsto hTζ hl
    have hcode := codeOf_mem_cRel_of_path (Ω := Ω) (ω := ω)
      (xL := fun i => VL i (T ω) ω - W (T ω) ω) (xR := fun j => VR j (T ω) ω - W (T ω) ω)
      (W := fun t ω' => W (T ω' + t) ω' - W (T ω') ω')
      (VL := fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (VR := fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω')
      (B := smShift Bv T) (B' := smShift Bv T) (ζ := fun ω' => ζ ω' - T ω') hr
      (((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const) (fun t => rfl) hrl
    rw [hst_eq]
    exact ⟨rfl, hsep, hcode.1, rfl, rfl, fun t ht => (hcode.2 t ht).1, fun t ht => (hcode.2 t ht).2.1,
      fun t ht => (hcode.2 t ht).2.2.1, hasLimW_of_tendsto (fun t ht => (hcode.2 t ht).1) hrl⟩


/-- **The conditional law of a coded event of the restarted state** `(W_{T+·} − W_T, V_{T+·} − W_T, ζ − T)`. -/
theorem measure_restart_stateEvent (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    {S : Set (XCode nL nR)}
    {Ψ : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΨ : ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ S ↔ Ψ (cw x) (cvL x) (cvR x) (cζ x)))
    (hΨ : ∀ (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) →
      Ψ w vL vR τ → Ψ w' vL' vR' τ) :
    P (A ∩ {ω | Ψ (fun t => W (T ω + t) ω - W (T ω) ω) (fun i t => VL i (T ω + t) ω - W (T ω) ω)
        (fun j t => VR j (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)}) =
      ∫⁻ ω in A, codeLaw a ρL ρR S (wordAt W VL VR T ω) ∂P := by
  obtain ⟨st, g, c, -, -, hlaw, hid⟩ := restart_core_state ha hE hT hA hAT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hset : (A ∩ {ω | Ψ (fun t => W (T ω + t) ω - W (T ω) ω) (fun i t => VL i (T ω + t) ω - W (T ω) ω)
      (fun j t => VR j (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)} : Set Ω) =ᵐ[P]
      A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSetS a ρL ρR S := by
    filter_upwards [hid] with ω h
    have key : ∀ hωA : ω ∈ A, (Ψ (fun t => W (T ω + t) ω - W (T ω) ω)
        (fun i t => VL i (T ω + t) ω - W (T ω) ω) (fun j t => VR j (T ω + t) ω - W (T ω) ω) (ζ ω - T ω) ↔
        (st ω, g ω) ∈ restartSetS a ρL ρR S) := fun hωA => by
      obtain ⟨-, hsep, hc, hc1, hcζ, hcw, hcL, hcR, hcl⟩ := h hωA
      have e1 : (st ω, g ω) ∈ restartSetS a ρL ρR S ↔
          (((st ω).1, (st ω).2), (c ω).1) ∈ lawSetS a ρL ρR S := by
        rw [hc1]; exact Iff.rfl
      rw [e1, mem_lawSetS_iff hsep hc, hSΨ _ (mem_cRelF_iff.2 hc).1 hcl, hcζ]
      exact ⟨hΨ _ _ _ _ _ _ _ fun t ht => ⟨(hcw t ht).symm, fun i => (hcL t ht i).symm,
          fun j => (hcR t ht j).symm⟩,
        hΨ _ _ _ _ _ _ _ fun t ht => ⟨hcw t ht, hcL t ht, hcR t ht⟩⟩
    exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  rw [measure_congr hset, hlaw _ (measurableSet_restartSetS hS)]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hid] with ω h hωA
  rw [(h hωA).1]
  rfl

/-- **The canonical law of a coded state event**: every integrated evolution from a separated start has
`P {Ψ(W, V_L, V_R, ζ)} = codeLaw S (xL, xR)`. -/
theorem measure_eventOf_eq_codeLaw_state [IsProbabilityMeasure P] (ha : 0 < a) (hsep : ∀ i j, xL i < xR j)
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)}
    {Ψ : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΨ : ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ S ↔ Ψ (cw x) (cvL x) (cvR x) (cζ x)))
    (hΨ : ∀ (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) →
      Ψ w vL vR τ → Ψ w' vL' vR' τ) :
    P {ω | Ψ (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)} =
      codeLaw a ρL ρR S (xL, xR) := by
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  rw [codeLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSetS hS).preimage measurable_prodMk_left)]
  refine measure_congr ?_
  filter_upwards [ae_codeOf_mem ha h hc hae, h.ae_tendsto_threshold ha] with ω ⟨hmem, hdec⟩ hl
  set x := codeOf xL xR B' W VL VR ζ ω with hx
  have hx1 : x.1 = enc (B' · ω) := rfl
  have hxζ : cζ x = ζ ω := rfl
  have hxF : x ∈ CRelF a ρL ρR := (mem_cRelF_iff.2 hmem).1
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  refine propext ?_
  show Ψ (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) ↔
    ((xL, xR), enc (B' · ω)) ∈ lawSetS a ρL ρR S
  rw [← hx1, mem_lawSetS_iff hsep hmem, hSΨ x hxF hxl, hxζ]
  exact ⟨hΨ _ _ _ _ _ _ _ fun t ht => ⟨((hdec t ht).1).symm, fun i => ((hdec t ht).2.1 i).symm,
      fun j => ((hdec t ht).2.2.1 j).symm⟩,
    hΨ _ _ _ _ _ _ _ fun t ht => ⟨(hdec t ht).1, (hdec t ht).2.1, (hdec t ht).2.2.1⟩⟩

end StateCode

/-! ### The recurrence event -/

/-- The ratio gap `R − rL` of a one-mark-per-side state (`L = w − v_L`, `R = v_R − w`). -/
def rgap (r : ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (vR 0 t - w t) - r * (w t - vL 0 t)

/-- **The recurrence event** of a state: infinite horizon, and `R − rL` takes both signs at arbitrarily late rational
times. -/
def RecEvent (r : ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ ∀ N : ℕ, ∃ q₁ q₂ : ℚ≥0, (N : ℝ≥0) ≤ q₁ ∧ (N : ℝ≥0) ≤ q₂ ∧ rgap r w vL vR q₁ < 0 ∧
    0 < rgap r w vL vR q₂

/-- The Borel set of solution codes with the recurrence event. -/
def recCodeSet (r : ℝ) : Set (XCode 1 1) := {x | RecEvent r (cw x) (cvL x) (cvR x) (cζ x)}

theorem measurableSet_recCodeSet (r : ℝ) : MeasurableSet (recCodeSet r) := by
  have hg : ∀ q : ℚ≥0, Measurable fun x : XCode 1 1 => rgap r (cw x) (cvL x) (cvR x) q := fun q =>
    (((measurable_dec_at (measurable_code_vR 0) q).sub (measurable_dec_at measurable_code_w q)).sub
      (measurable_const.mul ((measurable_dec_at measurable_code_w q).sub
        (measurable_dec_at (measurable_code_vL 0) q))))
  have e : recCodeSet r = {x : XCode 1 1 | cζ x = ⊤} ∩ ⋂ N : ℕ, ⋃ q₁ : ℚ≥0, ⋃ q₂ : ℚ≥0,
      ({_x : XCode 1 1 | (N : ℝ≥0) ≤ q₁ ∧ (N : ℝ≥0) ≤ q₂} ∩
        ({x | rgap r (cw x) (cvL x) (cvR x) q₁ < 0} ∩ {x | 0 < rgap r (cw x) (cvL x) (cvR x) q₂})) := by
    ext x
    simp only [recCodeSet, RecEvent, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, and_assoc]
  rw [e]
  exact (measurable_cζ (measurableSet_singleton ⊤)).inter (MeasurableSet.iInter fun N =>
    MeasurableSet.iUnion fun q₁ => MeasurableSet.iUnion fun q₂ => (MeasurableSet.const _).inter
      ((measurableSet_lt (hg q₁) measurable_const).inter (measurableSet_lt measurable_const (hg q₂))))

theorem recEvent_congr (r : ℝ) (w w' : ℝ≥0 → ℝ) (vL vL' vR vR' : Fin 1 → ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hR : RecEvent r w vL vR τ) : RecEvent r w' vL' vR' τ := by
  obtain ⟨hτ, h2⟩ := hR
  subst hτ
  have hw : w = w' := funext fun t => (h t ENNReal.coe_lt_top).1
  have hL : vL = vL' := funext fun i => funext fun t => (h t ENNReal.coe_lt_top).2.1 i
  have hRR : vR = vR' := funext fun j => funext fun t => (h t ENNReal.coe_lt_top).2.2 j
  subst hw hL hRR
  exact ⟨rfl, h2⟩

/-- The recurrence in real time: `R − rL` takes both signs after every time. -/
def RealRec (r : ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) : Prop :=
  ∀ N : ℝ≥0, ∃ t₁ t₂ : ℝ≥0, N ≤ t₁ ∧ N ≤ t₂ ∧ rgap r w vL vR t₁ < 0 ∧ 0 < rgap r w vL vR t₂

theorem recEvent_top_iff {r : ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ}
    (hc : Continuous (rgap r w vL vR)) : RecEvent r w vL vR ⊤ ↔ RealRec r w vL vR := by
  constructor
  · rintro ⟨-, h⟩ N
    obtain ⟨M, hM⟩ := exists_nat_ge (N : ℝ)
    obtain ⟨q₁, q₂, h1, h2, h3, h4⟩ := h M
    have hN : N ≤ (M : ℝ≥0) := by rw [← NNReal.coe_le_coe]; exact_mod_cast hM
    exact ⟨q₁, q₂, hN.trans h1, hN.trans h2, h3, h4⟩
  · intro h
    refine ⟨rfl, fun N => ?_⟩
    obtain ⟨t₁, t₂, h1, h2, h3, h4⟩ := h N
    have l1 := ((hc.tendsto t₁).comp (Sec7.tendsto_ratAbove t₁)).eventually (gt_mem_nhds h3)
    have l2 := ((hc.tendsto t₂).comp (Sec7.tendsto_ratAbove t₂)).eventually (lt_mem_nhds h4)
    obtain ⟨m₁, hm₁⟩ := l1.exists
    obtain ⟨m₂, hm₂⟩ := l2.exists
    exact ⟨Sec7.ratAbove t₁ m₁, Sec7.ratAbove t₂ m₂, h1.trans (Sec7.le_ratAbove t₁ m₁),
      h2.trans (Sec7.le_ratAbove t₂ m₂), hm₁, hm₂⟩

/-- The real-time recurrence is invariant under Brownian scaling of the state. -/
theorem realRec_dilate {c : ℝ≥0} (hc : c ≠ 0) (r : ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) :
    RealRec r (fun t => (√(c : ℝ))⁻¹ * w (c * t)) (fun i t => (√(c : ℝ))⁻¹ * vL i (c * t))
        (fun j t => (√(c : ℝ))⁻¹ * vR j (c * t)) ↔ RealRec r w vL vR := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hcc : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
  set l : ℝ := (√(c : ℝ))⁻¹ with hl
  have hl0 : 0 < l := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hg : ∀ t, rgap r (fun t => l * w (c * t)) (fun i t => l * vL i (c * t)) (fun j t => l * vR j (c * t)) t =
      l * rgap r w vL vR (c * t) := fun t => by simp only [rgap]; ring
  simp only [RealRec, hg]
  constructor
  · intro h N
    obtain ⟨t₁, t₂, h1, h2, h3, h4⟩ := h (N / c)
    refine ⟨c * t₁, c * t₂, ?_, ?_, ?_, (mul_pos_iff_of_pos_left hl0).1 h4⟩
    rotate_left 2
    · by_contra hge
      push Not at hge
      exact absurd h3 (not_lt.2 (mul_nonneg hl0.le hge))
    · rwa [div_le_iff₀ hcc, mul_comm] at h1
    · rwa [div_le_iff₀ hcc, mul_comm] at h2
  · intro h N
    obtain ⟨t₁, t₂, h1, h2, h3, h4⟩ := h (c * N)
    refine ⟨t₁ / c, t₂ / c, ?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hcc, mul_comm]; exact h1
    · rw [le_div_iff₀ hcc, mul_comm]; exact h2
    · rw [mul_div_cancel₀ t₁ hc]; exact mul_neg_of_pos_of_neg hl0 h3
    · rw [mul_div_cancel₀ t₂ hc]; exact mul_pos hl0 h4

/-! ### Two-seed recurrence after every time -/

section TwoSeed

open Sec2.Jacobi Sec2.TwoSeed

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

theorem ae_exists_ratio_lt_after [IsProbabilityMeasure P] (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {r : ℝ} (hr : 0 < r) {t₀ : ℝ≥0} (ht₀ : 0 < t₀) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, t₀ ≤ t ∧ VR 0 t ω - W t ω < r * (W t ω - VL 0 t ω) := by
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good hE
  have hJ := isJacobiMP_angleG hE hρL hρR hGm hGc hgood hκ
  set α : ℝ := 1 / (1 + r) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by linarith)]; linarith
  have hρL' : ∀ i, -2 < ρL i := fun i => by rw [Fin.fin_one_eq_zero i]; exact hρL
  have hρR' : ∀ i, -2 < ρR i := fun i => by rw [Fin.fin_one_eq_zero i]; exact hρR
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, ∃ u, (q : ℝ) ≤ u ∧ α < angleG G W VL VR ζ u ω := by
    rw [ae_all_iff]; intro q
    exact jmp_ae_exists_gt hJ hκ (by linarith) (by linarith) hα0 hα1 q
  filter_upwards [hrat, hζ, ae_of_all _ fun ω (h : ω ∈ G) => h, measure_eq_zero_iff_ae_notMem.1 hGc]
    with ω hq hζω _ hGω
  have hωG : ω ∈ G := by simpa using hGω
  obtain ⟨hp, -, -⟩ := hgood ω hωG
  rw [hζω] at hp
  -- the separation at time `t₀` and a rational log-level above it
  have h1 : ((t₀ : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hsep1 := sepN_pos hp h1 ht₀
  obtain ⟨q, hq1⟩ := exists_rat_gt (Real.log (sepN (fun i t => VL i t ω) (fun i t => VR i t ω) t₀))
  obtain ⟨u, hqu, hαu⟩ := hq q
  simp only [angleG, hωG, ↓reduceIte] at hαu
  rw [hζω] at hαu
  -- a time at which the separation is `e^u`
  obtain ⟨t₁, ht₁, hut₁⟩ := sepN_unbounded_of_top hp (Real.exp u)
  obtain ⟨hτt₁, hτ⟩ := hitTime_spec hp ht₁ hut₁
  set τ := hitTime (fun i t => VL i t ω) (fun i t => VR i t ω) ⊤ u with hτdef
  refine ⟨τ, ?_, ?_⟩
  · -- `τ ≥ t₀`: otherwise the separation at `τ` would be below that at `t₀`
    by_contra hlt
    push Not at hlt
    have hlt' := sepN_lt_sepN hp (show ((t₀ : ℝ≥0) : ℝ≥0∞) < ⊤ from h1) hlt le_rfl
    rw [hτ] at hlt'
    have : Real.log (sepN (fun i t => VL i t ω) (fun i t => VR i t ω) t₀) < u := lt_of_lt_of_le hq1 hqu
    have := Real.exp_lt_exp.2 this
    rw [Real.exp_log hsep1] at this
    linarith
  · -- `L > α e^u = α (L + R)`, so `R < r L`
    have hlog : α < (W τ ω - VL 0 τ ω) / Real.exp u := hαu
    rw [lt_div_iff₀ (Real.exp_pos u), ← hτ] at hlog
    simp only [sepN] at hlog
    have hrα : r * α = 1 - α := by rw [hα]; field_simp; ring
    have h3 := mul_lt_mul_of_pos_left hlog hr
    rw [← mul_assoc, hrα, sub_mul, one_mul] at h3
    linarith


/-- **Two-seed recurrence after every time**: for the two-seed law with admissible weights and `r > 0`, almost surely
`R − rL` takes both signs after every time. -/
theorem ae_realRec_twoSeed [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, RealRec r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) := by
  obtain ⟨hwL, hwR⟩ : κ / 2 - 2 ≤ ρL 0 ∧ κ / 2 - 2 ≤ ρR 0 := by
    have h1 := hadm.1 (-1) (by norm_num) ⟨0, by norm_num⟩
    have h2 := hadm.2 0 le_rfl ⟨0, le_rfl⟩
    have hf1 : (Finset.univ.filter fun i : Fin 1 => (-1 : ℝ) < (fun _ => (0 : ℝ)) i) = Finset.univ := by
      ext i; simp
    have hf2 : (Finset.univ.filter fun i : Fin 1 => (fun _ => (0 : ℝ)) i ≤ 0) = Finset.univ := by
      ext i; simp
    rw [hf1, Fin.sum_univ_one] at h1
    rw [hf2, Fin.sum_univ_one] at h2
    exact ⟨h1, h2⟩
  have hρL : -2 < ρL 0 := by linarith
  have hρR : -2 < ρR 0 := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ Zhan.isOrderedForceWord_zero hadm hE).mono
      fun _ h => h.1
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have hz : -(fun _ : Fin 1 => (0 : ℝ)) = fun _ => 0 := by funext i; simp
  rw [hz] at hEr
  have hlt := ae_all_iff.2 fun n : ℕ =>
    ae_exists_ratio_lt_after hκ hρL hρR hE hζ hr (t₀ := (n : ℝ≥0) + 1) (by positivity)
  have hgt := ae_all_iff.2 fun n : ℕ =>
    ae_exists_ratio_lt_after hκ hρR hρL hEr hζ (inv_pos.2 hr) (t₀ := (n : ℝ≥0) + 1) (by positivity)
  filter_upwards [hlt, hgt] with ω hl hg N
  obtain ⟨n, hn⟩ := exists_nat_ge (N : ℝ)
  have hNn : N ≤ (n : ℝ≥0) + 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  obtain ⟨t₁, ht₁, h₁⟩ := hl n
  obtain ⟨t₂, ht₂, h₂⟩ := hg n
  simp only [Pi.neg_apply] at h₂
  have h₂' : r * (W t₂ ω - VL 0 t₂ ω) < VR 0 t₂ ω - W t₂ ω := by
    have := mul_lt_mul_of_pos_left h₂ hr
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    linarith
  exact ⟨t₁, t₂, hNn.trans ht₁, hNn.trans ht₂, by simp only [rgap]; linarith,
    by simp only [rgap]; linarith⟩

end TwoSeed

/-! ### The restart of the two-seed law at the ratio hitting time, for state events -/

section Restart

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem eq_zero_of_restart_ratio_state [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓖 W VL VR B ζ) {r : ℝ}
    {N : Set Ω} (hNm : ∀ t, MeasurableSet[𝓖 t] N) (hN0 : P N = 0)
    (hgood : ∀ ω ∉ N, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω) ∧ (∀ t : ℝ≥0, 0 < t → VL 0 t ω < W t ω) ∧
      ∃ t : ℝ≥0, 1 ≤ t ∧ ratioGap r W VL VR t ω = 0)
    {S : Set (XCode 1 1)}
    {Ψ : (ℝ≥0 → ℝ) → (Fin 1 → ℝ≥0 → ℝ) → (Fin 1 → ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΨ : ∀ x ∈ CRelF κ ρL ρR, HasLimW x → (x ∈ S ↔ Ψ (cw x) (cvL x) (cvR x) (cζ x)))
    (hΨ : ∀ (w w' : ℝ≥0 → ℝ) (vL vL' : Fin 1 → ℝ≥0 → ℝ) (vR vR' : Fin 1 → ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) →
      Ψ w vL vR τ → Ψ w' vL' vR' τ)
    (hfut : ∀ ω ∉ N, ∀ m : ℝ≥0, 1 ≤ m → ¬ Ψ (fun t => W (m + t) ω - W m ω)
      (fun i t => VL i (m + t) ω - W m ω) (fun j t => VR j (m + t) ω - W m ω) (ζ ω - m))
    {K : ℝ≥0∞} (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR S ((fun _ => -L), fun _ => r * L) = K) : K = 0 := by
  set Y := ratioGap r W VL VR with hY
  -- adaptedness of the processes defining the hitting time
  have hYa : AdaptedBefore 𝓖 ζ (posAfter Y) :=
    adaptedBefore_of_eq (fun t p => max ((p.2.2 - p.1) - r * (p.1 - p.2.1)) (1 - (t : ℝ)))
      (fun t => by fun_prop) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0) fun t ω => rfl
  have hYa' : AdaptedBefore 𝓖 ζ (posAfter (-Y)) :=
    adaptedBefore_of_eq (fun t p => max (-((p.2.2 - p.1) - r * (p.1 - p.2.1))) (1 - (t : ℝ)))
      (fun t => by fun_prop) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0) fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0)
      fun _ _ => rfl
  have hYc : ∀ ω ∉ N, Continuous fun t => Y t ω := fun ω hω => by
    obtain ⟨-, hw, -, hl, hr', -⟩ := hgood ω hω
    exact (hr'.sub hw).sub (continuous_const.mul (hw.sub hl))
  have hT₁ := Sec7.isStoppingTime_firstMeet_off hZa hYa hNm fun ω hω =>
    continuousOn_posAfter_sub (hYc ω hω) _
  have hT₂ := Sec7.isStoppingTime_firstMeet_off hZa hYa' hNm fun ω hω =>
    continuousOn_posAfter_sub (Y := -Y) (hYc ω hω).neg _
  set Th : Ω → ℝ≥0∞ := fun ω => max (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter Y) ζ) ω)
    (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter (-Y)) ζ) ω) with hTh
  have hThs : IsStoppingTime 𝓖 fun ω => (Th ω : WithTop ℝ≥0) := hT₁.max hT₂
  have hhit : ∀ ω ∉ N, ∃ m : ℝ≥0, Th ω = m ∧ 1 ≤ m ∧ Y m ω = 0 := fun ω hω => by
    obtain ⟨hζ, -, -, -, -, -, ⟨t₀, ht₀, hz⟩⟩ := hgood ω hω
    have : Th ω = hitAfter Y ζ ω := by
      simp only [hTh, hitAfter, Sec7.zeroOn_of_notMem hω]
    rw [this]
    exact exists_hitAfter (hYc ω hω) hζ ht₀ hz
  -- the capped stopping times and the restart events
  set Tn : ℕ → Ω → ℝ≥0 := fun n ω => (min (Th ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTn
  have hTn_coe : ∀ n ω, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = min (Th ω) ((n : ℝ≥0) : ℝ≥0∞) := fun n ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hTns : ∀ n, IsStoppingTime 𝓖 fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := hThs.min_const (n : ℝ≥0)
    have he : (fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (Th ω : WithTop ℝ≥0) (n : ℝ≥0) :=
      funext fun ω => hTn_coe n ω
    rw [he]; exact h
  set A : ℕ → Set Ω := fun n => Nᶜ ∩ {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} with hA
  have hTnA : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = Th ω := fun n ω hω => by
    rw [hTn_coe]; exact min_eq_left hω.2.le
  have hAm : ∀ n, MeasurableSet[(hTns n).measurableSpace] (A n) := by
    intro n
    have key : ∀ i : ℝ≥0, MeasurableSet[𝓖 i] (A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i}) := by
      intro i
      have heq : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          Nᶜ ∩ ({ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)}) := by
        ext ω
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, ?_⟩
          have h3' : ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i := h3
          rwa [hTnA n ω ⟨h1, h2⟩] at h3'
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i
          rw [hTnA n ω ⟨h1, h2⟩]; exact h3
      rw [heq]
      refine (hNm i).compl.inter ?_
      rcases lt_or_ge i (n : ℝ≥0) with hin | hni
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω ≤ (i : ℝ≥0∞)} := by
          refine inter_eq_right.2 fun ω (hω : Th ω ≤ i) => ?_
          exact lt_of_le_of_lt hω (by exact_mod_cast hin)
        rw [he]; exact hThs i
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
          refine inter_eq_left.2 fun ω (hω : Th ω < (n : ℝ≥0)) => ?_
          exact le_trans hω.le (by exact_mod_cast hni)
        rw [he]; exact 𝓖.mono hni _ (hThs.measurableSet_lt (n : ℝ≥0))
    refine ((hTns n).measurableSet _).2 ⟨?_, key⟩
    have h := key (n : ℝ≥0)
    have hsub : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A n :=
      inter_eq_left.2 fun ω _ => by
        show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞)
        rw [hTn_coe]; exact min_le_right _ _
    rw [hsub] at h
    exact le_iSup (fun t => 𝓖 t) (n : ℝ≥0) _ h
  have hAT : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < Tn n ω ∨ ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < (fun _ : Fin 1 => (0 : ℝ)) j) := fun n ω hω => by
    obtain ⟨hζ, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, -⟩ := hhit ω hω.1
    refine ⟨by rw [hζ]; exact ENNReal.coe_lt_top, Or.inl ?_⟩
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    rw [hTm]; exact lt_of_lt_of_le one_pos hm1
  -- the restart formula
  have hlaw := fun n => measure_restart_stateEvent hκ hE (hTns n) (hAm n) (hAT n) hS hSΨ hΨ
  -- the future fails the event
  have hLHS : ∀ n, A n ∩ {ω | Ψ (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω)
      (fun i t => VL i (Tn n ω + t) ω - W (Tn n ω) ω) (fun j t => VR j (Tn n ω + t) ω - W (Tn n ω) ω)
      (ζ ω - Tn n ω)} = ∅ := by
    intro n
    refine eq_empty_iff_forall_notMem.2 fun ω ⟨hω, hΨω⟩ => ?_
    obtain ⟨m, hm, hm1, -⟩ := hhit ω hω.1
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    have hΨω' : Ψ (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω)
        (fun i t => VL i (Tn n ω + t) ω - W (Tn n ω) ω) (fun j t => VR j (Tn n ω + t) ω - W (Tn n ω) ω)
        (ζ ω - Tn n ω) := hΨω
    rw [hTm] at hΨω'
    exact hfut ω hω.1 m hm1 hΨω'
  -- the restarted word lies on the ray
  have hRHS : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR S (wordAt W VL VR (Tn n) ω) ∂P = K * P (A n) := by
    intro n
    have hAmeas : MeasurableSet (A n) := (hTns n).measurableSpace_le _ (hAm n)
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun hAmeas fun ω hω => ?_
    obtain ⟨-, -, -, -, -, hsep, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, hYm⟩ := hhit ω hω.1
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    have hL : 0 < W m ω - VL 0 m ω := sub_pos.2 (hsep m (lt_of_lt_of_le one_pos hm1))
    have hYm' : VR 0 m ω - W m ω = r * (W m ω - VL 0 m ω) := by
      simp only [hY, ratioGap] at hYm; linarith
    have hword : wordAt W VL VR (Tn n) ω =
        ((fun _ => -(W m ω - VL 0 m ω)), fun _ => r * (W m ω - VL 0 m ω)) := by
      simp only [wordAt, hTm]
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]; simp only; ring
      · rw [Fin.fin_one_eq_zero j]; exact hYm'
    rw [hword, hdil _ hL]
  have hzero : ∀ n, K * P (A n) = 0 := fun n => by
    rw [← hRHS n, ← hlaw n, hLHS n, measure_empty]
  -- some restart event has positive probability
  have hcover : Nᶜ ⊆ ⋃ n, A n := fun ω hω => by
    obtain ⟨m, hm, -, -⟩ := hhit ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (m : ℝ)
    refine mem_iUnion.2 ⟨n, hω, ?_⟩
    show Th ω < ((n : ℝ≥0) : ℝ≥0∞)
    rw [hm]
    exact_mod_cast (show m < (n : ℝ≥0) by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn)
  by_contra hK
  have hA0 : ∀ n, P (A n) = 0 := fun n => (mul_eq_zero.1 (hzero n)).resolve_left hK
  have h0 : P Nᶜ = 0 := measure_mono_null hcover (measure_iUnion_null hA0)
  have h1 : P Nᶜ = 1 := by
    rw [prob_compl_eq_one_sub (𝓖.le 0 _ (hNm 0)), hN0, tsub_zero]
  rw [h0] at h1
  exact zero_ne_one h1

end Restart

/-! ### The transfer to separated words -/

section Transfer

/-- A sign change of `R − rL` after `N` gives a zero after `N`. -/
theorem exists_rgap_eq_zero {r : ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ}
    (hc : Continuous (rgap r w vL vR)) (h : RealRec r w vL vR) (N : ℝ≥0) :
    ∃ t : ℝ≥0, N ≤ t ∧ rgap r w vL vR t = 0 := by
  obtain ⟨t₁, t₂, h1, h2, h3, h4⟩ := h N
  rcases le_total t₁ t₂ with h12 | h21
  · obtain ⟨t, ht, hz⟩ := intermediate_value_Icc h12 hc.continuousOn ⟨h3.le, h4.le⟩
    exact ⟨t, h1.trans ht.1, hz⟩
  · obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' h21 hc.continuousOn ⟨h3.le, h4.le⟩
    exact ⟨t, h2.trans ht.1, hz⟩

theorem not_recEvent_congr (r : ℝ) (w w' : ℝ≥0 → ℝ) (vL vL' vR vR' : Fin 1 → ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hn : ¬ RecEvent r w vL vR τ) : ¬ RecEvent r w' vL' vR' τ := fun hr =>
  hn (recEvent_congr r w' w vL' vL vR' vR τ (fun t ht => ⟨(h t ht).1.symm, fun i => ((h t ht).2.1 i).symm,
    fun j => ((h t ht).2.2 j).symm⟩) hr)

theorem continuous_rgap {r : ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} (hw : Continuous w)
    (hL : Continuous (vL 0)) (hR : Continuous (vR 0)) : Continuous (rgap r w vL vR) :=
  (hR.sub hw).sub (continuous_const.mul (hw.sub hL))

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL xR ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- Continuity of the state of an evolution with infinite lifetime. -/
theorem continuous_state_of_top {ω : Ω} (hζω : ζ ω = ⊤)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω)) :
    Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧ Continuous (fun t => VR 0 t ω) := by
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => by
      show (t : ℝ≥0∞) < ζ ω
      rw [hζω]; exact ENNReal.coe_lt_top)
  exact ⟨hcont hp.2.2.2.1, hcont (hp.2.2.2.2.1 0), hcont (hp.2.2.2.2.2.1 0)⟩

/-- **Dilation invariance of the non-recurrence probability.** -/
theorem codeLaw_recCompl_dilate [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {c : ℝ≥0}
    (hc : c ≠ 0) (r : ℝ) :
    codeLaw κ ρL ρR (recCodeSet r)ᶜ ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR (recCodeSet r)ᶜ (xL, xR) := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_eventOf_eq_codeLaw_state hκ hsep' (hE.dilate hc) (measurableSet_recCodeSet r).compl
      (Ψ := fun w vL vR τ => ¬ RecEvent r w vL vR τ) (fun _ _ _ => Iff.rfl) (not_recEvent_congr r),
    ← measure_eventOf_eq_codeLaw_state hκ hsep hE (measurableSet_recCodeSet r).compl
      (Ψ := fun w vL vR τ => ¬ RecEvent r w vL vR τ) (fun _ _ _ => Iff.rfl) (not_recEvent_congr r)]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
  obtain ⟨hw, hl, hr⟩ := continuous_state_of_top hζω hp
  have hcg : Continuous (rgap r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) :=
    continuous_rgap hw hl hr
  have hcm : Continuous fun t : ℝ≥0 => c * t := continuous_const.mul continuous_id
  have hcg' : Continuous (rgap r (fun t => (√(c : ℝ))⁻¹ * W (c * t) ω)
      (fun i t => (√(c : ℝ))⁻¹ * VL i (c * t) ω) (fun j t => (√(c : ℝ))⁻¹ * VR j (c * t) ω)) :=
    continuous_rgap (continuous_const.mul (hw.comp hcm)) (continuous_const.mul (hl.comp hcm))
      (continuous_const.mul (hr.comp hcm))
  show ¬ RecEvent r (fun t => (√(c : ℝ))⁻¹ * W (c * t) ω) (fun i t => (√(c : ℝ))⁻¹ * VL i (c * t) ω)
      (fun j t => (√(c : ℝ))⁻¹ * VR j (c * t) ω) (ζ ω / c) ↔
    ¬ RecEvent r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, recEvent_top_iff hcg', recEvent_top_iff hcg]
  exact not_congr (realRec_dilate hc r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω))

/-- **The non-recurrence probability vanishes along the ray of words `(−L, rL)`**, by the restart of the two-seed
law. -/
theorem codeLaw_rec_eq_zero (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ}
    (hadm0 : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0)) {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0∞}
    (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR (recCodeSet r)ᶜ ((fun _ => -L), fun _ => r * L) = K) :
    K = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ := Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ
    (xL := fun _ => (0 : ℝ)) (xR := fun _ => (0 : ℝ)) (fun _ => rfl) (fun _ => rfl) ρL ρR
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hgood : ∀ᵐ ω ∂P, (ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      Continuous (fun t => VL 0 t ω) ∧ Continuous (fun t => VR 0 t ω) ∧
      (∀ t : ℝ≥0, 0 < t → VL 0 t ω < W t ω) ∧ ∃ t : ℝ≥0, 1 ≤ t ∧ ratioGap r W VL VR t ω = 0) ∧
      RealRec r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) := by
    filter_upwards [Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ Zhan.isOrderedForceWord_zero hadm0 hE,
      ae_realRec_twoSeed hκ hadm0 hE hr, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hrec hp
    obtain ⟨hw, hl, hrr⟩ := continuous_state_of_top hζ hp
    obtain ⟨t, ht, hz⟩ := exists_rgap_eq_zero (continuous_rgap hw hl hrr) hrec 1
    exact ⟨⟨hζ, hw, hp.1, hl, hrr, fun t ht => (hsep t ht).1 0, t, ht, hz⟩, hrec⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgood' : ∀ ω ∉ N, _ := fun ω (hω : ω ∉ N) => by
    by_contra h
    exact hω (hNsub h)
  refine eq_zero_of_restart_ratio_state hκ hEa (N := N)
    (fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t) hN0 (fun ω hω => (hgood' ω hω).1)
    (measurableSet_recCodeSet r).compl (Ψ := fun w vL vR τ => ¬ RecEvent r w vL vR τ)
    (fun _ _ _ => Iff.rfl) (not_recEvent_congr r) (fun ω hω m hm1 hn => hn ?_) hdil
  obtain ⟨⟨hζ, hw, -, hl, hrr, -⟩, hrec⟩ := hgood' ω hω
  have hζ' : ζ ω - m = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
  rw [hζ']
  have hsh : Continuous fun t : ℝ≥0 => m + t := continuous_const.add continuous_id
  have hcf : Continuous (rgap r (fun t => W (m + t) ω - W m ω) (fun i t => VL i (m + t) ω - W m ω)
      (fun j t => VR j (m + t) ω - W m ω)) :=
    continuous_rgap ((hw.comp hsh).sub continuous_const) ((hl.comp hsh).sub continuous_const)
      ((hrr.comp hsh).sub continuous_const)
  rw [recEvent_top_iff hcf]
  intro M
  obtain ⟨t₁, t₂, h1, h2, h3, h4⟩ := hrec (m + M)
  have hg : ∀ t, rgap r (fun t => W (m + t) ω - W m ω) (fun i t => VL i (m + t) ω - W m ω)
      (fun j t => VR j (m + t) ω - W m ω) t = rgap r (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (m + t) := fun t => by simp only [rgap]; ring
  refine ⟨t₁ - m, t₂ - m, le_tsub_of_add_le_left h1, le_tsub_of_add_le_left h2, ?_, ?_⟩
  · rw [hg, add_tsub_cancel_of_le (le_self_add.trans h1)]; exact h3
  · rw [hg, add_tsub_cancel_of_le (le_self_add.trans h2)]; exact h4

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Recurrence of the gap ratio for every separated two-force law** (B.3 (E11), additional note L1486–L1488): for
marks `x_L < 0 < x_R` with weights `≥ κ/2 − 2`, almost surely `R − rL` (`r = x_R/(−x_L)`) takes both signs after every
time. -/
theorem IsIntegratedSLEEvolution.ae_realRec_sep (hκ : 0 < κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, RealRec (xR 0 / (-xL 0)) (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hwL, hwR⟩ := weights_of_hasAdmissiblePartialSums hadm hxL hxR
  have hadm0 := hasAdmissiblePartialSums_seed hwL hwR
  have hxL' : ∀ i, xL i < 0 := fun i => by rw [Fin.fin_one_eq_zero i]; exact hxL
  have hxR' : ∀ j, 0 < xR j := fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR
  have hF : IsOrderedForceWord xL xR :=
    ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => (hxL' i).le,
      fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun j => (hxR' j).le⟩
  have hsep : ∀ i j, xL i < xR j := fun i j => (hxL' i).trans (hxR' j)
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun _ h => h.1
  set r : ℝ := xR 0 / (-xL 0) with hr
  have hr0 : 0 < r := div_pos hxR (neg_pos.2 hxL)
  have hK := codeLaw_rec_eq_zero hκ hadm0 hr0 (K := codeLaw κ ρL ρR (recCodeSet r)ᶜ (xL, xR))
    fun L hL => by
      have hxL0 : 0 < -xL 0 := neg_pos.2 hxL
      have hxne : xL 0 ≠ 0 := hxL.ne
      set c : ℝ≥0 := ⟨((-xL 0) / L) ^ 2, by positivity⟩ with hcdef
      have hc : c ≠ 0 := by
        intro h
        have : ((-xL 0) / L) ^ 2 = 0 := congrArg NNReal.toReal h
        exact (pow_pos (div_pos hxL0 hL) 2).ne' this
      have hsc : (√(c : ℝ))⁻¹ = L / (-xL 0) := by
        rw [show (c : ℝ) = ((-xL 0) / L) ^ 2 from rfl, Real.sqrt_sq (div_pos hxL0 hL).le, inv_div]
      rw [← codeLaw_recCompl_dilate hκ hsep hE hζ hc]
      congr 1
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]
        show -L = (√(c : ℝ))⁻¹ * xL 0
        rw [hsc]
        field_simp
      · rw [Fin.fin_one_eq_zero j]
        show r * L = (√(c : ℝ))⁻¹ * xR 0
        rw [hsc, hr]
        field_simp
  rw [← measure_eventOf_eq_codeLaw_state hκ hsep hE (measurableSet_recCodeSet r).compl
      (Ψ := fun w vL vR τ => ¬ RecEvent r w vL vR τ) (fun _ _ _ => Iff.rfl) (not_recEvent_congr r)] at hK
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hK, hζ, hE.2.2.2.2] with ω hn hζω hp
  have hrec : RecEvent r (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) := by
    by_contra h; exact hn h
  obtain ⟨hw, hl, hrr⟩ := continuous_state_of_top hζω hp
  rw [hζω, recEvent_top_iff (continuous_rgap hw hl hrr)] at hrec
  exact hrec

end Transfer

end InteractingSLE.ZhanGT4
