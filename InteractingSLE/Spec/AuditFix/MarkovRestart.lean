/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.MarkovKernel

/-!
# Theorem 2.2, the Markov sentence: the restart identity for the full state

Packet PROVE-AF-MARKOV. The landed `Sec2.Restart.measure_restart_killedState` (PROVE-RESTART) gives the
conditional law of the increments after a stopping time `T`. This file proves the same identity for the state
`X = (W, V^L, V^R, B)` itself:

* **`measure_restart_state`**: for an integrated evolution, a finite stopping time `T` and `A ∈ 𝓕_T` with `T < ζ`
  and (`0 < T` or a separated word) on `A`,

    `P(A ∩ {t_j < ζ − T, X_{T+t_j} ∈ K_j for all j}) = ∫_A shiftKer(X_T) dP`.

The proof is the landed one (as in `Supp12.RandInit.measure_restart_reach`) with the start `V_T − W_T` replaced by
the pair (shift `(W_T, B_T)`, start `V_T − W_T`) and the cylinder `KSet` replaced by the translated cylinder of
`lawSetP`: the future state is the shift plus the increments, `X_{T+t} = (W_T, B_T) + (W_{T+t} − W_T, …)`. The
Brownian coordinate at `T` is read off the continuous version, which is progressive in the usual augmentation,
where the restarted Brownian path is independent of the past.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace AuditFix

namespace Markov

open Sec2 Sec2.Assembly Sec2.Restart QuantumZipper.StrongMarkov

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restart identity for the full state.** For an integrated `SLE_a(ρ)` evolution, a finite stopping
time `T` of its filtration and `A ∈ 𝓕_T` with `T < ζ` and (`0 < T` or a separated word) on `A`: for times
`t_1, …, t_n` and Borel sets `K_j` of states,
`P(A ∩ {t_j < ζ − T, (W, V^L, V^R, B)_{T+t_j} ∈ K_j for all j}) = ∫_A shiftKer(X_T) dP`. -/
theorem measure_restart_state (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    {n : ℕ} (ts : Fin n → ℝ≥0) {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
          B (T ω + ts j) ω) ∈ K j}) =
      ∫⁻ ω in A, shiftKer a ρL ρR ts K (W (T ω) ω, (fun i => VL i (T ω) ω),
        (fun i => VR i (T ω) ω), B (T ω) ω) ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlimE := hE.ae_tendsto_threshold ha
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨Bv, hBvm, hBvc, hBvF, hBvae⟩ := exists_continuous_version hBF
  have h𝓕𝓖 : 𝓕 ≤ usualAugmentation 𝓕 P := Ito.le_usualAugmentation 𝓕 P
  have hT𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T ω : WithTop ℝ≥0) :=
    fun u => h𝓕𝓖 u _ (hT u)
  have hle𝓖 : hT.measurableSpace ≤ hT𝓖.measurableSpace :=
    Ito.measurableSpace_le_of_filtration_le h𝓕𝓖 hT hT𝓖
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hBvp : IsStronglyProgressive (usualAugmentation 𝓕 P) Bv :=
    isStronglyProgressive_of_rightContinuous (fun t => (hBvF.2.1 t).stronglyMeasurable)
      fun ω _ => (hBvc ω).continuousWithinAt
  -- the state at `T` (shift and relative start), through the progressive versions
  set q : Ω → (ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ)) := fun ω =>
    ((progVersion ζ W (T ω) ω, Bv (T ω) ω),
      ((fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω),
        fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω)) with hq
  have hqT : Measurable[hT𝓖.measurableSpace] q :=
    ((((measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT).mono hle𝓖 le_rfl).prodMk
      (measurable_eval_stop hBvp hT𝓖)).prodMk
      ((@measurable_start_aux nL nR Ω hT.measurableSpace _ _ _
        (measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT)
        (fun i => measurable_eval_stop (isStronglyProgressive_progVersion (hVLad i)) hT)
        (fun j => measurable_eval_stop (isStronglyProgressive_progVersion (hVRad j)) hT)).mono
        hle𝓖 le_rfl))
  have hqm : Measurable q := hqT.mono hT𝓖.measurableSpace_le le_rfl
  -- the restarted Brownian path: Wiener law, independent of `𝓖_T`
  set g : Ω → ℝ≥0 → ℝ := smPath Bv T with hg
  have hgm : Measurable g := measurable_smPath hBvc hBvm (measurable_of_isStoppingTime hT)
  have hind := indep_future hBvF
  have hlaw : P.map g = wienerPath :=
    map_path_eq_wienerPath
      (isBrownianReal_smShift hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖).toIsPreBrownianReal
      hgm
  have hindT := indep_smPath hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖
  have hpair : Measurable fun ω => (q ω, g ω) := hqm.prodMk hgm
  have hjoint : (P.restrict A).map (fun ω => (q ω, g ω)) =
      ((P.restrict A).map q).prod wienerPath := by
    refine (Measure.prod_eq fun D F hD hF => ?_).symm
    rw [Measure.map_apply hpair (hD.prod hF), Measure.map_apply hqm hD, ← hlaw,
      Measure.map_apply hgm hF, Measure.restrict_apply (hpair (hD.prod hF)),
      Measure.restrict_apply (hqm hD)]
    have hDA : MeasurableSet[hT𝓖.measurableSpace] (q ⁻¹' D ∩ A) := (hqT hD).inter (hle𝓖 _ hA)
    have e : (fun ω => (q ω, g ω)) ⁻¹' (D ×ˢ F) ∩ A = (q ⁻¹' D ∩ A) ∩ g ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [e]
    exact (Indep_iff _ _ _).1 hindT _ _ hDA ⟨F, hF, rfl⟩
  set S : Set (((ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) × (ℝ≥0 → ℝ)) :=
    {qb | (qb.1, enc qb.2) ∈ lawSetP a ρL ρR ts K} with hSdef
  have hS : MeasurableSet S :=
    (measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_lawSetP ts hK)
  have hmainA : P (A ∩ (fun ω => (q ω, g ω)) ⁻¹' S) =
      ∫⁻ ω in A, kerP a ρL ρR ts K (q ω) ∂P := by
    rw [inter_comm, ← Measure.restrict_apply (hpair hS), ← Measure.map_apply hpair hS, hjoint,
      Measure.prod_apply hS]
    change ∫⁻ x, kerP a ρL ρR ts K x ∂((P.restrict A).map q) = _
    rw [lintegral_map (measurable_kerP ts hK) hqm]
  -- the identification, almost surely on `A`
  have hid : ∀ᵐ ω ∂P, ω ∈ A →
      ((∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
          B (T ω + ts j) ω) ∈ K j) ↔ (q ω, g ω) ∈ S) ∧
      q ω = ((W (T ω) ω, B (T ω) ω),
        ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω)) := by
    filter_upwards [hpath, hBvae, hlimE] with ω hp hb hl hωA
    obtain ⟨hTζ, hT0⟩ := hAT ω hωA
    have h0 := restart_values hp hTζ
    have hq_eq : q ω = ((W (T ω) ω, B (T ω) ω),
        ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω)) := by
      simp only [hq, h0.1, h0.2.1, h0.2.2, hb]
    refine ⟨?_, hq_eq⟩
    rw [hq_eq]
    have hr := hp.restart hTζ
    have hb' : (fun t => B (T ω + t) ω - B (T ω) ω) = fun t => smShift Bv T t ω := by
      funext t; simp only [smShift, hb]
    rw [hb'] at hr
    have hsep : SepStart ((fun i => VL i (T ω) ω - W (T ω) ω),
        fun j => VR j (T ω) ω - W (T ω) ω) := by
      rcases hT0 with hT0 | hsx
      · exact sepStart_restart hp hT0 hTζ
      · exact sepStart_restart_of_sep hp hsx hTζ
    have hcode := codeOf_mem_cRel_of_path (Ω := Ω) (ω := ω)
      (xL := fun i => VL i (T ω) ω - W (T ω) ω) (xR := fun j => VR j (T ω) ω - W (T ω) ω)
      (W := fun t ω' => W (T ω' + t) ω' - W (T ω') ω')
      (VL := fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (VR := fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω')
      (B := smShift Bv T) (B' := smShift Bv T) (ζ := fun ω' => ζ ω' - T ω') hr
      (((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const) (fun t => rfl)
      (restart_tendsto hTζ hl)
    set c := codeOf (fun i => VL i (T ω) ω - W (T ω) ω) (fun j => VR j (T ω) ω - W (T ω) ω)
      (smShift Bv T) (fun t ω' => W (T ω' + t) ω' - W (T ω') ω')
      (fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω') (fun ω' => ζ ω' - T ω') ω with hc
    have hc1 : c.1 = enc (g ω) := rfl
    -- the future state is the shift plus the decoded increments
    have hst : ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω →
        shiftState (W (T ω) ω, B (T ω) ω) (fullCodeState c (ts j)) =
          (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
            B (T ω + ts j) ω) := by
      intro j hlt
      obtain ⟨e1, e2, e3, e4⟩ := hcode.2 (ts j) hlt
      simp only [shiftState, fullCodeState, e1, e2, e3, e4, smShift, hb, add_sub_cancel]
    have hKc : (∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
          B (T ω + ts j) ω) ∈ K j) ↔
        ∀ j, (ts j : ℝ≥0∞) < cζ c ∧
          shiftState (W (T ω) ω, B (T ω) ω) (fullCodeState c (ts j)) ∈ K j := by
      refine forall_congr' fun j => ?_
      refine ⟨fun ⟨hlt, hmem⟩ => ⟨hlt, ?_⟩, fun ⟨hlt, hmem⟩ => ⟨hlt, ?_⟩⟩
      · rw [hst j hlt]; exact hmem
      · rw [hst j hlt] at hmem; exact hmem
    rw [hKc]
    show _ ↔ (((W (T ω) ω, B (T ω) ω), ((fun i => VL i (T ω) ω - W (T ω) ω),
      fun j => VR j (T ω) ω - W (T ω) ω)), enc (g ω)) ∈ lawSetP a ρL ρR ts K
    have hcF : c ∈ CRelF a ρL ρR ∧ startOf c = ((fun i => VL i (T ω) ω - W (T ω) ω),
        fun j => VR j (T ω) ω - W (T ω) ω) := mem_cRelF_iff.2 hcode.1
    constructor
    · intro hk
      refine ⟨((W (T ω) ω, B (T ω) ω), c), ⟨⟨hcF.1, ?_⟩, hk⟩, ?_⟩
      · rw [hcF.2]; exact hsep
      · simp only [hcF.2, hc1]
    · rintro ⟨⟨c', y⟩, ⟨⟨hyF, -⟩, hyK⟩, hy⟩
      simp only [Prod.mk.injEq] at hy
      obtain ⟨⟨hc', hys⟩, hy1⟩ := hy
      have hyC : y ∈ CRel a (fun i => VL i (T ω) ω - W (T ω) ω)
          (fun j => VR j (T ω) ω - W (T ω) ω) ρL ρR := mem_cRelF_iff.1 ⟨hyF, hys⟩
      have : y = c := injOn_fst_cRel hsep hyC hcode.1 (by rw [hy1, ← hc1])
      rw [← this, ← hc']
      exact hyK
  -- conclusion
  have hset : (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
          B (T ω + ts j) ω) ∈ K j} : Set Ω) =ᵐ[P]
      A ∩ (fun ω => (q ω, g ω)) ⁻¹' S := by
    filter_upwards [hid] with ω h
    exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, ((h h1).1).1 h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, ((h h1).1).2 h2⟩⟩
  rw [measure_congr hset, hmainA]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hid] with ω h hωA
  exact congrArg (kerP a ρL ρR ts K) (h hωA).2

end Markov

end AuditFix

end InteractingSLE
