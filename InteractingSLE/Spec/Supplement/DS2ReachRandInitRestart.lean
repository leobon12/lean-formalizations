/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartLaw
import InteractingSLE.Spec.Coupling.AnnounceLifetime

/-!
# DS2 with converging random initial states, II: the restart kernel of a reach event

Packet PROVE-T14-DS3. Step (ii) of the proof of Lemma DS3 (spec p. 554, `source/spec/p529-576.md` L605–L611): "Retain
the joint entrance law through this deterministic time and use the integrated Markov transition law." The landed
`Sec2.Restart.measure_restart_killedState` (PROVE-RESTART) gives the conditional law at a stopping time for
finite-dimensional events of the killed state relative to the driver. The reach events of DS2 (`DSReach.reachEvent`)
involve the whole path and the *absolute* position of the state. This file extends the restart to them.

* `CodeReach T' O Bf w y`: a solution code `y`, shifted by `w`, reaches the open target `O` at a dyadic time
  `s < T'` before its lifetime while staying at distance `≥ 1/(N+1)` from `Bfᶜ` at all dyadic times `≤ s`;
  measurable in `(w, y)` (`measurableSet_codeReach`);
* `codeReach_iff`: for a code whose decoded state is a path continuous before the lifetime, `CodeReach` is exactly the
  reach event (dyadic witnesses suffice by continuity and compactness);
* `reachSetF`, `reachKer a ρL ρR T' O Bf w s`: the Wiener probability that the canonical solution from the separated
  relative start `s`, shifted by `w`, reaches `O` before `T'` inside `Bf` (Borel by Lusin–Souslin, as the landed
  `lawSetF`; measurable in `(w, s)`, `measurable_reachKer`);
* **`measure_restart_reach`**: for an integrated evolution, a finite stopping time `T` and `A ∈ 𝓕_T` with `T < ζ` and
  (`0 < T` or a separated word) on `A`,
  `P(A ∩ {the path after T reaches O before T + T' inside Bf}) = ∫_A reachKer(W_T, V_T − W_T) dP`.
  The proof is the landed one with the finite-dimensional set `KSet` replaced by `CodeReach` and the start
  `V_T − W_T` replaced by the pair `(W_T, V_T − W_T)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace RandInit

open Sec2 Sec2.Assembly Sec2.Restart QuantumZipper.StrongMarkov

variable {nL nR : ℕ}

/-- The decoded state of a code at time `t`, shifted by `w`. -/
def codeState (w : ℝ) (y : XCode nL nR) (t : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (w + cw y t, fun i => w + cvL y i t, fun j => w + cvR y j t)

theorem measurable_codeState (t : ℝ≥0) :
    Measurable fun p : ℝ × XCode nL nR => codeState p.1 p.2 t :=
  (measurable_fst.add ((measurable_cw_at t).comp measurable_snd)).prodMk
    ((measurable_pi_iff.2 fun i => measurable_fst.add ((measurable_cvL_at i t).comp measurable_snd)).prodMk
      (measurable_pi_iff.2 fun j => measurable_fst.add ((measurable_cvR_at j t).comp measurable_snd)))

/-- **Reach for a code**, at dyadic times. -/
def CodeReach (T' : ℝ≥0) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (w : ℝ) (y : XCode nL nR) : Prop :=
  ∃ n k : ℕ, dyad n k < T' ∧ (dyad n k : ℝ≥0∞) < cζ y ∧ codeState w y (dyad n k) ∈ O ∧
    ∃ N : ℕ, ∀ n' k' : ℕ, dyad n' k' ≤ dyad n k →
      (1 : ℝ) / ((N : ℝ) + 1) ≤ Metric.infDist (codeState w y (dyad n' k')) Bfᶜ

theorem measurableSet_codeReach (T' : ℝ≥0) {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) :
    MeasurableSet {p : ℝ × XCode nL nR | CodeReach T' O Bf p.1 p.2} := by
  refine measurableSet_setOfPred.2 ?_
  unfold CodeReach
  refine Measurable.exists fun n => Measurable.exists fun k => ?_
  refine measurable_const.and ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const
    (measurable_cζ.comp measurable_snd))).and ((measurableSet_setOfPred.1
      ((measurable_codeState _) hO.measurableSet)).and ?_))
  refine Measurable.exists fun N => Measurable.forall fun n' => Measurable.forall fun k' => ?_
  refine measurable_const_imp _ (measurableSet_setOfPred.1 (measurableSet_le measurable_const
    ((Metric.continuous_infDist_pt _).measurable.comp (measurable_codeState _))))

/-- **Dyadic witnesses suffice** for a path continuous before its lifetime. -/
theorem codeReach_iff {T' : ℝ≥0} {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O)
    (hBf : IsOpen Bf) (hBfc : Bfᶜ.Nonempty) {w : ℝ} {y : XCode nL nR} {ζ' : ℝ≥0∞}
    {f : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ'})
    (hζ : cζ y = ζ') (hy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → codeState w y t = f t) :
    CodeReach T' O Bf w y ↔ ∃ s : ℝ≥0, s < T' ∧ (s : ℝ≥0∞) < ζ' ∧ f s ∈ O ∧ ∀ u ≤ s, f u ∈ Bf := by
  have hBfcl : IsClosed Bfᶜ := hBf.isClosed_compl
  constructor
  · rintro ⟨n, k, hT', hζ', hO', N, hN⟩
    rw [hζ] at hζ'
    refine ⟨dyad n k, hT', hζ', by rwa [← hy _ hζ'], fun u hu => ?_⟩
    have huζ : (u : ℝ≥0∞) < ζ' := lt_of_le_of_lt (by exact_mod_cast hu) hζ'
    -- approximate `u` from below by dyadic times
    have hd : ∀ j, (1 : ℝ) / ((N : ℝ) + 1) ≤ Metric.infDist (f (dyad j (flr j u))) Bfᶜ := fun j => by
      have hle : dyad j (flr j u) ≤ dyad n k := (dyad_flr_le j u).trans hu
      rw [← hy _ (lt_of_le_of_lt (by exact_mod_cast hle) hζ')]
      exact hN j _ hle
    have hcont : Tendsto (fun j => f (dyad j (flr j u))) atTop (𝓝 (f u)) :=
      ((hf u huζ).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr u,
        Eventually.of_forall fun j => lt_of_le_of_lt (by exact_mod_cast dyad_flr_le j u) huζ⟩))
    have hlim : (1 : ℝ) / ((N : ℝ) + 1) ≤ Metric.infDist (f u) Bfᶜ :=
      ge_of_tendsto ((Metric.continuous_infDist_pt _).tendsto _ |>.comp hcont) (Eventually.of_forall hd)
    by_contra hnot
    have : Metric.infDist (f u) Bfᶜ = 0 := Metric.infDist_zero_of_mem hnot
    rw [this] at hlim
    exact absurd hlim (not_le.2 (by positivity))
  · rintro ⟨s, hsT, hsζ, hsO, hsB⟩
    have hIcc : Icc (0 : ℝ≥0) s ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ'} := fun t ht =>
      lt_of_le_of_lt (by exact_mod_cast ht.2) hsζ
    -- a uniform distance to `Bfᶜ` on `[0, s]`
    have hg : ContinuousOn (fun t => Metric.infDist (f t) Bfᶜ) (Icc (0 : ℝ≥0) s) :=
      (Metric.continuous_infDist_pt _).comp_continuousOn (hf.mono hIcc)
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le) hg
    have hpos : 0 < Metric.infDist (f t₀) Bfᶜ :=
      (hBfcl.notMem_iff_infDist_pos hBfc).1 (fun h => h (hsB t₀ ht₀.2))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
    -- a dyadic time `≤ s` with state in `O`
    obtain ⟨n, k, hks, hkO⟩ : ∃ n k : ℕ, dyad n k ≤ s ∧ f (dyad n k) ∈ O := by
      have hev : ∀ᶠ t in 𝓝[Icc (0 : ℝ≥0) s] s, f t ∈ O :=
        ((hf s hsζ).mono hIcc).tendsto (hO.mem_nhds hsO)
      have htend : Tendsto (fun j => dyad j (flr j s)) atTop (𝓝[Icc (0 : ℝ≥0) s] s) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr s, Eventually.of_forall fun j =>
          ⟨zero_le, dyad_flr_le j s⟩⟩
      obtain ⟨j, hj⟩ := (htend.eventually hev).exists
      exact ⟨j, flr j s, dyad_flr_le j s, hj⟩
    have hkζ : (dyad n k : ℝ≥0∞) < ζ' := lt_of_le_of_lt (by exact_mod_cast hks) hsζ
    refine ⟨n, k, lt_of_le_of_lt hks hsT, by rwa [hζ], by rwa [hy _ hkζ], N, fun n' k' hle => ?_⟩
    have hle' : dyad n' k' ≤ s := hle.trans hks
    rw [hy _ (lt_of_le_of_lt (by exact_mod_cast hle') hsζ)]
    exact hN.le.trans (hmin ⟨zero_le, hle'⟩)

/-! ### The kernel -/

/-- Triples (shift, separated start, driving code) whose canonical solution, shifted, reaches `O`. -/
def reachSetF (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (T' : ℝ≥0)
    (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :
    Set ((ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))) × PCode) :=
  (fun p : ℝ × XCode nL nR => ((p.1, startOf p.2), p.2.1)) ''
    {p | (p.2 ∈ CRelF a ρL ρR ∧ SepStart (startOf p.2)) ∧ CodeReach T' O Bf p.1 p.2}

theorem measurableSet_reachSetF {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (T' : ℝ≥0)
    {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) :
    MeasurableSet (reachSetF a ρL ρR T' O Bf) := by
  have : StandardBorelSpace (ℝ × XCode nL nR) := StandardBorelSpace.prod
  refine MeasurableSet.image_of_measurable_injOn ?_
    ((measurable_fst.prodMk (measurable_startOf.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)) ?_
  · exact ((((measurableSet_cRelF a ρL ρR).preimage measurable_snd).inter
      ((measurable_startOf measurableSet_sepStart).preimage measurable_snd)).inter
      (measurableSet_codeReach T' hO))
  · rintro ⟨w, x⟩ ⟨⟨hx, hsx⟩, -⟩ ⟨w', x'⟩ ⟨⟨hx', -⟩, -⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨hw, hs⟩, h1⟩ := h
    have hsx' : SepStart (startOf x') := by
      have : SepStart (startOf x) := hsx
      rwa [hs] at this
    have := injOn_startOf_fst a ρL ρR ⟨hx, hsx⟩ ⟨hx', hsx'⟩ (Prod.ext hs h1)
    simp only at hw this
    rw [hw, this]

/-- **The restart kernel of a reach event**: the Wiener probability that the canonical solution from the relative
start `s`, shifted by `w`, reaches `O` before `T'` inside `Bf`. -/
def reachKer (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (T' : ℝ≥0)
    (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (w : ℝ) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ≥0∞ :=
  wienerPath {b | ((w, s), enc b) ∈ reachSetF a ρL ρR T' O Bf}

theorem measurable_reachKer {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (T' : ℝ≥0)
    {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) :
    Measurable fun p : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) => reachKer a ρL ρR T' O Bf p.1 p.2 := by
  have hS : MeasurableSet {q : (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))) × (ℝ≥0 → ℝ) |
      (q.1, enc q.2) ∈ reachSetF a ρL ρR T' O Bf} :=
    (measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_reachSetF T' hO)
  exact measurable_measure_prodMk_left hS

/-! ### The restart identity -/

/-- **The restarted reach event**: after `T`, the absolute state reaches `O` before `T + T'` and before the lifetime,
staying in `Bf`. -/
def restartReach {Ω : Type*} (T : Ω → ℝ≥0) (T' : ℝ≥0) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ∃ s : ℝ≥0, s < T' ∧ (s : ℝ≥0∞) < ζ ω - T ω ∧ Coupling.stateAt W VL VR (T ω + s) ω ∈ O ∧
    ∀ u ≤ s, Coupling.stateAt W VL VR (T ω + u) ω ∈ Bf}

/-- **The restart identity for reach events.** For an integrated `SLE_a(ρ)` evolution, a finite stopping time `T`
and `A ∈ 𝓕_T` with `T < ζ` and (`0 < T` or a separated word) on `A`:
`P(A ∩ restartReach) = ∫_A reachKer(W_T, V_T − W_T) dP`. -/
theorem measure_restart_reach {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    (T' : ℝ≥0) {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) (hBf : IsOpen Bf)
    (hBfc : Bfᶜ.Nonempty) :
    P (A ∩ restartReach T T' O Bf W VL VR ζ) =
      ∫⁻ ω in A, reachKer a ρL ρR T' O Bf (W (T ω) ω)
        ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω) ∂P := by
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
  -- the state at `T` (shift and relative start), through the progressive versions
  set q : Ω → ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) := fun ω => (progVersion ζ W (T ω) ω,
    ((fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω),
      fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω)) with hq
  have hqT : Measurable[hT.measurableSpace] q :=
    (measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT).prodMk
      (@measurable_start_aux nL nR Ω hT.measurableSpace _ _ _
        (measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT)
        (fun i => measurable_eval_stop (isStronglyProgressive_progVersion (hVLad i)) hT)
        (fun j => measurable_eval_stop (isStronglyProgressive_progVersion (hVRad j)) hT))
  have hqm : Measurable q := hqT.mono (hT.measurableSpace_le) le_rfl
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
    have hDA : MeasurableSet[hT𝓖.measurableSpace] (q ⁻¹' D ∩ A) :=
      hle𝓖 _ ((hqT hD).inter hA)
    have e : (fun ω => (q ω, g ω)) ⁻¹' (D ×ˢ F) ∩ A = (q ⁻¹' D ∩ A) ∩ g ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [e]
    exact (Indep_iff _ _ _).1 hindT _ _ hDA ⟨F, hF, rfl⟩
  set S : Set ((ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))) × (ℝ≥0 → ℝ)) :=
    {qb | (qb.1, enc qb.2) ∈ reachSetF a ρL ρR T' O Bf} with hSdef
  have hS : MeasurableSet S :=
    (measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_reachSetF T' hO)
  have hmainA : P (A ∩ (fun ω => (q ω, g ω)) ⁻¹' S) =
      ∫⁻ ω in A, reachKer a ρL ρR T' O Bf (q ω).1 (q ω).2 ∂P := by
    rw [inter_comm, ← Measure.restrict_apply (hpair hS), ← Measure.map_apply hpair hS, hjoint,
      Measure.prod_apply hS]
    change ∫⁻ x, reachKer a ρL ρR T' O Bf x.1 x.2 ∂((P.restrict A).map q) = _
    rw [lintegral_map (measurable_reachKer T' hO) hqm]
  -- the identification, almost surely on `A`
  have hid : ∀ᵐ ω ∂P, ω ∈ A →
      (ω ∈ restartReach T T' O Bf W VL VR ζ ↔ (q ω, g ω) ∈ S) ∧
      q ω = (W (T ω) ω, ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω)) := by
    filter_upwards [hpath, hBvae, hlimE] with ω hp hb hl hωA
    obtain ⟨hTζ, hT0⟩ := hAT ω hωA
    have h0 := restart_values hp hTζ
    have hq_eq : q ω = (W (T ω) ω, ((fun i => VL i (T ω) ω - W (T ω) ω),
        fun j => VR j (T ω) ω - W (T ω) ω)) := by
      simp only [hq, h0.1, h0.2.1, h0.2.2]
    refine ⟨?_, hq_eq⟩
    rw [hq_eq]
    have hr := hp.restart hTζ
    have hb' : (fun t => B (T ω + t) ω - B (T ω) ω) = fun t => smShift Bv T t ω := by
      funext t; simp only [smShift, hb]
    rw [hb'] at hr
    have hsep : SepStart ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω) := by
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
    -- the reach event is the code reach event
    have hfc : ContinuousOn (fun t => Coupling.stateAt W VL VR (T ω + t) ω)
        {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω - T ω} := by
      have hfp := hr.isForcePath
      have e : (fun t => Coupling.stateAt W VL VR (T ω + t) ω) = fun t =>
          (W (T ω) ω + (W (T ω + t) ω - W (T ω) ω),
            fun i => W (T ω) ω + (VL i (T ω + t) ω - W (T ω) ω),
            fun j => W (T ω) ω + (VR j (T ω + t) ω - W (T ω) ω)) := by
        funext t; simp only [Coupling.stateAt, add_sub_cancel]
      rw [e]
      exact (continuousOn_const.add hfp.continuousOn_w).prodMk
        ((continuousOn_pi.2 fun i => continuousOn_const.add (hfp.continuousOn_vL i)).prodMk
          (continuousOn_pi.2 fun j => continuousOn_const.add (hfp.continuousOn_vR j)))
    have hreach : ω ∈ restartReach T T' O Bf W VL VR ζ ↔ CodeReach T' O Bf (W (T ω) ω) c := by
      rw [codeReach_iff hO hBf hBfc hfc rfl fun t ht => ?_]
      · rfl
      · obtain ⟨e1, e2, e3, -⟩ := hcode.2 t ht
        simp only [codeState, Coupling.stateAt, e1, e2, e3, add_sub_cancel]
    rw [hreach]
    show _ ↔ ((W (T ω) ω, _), enc (g ω)) ∈ reachSetF a ρL ρR T' O Bf
    have hcF : c ∈ CRelF a ρL ρR ∧ startOf c = ((fun i => VL i (T ω) ω - W (T ω) ω),
        fun j => VR j (T ω) ω - W (T ω) ω) := mem_cRelF_iff.2 hcode.1
    constructor
    · intro hk
      refine ⟨(W (T ω) ω, c), ⟨⟨hcF.1, ?_⟩, hk⟩, ?_⟩
      · rw [hcF.2]; exact hsep
      · simp only [hcF.2, hc1]
    · rintro ⟨⟨w', y⟩, ⟨⟨hyF, -⟩, hyK⟩, hy⟩
      simp only [Prod.mk.injEq] at hy
      obtain ⟨⟨hw', hys⟩, hy1⟩ := hy
      have hyC : y ∈ CRel a (fun i => VL i (T ω) ω - W (T ω) ω) (fun j => VR j (T ω) ω - W (T ω) ω)
          ρL ρR := mem_cRelF_iff.1 ⟨hyF, hys⟩
      have : y = c := injOn_fst_cRel hsep hyC hcode.1 (by rw [hy1, ← hc1])
      rw [← this, ← hw']
      exact hyK
  -- conclusion
  have hset : (A ∩ restartReach T T' O Bf W VL VR ζ : Set Ω) =ᵐ[P]
      A ∩ (fun ω => (q ω, g ω)) ⁻¹' S := by
    filter_upwards [hid] with ω h
    refine propext ⟨fun ⟨h1, h2⟩ => ⟨h1, ((h h1).1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, ((h h1).1).2 h2⟩⟩
  rw [measure_congr hset, hmainA]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hid] with ω h hωA
  rw [(h hωA).2]

end RandInit

end Supp12

end InteractingSLE
