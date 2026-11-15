/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartLaw

/-!
# §7.3: the conditional law of a restarted evolution on events of the whole solution

Packets PROVE-RANDRESTART, PROVE-RANDRESTART2. PROVE-RESTART's kernel `Sec2.Restart.restartLaw` gives the conditional law at a
stopping time of the restarted killed state at *finitely many* times. The restarts of §7.3 with a random force
word (Aux. lemmas 103, 106, 113, the one-sided step) need it for events of the *whole* restarted driving path, such
as "the restarted driver has a continuous generating trace up to its remaining lifetime". This file proves the
two identities for every event of the solution that is coded by a Borel set of solution codes:

* `codeLaw a ρL ρR S s`: the Wiener probability of the driving paths whose canonical solution from the start `s`
  has its code in the Borel set `S` (measurable in `s`, `measurable_codeLaw`);
* `measure_eventOf_eq_codeLaw` (**canonical law**): for a separated start `s`, every integrated evolution from `s`
  has `P {Φ(W, ζ)} = codeLaw S s`, whenever `S` codes the path predicate `Φ` on canonical solution codes;
* `measure_restart_eventOf` (**conditional law at a stopping time**): for `A ∈ 𝓕_T` with `T < ζ` on `A` and, on
  `A`, `0 < T` or a separated word,

    `P (A ∩ {Φ(W_{T+·} − W_T, ζ − T)}) = ∫_A codeLaw S (V_T − W_T) dP`.

The proofs are PROVE-RESTART's (`measure_killedState_eq_restartLaw`, `measure_restart_killedState`) with the
finite-time cylinder `KSet ts K` replaced by `S`: the code of an evolution is a canonical solution code that decodes
to its path before the lifetime, and on separated starts the start and the driving code determine the code
(`injOn_startOf_fst`, Lusin–Souslin for the Borel image).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace RandRestart

open Sec2 Sec2.Assembly Sec2.Restart QuantumZipper.StrongMarkov

variable {nL nR : ℕ}

/-! ### The law sets of Borel code events -/

/-- The pairs (start, driving code) of canonical solution codes from separated starts lying in `S`. -/
def lawSetS (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Set (XCode nL nR)) :
    Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × PCode) :=
  (fun x : XCode nL nR => (startOf x, x.1)) ''
    ((CRelF a ρL ρR ∩ {x | SepStart (startOf x)}) ∩ S)

/-- **Lusin–Souslin**: the law set of a Borel code event is Borel. -/
theorem measurableSet_lawSetS {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {S : Set (XCode nL nR)}
    (hS : MeasurableSet S) : MeasurableSet (lawSetS a ρL ρR S) :=
  (((measurableSet_cRelF a ρL ρR).inter (measurable_startOf measurableSet_sepStart)).inter
    hS).image_of_measurable_injOn (measurable_startOf.prodMk measurable_fst)
    ((injOn_startOf_fst a ρL ρR).mono inter_subset_left)

/-- A canonical solution code from a separated start lies in `S` iff its (start, driving code) pair lies in
the law set (pathwise uniqueness). -/
theorem mem_lawSetS_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {S : Set (XCode nL nR)} {x : XCode nL nR}
    (hx : x ∈ CRel a xL xR ρL ρR) : ((xL, xR), x.1) ∈ lawSetS a ρL ρR S ↔ x ∈ S := by
  constructor
  · rintro ⟨y, ⟨⟨hy, -⟩, hyS⟩, hyx⟩
    simp only [Prod.mk.injEq] at hyx
    have hy' : y ∈ CRel a xL xR ρL ρR := mem_cRelF_iff.1 ⟨hy, hyx.1⟩
    rw [← injOn_fst_cRel hsep hy' hx hyx.2]
    exact hyS
  · intro hxS
    obtain ⟨h1, h2⟩ := mem_cRelF_iff.2 hx
    refine ⟨x, ⟨⟨h1, ?_⟩, hxS⟩, ?_⟩
    · show SepStart (startOf x)
      rw [h2]
      exact hsep
    · simp only [h2]

/-- Pairs (start, Brownian path) whose solution from the start has its code in `S`. -/
def restartSetS (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Set (XCode nL nR)) :
    Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)) :=
  {p | (p.1, enc p.2) ∈ lawSetS a ρL ρR S}

theorem measurableSet_restartSetS {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {S : Set (XCode nL nR)} (hS : MeasurableSet S) : MeasurableSet (restartSetS a ρL ρR S) :=
  (measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_lawSetS hS)

/-- **The canonical law of a code event from a start** `s`: the Wiener probability of the driving paths whose
canonical solution from `s` has its code in `S`. -/
def codeLaw (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Set (XCode nL nR))
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ≥0∞ :=
  wienerPath (Prod.mk s ⁻¹' restartSetS a ρL ρR S)

/-- The canonical law of a Borel code event is measurable in the start. -/
theorem measurable_codeLaw {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {S : Set (XCode nL nR)}
    (hS : MeasurableSet S) : Measurable (codeLaw a ρL ρR S) :=
  measurable_measure_prodMk_left (measurableSet_restartSetS hS)

theorem codeLaw_le_one (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Set (XCode nL nR))
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : codeLaw a ρL ρR S s ≤ 1 :=
  prob_le_one

/-! ### The canonical law -/

/-- The decoded driver of a code has a left limit at a finite positive lifetime. Every evolution's code has it
almost surely (`IsIntegratedSLEEvolution.ae_tendsto_threshold`). -/
def HasLimW (x : XCode nL nR) : Prop :=
  0 < cζ x → cζ x < ⊤ → ∃ w₀ : ℝ, Tendsto (cw x) (𝓝[<] (cζ x).toNNReal) (𝓝 w₀)

/-- A code that decodes to a path with a threshold limit at a finite positive lifetime has `HasLimW`. -/
theorem hasLimW_of_tendsto {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : XCode nL nR} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cw x t = w t)
    (hl : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = cζ x →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    HasLimW x := by
  intro h0 hfin
  have hTζ : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hfin.ne
  have hT : 0 < (cζ x).toNNReal := by
    have : (0 : ℝ≥0∞) < ((cζ x).toNNReal : ℝ≥0∞) := by rw [hTζ]; exact h0
    exact_mod_cast this
  obtain ⟨w₀, vL₀, vR₀, htend, -⟩ := hl _ hT hTζ
  refine ⟨w₀, ((continuous_fst.tendsto _).comp htend).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℝ≥0∞) < cζ x := by rw [← hTζ]; exact_mod_cast ht
  exact (hdec t ht').symm

/-- **The canonical law of a coded path event.** Let `S` be a Borel set of solution codes that codes the path
predicate `Φ` on canonical solution codes with `HasLimW` (`x ∈ S ↔ Φ (cw x) (cζ x)`), where `Φ w τ` only depends
on `w` before `τ`. For a separated start `(xL, xR)`, every integrated evolution from it (on any filtered
probability space) has `P {Φ(W, ζ)} = codeLaw S (xL, xR)`. -/
theorem measure_eventOf_eq_codeLaw {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)}
    {Φ : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ S ↔ Φ (cw x) (cζ x)))
    (hΦ : ∀ (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞), (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) →
      Φ w τ → Φ w' τ) :
    P {ω | Φ (fun t => W t ω) (ζ ω)} = codeLaw a ρL ρR S (xL, xR) := by
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
  show Φ (fun t => W t ω) (ζ ω) ↔ ((xL, xR), enc (B' · ω)) ∈ lawSetS a ρL ρR S
  rw [← hx1, mem_lawSetS_iff hsep hmem, hSΦ x hxF hxl, hxζ]
  exact ⟨hΦ _ _ _ fun t ht => ((hdec t ht).1).symm, hΦ _ _ _ fun t ht => (hdec t ht).1⟩

/-! ### The conditional law at a stopping time -/

section Restart

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The force word at the time `T ω`, seen from the driver: `V_T − W_T`. -/
def wordAt (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (ω : Ω) : (Fin nL → ℝ) × (Fin nR → ℝ) :=
  ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω)

/-- **The restart at a stopping time, in code form** (the content of PROVE-RESTART's
`measure_restart_killedState` for a general event). There are a measurable state `st` (equal to the word `V_T − W_T`
almost surely on `A`), a measurable restarted Brownian path `g`, and restarted codes `c` such that

* `(st, g)` has, on `A`, the joint law `(law of st on A) ⊗ wienerPath`: `P(A ∩ {(st, g) ∈ E}) = ∫_A wienerPath(E_st)`;
* almost surely on `A`: `st` is separated, `c` is a canonical solution code from `st` driven by `g`, its lifetime is
  `ζ − T`, its driver is `W_{T+·} − W_T` before `ζ − T`, and it has `HasLimW`. -/
theorem restart_core (ha : 0 < a) (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
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
    exact ⟨rfl, hsep, hcode.1, rfl, rfl, fun t ht => (hcode.2 t ht).1,
      hasLimW_of_tendsto (fun t ht => (hcode.2 t ht).1) hrl⟩

/-- **The conditional law of a coded path event of the restarted driver.** Under the hypotheses of
`restart_core`, for a Borel code set `S` coding the path predicate `Φ` (as in `measure_eventOf_eq_codeLaw`),

  `P(A ∩ {Φ(W_{T+·} − W_T, ζ − T)}) = ∫_A codeLaw S (V_T − W_T) dP`. -/
theorem measure_restart_codeEvent (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    {S : Set (XCode nL nR)} {Φ : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ S ↔ Φ (cw x) (cζ x)))
    (hΦ : ∀ (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞), (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) →
      Φ w τ → Φ w' τ) :
    P (A ∩ {ω | Φ (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)}) =
      ∫⁻ ω in A, codeLaw a ρL ρR S (wordAt W VL VR T ω) ∂P := by
  obtain ⟨st, g, c, -, -, hlaw, hid⟩ := restart_core ha hE hT hA hAT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hset : (A ∩ {ω | Φ (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)} : Set Ω) =ᵐ[P]
      A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSetS a ρL ρR S := by
    filter_upwards [hid] with ω h
    have key : ∀ hωA : ω ∈ A, (Φ (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω) ↔
        (st ω, g ω) ∈ restartSetS a ρL ρR S) := fun hωA => by
      obtain ⟨-, hsep, hc, hc1, hcζ, hcw, hcl⟩ := h hωA
      have e1 : (st ω, g ω) ∈ restartSetS a ρL ρR S ↔
          (((st ω).1, (st ω).2), (c ω).1) ∈ lawSetS a ρL ρR S := by
        rw [hc1]; exact Iff.rfl
      rw [e1, mem_lawSetS_iff hsep hc, hSΦ _ (mem_cRelF_iff.2 hc).1 hcl, hcζ]
      exact ⟨hΦ _ _ _ fun t ht => (hcw t ht).symm, hΦ _ _ _ fun t ht => hcw t ht⟩
    exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  rw [measure_congr hset, hlaw _ (measurableSet_restartSetS hS)]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hid] with ω h hωA
  rw [(h hωA).1]
  rfl

/-- **Almost-sure solvability at the realized start.** Under the hypotheses of `restart_core`, almost surely on
`A` the word `V_T − W_T` is separated and Wiener-almost every path drives a solution from it. (Fubini on the joint
law of `(st, g)`: almost surely on `A` the restarted Brownian path drives the restarted solution.) -/
theorem ae_solvable_restart (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j)) :
    ∀ᵐ ω ∂P, ω ∈ A → SepStart (wordAt W VL VR T ω) ∧
      ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel a (wordAt W VL VR T ω).1 (wordAt W VL VR T ω).2 ρL ρR := by
  obtain ⟨st, g, c, hstm, -, hlaw, hid⟩ := restart_core ha hE hT hA hAT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  set E := (restartSetS a ρL ρR (univ : Set (XCode nL nR)))ᶜ with hEdef
  have hEm : MeasurableSet E := (measurableSet_restartSetS MeasurableSet.univ).compl
  have h0 : P (A ∩ (fun ω => (st ω, g ω)) ⁻¹' E) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hid] with ω h ⟨hωA, hωE⟩
    obtain ⟨-, hsep, hc, hc1, -⟩ := h hωA
    obtain ⟨hcF, hcs⟩ := mem_cRelF_iff.2 hc
    refine hωE ⟨c ω, ⟨⟨hcF, ?_⟩, mem_univ _⟩, ?_⟩
    · show SepStart (startOf (c ω))
      rw [hcs]
      exact hsep
    · show (startOf (c ω), (c ω).1) = (st ω, enc (g ω))
      rw [hcs, hc1]
  have hfm : Measurable fun ω => wienerPath (Prod.mk (st ω) ⁻¹' E) :=
    (measurable_measure_prodMk_left hEm).comp hstm
  rw [hlaw E hEm, lintegral_eq_zero_iff hfm,
    EventuallyEq, ae_restrict_iff' hAm] at h0
  filter_upwards [h0, hid] with ω h1 h2 hωA
  obtain ⟨hst, hsep, -⟩ := h2 hωA
  rw [← hst]
  refine ⟨hsep, ?_⟩
  have h3 : wienerPath (Prod.mk (st ω) ⁻¹' E) = 0 := h1 hωA
  rw [measure_eq_zero_iff_ae_notMem] at h3
  filter_upwards [h3] with f hf
  simp only [hEdef, mem_preimage, mem_compl_iff, not_not] at hf
  obtain ⟨y, ⟨⟨hyF, -⟩, -⟩, hy⟩ := hf
  simp only [Prod.mk.injEq] at hy
  exact ⟨y, mem_cRelF_iff.1 ⟨hyF, hy.1⟩, hy.2⟩

end Restart

end RandRestart

end Sec7

end InteractingSLE
