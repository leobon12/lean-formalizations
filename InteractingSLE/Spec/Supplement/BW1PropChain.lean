/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Supplement.Q3KernelConfig

/-!
# Proposition BW1: the relative chain of the counterflow before its first contact with the completed piece

Packet PROVE-BW1-PROP. Supplement p. 614: "Before `T`, every compact counterflow prefix is physically separated from
`A` [...] Fixed-hull restriction and positive separation give continuous, strict relative Loewner growth". GB6's
landed relative chain (`Q3Kernel.exists_relChain_trace`, `exists_relChain_tip`, PROVE-Q3-REL2) assumes an interior tip
`α(s) ∈ ℍ` of the retained flow prefix, but uses it only to get `s > 0`. Proposition BW1 retains the completed piece,
whose trace ends on `ℝ` at `q`; its driver frozen at the lifetime has a global trace (`BW1PropFrozen`), so the
GB6 argument applies verbatim with `0 < s` in place of the interior tip:

* **`exists_relChain_trace_close`**, **`exists_relChain_tip_close`**: the proofs of PROVE-Q3-REL2 with that one
  hypothesis changed (the derivation of `0 < s` removed); credit: `Q3KernelRelTrace.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.BW1Prop

open Supp8 Supp8.Q3Kernel
open Supp8.GB6 (relMap relInv relClock firstContactTime sphereInv)
open Supp8.Q3Rel (invHull)

/-! ### The relative chain for a stop with positive own time -/

section Chain

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {U : ℝ → ℝ} {t₂ : ℝ}

/-- **The relative chain has a continuous trace, for a stop with positive own time** (deterministic;
`Q3Kernel.exists_relChain_trace` with `0 < s` in place of the interior tip `α(s) ∈ ℍ`, which that proof uses only to
get `0 < s`: at Proposition BW1's threshold the completed piece ends on `ℝ`). Let `α` be a generating trace of the
driver `wα` with `s < Tα`, `U` a continuous driver from `0` agreeing with `wα` on `[0, t₂]`, `s < t₂`, and `γ` a
complete generating trace of the continuous counterflow driver `w`. Before every `t₁ < T_c` (the first contact of the
physical counterflow with `α([0, s])`) there is a globally continuous relative driver `Wr` from `0` with a continuous
Loewner trace, generating `Ψ(K'_t)` at the relative clock `a(t)` for every `t ≤ t₁` (`Ψ = relMap U s`,
`a = relClock U s`). -/
theorem exists_relChain_trace_close (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hs0 : (0 : ℝ) < s) (hU : Continuous U) (hU0 : U 0 = 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      (∀ t : ℝ≥0, t ≤ t₁ →
        relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
          fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) ∧
      relClock U s (fun r : ℝ => w r.toNNReal) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock U s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock U s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
        Disjoint (closure (fwdHull U s)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) T)) :=
    by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Wc : ℝ → ℝ := fun r => w r.toNNReal with hWcdef
  have hWcc : Continuous Wc := hw.comp continuous_real_toNNReal
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, (fun r : ℝ => wα r.toNNReal) r = U r := fun r hr => (hUeq r hr).symm
  have hhull : fwdHull (fun r : ℝ => wα r.toNNReal) s = fwdHull U s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have htip : Tendsto (fwdMapInv U s) (𝓝[H] 0) (𝓝 (α s)) := by
    have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 hs
    rwa [fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree] at h1
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull U s))
      (closure ((fun w : ℂ => -w⁻¹) '' fwdHull Wc T)) := fun T hT => by
    rw [← hhull]
    exact GB6.disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα hwα0 hγ hw.continuousOn hw0 hs
      ENNReal.coe_lt_top hT
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hTc : 0 < Tc := by
    have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
      (hα.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le)
    have := GB6.firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
    rwa [image_image] at this
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → IsFilling (fwdHull Wc t) (γ '' Icc 0 t) :=
    fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨W', hW'0, ha0, hsm, hac, hW'c, hK⟩ := GB6.exists_glued_relChain hw hw0 hU hU0 hs0 htip hTc hd hγK
  set a : ℝ → ℝ := relClock U s Wc with hadef
  obtain ⟨t₃, ht₁₃, ht₃⟩ : ∃ t₃ : ℝ≥0, t₁ < t₃ ∧ (t₃ : ℝ≥0∞) < Tc := by
    obtain ⟨r, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₁
    exact ⟨r, ENNReal.coe_lt_coe.1 h1, h2⟩
  obtain ⟨t₄, ht₃₄, ht₄⟩ : ∃ t₄ : ℝ≥0, t₃ < t₄ ∧ (t₄ : ℝ≥0∞) < Tc := by
    obtain ⟨r, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₃
    exact ⟨r, ENNReal.coe_lt_coe.1 h1, h2⟩
  -- the clock on `[0, t₃]` as a function of a real variable
  have hltTc : ∀ r : ℝ, r ≤ t₃ → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr)) ht₃
  have haR : ∀ r : ℝ, 0 ≤ r → a r = a (r.toNNReal : ℝ) := fun r hr => by rw [Real.coe_toNNReal _ hr]
  have hsmI : StrictMonoOn a (Icc 0 (t₃ : ℝ)) := fun x hx y hy hxy => by
    rw [haR x hx.1, haR y hy.1]
    exact hsm (hltTc x hx.2) (hltTc y hy.2) ((Real.toNNReal_lt_toNNReal_iff' ).2 ⟨hxy, lt_of_le_of_lt hx.1 hxy⟩)
  have hacI : ContinuousOn a (Icc 0 (t₃ : ℝ)) := by
    have h1 : ContinuousOn (fun r : ℝ => a (r.toNNReal : ℝ)) (Icc 0 (t₃ : ℝ)) :=
      hac.comp continuous_real_toNNReal.continuousOn fun r hr => hltTc r hr.2
    exact h1.congr fun r hr => haR r hr.1
  obtain ⟨c, hcc, hcmem, hca⟩ := exists_clockInv_Icc (T := (t₃ : ℝ)) t₃.2 ha0 hacI hsmI
  have hmonoI : MonotoneOn a (Icc 0 (t₃ : ℝ)) := hsmI.monotoneOn
  set b : ℝ := a t₁ with hbdef
  set b₃ : ℝ := a t₃ with hb₃def
  have hbb₃ : b < b₃ := hsm (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁₃.le) ht₃) ht₃ ht₁₃
  have hb₃₄ : b₃ < a t₄ := hsm ht₃ ht₄ ht₃₄
  have hb0 : 0 ≤ b := by
    have := hmonoI ⟨le_rfl, t₃.2⟩ ⟨t₁.2, by exact_mod_cast ht₁₃.le⟩ t₁.2
    rwa [ha0] at this
  have hb₃0 : 0 ≤ b₃ := hb0.trans hbb₃.le
  -- the relative driver frozen after `b₃`
  set W₃ : ℝ → ℝ := frozenDrive W' b₃ with hW₃def
  have hW₃c : Continuous W₃ := continuous_frozenDrive (hW'c.mono fun u hu => by
    refine ⟨t₄, ht₄, lt_of_le_of_lt ?_ hb₃₄⟩
    have : (u : ℝ) ≤ (b₃.toNNReal : ℝ) := by exact_mod_cast hu
    rwa [Real.coe_toNNReal _ hb₃0] at this)
  have hW₃0 : W₃ 0 = 0 := by rw [hW₃def, frozenDrive_zero hb₃0, hW'0]
  have hW₃eq : ∀ r ∈ Icc (0 : ℝ) b₃, W₃ r = (fun r : ℝ => W' r.toNNReal) r := fun r hr => frozenDrive_eq hr
  have hW₃hull : ∀ v, 0 ≤ v → v < b₃ → fwdHull W₃ v = fwdHull (fun r : ℝ => W' r.toNNReal) v :=
    fun v hv hvb => fwdHull_eq_of_eqOn hv hvb hW₃eq
  -- the counterflow trace stays among the good points of `Ψ` up to `t₃`
  have hγL := isLoewnerTrace_of_isGeneratingTrace hγ
  have hdA : Disjoint (closure (fwdHull Wc t₃)) (closure (invHull U s)) :=
    Q3Rel.disjoint_closure_invHull hU hs0.le (hd t₃ ht₃)
  have hgood : ∀ r : ℝ≥0, r ≤ t₃ → γ r ∈ relGood U s := by
    intro r hr
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ r) with h0 | h0
    · rw [← h0]
      show γ 0 ∈ relGood U s
      rw [hγ.1]
      exact Or.inr ⟨Complex.zero_im, zero_notMem_closure_invHull hU hs0.le⟩
    · have h1 : γ r ∈ closure (fwdHull Wc r) := by
        have := trace_mem_closure_fwdHull hγL hWcc (by simp [hw0]) (u := (r : ℝ)) (by exact_mod_cast h0)
        simpa using this
      have h2 : γ r ∈ closure (fwdHull Wc t₃) := closure_mono (fwdHull_mono' (by exact_mod_cast hr)) h1
      have hnA : γ r ∉ closure (invHull U s) := fun h => Set.disjoint_left.1 hdA h2 h
      have hHb : γ r ∈ Hbar := by
        have hsub : closure (fwdHull Wc t₃) ⊆ Hbar := by
          rw [← closure_H]; exact closure_mono (isHPHull_fwdHull hWcc t₃.2).1
        exact hsub h2
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (γ r).im from hHb) with him | him
      · exact Or.inr ⟨him.symm, hnA⟩
      · exact Or.inl ⟨him, fun h => hnA (subset_closure h)⟩
  -- the relative trace before `b₃`: the chart image of the counterflow trace through the inverse clock
  set Γ : ℝ → ℂ := fun v => relExt U s (γ (c v).toNNReal) with hΓdef
  have hcle : ∀ v ∈ Icc (0 : ℝ) b₃, (c v).toNNReal ≤ t₃ := fun v hv =>
    Real.toNNReal_le_iff_le_coe.2 (hcmem v hv).1.2
  have hc0 : c 0 = 0 := by
    have := hca 0 ⟨le_rfl, t₃.2⟩
    rwa [ha0] at this
  have hΓ0 : Γ 0 = 0 := by
    simp only [hΓdef, hc0, Real.toNNReal_zero]
    rw [hγ.1]
    exact relExt_zero hU hU0 hs0.le
  have hΓc : ContinuousOn Γ (Icc 0 b₃) := by
    have h1 : ContinuousOn (fun v => γ (c v).toNNReal) (Icc 0 b₃) :=
      (hγc.comp continuous_real_toNNReal).comp_continuousOn hcc
    exact (continuousOn_relExt hU hU0 hs0.le).comp h1 fun v hv => hgood _ (hcle v hv)
  have himg : ∀ v ∈ Icc (0 : ℝ) b₃, Γ '' Icc 0 v = relExt U s '' (γ '' Icc 0 (c v).toNNReal) := by
    intro v hv
    have hcv := hcmem v hv
    have hci : c '' Icc 0 v = Icc 0 (c v) := by
      ext r
      constructor
      · rintro ⟨v', hv', rfl⟩
        have hv'b : v' ∈ Icc (0 : ℝ) b₃ := ⟨hv'.1, hv'.2.trans hv.2⟩
        have hcv' := hcmem v' hv'b
        refine ⟨hcv'.1.1, ?_⟩
        by_contra hlt
        push Not at hlt
        have := hsmI hcv.1 hcv'.1 hlt
        rw [hcv.2, hcv'.2] at this
        linarith [hv'.2]
      · intro hr
        have hrI : r ∈ Icc (0 : ℝ) t₃ := ⟨hr.1, hr.2.trans hcv.1.2⟩
        refine ⟨a r, ⟨?_, ?_⟩, hca r hrI⟩
        · have := hmonoI ⟨le_rfl, t₃.2⟩ hrI hr.1
          rwa [ha0] at this
        · have := hmonoI hrI hcv.1 hr.2
          rwa [hcv.2] at this
    rw [show Γ = relExt U s ∘ (fun x : ℝ => γ x.toNNReal) ∘ c from rfl, image_comp, image_comp, hci,
      image_toNNReal_Icc γ hcv.1.1]
  have hLT : IsLoewnerTraceLT W₃ b₃ Γ := by
    refine ⟨hΓ0, hΓc.mono Ico_subset_Icc_self, fun v hv hvb => ?_⟩
    have hvI : v ∈ Icc (0 : ℝ) b₃ := ⟨hv, hvb.le⟩
    obtain ⟨hcvI, hacv⟩ := hcmem v hvI
    set tN : ℝ≥0 := (c v).toNNReal with htN
    have htNc : (tN : ℝ) = c v := Real.coe_toNNReal _ hcvI.1
    have htN3 : tN ≤ t₃ := hcle v hvI
    have htNTc : (tN : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htN3) ht₃
    have hav : a (tN : ℝ) = v := by rw [htNc]; exact hacv
    obtain ⟨hKt, hFt⟩ := hK tN htNTc
    rw [hW₃hull v hv hvb, himg v hvI]
    rw [hav] at hKt hFt
    have hsubg : γ '' Icc 0 tN ⊆ relGood U s := by
      rintro _ ⟨r, hr, rfl⟩
      exact hgood r (hr.2.trans htN3)
    have hKcc : IsCompact (relExt U s '' (γ '' Icc 0 tN)) := (isCompact_Icc.image hγc).image_of_continuousOn
      ((continuousOn_relExt hU hU0 hs0.le).mono hsubg)
    have hKcH := relExt_image_inter_H hU hU0 hs0.le hsubg
    have hHK : H \ relExt U s '' (γ '' Icc 0 tN) = H \ relMap U s '' (γ '' Icc 0 tN ∩ H) := by
      rw [← hKcH, sdiff_inter_self_eq_sdiff]
    have hFill : IsFilling (fwdHull (fun r : ℝ => W' r.toNNReal) v) (relExt U s '' (γ '' Icc 0 tN)) := by
      unfold IsFilling at hFt ⊢
      rw [hHK]
      exact hFt
    have hKH : fwdHull (fun r : ℝ => W' r.toNNReal) v ⊆ H := by
      rw [← hW₃hull v hv hvb]
      exact (isHPHull_fwdHull hW₃c hv).1
    exact (fillH_eq_iff_isFilling_of_isClosed hKcc.isBounded hKcc.isClosed hKH).1 hFill
  have hext := hLT.isLoewnerTrace_ext hW₃c hW₃0 hb0 hbb₃
  refine ⟨YuanCorollary13.extDrive W₃ b, YuanCorollary13.extTrace W₃ Γ b, YuanCorollary13.continuous_extDrive hW₃c,
    YuanCorollary13.extDrive_zero hW₃0 hb0, hext, fun t ht => ?_, ha0, hsm, hac, hd⟩
  have htTc : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) ht₁
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) t₃ := ⟨t.2, by exact_mod_cast ht.trans ht₁₃.le⟩
  have hav0 : 0 ≤ a t := by
    have := hmonoI ⟨le_rfl, t₃.2⟩ htI t.2
    rwa [ha0] at this
  have hatb : a t ≤ b := hmonoI htI ⟨t₁.2, by exact_mod_cast ht₁₃.le⟩ (by exact_mod_cast ht)
  show relMap U s '' fwdHull Wc t = fwdHull (YuanCorollary13.extDrive W₃ b) (a t)
  rw [YuanCorollary13.fwdHull_eq_of_eqOn_Icc (YuanCorollary13.continuous_extDrive hW₃c) hW₃c hav0
    (fun r hr => YuanCorollary13.extDrive_eq (hr.2.trans hatb)), hW₃hull _ hav0 (hatb.trans_lt hbb₃)]
  exact (hK t htTc).1.symm

/-- **The relative chain at a counterflow time `t`, with the tip identity, for a stop with positive own time**
(deterministic; `Q3Kernel.exists_relChain_tip` with `0 < s` in place of the interior tip `α(s) ∈ ℍ`, which that
proof uses only to get `0 < s`). For `0 < t < t₁ < T_c`: a globally continuous relative driver `Wr` from `0` with a
continuous Loewner trace generates `Ψ(K'_t)` at `u = a(t) > 0`, the flow-frame closures are disjoint at `t`, and the
transition `g'_t ∘ Ψi ∘ f̃_u` tends to `0` at `0`. -/
theorem exists_relChain_tip_close (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hs0 : (0 : ℝ) < s) (hU : Continuous U) (hU0 : U 0 = 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hΨ : Q3Rel.IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (Q3Rel.relLog U s) (Q3Rel.relBad U s))
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t t₁ : ℝ≥0} (ht0 : 0 < t)
    (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) ∧
      Disjoint (closure (fwdHull U s)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) t)) ∧
      Tendsto (fun y => fwdMap (fun r : ℝ => w r.toNNReal) t
        (relInv U s (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) y))) (𝓝[H] 0) (𝓝 0) := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Wc : ℝ → ℝ := fun r => w r.toNNReal with hWcdef
  have hWcc : Continuous Wc := hw.comp continuous_real_toNNReal
  have hWc0 : Wc 0 = 0 := by simp [hWcdef, hw0]
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hK, ha0, hsm, hac, hd⟩ :=
    exists_relChain_trace_close hα hwα hwα0 hs hs0 hU hU0 hst₂ hUeq hγ hw hw0 ht₁
  set a : ℝ → ℝ := relClock U s Wc with hadef
  have htTc : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htt₁.le) ht₁
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := lt_of_le_of_lt bot_le htTc
  have hu : 0 < a t := by
    have := hsm h0Tc htTc ht0
    simpa [ha0] using this
  have hKt := hK t htt₁.le
  have hdt := hd t htTc
  have hdA : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull Wc T)) (closure (invHull U s)) :=
    fun T hT => Q3Rel.disjoint_closure_invHull hU hs0.le (hd T hT)
  have hγL := isLoewnerTrace_of_isGeneratingTrace hγ
  have hSbK := Q3Rel.relBad_notMem_closure hU hU0 hs0.le hWcc t.2 hKt (hdA t htTc)
  obtain ⟨hg, hA0⟩ := goodPt_zero_and_notMem hΨ hWcc t.2 hWr hWr0 hηr hu hKt (hdA t htTc) hSbK
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hKt, hdt, ?_⟩
  refine tendsto_tip_of_later hΨ hWcc hWc0 hγL t.2 hWr hWr0 hηr hu.le hKt (hdA t htTc) hg hA0 fun δ hδ => ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt (fun t : ℝ≥0 => a t) t := hac.continuousAt (hopen.mem_nhds htTc)
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hcont δ hδ
  set ε : ℝ := min (min δ η) ((t₁ : ℝ) - t) / 2 with hεdef
  have htt₁' : (t : ℝ) < t₁ := by exact_mod_cast htt₁
  have hε0 : 0 < ε := by
    have : 0 < min (min δ η) ((t₁ : ℝ) - t) := lt_min (lt_min hδ hη) (by linarith)
    rw [hεdef]; linarith
  have hεδ : ε < δ := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_left δ η
    rw [hεdef]; linarith
  have hεη : ε < η := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_right δ η
    rw [hεdef]; linarith
  have hεt : ε < (t₁ : ℝ) - t := by
    have := min_le_right (min δ η) ((t₁ : ℝ) - t)
    rw [hεdef]; linarith
  set t' : ℝ≥0 := ⟨(t : ℝ) + ε, by positivity⟩ with ht'def
  have ht'v : (t' : ℝ) = t + ε := rfl
  have htt' : t < t' := by rw [← NNReal.coe_lt_coe, ht'v]; linarith
  have ht't₁ : t' ≤ t₁ := by rw [← NNReal.coe_le_coe, ht'v]; linarith
  have ht'Tc : (t' : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht't₁) ht₁
  have hdist : dist t' t < η := by
    rw [NNReal.dist_eq, ht'v, add_sub_cancel_left, abs_of_pos hε0]
    exact hεη
  have hau : a t < a t' := hsm htTc ht'Tc htt'
  have hau' : a t' < a t + δ := by
    have := hηb hdist
    rw [Real.dist_eq] at this
    linarith [le_abs_self (a t' - a t)]
  refine ⟨t', a t', by rw [ht'v]; linarith, by rw [ht'v]; linarith, hau, hau', hK t' ht't₁, ?_⟩
  exact Set.disjoint_of_subset_left subset_closure
    (Set.disjoint_of_subset_right subset_closure (hdA t' ht'Tc))

end Chain

end InteractingSLE.Theorem14.BW1Prop
