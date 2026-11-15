/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11Proof
import InteractingSLE.Foundations.Loewner.ConformalImageLoewner

/-!
# Lemma GB11's relative Loewner parametrization: reduction to the local growth of the relative hulls

Packet PROVE-T14-GW4T3, item (1). `GW4Reg.GB11RelParamStatement` (PROVE-T14-GW4T2) asks, for an actual extreme pocket
`C` with a component chart `c`, a **maximal** continuous relative Loewner parametrization `(S, W_rel, T)` of the
traversal (`GB11.IsGB11RelParam`) with `T 0 = τ` the entry time. Its relative hulls are
`B(u) = Φ(K'_{τ+u} ∩ R⁻¹(C))`, `Φ = relMapC c`, `0 ≤ u < L = σ − τ`.

By [Law05] §4.1 (landed: `ConformalImage.IsContinuouslyGrowing.loewner`), a family of compact `ℍ`-hulls that is empty
at `0`, increasing, strictly increasing and **continuously growing** with a continuous driving function `U` is a
Loewner chain after the capacity time change. This file proves:

* `fwdHull_eq_of_eqOn_of_lt`: drivers agreeing on `[0, t']` have the same hull at every `t < t'` (no continuity);
* **`exists_maxChain`** (general): a family continuously growing on every `[0, T]`, `T < L`, with one driving
  function `U`, is a maximal Loewner chain on `[0, S)`, `S = sup_{T < L} hcap(B T)/2`, with a continuous strictly
  increasing inverse clock `θ` from `0` that tends to `L`;
* the elementary facts of the relative hulls of a pocket traversal: `relHull_zero` (empty at the entry time, from the
  entry and density clauses), `relHull_mono`, `relHull_strict` (strictly increasing, from the density clause and the
  strict growth of the ambient hulls), and `entryTime_lt_firstVisit` (`τ < σ`);
* **`gb11RelParamStatement_of_growth`**: `GB11RelParamStatement` from **`GB11RelGrowthStatement`**, the analytic core:
  the relative hulls are compact `ℍ`-hulls, and they grow continuously with a continuous driving function `U` from
  `U 0 = 0` (the relative chart sends the entry to `0`) on every `[0, T]`, `T < L`;
* the hull property from (GB11.2): `notMem_closure_fwdHull_of_lt` (a later trace point off the earlier trace is not in
  the closure of the earlier hull), `isBounded_relHull`, `isSimplyConnected_relDom`, and
  **`isHPHull_relHull_of_isPreconnected`**: `B u` is a compact `ℍ`-hull as soon as `R⁻¹(C) \ K'_{τ+u}` is preconnected;
* **`gb11RelGrowthStatement_of_conn`**, **`gb11RelParamStatement_of_connGrowth`**: the core from
  **`GB11RelConnGrowthStatement`** = (GB11.2) (that preconnectedness) + the local growth with `U 0 = 0`.

The remaining core is the relative-chain part of Aux. lemma 41 for walls that may run along `ℝ`; see the handoff of
PROVE-T14-GW4T3 for its status.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Theorem14

namespace GW4Reg

open GW4Traverse GW4Ident ConformalImage ConformalImage.IsContinuouslyGrowing

/-! ### Hulls of drivers agreeing slightly beyond the time -/

/-- **Two drivers agreeing on `[0, t']` have the same hull at every time `0 ≤ t < t'`** (no continuity needed: a
point outside the hull at time `t` has a forward solution on some `[0, T]`, `T > t`, which restricts to
`[0, min T t']`). -/
theorem fwdHull_eq_of_eqOn_of_lt {V V' : ℝ → ℝ} {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t')
    (h : ∀ r ∈ Icc (0 : ℝ) t', V r = V' r) : fwdHull V t = fwdHull V' t := by
  have key : ∀ {V V' : ℝ → ℝ}, (∀ r ∈ Icc (0 : ℝ) t', V r = V' r) → fwdHull V t ⊆ fwdHull V' t := by
    intro V V' h z hz
    refine ⟨hz.1, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨_, ⟨T, ⟨hT0, u, hu⟩, rfl⟩, hTlt⟩ := lt_sSup_iff.1 hlt
    have hTt : t < T := ((ENNReal.ofReal_lt_ofReal_iff').1 hTlt).1
    have hT₀ : t < min T t' := lt_min hTt htt'
    have hu' : QuantumZipper.IsForwardSol V' z (min T t') u :=
      QuantumZipper.isForwardSol_restrict hu (ht.trans hT₀.le) (min_le_left _ _)
    have hu'' : QuantumZipper.IsForwardSol V z (min T t') u :=
      QuantumZipper.isForwardSol_congr_drive
        (fun r hr => (h r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩).symm) hu'
    have hle := QuantumZipper.ofReal_le_swallowTime (ht.trans hT₀.le) ⟨u, hu''⟩
    have hlt' : ENNReal.ofReal t < ENNReal.ofReal (min T t') := (ENNReal.ofReal_lt_ofReal_iff (ht.trans_lt hT₀)).2 hT₀
    exact absurd hz.2 (not_le.2 (hlt'.trans_le hle))
  exact (key h).antisymm (key fun r hr => (h r hr).symm)

/-! ### A maximal Loewner chain from a family growing on `[0, L)` -/

section MaxChain

variable {B : ℝ → Set ℂ} {U : ℝ → ℝ} {L : ℝ≥0∞}

/-- The admissible horizons `T ∈ [0, L)`. -/
def horizon (L : ℝ≥0∞) : Set ℝ := {T | 0 ≤ T ∧ ENNReal.ofReal T < L}

/-- The inverse capacity clock on `[0, L)`. -/
def invClock (B : ℝ → Set ℂ) (L : ℝ≥0∞) (s : ℝ) : ℝ := Function.invFunOn (cap B) (horizon L) s

/-- The total capacity time `sup_{T < L} hcap(B T)/2`. -/
def capSup (B : ℝ → Set ℂ) (L : ℝ≥0∞) : ℝ≥0∞ := ⨆ T ∈ horizon L, ENNReal.ofReal (cap B T)

theorem strictMonoOn_cap_horizon (hG : ∀ T ∈ horizon L, IsContinuouslyGrowing B U T) :
    StrictMonoOn (cap B) (horizon L) := fun _ ha b hb hab =>
  (hG b hb).strictMonoOn_cap ⟨ha.1, hab.le⟩ ⟨hb.1, le_rfl⟩ hab

theorem mem_horizon_of_le {T T' : ℝ} (hT : T ∈ horizon L) (h0 : 0 ≤ T') (hle : T' ≤ T) : T' ∈ horizon L :=
  ⟨h0, (ENNReal.ofReal_le_ofReal hle).trans_lt hT.2⟩

/-- On `[0, hcap(B T)/2]` the inverse clock is the inverse clock of the growth on `[0, T]`. -/
theorem invClock_eq_invCap (hG : ∀ T ∈ horizon L, IsContinuouslyGrowing B U T) {T s : ℝ} (hT : T ∈ horizon L)
    (hs : s ∈ Icc 0 (cap B T)) : invClock B L s = invCap B T s := by
  have hm := (hG T hT).invCap_mem hT.1 hs
  have hc := (hG T hT).cap_invCap hT.1 hs
  have hmem : invCap B T s ∈ horizon L := mem_horizon_of_le hT hm.1 hm.2
  have hex : s ∈ cap B '' horizon L := ⟨_, hmem, hc⟩
  exact (strictMonoOn_cap_horizon hG).injOn (Function.invFunOn_mem hex) hmem
    ((Function.invFunOn_eq hex).trans hc.symm)

theorem invClock_mem (hG : ∀ T ∈ horizon L, IsContinuouslyGrowing B U T) {T s : ℝ} (hT : T ∈ horizon L)
    (hs : s ∈ Icc 0 (cap B T)) : invClock B L s ∈ Icc 0 T := by
  rw [invClock_eq_invCap hG hT hs]
  exact (hG T hT).invCap_mem hT.1 hs

theorem cap_invClock (hG : ∀ T ∈ horizon L, IsContinuouslyGrowing B U T) {T s : ℝ} (hT : T ∈ horizon L)
    (hs : s ∈ Icc 0 (cap B T)) : cap B (invClock B L s) = s := by
  rw [invClock_eq_invCap hG hT hs]
  exact (hG T hT).cap_invCap hT.1 hs

/-- Below the total capacity, a horizon with larger capacity exists. -/
theorem exists_lt_cap {s : ℝ} (hs : ENNReal.ofReal s < capSup B L) : ∃ T ∈ horizon L, s < cap B T := by
  obtain ⟨T, hT⟩ := lt_iSup_iff.1 hs
  obtain ⟨hTm, hlt⟩ := lt_iSup_iff.1 hT
  exact ⟨T, hTm, ((ENNReal.ofReal_lt_ofReal_iff').1 hlt).1⟩

theorem ofReal_cap_le_capSup {T : ℝ} (hT : T ∈ horizon L) : ENNReal.ofReal (cap B T) ≤ capSup B L :=
  le_iSup₂ (f := fun T (_ : T ∈ horizon L) => ENNReal.ofReal (cap B T)) T hT

/-- **A maximal Loewner chain from a family that grows continuously on every `[0, T]`, `T < L`** (with one driving
function `U`): with `S = sup_{T < L} hcap(B T)/2 > 0` and the inverse capacity clock `θ` (continuous, strictly
increasing, `θ 0 = 0`, `θ < L`, `θ → L` as `s → S`), the driver `V = U ∘ θ` is continuous on `[0, S)` and its hull at
time `s < S` is `B (θ s)`. -/
theorem exists_maxChain (hL : 0 < L) (hG : ∀ T ∈ horizon L, IsContinuouslyGrowing B U T) :
    ∃ (S : ℝ≥0∞) (V : ℝ≥0 → ℝ) (θ : ℝ≥0 → ℝ≥0), 0 < S ∧ ContinuousOn V {s | (s : ℝ≥0∞) < S} ∧ V 0 = U 0 ∧
      StrictMonoOn θ {s | (s : ℝ≥0∞) < S} ∧ ContinuousOn θ {s | (s : ℝ≥0∞) < S} ∧ θ 0 = 0 ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < S → (θ s : ℝ≥0∞) < L) ∧
      Tendsto (fun s : ℝ≥0 => (θ s : ℝ≥0∞)) (comap (fun s : ℝ≥0 => (s : ℝ≥0∞)) (𝓝[<] S)) (𝓝 L) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) < S → fwdHull (fun r : ℝ => V r.toNNReal) s = B (θ s) := by
  obtain ⟨T₀, hT₀0, hT₀pos, hT₀L⟩ := ENNReal.lt_iff_exists_real_btwn.1 hL
  have hT₀ : T₀ ∈ horizon L := ⟨hT₀0, hT₀L⟩
  have hcap0 : cap B 0 = 0 := (hG T₀ hT₀).cap_zero hT₀0
  have h0h : (0 : ℝ) ∈ horizon L := mem_horizon_of_le hT₀ le_rfl hT₀0
  have hcapT₀ : 0 < cap B T₀ := hcap0 ▸ strictMonoOn_cap_horizon hG h0h hT₀ (ENNReal.ofReal_pos.1 hT₀pos)
  have hbig : ∀ s : ℝ≥0, (s : ℝ≥0∞) < capSup B L → ∃ T ∈ horizon L, (s : ℝ) < cap B T := fun s hs =>
    exists_lt_cap (by rwa [ENNReal.ofReal_coe_nnreal])
  have hI : ∀ (s : ℝ≥0) {T : ℝ}, (s : ℝ) < cap B T → (s : ℝ) ∈ Icc 0 (cap B T) := fun s _ h => ⟨s.2, h.le⟩
  have hinv0 : invClock B L 0 = 0 := by
    rw [invClock_eq_invCap hG hT₀ ⟨le_rfl, hcapT₀.le⟩]
    exact (hG T₀ hT₀).invCap_zero hT₀0
  have hmemH : ∀ (s : ℝ≥0) {T : ℝ}, T ∈ horizon L → (s : ℝ) < cap B T → invClock B L s ∈ horizon L :=
    fun s T hT h => mem_horizon_of_le hT (invClock_mem hG hT (hI s h)).1 (invClock_mem hG hT (hI s h)).2
  have hnhds : ∀ (s : ℝ≥0) {T : ℝ}, (s : ℝ) < cap B T → {s' : ℝ≥0 | (s' : ℝ) < cap B T} ∈ 𝓝 s :=
    fun s _ h => (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds h
  refine ⟨capSup B L, fun s => U (invClock B L s), fun s => (invClock B L s).toNNReal,
    (ENNReal.ofReal_pos.2 hcapT₀).trans_le (ofReal_cap_le_capSup hT₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨T, hT, hlt⟩ := hbig s hs
    have hev : (fun s' : ℝ≥0 => drv B U T s') =ᶠ[𝓝 s] fun s' : ℝ≥0 => U (invClock B L s') := by
      filter_upwards [hnhds s hlt] with s' hs'
      rw [drv_eq B U T (hI s' hs'), invClock_eq_invCap hG hT (hI s' hs')]
    exact ((((hG T hT).continuous_drv hT.1).comp NNReal.continuous_coe).continuousAt.congr hev).continuousWithinAt
  · show U (invClock B L ((0 : ℝ≥0) : ℝ)) = U 0
    rw [NNReal.coe_zero, hinv0]
  · intro s hs s' hs' hss'
    obtain ⟨T, hT, hlt⟩ := hbig s' hs'
    have hlt₀ : (s : ℝ) < cap B T := (NNReal.coe_lt_coe.2 hss').trans hlt
    have hlt' : invClock B L s < invClock B L s' := by
      refine ((strictMonoOn_cap_horizon hG).lt_iff_lt (hmemH s hT hlt₀) (hmemH s' hT hlt)).1 ?_
      rw [cap_invClock hG hT (hI s hlt₀), cap_invClock hG hT (hI s' hlt)]
      exact hss'
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (hmemH s hT hlt₀).1).2 hlt'
  · intro s hs
    obtain ⟨T, hT, hlt⟩ := hbig s hs
    have hc : ContinuousOn (fun s' : ℝ≥0 => invCap B T s') {s' : ℝ≥0 | (s' : ℝ) < cap B T} :=
      ((hG T hT).continuousOn_invCap hT.1).comp NNReal.continuous_coe.continuousOn fun s' hs' => hI s' hs'
    have hev : (fun s' : ℝ≥0 => (invCap B T s').toNNReal) =ᶠ[𝓝 s]
        fun s' : ℝ≥0 => (invClock B L s').toNNReal := by
      filter_upwards [hnhds s hlt] with s' hs'
      rw [invClock_eq_invCap hG hT (hI s' hs')]
    exact ((continuous_real_toNNReal.continuousAt.comp ((hc s hlt).continuousAt (hnhds s hlt))).congr
      hev).continuousWithinAt
  · show (invClock B L ((0 : ℝ≥0) : ℝ)).toNNReal = 0
    rw [NNReal.coe_zero, hinv0, Real.toNNReal_zero]
  · intro s hs
    obtain ⟨T, hT, hlt⟩ := hbig s hs
    exact (hmemH s hT hlt).2
  · rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨T₂, hT₂0, haT₂, hT₂L⟩ := ENNReal.lt_iff_exists_real_btwn.1 ha
      obtain ⟨T₃, hT₃0, hT₂₃, hT₃L⟩ := ENNReal.lt_iff_exists_real_btwn.1 hT₂L
      have hT₂ : T₂ ∈ horizon L := ⟨hT₂0, hT₂L⟩
      have hT₃ : T₃ ∈ horizon L := ⟨hT₃0, hT₃L⟩
      have hc23 : cap B T₂ < cap B T₃ :=
        strictMonoOn_cap_horizon hG hT₂ hT₃ ((ENNReal.ofReal_lt_ofReal_iff').1 hT₂₃).1
      have hc2 : 0 ≤ cap B T₂ := by
        rcases eq_or_lt_of_le hT₂0 with h | h
        · rw [← h, hcap0]
        · exact hcap0 ▸ (strictMonoOn_cap_horizon hG h0h hT₂ h).le
      have hcS : ENNReal.ofReal (cap B T₂) < capSup B L :=
        ((ENNReal.ofReal_lt_ofReal_iff (hc2.trans_lt hc23)).2 hc23).trans_le (ofReal_cap_le_capSup hT₃)
      refine mem_comap.2 ⟨Ioo (ENNReal.ofReal (cap B T₂)) (capSup B L), Ioo_mem_nhdsLT hcS, fun s hs => ?_⟩
      obtain ⟨hs1, hs2⟩ := hs
      change ENNReal.ofReal (cap B T₂) < (s : ℝ≥0∞) at hs1
      change (s : ℝ≥0∞) < capSup B L at hs2
      show a < ENNReal.ofReal (invClock B L s)
      obtain ⟨T, hT, hlt⟩ := hbig s hs2
      rw [← ENNReal.ofReal_coe_nnreal] at hs1
      have hcs : cap B T₂ < s := ((ENNReal.ofReal_lt_ofReal_iff').1 hs1).1
      have hTs : T₂ < invClock B L s := by
        refine ((strictMonoOn_cap_horizon hG).lt_iff_lt hT₂ (hmemH s hT hlt)).1 ?_
        rw [cap_invClock hG hT (hI s hlt)]
        exact hcs
      exact haT₂.trans ((ENNReal.ofReal_lt_ofReal_iff (hT₂0.trans_lt hTs)).2 hTs)
    · refine mem_comap.2 ⟨Iio (capSup B L), self_mem_nhdsWithin, fun s hs => ?_⟩
      obtain ⟨T, hT, hlt⟩ := hbig s hs
      exact (hmemH s hT hlt).2.trans ha
  · intro s hs
    obtain ⟨T, hT, hlt⟩ := hbig s hs
    have hV : ∀ r ∈ Icc (0 : ℝ) (cap B T), (fun r : ℝ => U (invClock B L (r.toNNReal : ℝ))) r = drv B U T r :=
      fun r hr => by
        simp only
        rw [Real.coe_toNNReal r hr.1, drv_eq B U T hr, invClock_eq_invCap hG hT hr]
    show fwdHull (fun r : ℝ => U (invClock B L (r.toNNReal : ℝ))) s = B ((invClock B L s).toNNReal : ℝ)
    rw [fwdHull_eq_of_eqOn_of_lt s.coe_nonneg hlt hV]
    have hm := (hG T hT).invCap_mem hT.1 (hI s hlt)
    have hloe := ((hG T hT).loewner hT.1 hm).2.1
    rw [(hG T hT).cap_invCap hT.1 (hI s hlt)] at hloe
    rw [hloe, Real.coe_toNNReal _ (hmemH s hT hlt).1, invClock_eq_invCap hG hT (hI s hlt)]

end MaxChain

/-! ### The relative hulls of a pocket traversal -/

section RelHull

variable {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {C : Set ℂ}

/-- **The relative hull** of the traversal of `C` at relative time `u` after the entry time `τ`:
`Φ(K'_{τ+u} ∩ R⁻¹(C))`, `Φ = relMapC c`. -/
def relHull (W' : ℝ≥0 → ℝ) (c : Chart) (C : Set ℂ) (τ : ℝ≥0) (u : ℝ) : Set ℂ :=
  relMapC c '' (fwdHull (fun r : ℝ => W' r.toNNReal) ((τ : ℝ) + u) ∩ relDom C)

theorem relDom_eq_image (C : Set ℂ) : relDom C = (fun w : ℂ => -w⁻¹) '' C := by
  ext w
  constructor
  · intro hw
    exact ⟨-w⁻¹, hw, negInv_negInv' w⟩
  · rintro ⟨z, hz, rfl⟩
    show -(-z⁻¹)⁻¹ ∈ C
    rw [negInv_negInv']
    exact hz

theorem isPreconnected_relDom (hC : IsPreconnected C) (hCH : C ⊆ H) : IsPreconnected (relDom C) := by
  rw [relDom_eq_image]
  exact hC.image _ fun z hz => (continuousAt_negInv (ne_zero_of_mem_H' (hCH hz))).continuousWithinAt

theorem injOn_relMapC {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) :
    InjOn (relMapC c) (relDom C) :=
  fun w hw w' hw' h => by rw [← relInvC_relMapC hc hw, ← relInvC_relMapC hc hw', h]

/-- **No relative hull at the entry time**: `K'_τ ∩ R⁻¹(C) = ∅`. Before `τ` the counterflow avoids `C̄`, at `τ`
it is not in the open `C` (else it was there just before), so the preconnected `R⁻¹(C)` lies in one component of
`ℍ \ γ([0, τ])`; it cannot be filled, since it is open and the trace visits it after `τ` (density) while a
generating trace never visits the interior of an earlier hull. -/
theorem fwdHull_inter_relDom_eq_empty (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hCo : IsOpen C) (hCH : C ⊆ H) (hCc : IsPreconnected C) {τ : ℝ≥0} {σ : ℝ≥0∞} (hτσ : (τ : ℝ≥0∞) < σ)
    (hE : ∀ t : ℝ≥0, t < τ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C)
    (hD : ∀ a b : ℝ≥0, τ ≤ a → a < b → (b : ℝ≥0∞) < σ → ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) :
    fwdHull (fun r : ℝ => W' r.toNNReal) τ ∩ relDom C = ∅ := by
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hWc : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  rcases eq_zero_or_pos τ with h0 | hpos
  · rw [h0, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc, empty_inter]
  have hopen : IsOpen (γ ⁻¹' relDom C) := (isOpen_relDom hCo hCH).preimage hγc
  have hbefore : ∀ t : ℝ≥0, t < τ → γ t ∉ relDom C := fun t ht hmem => by
    have hne : γ t ≠ 0 := fun h0 => by
      have h' : -(γ t)⁻¹ ∈ C := hmem
      rw [h0, inv_zero, neg_zero] at h'
      exact ne_zero_of_mem_H' (hCH h') rfl
    exact hE t ht hne (subset_closure hmem)
  have hdisj : ∀ t ∈ Icc (0 : ℝ≥0) τ, γ t ∉ relDom C := by
    intro t ht hmem
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds (hopen.mem_nhds hmem) ⟨0, heq ▸ hpos⟩
      obtain ⟨t', ht'1, ht'2⟩ := exists_between hl
      exact hbefore t' (heq ▸ ht'2) (hsub ⟨ht'1, ht'2.le⟩)
    · exact hbefore t hlt hmem
  obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hγ.2.2 τ ENNReal.coe_lt_top
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) τ with hK
  have hsubF : relDom C ⊆ H \ γ '' Icc 0 τ := fun w hw =>
    ⟨relDom_subset_H hCH hw, fun ⟨t, ht, e⟩ => hdisj t ht (e ▸ hw)⟩
  by_contra hne
  obtain ⟨w, hwK, hwC⟩ := nonempty_iff_ne_empty.2 hne
  by_cases hx : ∃ x ∈ relDom C, x ∉ K
  · obtain ⟨x, hxC, hxK⟩ := hx
    have hxH : x ∈ connectedComponentIn (H \ γ '' Icc 0 τ) z₀ := by
      rw [hcomp]
      exact ⟨relDom_subset_H hCH hxC, hxK⟩
    have hsub := (isPreconnected_relDom hCc hCH).subset_connectedComponentIn hxC hsubF
    rw [← connectedComponentIn_eq hxH, hcomp] at hsub
    exact (hsub hwC).2 hwK
  · push Not at hx
    have hint : relDom C ⊆ interior K := (isOpen_relDom hCo hCH).subset_interior_iff.2 hx
    obtain ⟨b, hτb, hbσ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτσ
    obtain ⟨t, ht, -, hmem⟩ := hD τ b le_rfl (ENNReal.coe_lt_coe.1 hτb) hbσ
    exact Sec5.notMem_interior_fwdHull_of_lt hW' hW'0 hγ ht.1 (hint hmem)

/-- **The traversal fills new points of the pocket on every interval** `[a, b] ⊆ [τ, σ)`: some `w ∈ R⁻¹(C)` lies in
`K'_b \ K'_a` (an open-`C` visit at `t₀ ∈ (a, b)`; on a left neighbourhood `(l, t₀]` the trace stays in `R⁻¹(C)`, and
on every interval the trace visits the new part of its hull). -/
theorem exists_mem_relDom_fwdHull_sdiff (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hCo : IsOpen C) (hCH : C ⊆ H) {τ : ℝ≥0} {σ : ℝ≥0∞}
    (hD : ∀ a b : ℝ≥0, τ ≤ a → a < b → (b : ℝ≥0∞) < σ → ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    {a b : ℝ≥0} (ha : τ ≤ a) (hab : a < b) (hb : (b : ℝ≥0∞) < σ) :
    ∃ w ∈ relDom C, w ∈ fwdHull (fun r : ℝ => W' r.toNNReal) b ∧ w ∉ fwdHull (fun r : ℝ => W' r.toNNReal) a := by
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  obtain ⟨t₀, ht₀, -, hmem⟩ := hD a b ha hab hb
  have hopen : IsOpen (γ ⁻¹' relDom C) := (isOpen_relDom hCo hCH).preimage hγc
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds (hopen.mem_nhds hmem) ⟨a, ht₀.1⟩
  obtain ⟨v, hv1, hv2, hvK⟩ := Sec5.exists_mem_fwdHull_sdiff hW' hW'0 hγ (max_lt hl ht₀.1)
  exact ⟨γ v, hsub ⟨(le_max_left _ _).trans_lt hv1, hv2⟩,
    QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 ht₀.2.le) hvK.1,
    fun h => hvK.2 (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 (le_max_right _ _)) h)⟩

/-- A first visit time is positive (the trace starts at `0`, which is no physical point). -/
theorem firstVisit_pos (hγ0 : γ 0 = 0) (hγc : Continuous γ) (p : ℂ) : 0 < GB11.firstVisit γ p := by
  rcases eq_or_ne (GB11.firstVisit γ p) ⊤ with h | h
  · rw [h]
    exact ENNReal.zero_lt_top
  · obtain ⟨t, ht, hne, -⟩ := exists_eq_firstVisit hγc (lt_top_iff_ne_top.2 h)
    rw [← ht]
    have h0 : t ≠ 0 := fun h0 => hne (h0 ▸ hγ0)
    exact ENNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)

/-- **The entry precedes the exit**: `τ < σ` (reverse first visits along `α_R`; an exit at `x = 0` is never
visited). -/
theorem entryTime_lt_firstVisit (hγ0 : γ 0 = 0) (hγc : Continuous γ) {αR αL : ℝ≥0 → ℂ}
    (hB : GB11.IsGB11Barrier αR αL γ) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞} (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) :
    (entryTime γ αR s₂ : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) := by
  by_cases h2 : s₂ = ⊤
  · simp only [entryTime, h2, ↓reduceIte, ENNReal.coe_zero]
    exact firstVisit_pos hγ0 hγc _
  · simp only [entryTime, h2, ↓reduceIte]
    have hlt : s₁ < s₂.toNNReal := by
      have h := hs.lt
      rw [← ENNReal.coe_toNNReal h2] at h
      exact ENNReal.coe_lt_coe.1 h
    rcases eq_zero_or_pos s₁ with h1 | h1
    · have hfv : GB11.firstVisit γ 0 = ⊤ := by
        by_contra hne
        exact ne_zero_of_firstVisit_lt_top (lt_top_iff_ne_top.2 hne) rfl
      rw [h1, hB.1.2.2.1, hfv]
      exact ENNReal.coe_lt_top
    · have hrev := hB.2.2.2.2.2.1 s₁ s₂.toNNReal h1 hlt
      rw [ENNReal.coe_toNNReal (hrev.trans_le le_top).ne]
      exact hrev

end RelHull

/-! ### The relative hulls are compact `ℍ`-hulls, given the connectivity (GB11.2) -/

section HullProp

open SupercriticalConformalCovariance (IsConformalBijection)

variable {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {C : Set ℂ}

/-- **A later trace point outside the earlier trace is not in the closure of the earlier hull**: for `t < s` with
`γ s ∉ γ([0, t])`, `γ s ∉ closure K'_t`. (A small half-disc `Q` around `γ s` avoids `γ([0, t])`; if it met `K'_t` it
would lie in a bounded component, hence in `int K'_t`; then near `s` the trace is real, against the visits of the
trace to the new part of its hull on every interval.) -/
theorem notMem_closure_fwdHull_of_lt (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    {t s : ℝ≥0} (hts : t < s) (hnot : γ s ∉ γ '' Icc 0 t) :
    γ s ∉ closure (fwdHull (fun r : ℝ => W' r.toNNReal) t) := by
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) t with hK
  have hcl : IsClosed (γ '' Icc 0 t) := (isCompact_Icc.image hγc).isClosed
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl (γ s) hnot
  intro hmem
  obtain ⟨w, hwK, hwd⟩ := Metric.mem_closure_iff.1 hmem δ hδ
  set Q := Metric.ball (γ s) δ ∩ H with hQ
  have hQc : IsPreconnected Q :=
    ((convex_ball _ _).inter (convex_halfSpace_gt Complex.imLm.isLinear 0)).isPreconnected
  have hwQ : w ∈ Q := ⟨by rw [Metric.mem_ball, dist_comm]; exact hwd, hwK.1⟩
  obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hγ.2.2 t ENNReal.coe_lt_top
  have hQF : Q ⊆ H \ γ '' Icc 0 t := fun x hx => ⟨hx.2, hball hx.1⟩
  have hQK : Q ⊆ K := by
    intro x hx
    by_contra hxK
    have hxc : x ∈ connectedComponentIn (H \ γ '' Icc 0 t) z₀ := by
      rw [hcomp]
      exact ⟨hx.2, hxK⟩
    have hsub := hQc.subset_connectedComponentIn hx hQF
    rw [← connectedComponentIn_eq hxc, hcomp] at hsub
    exact (hsub hwQ).2 hwK
  have hQint : Q ⊆ interior K := (Metric.isOpen_ball.inter QuantumZipper.isOpen_H).subset_interior_iff.2 hQK
  have hev : ∀ᶠ r in 𝓝 s, γ r ∈ Metric.ball (γ s) δ ∧ t < r :=
    (hγc.continuousAt.eventually_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))).and
      (eventually_gt_nhds hts)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hev ⟨t, hts⟩
  obtain ⟨v, hv1, hv2, hvK⟩ := Sec5.exists_mem_fwdHull_sdiff hW' hW'0 hγ hl
  obtain ⟨hvb, htv⟩ := hsub ⟨hv1, hv2⟩
  exact Sec5.notMem_interior_fwdHull_of_lt hW' hW'0 hγ htv (hQint ⟨hvb, hvK.1.1⟩)

/-- **The relative hull before the exit is bounded**: the chart stays away from `0` on the reversed hull. Otherwise
the exit `x_C` (the boundary value of the inverse chart at `0`) would lie in the closure of `R(K'_t ∩ R⁻¹(C))`: for
`x_C = 0` against the boundedness of `K'_t`; for `x_C ≠ 0` its point `p = −1/x_C`, first visited at `σ > t`, would lie
in `closure K'_t` (`notMem_closure_fwdHull_of_lt`). -/
theorem isBounded_relHull (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    {αR αL : ℝ≥0 → ℂ} (hB : GB11.IsGB11Barrier αR αL γ) {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c)
    {s₁ : ℝ≥0} (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁)) :
    Bornology.IsBounded (relMapC c '' (fwdHull (fun r : ℝ => W' r.toNNReal) t ∩ relDom C)) := by
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) t with hK
  have hWc : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  suffices hε : ∃ ε > 0, ∀ w ∈ K ∩ relDom C, ε ≤ ‖c.1 (-w⁻¹)‖ by
    obtain ⟨ε, hε, hle⟩ := hε
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨ε⁻¹, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff]
    show ‖-(c.1 (-w⁻¹))⁻¹‖ ≤ ε⁻¹
    rw [norm_neg, norm_inv]
    exact inv_anti₀ hε (hle w hw)
  by_contra hne
  push Not at hne
  set S := (fun w : ℂ => -w⁻¹) '' (K ∩ relDom C) with hS
  have hSC : S ⊆ C := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  set Z := c.1 '' S with hZ
  have hZH : Z ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hc.2.1 (hSC hz)
  have h0Z : (0 : ℂ) ∈ closure Z := Metric.mem_closure_iff.2 fun ε hε => by
    obtain ⟨w, hw, hlt⟩ := hne ε hε
    exact ⟨c.1 (-w⁻¹), ⟨-w⁻¹, ⟨w, hw, rfl⟩, rfl⟩, by rw [dist_zero_left]; exact hlt⟩
  have hNB : (𝓝[Z] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 h0Z
  have hlim : Tendsto c.2.1 (𝓝[Z] 0) (𝓝 (αR s₁)) := hxC.mono_left (nhdsWithin_mono _ hZH)
  have hxS : αR s₁ ∈ closure S := by
    refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun z hz => ?_)
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hc.2.2.2.1.1 (hSC hy)]
    exact hy
  rcases eq_or_ne (αR s₁) 0 with h0 | h0
  · obtain ⟨ρ, hρ, hKρ⟩ := (isHPHull_fwdHull hWc (NNReal.coe_nonneg t)).exists_subset_ball
    rw [h0] at hxS
    obtain ⟨_, ⟨w, hw, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hxS ρ⁻¹ (inv_pos.2 hρ)
    rw [dist_zero_left, norm_neg, norm_inv] at hd
    have hwρ : ‖w‖ < ρ := mem_ball_zero_iff.1 (hKρ hw.1)
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (ne_zero_of_mem_H' hw.1.1)
    exact absurd hd (not_lt.2 ((inv_le_inv₀ hρ hw0).2 hwρ.le))
  · have hs₁ : 0 < s₁ := pos_iff_ne_zero.2 fun h => h0 (by rw [h]; exact hB.1.2.2.1)
    obtain ⟨σ', hσ', hne0, hσx⟩ :=
      exists_eq_firstVisit (Sec5.continuous_of_isGeneratingTrace_top hγ) (hB.firstVisit_lt_top_R hs₁)
    have hγσ : γ σ' = -(αR s₁)⁻¹ := by rw [← hσx, negInv_negInv']
    have htσ : t < σ' := by
      rw [← hσ'] at ht
      exact ENNReal.coe_lt_coe.1 ht
    have hnot : γ σ' ∉ γ '' Icc 0 t := by
      rintro ⟨r, hr, e⟩
      have hr0 : γ r ≠ 0 := e ▸ hne0
      have hle := GB11.firstVisit_le hr0
      rw [e, hσx, ← hσ'] at hle
      exact absurd (ENNReal.coe_le_coe.1 hle) (not_le.2 (hr.2.trans_lt htσ))
    have hpK : -(αR s₁)⁻¹ ∈ closure K := by
      have h1 := mem_closure_image (continuousAt_negInv h0) hxS
      have h2 : (fun w : ℂ => -w⁻¹) '' S ⊆ K := by
        rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        show -(-w⁻¹)⁻¹ ∈ K
        rw [negInv_negInv']
        exact hw.1
      exact closure_mono h2 h1
    exact notMem_closure_fwdHull_of_lt hW' hW'0 hγ htσ hnot (hγσ ▸ hpK)

theorem H_diff_relHull_eq {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (K : Set ℂ) :
    H \ relMapC c '' (K ∩ relDom C) = relMapC c '' (relDom C \ K) := by
  ext v
  constructor
  · rintro ⟨hvH, hv⟩
    exact ⟨relInvC c v, ⟨relInvC_mem hc hvH, fun hK =>
      hv ⟨relInvC c v, ⟨hK, relInvC_mem hc hvH⟩, relMapC_relInvC hc hvH⟩⟩, relMapC_relInvC hc hvH⟩
  · rintro ⟨w, ⟨hwD, hwK⟩, rfl⟩
    refine ⟨relMapC_mem_H hc hwD, ?_⟩
    rintro ⟨w', ⟨hw'K, hw'D⟩, e⟩
    exact hwK (injOn_relMapC hc hw'D hwD e ▸ hw'K)

theorem image_relDom_diff_eq {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (K : Set ℂ) :
    relMapC c '' (relDom C \ K) = H ∩ relInvC c ⁻¹' (relDom C \ K) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨relMapC_mem_H hc hw.1, ?_⟩
    rw [mem_preimage, relInvC_relMapC hc hw.1]
    exact hw
  · rintro ⟨hvH, hv⟩
    exact ⟨relInvC c v, hv, relMapC_relInvC hc hvH⟩

theorem differentiableOn_relMapC {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (hCo : IsOpen C)
    (hCH : C ⊆ H) : DifferentiableOn ℂ (relMapC c) (relDom C) := by
  intro w hw
  have hw0 : w ≠ 0 := ne_zero_of_mem_H' (relDom_subset_H hCH hw)
  have h1 : DifferentiableAt ℂ c.1 (-w⁻¹) := hc.1.differentiableAt (hCo.mem_nhds hw)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => c.1 (-z⁻¹)) w := h1.comp w (differentiableAt_inv hw0).neg
  have h3 : c.1 (-w⁻¹) ≠ 0 := ne_zero_of_mem_H' (hc.2.1 hw)
  exact (h2.inv h3).neg.differentiableWithinAt

theorem differentiableOn_relInvC {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (hCo : IsOpen C)
    (hCH : C ⊆ H) : DifferentiableOn ℂ (relInvC c) H := by
  intro v hv
  have hv0 : v ≠ 0 := ne_zero_of_mem_H' hv
  have h1 : DifferentiableAt ℂ c.2.1 (-v⁻¹) :=
    (GW3Word.differentiableOn_inv_of_isComponentChart hc hCo).differentiableAt
      (QuantumZipper.isOpen_H.mem_nhds (negInv_mem_H' hv))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => c.2.1 (-z⁻¹)) v := h1.comp v (differentiableAt_inv hv0).neg
  have h3 : c.2.1 (-v⁻¹) ≠ 0 := ne_zero_of_mem_H' (hCH (hc.2.2.1 (negInv_mem_H' hv)))
  exact (h2.inv h3).neg.differentiableWithinAt

/-- The reversed pocket `R⁻¹(C)` is simply connected (conformal image of `ℍ` under the inverse relative chart). -/
theorem isSimplyConnected_relDom {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (hCo : IsOpen C)
    (hCH : C ⊆ H) : IsSimplyConnected (relDom C) := by
  have hbij : BijOn (relInvC c) H (relDom C) :=
    ⟨fun v hv => relInvC_mem hc hv,
      fun v hv v' hv' e => by rw [← relMapC_relInvC hc hv, ← relMapC_relInvC hc hv', e],
      fun w hw => ⟨relMapC c w, relMapC_mem_H hc hw, relInvC_relMapC hc hw⟩⟩
  exact isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
    ⟨differentiableOn_relInvC hc hCo hCH, hbij⟩ isSimplyConnected_H

/-- **The relative hull before the exit is a compact `ℍ`-hull, given that `R⁻¹(C) \ K'_t` is preconnected**
(GB11.2: "its relative active component is exactly the original active component intersected with `C`"): it lies in
`ℍ` and is bounded (`isBounded_relHull`); its complement is the conformal image `Φ(R⁻¹(C) \ K'_t)`, open, nonempty (the
trace visits `R⁻¹(C)` after `t`), and simply connected: every complementary component of `R⁻¹(C) \ K'_t` contains a
complementary component of `R⁻¹(C)` or of `ℍ \ K'_t`, both simply connected. -/
theorem isHPHull_relHull_of_isPreconnected (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) {αR αL : ℝ≥0 → ℂ} (hB : GB11.IsGB11Barrier αR αL γ) {R L : Set ℂ} {c : Chart}
    (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) {s₁ : ℝ≥0}
    (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) {τ t : ℝ≥0}
    (hD : ∀ a b : ℝ≥0, τ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    (hτt : τ ≤ t) (ht : (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁))
    (hconn : IsPreconnected (relDom C \ fwdHull (fun r : ℝ => W' r.toNNReal) t)) :
    IsHPHull (relMapC c '' (fwdHull (fun r : ℝ => W' r.toNNReal) t ∩ relDom C)) := by
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) t with hK
  have hWc : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hKh : IsHPHull K := isHPHull_fwdHull hWc (NNReal.coe_nonneg t)
  have hDo : IsOpen (relDom C) := isOpen_relDom hCo hCH
  have hDKeq : relDom C \ K = relDom C ∩ (H \ K) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, relDom_subset_H hCH hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
  have hDKo : IsOpen (relDom C \ K) := by
    rw [hDKeq]
    exact hDo.inter hKh.isOpen
  have hne : (relDom C \ K).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
    have hint : relDom C ⊆ interior K := hDo.subset_interior_iff.2 hemp
    obtain ⟨b, htb, hbσ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    obtain ⟨t', ht', -, hmem⟩ := hD t b hτt (ENNReal.coe_lt_coe.1 htb) hbσ
    exact Sec5.notMem_interior_fwdHull_of_lt hW' hW'0 hγ ht'.1 (hint hmem)
  have hscD := isSimplyConnected_relDom hc hCo hCH
  have hscDK : IsSimplyConnected (relDom C \ K) := by
    rw [isSimplyConnected_iff_forall_not_isBounded hDKo ⟨hne, hconn⟩]
    intro a ha
    by_cases haD : a ∈ relDom C
    · have haK : a ∈ K := by
        by_contra h
        exact ha ⟨haD, h⟩
      have h1 := not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hKh.isOpen hKh.2.2.2
        (fun h : a ∈ H \ K => h.2 haK)
      have hsub : relDom C \ K ⊆ H \ K := fun x hx => ⟨relDom_subset_H hCH hx.1, hx.2⟩
      exact fun hb => h1 (hb.subset (connectedComponentIn_mono _ (compl_subset_compl.2 hsub)))
    · have h1 := not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hDo hscD haD
      exact fun hb => h1 (hb.subset (connectedComponentIn_mono _ (compl_subset_compl.2 sdiff_subset)))
  refine ⟨?_, isBounded_relHull hW' hW'0 hγ hB hc hxC ht, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact relMapC_mem_H hc hw.2
  · rw [H_diff_relHull_eq hc, image_relDom_diff_eq hc]
    exact (continuousOn_relInvC hc hCo hCH).isOpen_inter_preimage QuantumZipper.isOpen_H hDKo
  · rw [H_diff_relHull_eq hc]
    exact isSimplyConnected_of_isConformalBijection hDKo
      ⟨(differentiableOn_relMapC hc hCo hCH).mono sdiff_subset, ((injOn_relMapC hc).mono sdiff_subset).bijOn_image⟩
      hscDK

end HullProp

/-! ### The analytic core and the relative parametrization -/

/-- **Named input: the local growth of the relative hulls of a pocket traversal** (the analytic core of Lemma GB11's
relative parametrization: [Law05] §4.1's hypotheses for the relative chain; the source's (GB11.2) "relative active
component is exactly the original active component intersected with `C`" and "relative continuity by the
continuous-trace Loewner criterion"). Hypotheses of `GB11RelParamStatement`. With `τ` the entry time, `σ` the exit
time and `B u = Φ(K'_{τ+u} ∩ R⁻¹(C))` (`relHull`): every `B u`, `0 ≤ u < σ − τ`, is a compact `ℍ`-hull, and one
driving function `U` with `U 0 = 0` (the relative chart sends the entry `R⁻¹(y_C)` to `0`) is continuous on every
`[0, T]`, `T < σ − τ`, where the increments `g_{B s}(B t \ B s)` lie, uniformly in `s`, in small closed balls around
`U s`. -/
def GB11RelGrowthStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    (∀ u ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂),
      IsHPHull (relHull W' c C (entryTime γ αR s₂) u)) ∧
    ∃ U : ℝ → ℝ, U 0 = 0 ∧ ∀ T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂),
      ContinuousOn U (Icc 0 T) ∧ ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → t - s ≤ δ →
        mapOut (relHull W' c C (entryTime γ αR s₂) s) ''
            (relHull W' c C (entryTime γ αR s₂) t \ relHull W' c C (entryTime γ αR s₂) s) ⊆
          Metric.closedBall (U s : ℂ) ε

/-- `τ + u < σ` for `u` in the horizon `[0, σ − τ)`. -/
theorem coe_add_lt_of_mem_horizon {τ : ℝ≥0} {σ : ℝ≥0∞} {u : ℝ} (hu : u ∈ horizon (σ - τ)) :
    ((τ + u.toNNReal : ℝ≥0) : ℝ≥0∞) < σ := by
  have h := hu.2
  rw [ENNReal.coe_add]
  rw [lt_tsub_iff_left] at h
  exact h

/-- **Lemma GB11's relative Loewner parametrization from the local growth of the relative hulls** (item (1) of
PROVE-T14-GW4T3, conditional helper): the relative hulls are empty at the entry, increasing and strictly increasing
(`fwdHull_inter_relDom_eq_empty`, `exists_mem_relDom_fwdHull_sdiff`), so with the analytic core they are continuously
growing on every `[0, T]`, `T < σ − τ`; `exists_maxChain` gives the maximal parametrization, with clock
`T = τ + θ`. -/
theorem gb11RelParamStatement_of_growth (hG : GB11RelGrowthStatement) : GB11RelParamStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  obtain ⟨hHull, U, hU0, hUg⟩ := hG W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hτσ := entryTime_lt_firstVisit hγ.1 hγc hB hs
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hB.1)
    (isClosed_range_of_isCompleteSimpleFlow hB.2.1) hC
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  have hCc : IsPreconnected C := by
    obtain ⟨z, -, -, -, rfl⟩ := hC
    exact isPreconnected_connectedComponentIn
  set τ := entryTime γ αR s₂ with hτ
  set σ := GB11.firstVisit γ (αR s₁) with hσ
  have hL : 0 < σ - τ := tsub_pos_of_lt hτσ
  have hgrow : ∀ T ∈ horizon (σ - τ), IsContinuouslyGrowing (relHull W' c C τ) U T := by
    intro T hT
    obtain ⟨hUc, hgr⟩ := hUg T hT
    refine ⟨fun u hu => hHull u (mem_horizon_of_le hT hu.1 hu.2), ?_, ?_, ?_, hUc, hgr⟩
    · simp only [relHull, add_zero]
      rw [fwdHull_inter_relDom_eq_empty hW' hW'0 hγ hCo hCH hCc hτσ hE hD, image_empty]
    · intro u _ v _ huv
      exact image_mono (inter_subset_inter_left _ (QuantumZipper.fwdHull_mono.1 (by linarith)))
    · intro u hu v hv huv
      have hvh : v ∈ horizon (σ - τ) := mem_horizon_of_le hT hv.1 hv.2
      have huv' : τ + u.toNNReal < τ + v.toNNReal :=
        add_lt_add_right ((Real.toNNReal_lt_toNNReal_iff_of_nonneg hu.1).2 huv) τ
      obtain ⟨w, hwC, hwb, hwa⟩ := exists_mem_relDom_fwdHull_sdiff hW' hW'0 hγ hCo hCH hD
        (le_self_add) huv' (coe_add_lt_of_mem_horizon hvh)
      have hcu : ((τ + u.toNNReal : ℝ≥0) : ℝ) = (τ : ℝ) + u := by
        rw [NNReal.coe_add, Real.coe_toNNReal _ hu.1]
      have hcv : ((τ + v.toNNReal : ℝ≥0) : ℝ) = (τ : ℝ) + v := by
        rw [NNReal.coe_add, Real.coe_toNNReal _ hv.1]
      rw [hcu] at hwa
      rw [hcv] at hwb
      refine ⟨relMapC c w, ⟨w, ⟨hwb, hwC⟩, rfl⟩, ?_⟩
      rintro ⟨w', ⟨hw'a, hw'C⟩, e⟩
      exact hwa (injOn_relMapC hc hw'C hwC e ▸ hw'a)
  obtain ⟨S, V, θ, hS0, hVc, hV0, hθm, hθc, hθ0, hθL, hθt, hhull⟩ := exists_maxChain hL hgrow
  refine ⟨S, V, fun s => τ + θ s, ⟨hS0, hVc, hV0.trans hU0, fun a ha b hb hab => add_lt_add_right (hθm ha hb hab) τ,
    continuousOn_const.add hθc, fun s hs => ?_, ?_, fun s hs => ?_⟩, by simp only [hθ0, add_zero]⟩
  · have h := hθL s hs
    rw [lt_tsub_iff_left] at h
    rw [ENNReal.coe_add]
    exact h
  · have h := (tendsto_const_nhds (x := (τ : ℝ≥0∞))).add hθt
    rw [add_tsub_cancel_of_le hτσ.le] at h
    refine h.congr fun s => ?_
    rw [ENNReal.coe_add]
  · rw [hhull s hs]
    simp only [relHull, NNReal.coe_add]

/-- **Named input, refined: (GB11.2) and the local growth of the relative hulls.** Hypotheses of
`GB11RelParamStatement`. With `τ` the entry time and `σ` the exit time: (GB11.2) for every ambient time
`τ + u < σ`, the part `R⁻¹(C) \ K'_{τ+u}` of the reversed pocket outside the ambient hull is preconnected ("its
relative active component is exactly the original active component intersected with `C`"); and the local growth of
`GB11RelGrowthStatement` (one driving function `U`, `U 0 = 0`, continuous on every `[0, T]`, `T < σ − τ`, with uniformly
small increments `g_{B s}(B t \ B s)` around `U s`). The hull property of the relative hulls is proved
(`isHPHull_relHull_of_isPreconnected`). -/
def GB11RelConnGrowthStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    (∀ u ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂),
      IsPreconnected (relDom C \ fwdHull (fun r : ℝ => W' r.toNNReal) ((entryTime γ αR s₂ : ℝ) + u))) ∧
    ∃ U : ℝ → ℝ, U 0 = 0 ∧ ∀ T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂),
      ContinuousOn U (Icc 0 T) ∧ ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → t - s ≤ δ →
        mapOut (relHull W' c C (entryTime γ αR s₂) s) ''
            (relHull W' c C (entryTime γ αR s₂) t \ relHull W' c C (entryTime γ αR s₂) s) ⊆
          Metric.closedBall (U s : ℂ) ε

/-- **The analytic core from (GB11.2) and the local growth** (the hull property is proved). -/
theorem gb11RelGrowthStatement_of_conn (hG : GB11RelConnGrowthStatement) : GB11RelGrowthStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  obtain ⟨hconn, hgr⟩ := hG W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  refine ⟨fun u hu => ?_, hgr⟩
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hB.1)
    (isClosed_range_of_isCompleteSimpleFlow hB.2.1) hC
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  have hcu : ((entryTime γ αR s₂ + u.toNNReal : ℝ≥0) : ℝ) = (entryTime γ αR s₂ : ℝ) + u := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hu.1]
  have h := isHPHull_relHull_of_isPreconnected hW' hW'0 hγ hB hc hCo hCH hxC hD le_self_add
    (coe_add_lt_of_mem_horizon hu) (by rw [hcu]; exact hconn u hu)
  rw [hcu] at h
  exact h

/-- **Lemma GB11's relative Loewner parametrization from (GB11.2) and the local growth of the relative hulls**
(conditional helper). -/
theorem gb11RelParamStatement_of_connGrowth (hG : GB11RelConnGrowthStatement) : GB11RelParamStatement :=
  gb11RelParamStatement_of_growth (gb11RelGrowthStatement_of_conn hG)

end GW4Reg

end Theorem14

end InteractingSLE
