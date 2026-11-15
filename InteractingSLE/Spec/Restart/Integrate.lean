/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyCode
import InteractingSLE.Spec.Restart.Carrier
import InteractingSLE.Spec.Supplement.S10Theorem15
import InteractingSLE.Spec.Theorem15

/-!
# Integrating the chart propositions back from the restart carrier

Packet PROVE-RESTART-CPL, step (4). From the first-contact restart carrier (`FirstContactRestartStatement`, the
conditional coupling of W8 / Lemma 7.8 in kernel form) the chart-level propositions of Theorem 1.5 follow by applying a
theorem about canonical flow lines **at each datum** under the conditional law and integrating a **measurable** event
of the canonical space back (`ae_mem_of_compProd_eq`):

* `commonFlowAfterFirstContactStatement_of_restart` (merging, Theorem 7.12C equal angles, p. 542: "both conditional
  paths have the same field, initial finite word and angle. Universal finite-force determination gives one canonical
  path function. The two actual futures are that same path stopped at their respective reconstructed own stopping
  times"): from the carrier and the **per-datum** Lemma 7.5 (`Theorem15.Lemma75Statement`). The event "equal
  lifetimes and equal paths at dyadic times" is measurable, and by continuity it gives equality on the whole
  available interval. No jointly measurable determination map is needed.
* `chartInteriorExclusionStatement_of_restart` (critical exclusion in the chart, p. 544: "Apply 7.12D in that
  conditional chart. There is no subsequent common interior point"): from the carrier and Theorem 7.12D
  (`Theorem15.Thm712DStatement`) for the common-seed conditional pair. The event "no common point in `ℍ`" is
  measurable for continuous paths (`measurableSet_noInteriorContact`: a countable description by dyadic approximate
  contacts and compactness).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

open Sec2.Assembly

/-! ### Dyadic times on an available interval -/

/-- The dyadic approximations `⌊2ⁿ u⌋ / 2ⁿ` of a point `u` of an available interval `[0, U]` lie in it and converge
to `u` within it. -/
theorem tendsto_dyad_flr_within {U : ℝ≥0∞} {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ U) :
    Tendsto (fun n => dyad n (flr n u)) atTop (𝓝[{v : ℝ≥0 | (v : ℝ≥0∞) ≤ U}] u) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr u, Eventually.of_forall fun n =>
    (ENNReal.coe_le_coe.2 (dyad_flr_le n u)).trans hu⟩

/-- Two paths continuous on an available interval `[0, U]` that agree at its dyadic times agree on it. -/
theorem eqOn_of_dyad {f g : ℝ≥0 → ℂ} {U : ℝ≥0∞} (hf : ContinuousOn f {u | (u : ℝ≥0∞) ≤ U})
    (hg : ContinuousOn g {u | (u : ℝ≥0∞) ≤ U})
    (h : ∀ n k : ℕ, (dyad n k : ℝ≥0∞) ≤ U → f (dyad n k) = g (dyad n k)) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U → f u = g u := by
  intro u hu
  have hlim := tendsto_dyad_flr_within hu
  have hf' := ((hf u hu).tendsto).comp hlim
  have hg' := ((hg u hu).tendsto).comp hlim
  refine tendsto_nhds_unique hf' (hg'.congr' (Eventually.of_forall fun n => ?_))
  exact (h n _ ((ENNReal.coe_le_coe.2 (dyad_flr_le n u)).trans hu)).symm

/-! ### Merging -/

/-- The merging event on the canonical space: equal lifetimes and equal paths at every dyadic time of the
available interval. -/
def mergeEvent {S : Type*} (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) : Set S :=
  {s | U₁ s = U₂ s ∧ ∀ n k : ℕ, (dyad n k : ℝ≥0∞) ≤ U₁ s → γ₁ s (dyad n k) = γ₂ s (dyad n k)}

theorem measurableSet_mergeEvent {S : Type*} [MeasurableSpace S] {γ₁ γ₂ : S → ℝ≥0 → ℂ}
    {U₁ U₂ : S → ℝ≥0∞} (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hγ₁ : ∀ t, Measurable fun s => γ₁ s t) (hγ₂ : ∀ t, Measurable fun s => γ₂ s t) :
    MeasurableSet (mergeEvent γ₁ γ₂ U₁ U₂) := by
  unfold mergeEvent
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.forall fun n =>
    Measurable.forall fun k => Measurable.imp ?_ ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun hU₁ hU₂)
  · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const hU₁)
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (hγ₁ _) (hγ₂ _))

/-- **Merging in the chart from the restart carrier and the per-datum Lemma 7.5**: the remaining proposition
`Supp10.CommonFlowAfterFirstContactStatement` (Theorem 7.12C, equal angles, p. 542). At almost every datum `c`, the
two conditional continuations are angle-`θ` flow lines from `0` of the same GFF with datum `c`, so Lemma 7.5 at the
datum `c` makes them equal, with equal lifetimes, `K c`-almost surely; the measurable merging event integrates back,
and the physical continuations are `ψ ∘ γ` read through the capacity clocks. -/
theorem commonFlowAfterFirstContactStatement_of_restart (hR : FirstContactRestartStatement.{u})
    (h75 : Theorem15.Lemma75Statement.{0}) : Supp10.CommonFlowAfterFirstContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ hx Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ θ hx (lt_add_of_pos_right θ Real.pi_pos) P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨-, hU₁, hU₂, hγ₁, hγ₂, hc₁, hc₂⟩ := hcoord
  have hKE : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), s ∈ mergeEvent γ₁ γ₂ U₁ U₂ := by
    filter_upwards [hcond] with c hc
    obtain ⟨hgff, hf₁, hf₂⟩ := hc
    obtain ⟨Φ, -, hΦ⟩ := h75 κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData 0 θ
    filter_upwards [hΦ (K c) H hgff γ₁ U₁ hf₁, hΦ (K c) H hgff γ₂ U₂ hf₂] with s hs₁ hs₂
    have hU : U₁ s = U₂ s := hs₁.1.symm.trans hs₂.1
    refine ⟨hU, fun n k hle => ?_⟩
    rw [← hs₁.2 _ hle, hs₂.2 _ (hU ▸ hle)]
  have hae := ae_mem_of_compProd_eq hM hβ hX hlaw
    (measurableSet_mergeEvent hU₁ hU₂ hγ₁ hγ₂) hKE
  filter_upwards [hae, hpath] with ω hωE hωp
  intro s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨hωM, -, ψ, -, c₁, c₂, -, -, -, -, -, -, -, hm₁, him₁, hm₂, him₂, he₁, he₂⟩ :=
    hωp s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨hU, hγ⟩ := hωE hωM
  have heq : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ (X ω) → γ₁ (X ω) u = γ₂ (X ω) u :=
    eqOn_of_dyad (hc₁ (X ω)) (hU ▸ hc₂ (X ω)) hγ
  refine ⟨fun u => ψ (γ₁ (X ω) u), U₁ (X ω), U₂ (X ω), c₁, c₂, hm₁, hm₂, him₁, him₂, he₁,
    fun u hu => ?_⟩
  exact (he₂ u hu).trans (congrArg ψ (heq u (hU ▸ hu)).symm)

/-! ### Interior contacts of continuous paths: a countable description -/

/-- A dyadic approximate interior contact of the paths `f` (on `[0, A]`) and `g` (on `[0, B]`) at level `N` (both
parameters at most `N`, height above `1/(N+1)`) and precision `m`. -/
def ApproxContact (f g : ℝ≥0 → ℂ) (A B : ℝ≥0∞) (N m : ℕ) : Prop :=
  ∃ n k n' k' : ℕ, (dyad n k : ℝ≥0∞) ≤ A ∧ dyad n k ≤ (N : ℝ≥0) ∧ (dyad n' k' : ℝ≥0∞) ≤ B ∧ dyad n' k' ≤ (N : ℝ≥0) ∧
    dist (f (dyad n k)) (g (dyad n' k')) < 1 / ((m : ℝ) + 1) ∧
    1 / ((N : ℝ) + 1) - 1 / ((m : ℝ) + 1) < (f (dyad n k)).im

/-- The parameters of an available interval `[0, A]` that are at most `N` form a compact set. -/
theorem isCompact_le_le (A : ℝ≥0∞) (N : ℕ) :
    IsCompact {u : ℝ≥0 | (u : ℝ≥0∞) ≤ A ∧ u ≤ (N : ℝ≥0)} := by
  refine (isCompact_Icc (a := (0 : ℝ≥0)) (b := N)).of_isClosed_subset ?_ fun u hu => ⟨bot_le, hu.2⟩
  exact (isClosed_le ENNReal.continuous_coe continuous_const).inter isClosed_Iic

/-- **Interior contacts of continuous paths, countably.** For paths continuous on their available intervals, an
interior contact (a common point in `ℍ`) exists iff at some level `N` there are dyadic approximate contacts of every
precision. -/
theorem exists_interiorContact_iff {f g : ℝ≥0 → ℂ} {A B : ℝ≥0∞}
    (hf : ContinuousOn f {u | (u : ℝ≥0∞) ≤ A}) (hg : ContinuousOn g {u | (u : ℝ≥0∞) ≤ B}) :
    (∃ u v : ℝ≥0, (u : ℝ≥0∞) ≤ A ∧ (v : ℝ≥0∞) ≤ B ∧ f u = g v ∧ f u ∈ QuantumZipper.H) ↔
      ∃ N : ℕ, ∀ m : ℕ, ApproxContact f g A B N m := by
  constructor
  · rintro ⟨u, v, hu, hv, he, hH⟩
    have hH' : (0 : ℝ) < (f u).im := hH
    obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt hH'
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge (max (u : ℝ) (v : ℝ))
    refine ⟨max N₁ N₂, fun m => ?_⟩
    set N := max N₁ N₂
    have hlu := ((hf u hu).tendsto).comp (tendsto_dyad_flr_within hu)
    have hlv := ((hg v hv).tendsto).comp (tendsto_dyad_flr_within hv)
    have hd : Tendsto (fun n => dist (f (dyad n (flr n u))) (g (dyad n (flr n v)))) atTop (𝓝 0) := by
      have := hlu.dist hlv
      rwa [he, dist_self] at this
    have hNle : 1 / ((N : ℝ) + 1) < (f u).im :=
      lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (le_max_left N₁ N₂) 1)) hN₁
    have him : Tendsto (fun n => (f (dyad n (flr n u))).im) atTop (𝓝 (f u).im) :=
      (Complex.continuous_im.tendsto _).comp hlu
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨n, hn₁, hn₂⟩ := ((hd.eventually (gt_mem_nhds hm)).and
      (him.eventually (lt_mem_nhds hNle))).exists
    have huN : (u : ℝ) ≤ N := (le_max_left _ _).trans (hN₂.trans (by exact_mod_cast le_max_right N₁ N₂))
    have hvN : (v : ℝ) ≤ N := (le_max_right _ _).trans (hN₂.trans (by exact_mod_cast le_max_right N₁ N₂))
    refine ⟨n, flr n u, n, flr n v, (ENNReal.coe_le_coe.2 (dyad_flr_le n u)).trans hu, ?_,
      (ENNReal.coe_le_coe.2 (dyad_flr_le n v)).trans hv, ?_, hn₁, by linarith⟩
    · exact (dyad_flr_le n u).trans (by exact_mod_cast huN)
    · exact (dyad_flr_le n v).trans (by exact_mod_cast hvN)
  · rintro ⟨N, hN⟩
    choose n k n' k' hA hAN hB hBN hdist him using hN
    set a : ℕ → ℝ≥0 := fun m => dyad (n m) (k m)
    set b : ℕ → ℝ≥0 := fun m => dyad (n' m) (k' m)
    have hmem : ∀ m, (a m, b m) ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ A ∧ u ≤ (N : ℝ≥0)} ×ˢ
        {u : ℝ≥0 | (u : ℝ≥0∞) ≤ B ∧ u ≤ (N : ℝ≥0)} := fun m => ⟨⟨hA m, hAN m⟩, ⟨hB m, hBN m⟩⟩
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, φ, hφ, hlim⟩ :=
      ((isCompact_le_le A N).prod (isCompact_le_le B N)).tendsto_subseq hmem
    have ha : Tendsto (fun m => a (φ m)) atTop (𝓝[{u : ℝ≥0 | (u : ℝ≥0∞) ≤ A}] u) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).comp hlim,
        Eventually.of_forall fun m => hA (φ m)⟩
    have hb : Tendsto (fun m => b (φ m)) atTop (𝓝[{u : ℝ≥0 | (u : ℝ≥0∞) ≤ B}] v) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto _).comp hlim,
        Eventually.of_forall fun m => hB (φ m)⟩
    have hfa := ((hf u hu.1).tendsto).comp ha
    have hgb := ((hg v hv.1).tendsto).comp hb
    have hsmall : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hdle : dist (f u) (g v) ≤ 0 :=
      le_of_tendsto_of_tendsto' (hfa.dist hgb) hsmall fun m => (hdist (φ m)).le
    have heq : f u = g v := dist_le_zero.1 hdle
    have himlim : Tendsto (fun m => (f (a (φ m))).im) atTop (𝓝 (f u).im) :=
      (Complex.continuous_im.tendsto _).comp hfa
    have hlow : Tendsto (fun m => 1 / ((N : ℝ) + 1) - 1 / ((φ m : ℝ) + 1)) atTop
        (𝓝 (1 / ((N : ℝ) + 1))) := by
      simpa using tendsto_const_nhds.sub hsmall
    have hge : 1 / ((N : ℝ) + 1) ≤ (f u).im :=
      le_of_tendsto_of_tendsto' hlow himlim fun m => (him (φ m)).le
    refine ⟨u, v, hu.1, hv.1, heq, ?_⟩
    show (0 : ℝ) < (f u).im
    exact lt_of_lt_of_le (by positivity) hge

/-- The event "no interior contact" of the restart coordinates (in the order of Theorem 7.12D: the lower-angle path
`γ₂` first) is measurable. -/
theorem measurableSet_noInteriorContact {S : Type*} [MeasurableSpace S]
    {H : S → LQGMetric.DistOn upperHalfPlaneOpens} {γ₁ γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞}
    (hc : IsRestartCoordinates H γ₁ γ₂ U₁ U₂) :
    MeasurableSet {s | ¬ ∃ u v : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ s ∧ (v : ℝ≥0∞) ≤ U₁ s ∧
      γ₂ s u = γ₁ s v ∧ γ₂ s u ∈ QuantumZipper.H} := by
  obtain ⟨-, hU₁, hU₂, hγ₁, hγ₂, hc₁, hc₂⟩ := hc
  have hset : {s | ¬ ∃ u v : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ s ∧ (v : ℝ≥0∞) ≤ U₁ s ∧
      γ₂ s u = γ₁ s v ∧ γ₂ s u ∈ QuantumZipper.H} =
      {s | ¬ ∃ N : ℕ, ∀ m : ℕ, ApproxContact (γ₂ s) (γ₁ s) (U₂ s) (U₁ s) N m} := by
    ext s
    simp only [mem_ofPred_eq]
    rw [exists_interiorContact_iff (hc₂ s) (hc₁ s)]
  rw [hset]
  refine measurableSet_setOfPred.2 (Measurable.not (Measurable.exists fun N => Measurable.forall
    fun m => ?_))
  unfold ApproxContact
  refine Measurable.exists fun n => Measurable.exists fun k => Measurable.exists fun n' =>
    Measurable.exists fun k' => ?_
  refine Measurable.and (measurableSet_setOfPred.1 (measurableSet_le measurable_const hU₂))
    (Measurable.and measurable_const (Measurable.and
      (measurableSet_setOfPred.1 (measurableSet_le measurable_const hU₁))
      (Measurable.and measurable_const (Measurable.and ?_ ?_))))
  · exact measurableSet_setOfPred.1 (measurableSet_lt ((hγ₂ _).dist (hγ₁ _)) measurable_const)
  · exact measurableSet_setOfPred.1
      (measurableSet_lt measurable_const (Complex.measurable_im.comp (hγ₂ _)))

/-! ### Critical exclusion in the chart -/

/-- **Theorem 7.12D in the first-contact chart from the restart carrier**: the remaining proposition
`Supp10.ChartInteriorExclusionStatement` (supplement p. 544). At almost every datum `c`, the conditional continuations
are flow lines from the common seed `0` of one GFF with datum `c`, the lower-angle `γ₂` (angle `θ₂`) and the
higher-angle `γ₁` (angle `θ₁`) with `(θ₁ − θ₂)χ/λ ≥ κ/2`, so Theorem 7.12D at the datum `c` excludes a common point in
`ℍ`, `K c`-almost surely; the measurable event integrates back. A common point of the later physical portions in the
active domain `D` is `ψ(γ₁ v) = ψ(γ₂ u)` with both chart points in `ℍ` (the inverse chart sends real points off `D`),
hence a common interior point of the chart continuations. -/
theorem chartInteriorExclusionStatement_of_restart (hR : FirstContactRestartStatement.{u})
    (h712D : Theorem15.Thm712DStatement.{0}) : Supp10.ChartInteriorExclusionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx _ hθπ hcrit Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have hKE : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), s ∈ {s | ¬ ∃ u v : ℝ≥0,
      (u : ℝ≥0∞) ≤ U₂ s ∧ (v : ℝ≥0∞) ≤ U₁ s ∧ γ₂ s u = γ₁ s v ∧ γ₂ s u ∈ QuantumZipper.H} := by
    filter_upwards [hcond] with c hc
    obtain ⟨hgff, hf₁, hf₂⟩ := hc
    filter_upwards [h712D κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData 0 0 θ₂ θ₁ le_rfl
      hcrit (K c) H hgff γ₂ γ₁ U₂ U₁ hf₂ hf₁] with s hs
    rintro ⟨u, v, hu, hv, he, hH⟩
    exact hs u v hu hv he hH
  have hae := ae_mem_of_compProd_eq hM hβ hX hlaw (measurableSet_noInteriorContact hcoord) hKE
  filter_upwards [hae, hpath] with ω hωE hωp
  intro s₀ t₀ h₀ hs₀ ht₀ s t hs ht hsζ htζ hst hD
  obtain ⟨hωM, -, ψ, -, c₁, c₂, -, hbij, -, hout, -, -, -, -, him₁, -, him₂, he₁, he₂⟩ :=
    hωp s₀ t₀ h₀ hs₀ ht₀
  have hs' : s ∈ c₁ '' {u | (u : ℝ≥0∞) ≤ U₁ (X ω)} := by rw [him₁]; exact ⟨hs.le, hsζ⟩
  have ht' : t ∈ c₂ '' {u | (u : ℝ≥0∞) ≤ U₂ (X ω)} := by rw [him₂]; exact ⟨ht.le, htζ⟩
  obtain ⟨v, hv, rfl⟩ := hs'
  obtain ⟨u, hu, rfl⟩ := ht'
  have hv' := he₁ v hv
  have hu' := he₂ u hu
  have h1 : γ₁ (X ω) v ∈ QuantumZipper.H := by
    by_contra hn
    exact hout _ hn (hv' ▸ hD)
  have h2 : γ₂ (X ω) u ∈ QuantumZipper.H := by
    by_contra hn
    exact hout _ hn (hu' ▸ hst ▸ hD)
  have heq : γ₂ (X ω) u = γ₁ (X ω) v := hbij.injOn h2 h1 (by rw [← hu', ← hv', hst])
  exact hωE hωM ⟨u, v, hu, hv, heq, h2⟩

/-! ### The Theorem 1.5 inputs and clause (ii) from the restart carrier -/

/-- **Theorem 7.12C, equal angles** (`Theorem15.Thm712CMergingStatement`, p. 542) from the restart carrier and the
per-datum Lemma 7.5. -/
theorem thm712CMergingStatement_of_restart (hR : FirstContactRestartStatement.{u})
    (h75 : Theorem15.Lemma75Statement.{0}) : Theorem15.Thm712CMergingStatement.{u} :=
  Supp10.thm712CMergingStatement_of_inputs (commonFlowAfterFirstContactStatement_of_restart hR h75)

/-- **The critical exclusion after a crossing** (`Theorem15.CriticalExclusionAfterCrossingStatement`, p. 544) from the
restart carrier, Theorem 7.12D (at the conditional common-seed pair), Lemma 7.7 and Aux. lemma 25. -/
theorem criticalExclusionAfterCrossingStatement_of_restart (hR : FirstContactRestartStatement.{u})
    (h712D : Theorem15.Thm712DStatement.{0}) (h77 : Supp10.Lemma77Statement.{u})
    (hA25 : Theorem15.Aux25Statement.{u}) : Theorem15.CriticalExclusionAfterCrossingStatement.{u} :=
  Supp10.criticalExclusionAfterCrossingStatement_of_inputs h77 hA25
    (chartInteriorExclusionStatement_of_restart hR h712D)

/-- **Theorem 1.5 (ii)** (Specification p. 5), with exactly the conclusion of the frozen `IsFlowLine.merges`, from
Theorem W8's common first contact, Aux. lemma 25, Lemma 7.5 (per datum, in the given universe and on the canonical
space) and the restart carrier. -/
theorem merges_of_restart (hW8 : Theorem15.W8FirstContactStatement.{u})
    (hA25 : Theorem15.Aux25Statement.{u}) (hL75 : Theorem15.Lemma75Statement.{u})
    (h75 : Theorem15.Lemma75Statement.{0}) (hR : FirstContactRestartStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t :=
  Theorem15.merges_of_inputs hW8 (thm712CMergingStatement_of_restart hR h75) hA25 hL75 hκ hκ4 b jumps hb
    hx hh hη₁ hη₂

end Restart

end InteractingSLE
