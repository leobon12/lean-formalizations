/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LnMean
import InteractingSLE.Spec.Supplement.GW2SfMeanChart
import InteractingSLE.Spec.Coupling.CouplingThrough

/-!
# SB2(2)'s line mean from a configuration record at each sample

Packet PROVE-GW2-GEOM2, round 9 (PROVE-SB2-LCMEAN's handoff R13.8, item 1: the line mean `hmean` of
`Mu.ae_isStopDrvMatch_of_lines`). The union mean of the retained set `A₁` and the explored set `A₂` is
`Ln.ae_chartTransport_eq_couplingMean_of_stagePullback`. It is applied here with three choices:

* **the field shifted by the angle**: B's pieces are flow lines of angle `ψ` (`ψ = −π/2`), so their sides carry the
  heights `∓λ` of the field `h + ψχ`; the union mean is computed for `(h + ψχ, u₀ + ψχ)`, whose centred field is the
  centred field of `(h, u₀)`, and read back with the chart offset `ψχ` (`GW2Sf.chartTransport_add_const_mean`);
* **the configuration chosen at each sample** from a record (`IsCfg`): the mirrored configuration `Lm.IsRelConfigJKL`
  in B's stage chart `c` whose retained set is the stage image of `A₁`, whose relative chart `Ψ` composed with `c`
  is the canonical chart `Φ` (inverse and lift), whose retained extension is the retained word's mean shifted by
  `ψχ`, whose explored extension is the explored word's mean shifted by `ψχ`, and whose union extension is the given
  `Gu` (K2's `bheProc` in the consumer);
* **the offset and lift constant `0`**.

* `CfgData`, **`IsCfg`**: the record at one sample;
* `IsCfg.fwd_eq`, `IsCfg.lift_eq`: `Ψ ∘ c = Φ` and the lifts add on `ℍ ∖ A₁`;
* **`ae_chartTransport_eq_of_cfg`**: almost surely on the record's event, for every test off the relative hull,
  `chartTransport Φ 1 (ψχ) χ (g + u₀) = ∫ couplingMean κ W u Gu`.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Om

open LocalSets Ln

/-- **The configuration data at one sample.** -/
structure CfgData where
  A : Set ℂ
  Ψ : ℂ → ℂ
  Ψi : ℂ → ℂ
  LΨ : ℂ → ℂ
  Sb : Finset ℝ
  η : ℝ → ℂ
  ηr : ℝ → ℂ
  β₀ : ℝ → ℝ
  βE : ℝ → ℝ
  βu : ℝ → ℝ
  S₀ : Finset ℝ
  SE : Finset ℝ
  Su : Finset ℝ
  G₀ : ℂ → ℝ
  GE : ℂ → ℝ
  G : ℂ → ℝ
  v : ℂ → ℝ

instance : Nonempty CfgData := ⟨⟨∅, 0, 0, 0, ∅, 0, 0, 0, 0, 0, ∅, ∅, ∅, 0, 0, 0, 0⟩⟩

/-- **The configuration record at one sample**: in B's stage chart `c`, the mirrored configuration whose retained set
is the stage image of `A₁` (on `ℍ`), whose relative chart read through `c` is the canonical chart `Φ` (inverse and
lift), with retained extension `β₁.mean + ψχ`, explored extension `GE₀ + ψχ` and union extension `Gu`. -/
def IsCfg (κ ψ : ℝ) (c Φ : Chart) (A₁ : Set ℂ) (wB : ℝ → ℝ) (sB : ℝ) (W : ℝ → ℝ) (u : ℝ)
    (β₁ : Restart.BoundaryWord) (GE₀ Gu : ℂ → ℝ) (d : CfgData) : Prop :=
  (∀ z ∈ H, z ∈ d.A ↔ c.2.1 z ∈ A₁) ∧
    Lm.IsRelConfigJKL d.A d.Ψ d.Ψi d.LΨ d.Sb wB W d.η d.ηr sB u (chiC κ) (Real.pi / Real.sqrt κ) d.β₀ d.βE d.βu
      d.S₀ d.SE d.Su d.G₀ d.GE d.G d.v ∧
    (∀ y ∈ H, Φ.2.1 y = c.2.1 (d.Ψi y)) ∧
    (∀ y ∈ H, Φ.2.2 (Φ.2.1 y) = (d.LΨ (d.Ψi y)).im + c.2.2 (Φ.2.1 y)) ∧
    EqOn d.G₀ (fun z => β₁.mean z + ψ * chiC κ) H ∧
    EqOn d.GE (fun z => GE₀ z + ψ * chiC κ) H ∧
    EqOn d.G Gu H

section Rec

variable {κ ψ : ℝ} {c Φ : Chart} {A₁ : Set ℂ} {wB W : ℝ → ℝ} {sB u : ℝ} {β₁ : Restart.BoundaryWord}
  {GE₀ Gu : ℂ → ℝ} {d : CfgData}

/-- On `ℍ ∖ A₁` (the canonical chart's domain), the relative chart after the stage chart is the canonical chart, and
`c.1 z = Ψi (Φ.1 z)`. -/
theorem IsCfg.fwd_eq (hd : IsCfg κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu d) (hc : c.IsConformal) (hΦ : Φ.IsConformal)
    (hdom : (Φ.dom : Set ℂ) = H \ A₁) {z : ℂ} (hz : z ∈ H \ A₁) :
    c.1 z = d.Ψi (Φ.1 z) ∧ d.Ψ (c.1 z) = Φ.1 z := by
  have hzd : z ∈ (Φ.dom : Set ℂ) := by rw [hdom]; exact hz
  have hy : Φ.1 z ∈ H := hΦ.fwd_mem hzd
  have hinv : Φ.2.1 (Φ.1 z) = z := hΦ.inv_fwd hzd
  have hi := hd.2.2.1 _ hy
  rw [hinv] at hi
  have hmem := IsRelConfigJKL.inv_mem hd.2.1 hy
  have hc1 : c.1 z = d.Ψi (Φ.1 z) := by
    have e := hc.2.2 _ hmem.1
    rw [← hi] at e
    exact e
  exact ⟨hc1, by rw [hc1]; exact IsRelConfigJKL.fwd_inv hd.2.1 hy⟩

/-- On `ℍ ∖ A₁`, the canonical chart's lift is the relative lift after the stage chart plus the stage lift. -/
theorem IsCfg.lift_eq (hd : IsCfg κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu d) (hc : c.IsConformal) (hΦ : Φ.IsConformal)
    (hdom : (Φ.dom : Set ℂ) = H \ A₁) {z : ℂ} (hz : z ∈ H \ A₁) :
    Φ.2.2 z = (d.LΨ (c.1 z)).im + c.2.2 z := by
  have hzd : z ∈ (Φ.dom : Set ℂ) := by rw [hdom]; exact hz
  have hy : Φ.1 z ∈ H := hΦ.fwd_mem hzd
  have hinv : Φ.2.1 (Φ.1 z) = z := hΦ.inv_fwd hzd
  have hl := hd.2.2.2.1 _ hy
  rw [hinv] at hl
  rw [hl, (hd.fwd_eq hc hΦ hdom hz).1]

end Rec

/-! ### The line mean from the records -/

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

open Classical in
/-- The configuration data chosen at a sample where a record exists. -/
def cfgOf (κ ψ : ℝ) (c Φ : Chart) (A₁ : Set ℂ) (wB : ℝ → ℝ) (sB : ℝ) (W : ℝ → ℝ) (u : ℝ)
    (β₁ : Restart.BoundaryWord) (GE₀ Gu : ℂ → ℝ) : CfgData :=
  Classical.epsilon (IsCfg κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu)

theorem isCfg_cfgOf {κ ψ : ℝ} {c Φ : Chart} {A₁ : Set ℂ} {wB : ℝ → ℝ} {sB : ℝ} {W : ℝ → ℝ} {u : ℝ}
    {β₁ : Restart.BoundaryWord} {GE₀ Gu : ℂ → ℝ} (h : ∃ d, IsCfg κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu d) :
    IsCfg κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu (cfgOf κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu) :=
  Classical.epsilon_spec h

open Classical in
/-- The stage chart's boundary map chosen at a sample where a stage pull-back exists. -/
def gbOf (c : Chart) (A₁ A₂ A' K : Set ℂ) : ℂ → ℂ :=
  Classical.epsilon fun g => IsStagePullback c g A₁ A₂ A' K

/-- **The stage pull-back only reads the retained preimage on `ℍ`.** -/
theorem stagePullback_congr_retained {c : Chart} {g : ℂ → ℂ} {A₁ A₂ A' A'' K : Set ℂ}
    (hp : IsStagePullback c g A₁ A₂ A' K) (hA : ∀ z ∈ H, z ∈ A'' ↔ z ∈ A') : IsStagePullback c g A₁ A₂ A'' K :=
  { hp with corr₁ := fun z hz => (hp.corr₁ z hz).trans (hA z hz).symm }

/-- **SB2(2)'s line mean from configuration records** (K2's `hmean` form). Let `A₁`, `A₂` be the retained and explored
sets (measurable, local, `A₁` determined by the field, unbounded lower components, local-set means `g₁`, `g₂`, `g`
of `A₁`, `A₂`, `A₁ ∪ A₂`), `c` B's stage chart with a stage pull-back onto the stage image of `A₁` and the hull of
the explored piece `(wB, sB)`, `Φ` a conformal chart of `ℍ ∖ A₁`. If almost surely on `D` a configuration record
holds, the retained mean is `β₁.mean ∘ Φ − χ lift Φ` and the explored mean is `GE₀ ∘ fwdMap − χ (…)`, then almost
surely on `D` the chart transport of `g + u₀` with offset `ψχ` is the coupling mean of the relative driver `W` at
`u` with the union extension `Gu`, against every test off the relative hull. -/
theorem ae_chartTransport_eq_of_cfg {κ ψ : ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A₁ A₂ : Ω → Set ℂ} (hA₁m : Measurable[mΩ, hittingSigma] A₁) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hd₁ : MeasurableSpace.comap A₁ hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hl₁ : IsLocalSet A₁ (WholeField.centredField h u₀) P) (hl₂ : IsLocalSet A₂ (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean A₂ (WholeField.centredField h u₀) P g₂)
    {c : Ω → Chart} {wB : Ω → ℝ → ℝ} {sB : Ω → ℝ} {D : Set Ω}
    (hpb : ∀ᵐ ω ∂P, ω ∈ D → ∃ gb : ℂ → ℂ, IsStagePullback (c ω) gb (A₁ ω) (A₂ ω)
      {z | (c ω).2.1 z ∈ A₁ ω} (fwdHull (wB ω) (sB ω)))
    {Φ : Ω → Chart} (hΦ : ∀ ω, (Φ ω).IsConformal) (hΦℓ : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hdom : ∀ᵐ ω ∂P, ω ∈ D → ((Φ ω).dom : Set ℂ) = H \ A₁ ω)
    {W : Ω → ℝ → ℝ} {u : Ω → ℝ} {β₁ : Ω → Restart.BoundaryWord} {GE₀ Gu : Ω → ℂ → ℝ}
    (hrec : ∀ᵐ ω ∂P, ω ∈ D → ∃ d, IsCfg κ ψ (c ω) (Φ ω) (A₁ ω) (wB ω) (sB ω) (W ω) (u ω) (β₁ ω) (GE₀ ω) (Gu ω) d)
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => (β₁ ω).mean ((Φ ω).1 z) - chiC κ * (Φ ω).2.2 z) (H \ A₁ ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE₀ ω (fwdMap (wB ω) (sB ω) ((c ω).1 z)) -
        chiC κ * ((logDerivFwd (wB ω) (sB ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ φ : TestOn upperHalfPlaneOpens, Disjoint (tsupport φ) (fwdHull (W ω) (u ω)) →
      Chart.chartTransport (hΦ ω) 1 (ψ * chiC κ) (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, couplingMean κ (W ω) (u ω) (Gu ω) z * φ z := by
  classical
  -- the field shifted by the angle
  set u₀' : ℂ → ℝ := fun z => u₀ z + ψ * chiC κ with hu₀'
  set h' : Ω → DistOn upperHalfPlaneOpens :=
    fun ω => WholeField.centredField h u₀ ω + smoothDist upperHalfPlaneOpens u₀' with hh'
  have hcf : WholeField.centredField h' u₀' = WholeField.centredField h u₀ := by
    funext ω
    simp only [WholeField.centredField, hh', add_sub_cancel_right]
  have hu₀'h : InnerProductSpace.HarmonicOnNhd u₀' H := fun z hz =>
    (hu₀ z hz).add (InnerProductSpace.harmonicAt_const (ψ * chiC κ))
  have hu₀'b : ∃ M : ℝ, ∀ z ∈ H, |u₀' z| ≤ M := by
    obtain ⟨M, hM⟩ := hu₀b
    refine ⟨M + |ψ * chiC κ|, fun z hz => ?_⟩
    exact (abs_add_le _ _).trans (by linarith [hM z hz])
  -- the chosen configurations and boundary maps
  set d : Ω → CfgData := fun ω =>
    cfgOf κ ψ (c ω) (Φ ω) (A₁ ω) (wB ω) (sB ω) (W ω) (u ω) (β₁ ω) (GE₀ ω) (Gu ω) with hddef
  set gb : Ω → ℂ → ℂ := fun ω =>
    gbOf (c ω) (A₁ ω) (A₂ ω) {z | (c ω).2.1 z ∈ A₁ ω} (fwdHull (wB ω) (sB ω)) with hgbdef
  have hrec' : ∀ᵐ ω ∂P, ω ∈ D →
      IsCfg κ ψ (c ω) (Φ ω) (A₁ ω) (wB ω) (sB ω) (W ω) (u ω) (β₁ ω) (GE₀ ω) (Gu ω) (d ω) := by
    filter_upwards [hrec] with ω hω hD
    exact isCfg_cfgOf (hω hD)
  have hpb' : ∀ᵐ ω ∂P, ω ∈ D → IsStagePullback (c ω) (gb ω) (A₁ ω) (A₂ ω) (d ω).A
      (fwdHull (wB ω) (sB ω)) := by
    filter_upwards [hpb, hrec'] with ω hp hr hD
    have hp' : IsStagePullback (c ω) (gb ω) (A₁ ω) (A₂ ω) {z | (c ω).2.1 z ∈ A₁ ω}
        (fwdHull (wB ω) (sB ω)) := Classical.epsilon_spec (hp hD)
    exact stagePullback_congr_retained hp' (hr hD).1
  have hcfg : ∀ᵐ ω ∂P, ω ∈ D → Lm.IsRelConfigJKL (d ω).A (d ω).Ψ (d ω).Ψi (d ω).LΨ (d ω).Sb (wB ω) (W ω)
      (d ω).η (d ω).ηr (sB ω) (u ω) (chiC κ) (Real.pi / Real.sqrt κ) (d ω).β₀ (d ω).βE (d ω).βu (d ω).S₀
      (d ω).SE (d ω).Su (d ω).G₀ (d ω).GE (d ω).G (d ω).v := by
    filter_upwards [hrec'] with ω hr hD
    exact (hr hD).2.1
  have hind₁' : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀' z)
        (fun z => (d ω).G₀ ((d ω).Ψ ((c ω).1 z)) -
          chiC κ * (((d ω).LΨ ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₁ ω) := by
    filter_upwards [hind₁, hrec', hpb', hdom] with ω h1 hr hp hdm hD w₁ hw₁ hrep z hz
    have hrω := hr hD
    have hcω := (hp hD).conf
    have hdω := hdm hD
    have e1 := h1 hD w₁ hw₁ hrep hz
    simp only at e1
    obtain ⟨-, hΨ⟩ := hrω.fwd_eq hcω (hΦ ω) hdω hz
    have hl := hrω.lift_eq hcω (hΦ ω) hdω hz
    have hzd : z ∈ ((Φ ω).dom : Set ℂ) := by rw [hdω]; exact hz
    have hG := hrω.2.2.2.2.1 ((hΦ ω).fwd_mem hzd)
    simp only [hu₀']
    rw [hΨ, hG, ← hl]
    simp only
    linarith
  have hind₂' : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀' z) (fun z => (d ω).GE (fwdMap (wB ω) (sB ω) ((c ω).1 z)) -
        chiC κ * ((logDerivFwd (wB ω) (sB ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ ω) := by
    filter_upwards [hind₂, hrec', hpb', hcfg] with ω h2 hr hp hc hD w₂ hw₂ hrep z hz
    have e2 := h2 hD w₂ hw₂ hrep hz
    simp only at e2
    have hp' := hp hD
    have hzd : z ∈ ((c ω).dom : Set ℂ) := by
      by_contra hn
      exact hz.2 (hp'.dom₂ ⟨hz.1, hn⟩)
    have hcz : (c ω).1 z ∈ H := hp'.conf.fwd_mem hzd
    have hzK : (c ω).1 z ∉ fwdHull (wB ω) (sB ω) := by
      intro hK
      have h2' := (hp'.corr₂ _ hcz).2 hK
      rw [hp'.conf.inv_fwd hzd] at h2'
      exact hz.2 h2'
    have hcf' := FinRel.IsRelConfigJK.hw (hc hD)
    have hts := FinRel.IsRelConfigJK.ht (hc hD)
    have hwc : ContinuousOn (wB ω) (Icc 0 (sB ω)) := by
      have h := hcf'.neg
      simp only [neg_neg] at h
      exact h.continuousOn
    have hmem := WFS.fwdMap_mem_H_of_notMem hts hwc hcz hzK
    have hGE := (hr hD).2.2.2.2.2.1 hmem
    simp only [hu₀']
    rw [hGE]
    simp only
    linarith
  have hcrinv : ∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (Φ ω).2.1 y = (c ω).2.1 ((d ω).Ψi y) := by
    filter_upwards [hrec'] with ω hr hD
    exact (hr hD).2.2.1
  have hcrlift : ∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (Φ ω).2.2 ((Φ ω).2.1 y) =
      ((d ω).LΨ ((d ω).Ψi y)).im + (c ω).2.2 ((Φ ω).2.1 y) + 0 := by
    filter_upwards [hrec'] with ω hr hD y hy
    rw [add_zero]
    exact (hr hD).2.2.2.1 y hy
  have hg' : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h' u₀') P g := by rw [hcf]; exact hg
  have hg₁' : IsLocalSetMean A₁ (WholeField.centredField h' u₀') P g₁ := by rw [hcf]; exact hg₁
  have hg₂' : IsLocalSetMean A₂ (WholeField.centredField h' u₀') P g₂ := by rw [hcf]; exact hg₂
  have hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀') P := by
    rw [hcf]; exact hh0
  have hd₁' : MeasurableSpace.comap A₁ hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P := by rw [hcf]; exact hd₁
  have hl₁' : IsLocalSet A₁ (WholeField.centredField h' u₀') P := by rw [hcf]; exact hl₁
  have hl₂' : IsLocalSet A₂ (WholeField.centredField h' u₀') P := by rw [hcf]; exact hl₂
  have hlU' : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h' u₀') P := by rw [hcf]; exact hlU
  have hLn := Ln.ae_chartTransport_eq_couplingMean_of_stagePullback (κ := κ) (h := h') (u₀ := u₀')
    hh0' hu₀'h hu₀'b hA₁m hA₂m hd₁' hl₁' hl₂' hlU' hunb₁ hunb₂ hg' hg₁' hg₂'
    (c := c) (gb := gb) (A := fun ω => (d ω).A) (Ψ := fun ω => (d ω).Ψ) (Ψi := fun ω => (d ω).Ψi)
    (LΨ := fun ω => (d ω).LΨ) (Sb := fun ω => (d ω).Sb) (w := wB) (Wr := W) (η := fun ω => (d ω).η)
    (ηr := fun ω => (d ω).ηr) (t := sB) (u := u) (lam := Real.pi / Real.sqrt κ) (β₀ := fun ω => (d ω).β₀)
    (βE := fun ω => (d ω).βE) (βu := fun ω => (d ω).βu) (S₀ := fun ω => (d ω).S₀) (SE := fun ω => (d ω).SE)
    (Su := fun ω => (d ω).Su) (G₀ := fun ω => (d ω).G₀) (GE := fun ω => (d ω).GE) (G := fun ω => (d ω).G)
    (v := fun ω => (d ω).v) (D := D) hpb' hcfg hind₁' hind₂' hΦ hΦℓ hcrinv hcrlift 0
  filter_upwards [hLn, hrec', hcfg] with ω hω hr hc hD φ hφ
  have hL := hω hD φ hφ
  simp only [mul_zero, add_zero] at hL
  have hT : Chart.chartTransport (hΦ ω) 1 (ψ * chiC κ) (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) =
      Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀') := by
    have := GW2Sf.chartTransport_add_const_mean (hΦ ω) 0 (ψ * chiC κ) (chiC κ) (g ω) hu₀ hu₀'h
      (fun z _ => rfl)
    rw [zero_add] at this
    exact this
  rw [hT, hL]
  -- the union extension is `Gu` on `ℍ`
  have hus := FinRel.IsRelConfigJK.hu (hc hD)
  have hWc : Continuous (W ω) := by
    have h := (FinRel.IsRelConfigJK.hWr (hc hD)).neg
    simp only [neg_neg] at h
    exact h
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show couplingMean κ (W ω) (u ω) (fun z => (d ω).G z) z * φ z = couplingMean κ (W ω) (u ω) (Gu ω) z * φ z
  by_cases hz : z ∈ tsupport φ
  · have hzH : z ∈ H := φ.tsupport_subset hz
    have hzK : z ∉ fwdHull (W ω) (u ω) := Set.disjoint_left.1 hφ hz
    have hmem := WFS.fwdMap_mem_H_of_notMem hus hWc.continuousOn hzH hzK
    simp only [couplingMean, (hr hD).2.2.2.2.2.2 hmem]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end Mean

end InteractingSLE.Theorem14.SB.Om
