/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS3Ident

/-!
# The restarted word at fixed restarted times: own times, validity events, right limits (deterministic)

Packet PROVE-STAGED-S4 (§5.2 of `planning/handoffs/PROVE-STAGED-S3.md`). For the restarted image word of
PROVE-STAGED-S3 (`s3W`, `s3VL`, `s3VR`, `s3ζ`, `s3Chart`; restart capacity `S₀ = σ(τ)`):

* `s4Theta r`: the own time whose capacity is the restarted time `r` (`σ(θ) = S₀ + r`); `s4R q`: the restarted time
  `σ(q) − S₀` of the own time `q`; `s4Av φ q`: the validity event at the own time `q` (alive, `τ < q`, `q` before
  contact, chart avoidance at `s4R q`); `s4F r`: the chart formula `exp(i chartMean − ½ chartVar)` at `r`;
* `continuousOn_lift_trans`, `continuousOn_lift_rChart`: chain-rule lifts of conformal charts are continuous;
* `continuousOn_s3W`, `continuousOn_s3VL`, `continuousOn_s3VR`: the restarted word is continuous before `s3ζ`;
* **`dyIdx_s4Theta_and_mem_s4Av_iff`**: the dyadic level sets of `θ` on the validity events, through capacities;
* **`tendsto_s4F_dyF`**: the right limit along the strict upper dyadic own times `dyF n θ ↓ θ`.

Deterministic; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Word49 StagedS3
open Sec7.Lemma71C (capClock)
open Prop59Pieces (arcW arcVL arcVR arcζ lt_arcζ_iff arcW_of_lt continuousOn_arcW continuousOn_rightImg_realPath)
open WangWu.ChartConst (dyq dyIdx dyF dyIdx_eq_iff lt_dyF tendsto_dyF antitone_dyF)

/-! ### Lifts of composed charts -/

section Lift

/-- **The chain-rule lift of two conformal charts is continuous on the composed domain.** -/
theorem continuousOn_lift_trans {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal)
    (hcl : ContinuousOn c.2.2 c.dom) (hdl : ContinuousOn d.2.2 d.dom) :
    ContinuousOn (c.trans d).2.2 (c.trans d).dom := by
  have hcd := hc.trans hd
  have hsub : ((c.trans d).dom : Set ℂ) ⊆ c.dom ∩ c.1 ⁻¹' d.dom := by
    intro z hz
    rw [SetLike.mem_coe, hcd.mem_dom_iff] at hz
    obtain ⟨h1, h2⟩ := hz
    have hw : d.2.1 (d.1 (c.1 z)) ∈ H := hd.2.1 h1
    have hz' : z ∈ c.dom := by
      rw [← h2]
      exact hc.inv_mem_dom hw
    refine ⟨hz', ?_⟩
    show c.1 z ∈ d.dom
    rw [hd.mem_dom_iff]
    refine ⟨h1, ?_⟩
    have := congrArg c.1 h2
    simp only [Chart.trans_fst, Chart.trans_inv] at this
    rw [hc.2.2 _ hw] at this
    exact this
  have hfwd : ContinuousOn c.1 c.dom := hc.differentiableOn_fwd.continuousOn
  have h1 : ContinuousOn (fun z => d.2.2 (c.1 z)) ((c.trans d).dom : Set ℂ) :=
    hdl.comp (hfwd.mono fun z hz => (hsub hz).1) fun z hz => (hsub hz).2
  exact h1.add (hcl.mono fun z hz => (hsub hz).1)

variable {γ : ℝ → ℂ} {P : Set ℝ} {S₀ : ℝ≥0}

/-- **The restarted chart has a continuous lift.** -/
theorem continuousOn_lift_rChart {c : Chart} (hc : c.IsConformal) (hcl : ContinuousOn c.2.2 c.dom)
    (hγ : IsKilledArc γ P) (hS : (S₀ : WithTop ℝ≥0) < kLife γ P) :
    ContinuousOn (rChart c γ P S₀).2.2 (rChart c γ P S₀).dom := by
  have hw := continuous_clampDrv_kPath hγ hS
  have hw0 := clampDrv_kPath_zero (S₀ := S₀) hγ
  have hid : (Chart.id.loewner (Ito.clampDrv (kPath γ P) S₀) S₀).IsConformal :=
    Chart.isConformal_id.loewner hw hw0 S₀.coe_nonneg
  rw [rChart, loewner_eq_trans]
  exact continuousOn_lift_trans hc hid hcl (Chart.continuousOn_lift_loewner hw hw0 S₀.coe_nonneg)

end Lift

/-! ### Definitions -/

section Defs

variable {Ω : Type*} {nL nR : ℕ}

/-- **The own time of the restarted time `r`**: `σ⁻¹(S₀ + r)` (Word49's `cfTheta` at the image time `S₀ + r`). -/
def s4Theta (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) (r : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  Word49.cfTheta s (fun _ => ⊤) Wj E (s3Start s Wj E τ p + r) p

/-- **The restarted time of the own time `q`**: `σ(q) − S₀`. -/
def s4R (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) (q : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  (capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal - s3Start s Wj E τ p

/-- **The validity event at the own time `q`**: alive, `q` after the last switch and before the first contact, and
the restarted chart avoidance at `σ(q) − S₀`. -/
def s4Av (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) (φ : TestOn upperHalfPlaneOpens)
    (q : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ s3Alive s Wj E τ ∧ τ < q ∧ (q : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p ∧
    Sec7.Lemma71D.IsChartAvoid (fun r => s3W s Wj E τ r p) (s3ζ s Wj E τ p) (s3Chart s Wj E τ p) φ
      (s4R s Wj E τ q p)}

/-- **The chart formula of the restarted word at the restarted time `r`.** -/
def s4F (κ : ℝ) {m n : ℕ} (ρL : Fin m → ℝ) (ρR : Fin n → ℝ) (VL : Fin m → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ)
    (VR : Fin n → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) (a : ℝ) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) (p : Ω × HistorySpace 0 0) : ℂ :=
  Complex.exp (Complex.I * ((Sec7.Lemma71D.chartMean κ ρL ρR (fun r => s3W s Wj E τ r p)
      (fun i r => VL i r p) (fun i r => VR i r p) (s3Chart s Wj E τ p) a (chiC κ) φ r : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar (fun r => s3W s Wj E τ r p) (s3Chart s Wj E τ p) φ r : ℝ) : ℂ))

end Defs

/-! ### Per-sample facts -/

section Sample

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}
  {p : Ω × HistorySpace 0 0}

theorem s3Start_of_alive (hp : p ∈ s3Alive s Wj E τ) :
    s3Start s Wj E τ p = (capClock (gCurve s (fun _ => ⊤) Wj E p) τ).toNNReal := by
  classical
  simp only [s3Start, hp, ↓reduceIte]

theorem coe_s3Start_of_alive (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) :
    ((s3Start s Wj E τ p : ℝ≥0) : ℝ) = capClock (gCurve s (fun _ => ⊤) Wj E p) τ := by
  rw [s3Start_of_alive hp, Real.coe_toNNReal _ ((isKilledArc_gCurve hEg p).capClock_nonneg hp.2)]

theorem lt_s3ζ_iff {r : ℝ≥0} :
    (r : ℝ≥0∞) < s3ζ s Wj E τ p ↔
      ((s3Start s Wj E τ p + r : ℝ≥0) : WithTop ℝ≥0) < kLife (gCurve s (fun _ => ⊤) Wj E p)
        (gPre s (fun _ => ⊤) Wj E p) := by
  rw [s3ζ, lt_arcζ_iff]
  simp only [mem_univ, true_and]

/-- **The own time of a restarted time before the lifetime**: before contact, with capacity `S₀ + r`, and after the
last switch. -/
theorem s4Theta_spec (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < s3ζ s Wj E τ p) :
    ((s4Theta s Wj E τ r p : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p ∧
      capClock (gCurve s (fun _ => ⊤) Wj E p) (s4Theta s Wj E τ r p) = (s3Start s Wj E τ p + r : ℝ≥0) ∧
      τ ≤ s4Theta s Wj E τ r p := by
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨hθP, hθc⟩ := Word49.cfTheta_spec hEg (lt_s3ζ_iff.1 hr)
  refine ⟨hθP, hθc, ?_⟩
  by_contra hlt
  have h : capClock (gCurve s (fun _ => ⊤) Wj E p) (s4Theta s Wj E τ r p) <
      capClock (gCurve s (fun _ => ⊤) Wj E p) τ := hγ.strictMonoOn_capClock hθP hp.2 (not_le.1 hlt)
  have h' : capClock (gCurve s (fun _ => ⊤) Wj E p) (s4Theta s Wj E τ r p) = (s3Start s Wj E τ p + r : ℝ≥0) :=
    hθc
  rw [h', ← coe_s3Start_of_alive hEg hp, NNReal.coe_add] at h
  linarith [r.coe_nonneg]

/-- The restarted time of an own time after the last switch, before contact. -/
theorem coe_s4R (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {q : ℝ}
    (hq : q ∈ gPre s (fun _ => ⊤) Wj E p) (hτq : τ ≤ q) :
    ((s4R s Wj E τ q.toNNReal p : ℝ≥0) : ℝ) =
      capClock (gCurve s (fun _ => ⊤) Wj E p) q - s3Start s Wj E τ p := by
  have hγ := isKilledArc_gCurve hEg p
  have hq0 : 0 ≤ q := hγ.nonneg _ hq
  have hle : (s3Start s Wj E τ p : ℝ) ≤ capClock (gCurve s (fun _ => ⊤) Wj E p) q := by
    rw [coe_s3Start_of_alive hEg hp]
    exact hγ.strictMonoOn_capClock.monotoneOn hp.2 hq hτq
  have hle' : s3Start s Wj E τ p ≤ (capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal :=
    (Real.le_toNNReal_iff_coe_le ((NNReal.coe_nonneg _).trans hle)).2 hle
  rw [s4R, Real.coe_toNNReal _ hq0, NNReal.coe_sub hle', Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hle)]

/-- **The restarted driver is continuous before the restarted lifetime.** -/
theorem continuousOn_s3W (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (p : Ω × HistorySpace 0 0) :
    ContinuousOn (fun r => s3W s Wj E τ r p) {r | (r : ℝ≥0∞) < s3ζ s Wj E τ p} :=
  continuousOn_arcW (fun p => isKilledArc_gCurve hEg p) p

/-- **The restarted left marks are continuous before the restarted lifetime.** -/
theorem continuousOn_s3VL (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (xL : Fin nL → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ)
    (p : Ω × HistorySpace 0 0) (i : Fin (ℓ + (nL + 1))) :
    ContinuousOn (fun r => s3VL xL τs ℓ s Wj E τ i r p) {r | (r : ℝ≥0∞) < s3ζ s Wj E τ p} := by
  have hcn : ContinuousOn ((fun u p => -s3W s Wj E τ u p) · p) {u | (u : ℝ≥0∞) < s3ζ s Wj E τ p} :=
    (continuousOn_s3W hEg p).neg
  refine ((continuousOn_rightImg_realPath (X := fun u p => -s3W s Wj E τ u p) (ω := p) hcn
    (-s3XL xL τs ℓ s Wj E τ p i)).neg).congr fun u hu => ?_
  have hu' : (u : ℝ≥0∞) < s3ζ s Wj E τ p := hu
  have hu'' : (u : ℝ≥0∞) < arcζ (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ p :=
    hu'
  simp only [s3VL, arcVL, Pi.neg_apply, hu'', ↓reduceIte]
  rfl

/-- **The restarted right marks are continuous before the restarted lifetime.** -/
theorem continuousOn_s3VR (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (xR : Fin nR → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ)
    (p : Ω × HistorySpace 0 0) (k : Fin (ℓ + (nR + 1))) :
    ContinuousOn (fun r => s3VR xR τs ℓ s Wj E τ k r p) {r | (r : ℝ≥0∞) < s3ζ s Wj E τ p} := by
  refine (continuousOn_rightImg_realPath (continuousOn_s3W hEg p) (s3XR xR τs ℓ s Wj E τ p k)).congr
    fun u hu => ?_
  have hu' : (u : ℝ≥0∞) < s3ζ s Wj E τ p := hu
  have hu'' : (u : ℝ≥0∞) < arcζ (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ p :=
    hu'
  simp only [s3VR, arcVR, hu'', ↓reduceIte]
  rfl

/-- The restart capacity is before the terminal capacity on the alive event. -/
theorem s3Start_lt_kLife (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) :
    (s3Start s Wj E τ p : WithTop ℝ≥0) <
      kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
  rw [s3Start_of_alive hp]
  exact (isKilledArc_gCurve hEg p).lt_kLife hp.2

/-- **The restarted chart is conformal with a continuous lift** on the alive event. -/
theorem isConformal_s3Chart (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) :
    (s3Chart s Wj E τ p).IsConformal ∧ ContinuousOn (s3Chart s Wj E τ p).2.2 (s3Chart s Wj E τ p).dom :=
  ⟨isConformal_rChart (isConformal_cfChart p.2) (isKilledArc_gCurve hEg p) (s3Start_lt_kLife hEg hp),
    continuousOn_lift_rChart (isConformal_cfChart p.2) (continuousOn_lift_cfChart p.2) (isKilledArc_gCurve hEg p)
      (s3Start_lt_kLife hEg hp)⟩

/-- **The dyadic level sets of the own time `θ_r` on the validity events**, through capacities: `⌊2ⁿθ⌋ = k` and
validity at `dyq n k` iff `dyq n k` is before contact with `S₀ + r < σ(dyq n k)`, but not
`k/2ⁿ` (before contact with `S₀ + r < σ(k/2ⁿ)`), and validity at `dyq n k`. -/
theorem dyIdx_s4Theta_and_mem_s4Av_iff (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p)
    (hp : p ∈ s3Alive s Wj E τ) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < s3ζ s Wj E τ p) (n k : ℕ)
    (φ : TestOn upperHalfPlaneOpens) :
    (dyIdx n (s4Theta s Wj E τ r p) = k ∧ p ∈ s4Av s Wj E τ φ (dyq n k)) ↔
      (((dyq n k : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p ∧
          ((s3Start s Wj E τ p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) (dyq n k)) ∧
        ¬ ((((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p ∧
          ((s3Start s Wj E τ p + r : ℝ≥0) : ℝ) <
            capClock (gCurve s (fun _ => ⊤) Wj E p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)) ∧
        p ∈ s4Av s Wj E τ φ (dyq n k) := by
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨hθP, hθc, -⟩ := s4Theta_spec hEg hp hr
  set θ := s4Theta s Wj E τ r p with hθdef
  set R : ℝ≥0 := s3Start s Wj E τ p + r with hR
  have key : ∀ u : ℝ, u ∈ gPre s (fun _ => ⊤) Wj E p →
      ((θ : ℝ) < u ↔ (R : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) u) := by
    intro u hu
    constructor
    · intro hlt
      rw [← hθc]
      exact hγ.strictMonoOn_capClock hθP hu hlt
    · intro hlt
      by_contra hle
      have := hγ.strictMonoOn_capClock.monotoneOn hu hθP (not_lt.1 hle)
      rw [hθc] at this
      linarith
  have hk0 : (0 : ℝ) ≤ (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hkt : (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ≤ ((dyq n k : ℝ≥0) : ℝ) := by
    exact_mod_cast Word49.div_le_dyq n k
  rw [dyIdx_eq_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hAv⟩
    have hP : ((dyq n k : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p := hAv.2.2.1
    have hP' := hγ.icc _ hP ⟨hk0, hkt⟩
    have h2' : (θ : ℝ) < ((dyq n k : ℝ≥0) : ℝ) := by exact_mod_cast h2
    refine ⟨⟨hP, (key _ hP).1 h2'⟩, fun hh => ?_, hAv⟩
    have h4 := (key _ hP').2 hh.2
    exact absurd (show θ < (k : ℝ≥0) / 2 ^ n by exact_mod_cast h4) (not_lt.2 h1)
  · rintro ⟨⟨hP, h2⟩, h3, hAv⟩
    have hP' := hγ.icc _ hP ⟨hk0, hkt⟩
    refine ⟨⟨?_, ?_⟩, hAv⟩
    · by_contra hlt
      have h5 : (θ : ℝ) < (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by exact_mod_cast not_le.1 hlt
      exact h3 ⟨hP', (key _ hP').1 h5⟩
    · have := (key _ hP).2 h2
      exact_mod_cast this

/-- **The right limit of the restarted chart formula.** On the alive event, if the restarted chart clause is valid
at the restarted time `r`, then along the strict upper dyadic own times `dyF n θ_r ↓ θ_r` the validity events hold
eventually and the chart formula at `σ(dyF n θ_r) − S₀` converges to the chart formula at `r`. -/
theorem tendsto_s4F_dyF (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ)
    {κ : ℝ} {m n' : ℕ} {ρL : Fin m → ℝ} {ρR : Fin n' → ℝ} {VL : Fin m → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ}
    {VR : Fin n' → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ}
    (hVL : ∀ i, ContinuousOn (fun r => VL i r p) {r | (r : ℝ≥0∞) < s3ζ s Wj E τ p})
    (hVR : ∀ i, ContinuousOn (fun r => VR i r p) {r | (r : ℝ≥0∞) < s3ζ s Wj E τ p}) (a : ℝ)
    {r : ℝ≥0} {φ : TestOn upperHalfPlaneOpens}
    (hav : Sec7.Lemma71D.IsChartAvoid (fun r => s3W s Wj E τ r p) (s3ζ s Wj E τ p) (s3Chart s Wj E τ p) φ r) :
    (∀ᶠ n in atTop, p ∈ s4Av s Wj E τ φ (dyF n (s4Theta s Wj E τ r p))) ∧
      Tendsto (fun n => s4F κ ρL ρR VL VR s Wj E τ a φ (s4R s Wj E τ (dyF n (s4Theta s Wj E τ r p)) p) p) atTop
        (𝓝 (s4F κ ρL ρR VL VR s Wj E τ a φ r p)) := by
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  set θ := s4Theta s Wj E τ r p with hθdef
  set S₀ := s3Start s Wj E τ p with hS₀
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  obtain ⟨hθP, hθc, hτθ⟩ := s4Theta_spec hEg hp hav.1
  obtain ⟨S', hS'P, hθS'⟩ := hγ.exists_gt _ hθP
  have hdyR : Tendsto (fun n => ((dyF n θ : ℝ≥0) : ℝ)) atTop (𝓝 (θ : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_dyF θ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdyR.eventually (gt_mem_nhds hθS'))
  have hmemP : ∀ n ≥ N, ((dyF n θ : ℝ≥0) : ℝ) ∈ P := fun n hn =>
    hγ.icc S' hS'P ⟨NNReal.coe_nonneg _, (hN n hn).le⟩
  set si : ℕ → ℝ≥0 := fun i => s4R s Wj E τ (dyF (i + N) θ) p with hsi
  have hsa : Antitone si := fun a b hab => tsub_le_tsub_right (Real.toNNReal_le_toNNReal
    (hγ.strictMonoOn_capClock.monotoneOn (hmemP _ (Nat.le_add_left N b)) (hmemP _ (Nat.le_add_left N a))
      (by exact_mod_cast antitone_dyF θ (Nat.add_le_add_right hab N)))) _
  have hts : ∀ i, r < si i := fun i => by
    have h := hγ.strictMonoOn_capClock hθP (hmemP (i + N) (Nat.le_add_left N i))
      (by exact_mod_cast lt_dyF (i + N) θ)
    rw [hθc] at h
    have h' : S₀ + r < (capClock γ (dyF (i + N) θ)).toNNReal := Real.lt_toNNReal_iff_coe_lt.2 h
    exact lt_tsub_iff_left.2 h'
  have hlim : Tendsto si atTop (𝓝 r) := by
    have hin : Tendsto (fun i => ((dyF (i + N) θ : ℝ≥0) : ℝ)) atTop (𝓝[P] (θ : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hdyR.comp (tendsto_add_atTop_nat N),
        Eventually.of_forall fun i => hmemP (i + N) (Nat.le_add_left N i)⟩
    have hcap := ((hγ.continuousOn_capClock _ hθP).tendsto).comp hin
    rw [hθc] at hcap
    have h2 := (continuous_real_toNNReal.tendsto _).comp hcap
    rw [Real.toNNReal_coe] at h2
    have h3 := h2.sub_const S₀
    rwa [add_tsub_cancel_left] at h3
  obtain ⟨hcc, hcl⟩ := isConformal_s3Chart hEg hp
  obtain ⟨hev, hmean, hvar⟩ := Sec7.Lemma71D.tendsto_chart_of_isChartAvoid (κ := κ) (ρL := ρL) (ρR := ρR)
    (a := a) (k := chiC κ) (vL := fun i t => VL i t p) (vR := fun j t => VR j t p) hcc hcl
    (continuousOn_s3W hEg p) hVL hVR hav hsa hts hlim
  refine ⟨?_, ?_⟩
  · obtain ⟨I, hI⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨I + N, fun n hn => ?_⟩
    have hnN : n - N + N = n := Nat.sub_add_cancel (le_trans (Nat.le_add_left N I) hn)
    have h := hI (n - N) (by omega)
    simp only [hsi, hnN] at h
    refine ⟨hp, ?_, hmemP n (le_trans (Nat.le_add_left N I) hn), h⟩
    exact lt_of_le_of_lt hτθ (by exact_mod_cast lt_dyF n θ)
  · have hF' : Tendsto (fun i => s4F κ ρL ρR VL VR s Wj E τ a φ (si i) p) atTop
        (𝓝 (s4F κ ρL ρR VL VR s Wj E τ a φ r p)) := by
      simp only [s4F]
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hmean)).sub ?_
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hvar)
    exact (tendsto_add_atTop_iff_nat N).1 hF'

end Sample

end InteractingSLE.Sec5.CrossCond.StagedS4
