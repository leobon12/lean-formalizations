/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65Time
import InteractingSLE.Spec.Sec6.CircleAverage
import MathFin.Probability.Brownian.ExitTime
import InteractingSLE.GFF.LocalSets.MarkovNesting

/-!
# Proposition 6.5, part 3: the conditional mean at a point

Packet PROVE-SEC6-B (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, pp. 157–159).

This file connects the abstract time-continuity theorem (`Prop65Time`) to the setting of
Proposition 6.5. Fix `z ∈ ℍ`, a level `c > 0` and a horizon `R`. On the `𝓕₀`-event `G = {r₀(z) > c}`
and up to the first time `ρ` at which the conformal radius `r_t(z)` reaches `c` (capped at `R`), the
Koebe covering theorem keeps a fixed radial bump `b` around `z` inside the component `D_t(z)`. The
normalized pairing `X = 1_G (h, b)/∫b` is then conditionally Gaussian at every stopping time `T ≤ ρ`,
with mean `1_G H_T(z)` (mean-value property) and variance
`1_G (∫b)^{-2} Var_{D_T(z)}(b) = 1_G (const + log r_T(z))` (the variance identity of Lemma 6.4,
`zeroGFFTestCov_sub_eq_log_confRadius`, after reducing the Green covariance of `ℍ ∖ Z_T` to the
component `D_T(z)`).

The hitting time is built from MathFin's exit time of a continuous adapted process (no right-continuity
of the filtration is needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### The capped first time a continuous process is `≤ c` -/

/-- The auxiliary process `max 0 (1 + (c − Y))`, whose absolute value reaches `1` exactly when
`Y ≤ c`. -/
def hitProc (Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ := max 0 (1 + (c - Y s ω))

omit mΩ in
lemma one_le_abs_hitProc_iff {Y : ℝ≥0 → Ω → ℝ} {c : ℝ} {s : ℝ≥0} {ω : Ω} :
    ((1 : ℕ) : ℝ) ≤ |hitProc Y c s ω| ↔ Y s ω ≤ c := by
  simp only [hitProc, Nat.cast_one]
  rw [abs_of_nonneg (le_max_left _ _)]
  constructor
  · intro h
    rcases le_total 0 (1 + (c - Y s ω)) with h0 | h0
    · rw [max_eq_right h0] at h; linarith
    · rw [max_eq_left h0] at h; linarith
  · intro h
    exact le_max_of_le_right (by linarith)

omit mΩ in
lemma continuous_hitProc {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) (c : ℝ)
    (ω : Ω) : Continuous fun s => hitProc Y c s ω :=
  continuous_const.max (continuous_const.add (continuous_const.sub (hYc ω)))

/-- The first time `Y ≤ c`, capped at `R`. -/
def hitLe (Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (R : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (MathFin.exitTime (hitProc Y c) 1 ω) (R : WithTop ℝ≥0)).untopD R

omit mΩ in
lemma coe_hitLe (Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (R : ℝ≥0) (ω : Ω) :
    ((hitLe Y c R ω : ℝ≥0) : WithTop ℝ≥0) = min (MathFin.exitTime (hitProc Y c) 1 ω) R := by
  have hne : min (MathFin.exitTime (hitProc Y c) 1 ω) (R : WithTop ℝ≥0) ≠ ⊤ :=
    ((min_le_right _ _).trans_lt (WithTop.coe_lt_top R)).ne
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [hitLe, ← hx]
  rfl

omit mΩ in
lemma hitLe_le (Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (R : ℝ≥0) (ω : Ω) : hitLe Y c R ω ≤ R := by
  have := coe_hitLe Y c R ω
  rw [← WithTop.coe_le_coe, this]
  exact min_le_right _ _

omit mΩ in
lemma exitTime_le_iff' {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) (c : ℝ)
    (t : ℝ≥0) (ω : Ω) :
    MathFin.exitTime (hitProc Y c) 1 ω ≤ (t : WithTop ℝ≥0) ↔ ∃ s ∈ Icc (0 : ℝ≥0) t, Y s ω ≤ c := by
  rw [MathFin.exitTime_le_iff (fun ω => continuous_hitProc hYc c ω)]
  simp only [one_le_abs_hitProc_iff]

omit mΩ in
/-- Before the hitting time, `Y > c`. -/
lemma lt_of_lt_hitLe {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) {c : ℝ}
    {R t : ℝ≥0} {ω : Ω} (ht : t < hitLe Y c R ω) : c < Y t ω := by
  by_contra hle
  push Not at hle
  have h1 : MathFin.exitTime (hitProc Y c) 1 ω ≤ (t : WithTop ℝ≥0) :=
    (exitTime_le_iff' hYc c t ω).2 ⟨t, ⟨zero_le, le_rfl⟩, hle⟩
  have h2 : ((hitLe Y c R ω : ℝ≥0) : WithTop ℝ≥0) ≤ t := by
    rw [coe_hitLe]; exact (min_le_left _ _).trans h1
  exact (lt_irrefl _ (ht.trans_le (WithTop.coe_le_coe.1 h2)))

omit mΩ in
/-- Up to (and including) the hitting time, `Y ≥ c`, if `Y₀ > c`. -/
lemma le_of_le_hitLe {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) {c : ℝ}
    {R t : ℝ≥0} {ω : Ω} (h0 : c < Y 0 ω) (ht : t ≤ hitLe Y c R ω) : c ≤ Y t ω := by
  rcases ht.lt_or_eq with ht | ht
  · exact (lt_of_lt_hitLe hYc ht).le
  · rcases (zero_le (a := t)).eq_or_lt with h00 | hpos
    · rw [← h00]; exact h0.le
    · have hlim : Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (Y t ω)) :=
        ((hYc ω).tendsto t).mono_left nhdsWithin_le_nhds
      have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (lt_of_lt_hitLe hYc (ht ▸ hs)).le

omit mΩ in
/-- If `Y > c` on `[0, t]` and `t ≤ R`, then `t ≤` the hitting time. -/
lemma le_hitLe_of_forall {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) {c : ℝ}
    {R t : ℝ≥0} {ω : Ω} (htR : t ≤ R) (hY : ∀ s ≤ t, c < Y s ω) : t ≤ hitLe Y c R ω := by
  rw [← WithTop.coe_le_coe, coe_hitLe]
  refine le_min ?_ (WithTop.coe_le_coe.2 htR)
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hs, hYs⟩ := (exitTime_le_iff' hYc c t ω).1 hlt.le
  exact (hY s hs.2).not_ge hYs

omit mΩ in
/-- If `Y₀ ≤ c`, the hitting time is `0`. -/
lemma hitLe_eq_zero {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) {c : ℝ}
    {R : ℝ≥0} {ω : Ω} (h0 : Y 0 ω ≤ c) : hitLe Y c R ω = 0 := by
  have h1 : MathFin.exitTime (hitProc Y c) 1 ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) :=
    (exitTime_le_iff' hYc c 0 ω).2 ⟨0, ⟨le_rfl, le_rfl⟩, h0⟩
  have h2 : ((hitLe Y c R ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    rw [coe_hitLe]; exact (min_le_left _ _).trans h1
  exact le_antisymm (WithTop.coe_le_coe.1 h2) zero_le

omit mΩ in
/-- The hitting time increases when the level decreases and the cap increases. -/
lemma hitLe_mono {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω) {c c' : ℝ}
    {R R' : ℝ≥0} (hc : c' ≤ c) (hR : R ≤ R') (ω : Ω) : hitLe Y c R ω ≤ hitLe Y c' R' ω := by
  by_contra hlt
  push Not at hlt
  set s := hitLe Y c' R' ω
  have hsR' : s < R' := hlt.trans_le ((hitLe_le Y c R ω).trans hR)
  have hex : MathFin.exitTime (hitProc Y c') 1 ω ≤ (s : WithTop ℝ≥0) := by
    have := coe_hitLe Y c' R' ω
    rcases min_choice (MathFin.exitTime (hitProc Y c') 1 ω) (R' : WithTop ℝ≥0) with h | h
    · rw [this, h]
    · rw [h] at this
      exact absurd (WithTop.coe_le_coe.1 this.symm.le) (not_le.2 hsR')
  obtain ⟨s', hs', hYs'⟩ := (exitTime_le_iff' hYc c' s ω).1 hex
  exact (lt_of_lt_hitLe hYc (hs'.2.trans_lt hlt)).not_ge (hYs'.trans hc)

/-- The capped hitting time is a stopping time. -/
theorem isStoppingTime_hitLe {𝓕 : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun t => Y t ω) (hYm : ∀ t, Measurable[𝓕 t] (Y t)) (c : ℝ)
    (R : ℝ≥0) : IsStoppingTime 𝓕 fun ω => (hitLe Y c R ω : WithTop ℝ≥0) := by
  have hm : ∀ t, Measurable[𝓕 t] (hitProc Y c t) := fun t =>
    measurable_const.max (measurable_const.add (measurable_const.sub (hYm t)))
  have h1 := (MathFin.isStoppingTime_exitTime_of_measurable hm
    (fun ω => continuous_hitProc hYc c ω) 1).min (isStoppingTime_const 𝓕 R)
  have e : (fun ω => min (MathFin.exitTime (hitProc Y c) 1 ω) (R : WithTop ℝ≥0)) =
      fun ω => ((hitLe Y c R ω : ℝ≥0) : WithTop ℝ≥0) := funext fun ω => (coe_hitLe Y c R ω).symm
  rwa [e] at h1

/-! ### The setting of Proposition 6.5 -/

open QuantumZipper (H zeroGFFTestCov)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn TestOn)

/-- `V ∖ (component of V containing x)` is open, for open `V ⊆ ℂ`. -/
theorem isOpen_diff_connectedComponentIn {V : Set ℂ} (hV : IsOpen V) (x : ℂ) :
    IsOpen (V \ connectedComponentIn V x) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨connectedComponentIn V y, fun w hw => ⟨connectedComponentIn_subset _ _ hw, fun hwx => ?_⟩,
    hV.connectedComponentIn, mem_connectedComponentIn hy.1⟩
  have h1 : connectedComponentIn V x = connectedComponentIn V w := connectedComponentIn_eq hwx
  have h2 : connectedComponentIn V y = connectedComponentIn V w := connectedComponentIn_eq hw
  exact hy.2 (h1.trans h2.symm ▸ mem_connectedComponentIn hy.1)

/-- **The setting of Proposition 6.5** on `D = ℍ` (`h` a GFF with deterministic harmonic mean `F`;
`Z_t` an increasing exploration with relatively closed values, `ℍ ∖ Z_t` open; the conditional law of the
unexplored field at every bounded stopping time `T`: `h|_{ℍ∖Z_T} = H_T + h⁰_T` with `H_T` harmonic on
`ℍ ∖ Z_T` and, given `𝓕_T`, `h⁰_T` a centred Gaussian field with the Green covariance of `ℍ ∖ Z_T`; the
components of `ℍ ∖ Z_t` simply connected with conformal radius `r_t(z)` at `z`, `r_t(z) = 0` once
`z ∈ Z_t`, `t ↦ r_t(z)` continuous and adapted). -/
structure Setting (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (h : Ω → DistOn upperHalfPlaneOpens)
    (F : ℂ → ℝ) (Z : ℝ≥0 → Ω → Set ℂ) (Hc : ℝ≥0 → Ω → ℂ → ℝ) (r : ℝ≥0 → Ω → ℂ → ℝ) :
    Prop where
  measurable_field : Measurable h
  harmonic_mean : InnerProductSpace.HarmonicOnNhd F H
  gff : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ x, F x * φ x) P
  isOpen : ∀ t ω, IsOpen (H \ Z t ω)
  mono : ∀ ω, Monotone fun t => Z t ω
  harmonic : ∀ t ω, InnerProductSpace.HarmonicOnNhd (Hc t ω) (H \ Z t ω)
  law : ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)),
    (∃ C : ℝ≥0, ∀ ω, T ω ≤ C) → ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      Disjoint (tsupport φ) (Z (T ω) ω) →
        P[fun ω' => cexp (I * (h ω' φ : ℂ)) | hT.measurableSpace] ω =
          cexp (I * ((∫ x, Hc (T ω) ω x * φ x : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov (H \ Z (T ω) ω) φ φ : ℝ) : ℂ))
  radius : ∀ t ω z, z ∈ H → z ∉ Z t ω → ∃ φ : ℂ → ℂ,
    IsConformalBijection φ (ball 0 1) (connectedComponentIn (H \ Z t ω) z) ∧ φ 0 = z ∧
      ‖deriv φ 0‖ = r t ω z
  radius_zero : ∀ t ω z, z ∈ Z t ω → r t ω z = 0
  radius_cont : ∀ ω z, z ∈ H → Continuous fun t => r t ω z
  radius_adapted : ∀ t z, z ∈ H → Measurable[𝓕 t] fun ω => r t ω z

namespace Setting

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {h : Ω → DistOn upperHalfPlaneOpens} {F : ℂ → ℝ}
  {Z : ℝ≥0 → Ω → Set ℂ} {Hc : ℝ≥0 → Ω → ℂ → ℝ} {r : ℝ≥0 → Ω → ℂ → ℝ}

theorem r_pos (S : Setting P 𝓕 h F Z Hc r) {t : ℝ≥0} {ω : Ω} {z : ℂ} (hz : z ∈ H)
    (hzZ : z ∉ Z t ω) : 0 < r t ω z := by
  obtain ⟨φ, hφ, hφ0, hφr⟩ := S.radius t ω z hz hzZ
  rw [← hφr]
  exact norm_pos_iff.2 (QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hφ.1 hφ.2.injOn
    (mem_ball_self one_pos))

theorem notMem_of_r_pos (S : Setting P 𝓕 h F Z Hc r) {t : ℝ≥0} {ω : Ω} {z : ℂ}
    (hr : 0 < r t ω z) : z ∉ Z t ω := fun hz => by
  rw [S.radius_zero t ω z hz] at hr; exact lt_irrefl _ hr

/-- **Koebe**: if `r_t(z) ≥ c > 0`, the closed ball of radius `κ c/2` about `z` lies in the component
`D_t(z)`. -/
theorem closedBall_subset (S : Setting P 𝓕 h F Z Hc r) {t : ℝ≥0} {ω : Ω} {z : ℂ} (hz : z ∈ H)
    {c : ℝ} (hc : 0 < c) (hcr : c ≤ r t ω z) :
    closedBall z (QuantumZipper.CA.Koebe.koebeCovConst * c / 2) ⊆
      connectedComponentIn (H \ Z t ω) z := by
  obtain ⟨φ, hφ, hφ0, hφr⟩ := S.radius t ω z hz (S.notMem_of_r_pos (hc.trans_le hcr))
  have hk0 := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe (c := 0) (r := 1) hφ.1 hφ.2.injOn
  rw [hφ.2.image_eq, hφ0, hφr] at hk
  refine (closedBall_subset_ball ?_).trans hk
  nlinarith

/-- **The variance identity on the component** (Lemma 6.4's identity, reduced from `ℍ ∖ Z_t` to the
component `D_t(z)`): `Var_{ℍ∖Z_t}(b) = Var_ℍ(b) − (∫ b)² (log(2 Im z) − log r_t(z))` for a radial bump
`b` of radius `ε ≤ κ c/2`, when `r_t(z) ≥ c > 0`. -/
theorem var_eq (S : Setting P 𝓕 h F Z Hc r) {t : ℝ≥0} {ω : Ω} {z : ℂ} (hz : z ∈ H) {c : ℝ}
    (hc : 0 < c) (hcr : c ≤ r t ω z) {ε : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ QuantumZipper.CA.Koebe.koebeCovConst * c / 2)
    (hεH : closedBall z ε ⊆ upperHalfPlaneOpens) :
    zeroGFFTestCov (H \ Z t ω) (GFF.bumpTest z hε hεH) (GFF.bumpTest z hε hεH) =
      zeroGFFTestCov upperHalfPlaneOpens (GFF.bumpTest z hε hεH) (GFF.bumpTest z hε hεH) -
        (ε ^ 2 * GFF.bumpMass) ^ 2 * (Real.log (2 * z.im) - Real.log (r t ω z)) := by
  have hr := hc.trans_le hcr
  set D := connectedComponentIn (H \ Z t ω) z with hD
  have hDo : IsOpen D := (S.isOpen t ω).connectedComponentIn
  have hDsub : D ⊆ H \ Z t ω := connectedComponentIn_subset _ _
  have hDH : D ⊆ H := hDsub.trans sdiff_subset
  have hball : closedBall z ε ⊆ D :=
    (closedBall_subset_closedBall hεc).trans (S.closedBall_subset hz hc hcr)
  have hsupp : tsupport (GFF.bumpTest z hε hεH) ⊆ D :=
    (GFF.tsupport_bumpFun_subset hε).trans hball
  have hcomp := LocalSets.zeroGFFTestCov_eq_of_isClopen (S.isOpen t ω) sdiff_subset hDo hDsub
    (isOpen_diff_connectedComponentIn (S.isOpen t ω) z) (GFF.bumpTest z hε hεH) hsupp
  obtain ⟨φ, hφ, hφ0, hφr⟩ := S.radius t ω z hz (S.notMem_of_r_pos hr)
  obtain ⟨ψ, hψ, hψz, hψd⟩ := exists_isConformalBijection_inv hφ hφ0 hφr hr
  have key := zeroGFFTestCov_sub_eq_log_confRadius (U := ⟨D, hDo⟩) hDH hψ hψz hε hball
  rw [hψd, Real.log_inv] at key
  rw [hcomp]
  change zeroGFFTestCov D (GFF.bumpFun z ε) (GFF.bumpFun z ε) =
    zeroGFFTestCov upperHalfPlaneOpens (GFF.bumpFun z ε) (GFF.bumpFun z ε) - _
  change zeroGFFTestCov upperHalfPlaneOpens (GFF.bumpFun z ε) (GFF.bumpFun z ε) -
    zeroGFFTestCov D (GFF.bumpFun z ε) (GFF.bumpFun z ε) = _ at key
  linarith

end Setting

/-! ### The localized observable -/

/-- The bump radius at level `c` around `z`. -/
def bumpRad (z : ℂ) (c : ℝ) : ℝ := min (QuantumZipper.CA.Koebe.koebeCovConst * c / 2) (z.im / 2)

lemma bumpRad_pos {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) : 0 < bumpRad z c :=
  lt_min (by have := QuantumZipper.CA.Koebe.koebeCovConst_pos; positivity) (by linarith)

lemma bumpRad_le (z : ℂ) (c : ℝ) :
    bumpRad z c ≤ QuantumZipper.CA.Koebe.koebeCovConst * c / 2 := min_le_left _ _

lemma closedBall_bumpRad_subset {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    closedBall z (bumpRad z c) ⊆ upperHalfPlaneOpens := by
  intro w hw
  change 0 < w.im
  have h1 : |w.im - z.im| ≤ dist w z := by
    rw [Complex.dist_eq]; exact (Complex.abs_im_le_norm (w - z)).trans_eq' (by simp)
  have h2 : bumpRad z c ≤ z.im / 2 := min_le_right _ _
  have h3 := mem_closedBall.1 hw
  have := neg_abs_le (w.im - z.im)
  linarith

/-- The radial bump test function at level `c`. -/
def bumpT {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) : TestOn upperHalfPlaneOpens :=
  GFF.bumpTest z (bumpRad_pos hz hc) (closedBall_bumpRad_subset hz c)

/-- Its mass `∫ b = ε² m₁`. -/
def bumpM (z : ℂ) (c : ℝ) : ℝ := bumpRad z c ^ 2 * GFF.bumpMass

lemma bumpM_pos {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) : 0 < bumpM z c :=
  mul_pos (pow_pos (bumpRad_pos hz hc) 2) GFF.bumpMass_pos

/-- The `𝓕₀`-event `{r₀(z) > c}`. -/
def startEv (r : ℝ≥0 → Ω → ℂ → ℝ) (z : ℂ) (c : ℝ) : Set Ω := {ω | c < r 0 ω z}

/-- The localized observable `X = 1_G (h, b)/∫b` (`G` an `𝓕₀`-event). -/
def obsX (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) {z : ℂ} (hz : 0 < z.im)
    {c : ℝ} (hc : 0 < c) (ω : Ω) : ℝ :=
  G.indicator (fun ω => (bumpM z c)⁻¹ * h ω (bumpT hz hc)) ω

/-- The constant `K₀ = (∫b)^{-2} Var_ℍ(b) − log(2 Im z)`. -/
def varK₀ {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) : ℝ :=
  (bumpM z c)⁻¹ ^ 2 * zeroGFFTestCov upperHalfPlaneOpens (bumpT hz hc) (bumpT hz hc) -
    Real.log (2 * z.im)

/-- The variance bound `K = (∫b)^{-2} Var_ℍ(b)`. -/
def varK {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) : ℝ :=
  (bumpM z c)⁻¹ ^ 2 * zeroGFFTestCov upperHalfPlaneOpens (bumpT hz hc) (bumpT hz hc)

/-- The variance process `v_t = 1_G (K₀ + log max(r_t(z), c))`. -/
def varV (G : Set Ω) (r : ℝ≥0 → Ω → ℂ → ℝ) {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  G.indicator (fun ω => varK₀ hz hc + Real.log (max (r t ω z) c)) ω

/-- The localizing time: the first time `r_t(z) ≤ c`, capped at `R`. -/
def locTime (r : ℝ≥0 → Ω → ℂ → ℝ) (z : ℂ) (c : ℝ) (R : ℝ≥0) : Ω → ℝ≥0 :=
  hitLe (fun t ω => r t ω z) c R

namespace Setting

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {h : Ω → DistOn upperHalfPlaneOpens} {F : ℂ → ℝ}
  {Z : ℝ≥0 → Ω → Set ℂ} {Hc : ℝ≥0 → Ω → ℂ → ℝ} {r : ℝ≥0 → Ω → ℂ → ℝ}

theorem le_r_of_le_locTime (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) {c : ℝ}
    {R t : ℝ≥0} {ω : Ω} (hω : ω ∈ startEv r z c) (ht : t ≤ locTime r z c R ω) : c ≤ r t ω z :=
  le_of_le_hitLe (fun ω => S.radius_cont ω z hz) hω ht

theorem measurableSet_startEv (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    MeasurableSet[𝓕 0] (startEv r z c) :=
  measurableSet_lt measurable_const (S.radius_adapted 0 z hz)

theorem isStoppingTime_locTime (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) (c : ℝ)
    (R : ℝ≥0) : IsStoppingTime 𝓕 fun ω => (locTime r z c R ω : WithTop ℝ≥0) :=
  isStoppingTime_hitLe (fun ω => S.radius_cont ω z hz) (fun t => S.radius_adapted t z hz) c R

/-- On `G`, while `r_t(z) ≥ c`: `v_t = (∫b)^{-2} Var_{ℍ∖Z_t}(b)`. -/
theorem varV_eq (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω} {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c)
    {t : ℝ≥0} {ω : Ω} (hω : ω ∈ G) (hcr : c ≤ r t ω z) :
    varV G r hz hc t ω =
      (bumpM z c)⁻¹ ^ 2 * zeroGFFTestCov (H \ Z t ω) (bumpT hz hc) (bumpT hz hc) := by
  have hv := S.var_eq (t := t) (ω := ω) hz hc hcr (bumpRad_pos hz hc) (bumpRad_le z c)
    (closedBall_bumpRad_subset hz c)
  have hm := (bumpM_pos hz hc).ne'
  simp only [varV, indicator_of_mem hω, max_eq_left hcr, varK₀]
  change _ = (bumpM z c)⁻¹ ^ 2 * zeroGFFTestCov (H \ Z t ω) (bumpT hz hc) (bumpT hz hc)
  rw [show zeroGFFTestCov (H \ Z t ω) (bumpT hz hc) (bumpT hz hc) = _ from hv]
  change _ = (bumpM z c)⁻¹ ^ 2 * (_ - bumpM z c ^ 2 * _)
  rw [mul_sub, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hm, one_pow, one_mul]
  simp only [bumpT]
  ring

theorem continuous_varV (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω} {z : ℂ} (hz : 0 < z.im) {c : ℝ}
    (hc : 0 < c) (ω : Ω) : Continuous fun t => varV G r hz hc t ω := by
  by_cases hω : ω ∈ G
  · simp only [varV, indicator_of_mem hω]
    refine continuous_const.add (Continuous.log ((S.radius_cont ω z hz).max continuous_const)
      fun t => (hc.trans_le (le_max_right _ _)).ne')
  · simp only [varV, indicator_of_notMem hω]
    exact continuous_const

theorem measurable_varV (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω} (hG0 : MeasurableSet[𝓕 0] G)
    {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) (t : ℝ≥0) : Measurable[𝓕 t] (varV G r hz hc t) := by
  have hG : MeasurableSet[𝓕 t] G := 𝓕.mono (zero_le (a := t)) _ hG0
  exact (measurable_const.add (((S.radius_adapted t z hz).max measurable_const).log)).indicator hG

theorem varV_nonneg (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω} {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c)
    {t : ℝ≥0} {ω : Ω} (hcr : ω ∈ G → c ≤ r t ω z) : 0 ≤ varV G r hz hc t ω := by
  by_cases hω : ω ∈ G
  · rw [S.varV_eq hz hc hω (hcr hω)]
    exact mul_nonneg (sq_nonneg _) (LocalSets.zeroGFFTestCov_self_nonneg (S.isOpen t ω)
      sdiff_subset _)
  · simp [varV, hω]

theorem varV_le (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω} {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c)
    {t : ℝ≥0} {ω : Ω} (hcr : ω ∈ G → c ≤ r t ω z) :
    varV G r hz hc t ω ≤ varK hz hc := by
  have hK : 0 ≤ varK hz hc := mul_nonneg (sq_nonneg _)
    (LQGMetric.zeroGFFTestCov_self_nonneg (LQGMetric.zbAdmissible_of_subset_H subset_rfl) _)
  by_cases hω : ω ∈ G
  · rw [S.varV_eq hz hc hω (hcr hω), varK]
    exact mul_le_mul_of_nonneg_left (LocalSets.zeroGFFTestCov_mono (S.isOpen t ω)
      QuantumZipper.isOpen_H sdiff_subset subset_rfl _) (sq_nonneg _)
  · simp only [varV, indicator_of_notMem hω]; exact hK

theorem varV_anti (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω} {z : ℂ} (hz : 0 < z.im) {c : ℝ}
    (hc : 0 < c) {ρ : Ω → ℝ≥0} (hcrρ : ∀ ω ∈ G, ∀ t ≤ ρ ω, c ≤ r t ω z) (ω : Ω) (s t : ℝ≥0)
    (hst : s ≤ t) (htρ : t ≤ ρ ω) : varV G r hz hc t ω ≤ varV G r hz hc s ω := by
  by_cases hω : ω ∈ G
  · rw [S.varV_eq hz hc hω (hcrρ ω hω t htρ), S.varV_eq hz hc hω (hcrρ ω hω s (hst.trans htρ))]
    refine mul_le_mul_of_nonneg_left (LocalSets.zeroGFFTestCov_mono (S.isOpen t ω) (S.isOpen s ω)
      (sdiff_subset_sdiff_right (S.mono ω hst)) sdiff_subset _) (sq_nonneg _)
  · simp [varV, hω]

theorem memLp_obsX [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω}
    (hG0 : MeasurableSet[𝓕 0] G) {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) :
    MemLp (obsX G h hz hc) 2 P := by
  have hlaw := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess S.gff (bumpT hz hc)
  have hm : Measurable fun ω => h ω (bumpT hz hc) :=
    (LQGMetric.measurable_distOn_apply _).comp S.measurable_field
  have h1 : MemLp (fun ω => h ω (bumpT hz hc)) 2 P := by
    have := memLp_id_gaussianReal (μ := ∫ x, F x * bumpT hz hc x)
      (v := (zeroGFFTestCov upperHalfPlaneOpens (bumpT hz hc) (bumpT hz hc)).toNNReal) 2
    rw [← hlaw] at this
    exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).1 this
  exact (h1.const_mul _).indicator (𝓕.le 0 _ hG0)

/-- **The localized observable is conditionally Gaussian** at every stopping time `T ≤ ρ`, with mean
`1_G H_T(z)` and variance `v_T`. -/
theorem condGaussian_obsX [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω}
    (hG0 : MeasurableSet[𝓕 0] G) {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) {ρ : Ω → ℝ≥0}
    {R : ℝ≥0} (hρR : ∀ ω, ρ ω ≤ R) (hcrρ : ∀ ω ∈ G, ∀ t ≤ ρ ω, c ≤ r t ω z) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hTρ : ∀ ω, T ω ≤ ρ ω) :
    IsCondGaussian hT.measurableSpace P (obsX G h hz hc) (P[obsX G h hz hc | hT.measurableSpace])
        (fun ω => varV G r hz hc (T ω) ω) (varK hz hc) ∧
      P[obsX G h hz hc | hT.measurableSpace] =ᵐ[P]
        G.indicator (fun ω => Hc (T ω) ω z) := by
  set b := bumpT hz hc with hbdef
  set m := bumpM z c with hmdef
  have hm : 0 < m := bumpM_pos hz hc
  have hε := bumpRad_pos hz hc
  have hbcoe : ⇑b = GFF.bumpFun z (bumpRad z c) := rfl
  have h0T : 𝓕 0 ≤ hT.measurableSpace := by
    have := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓕 0) hT
      fun ω => WithTop.coe_le_coe.2 (zero_le (a := T ω))
    rwa [IsStoppingTime.measurableSpace_const] at this
  have hGT : MeasurableSet[hT.measurableSpace] G := h0T _ hG0
  have hGm : MeasurableSet G := 𝓕.le 0 _ hG0
  have hcr : ∀ ω ∈ G, c ≤ r (T ω) ω z := fun ω hω => hcrρ ω hω (T ω) (hTρ ω)
  have hball : ∀ ω ∈ G, closedBall z (bumpRad z c) ⊆ H \ Z (T ω) ω := fun ω hω =>
    ((closedBall_subset_closedBall (bumpRad_le z c)).trans
      (S.closedBall_subset hz hc (hcr ω hω))).trans (connectedComponentIn_subset _ _)
  have hTb : ∃ C : ℝ≥0, ∀ ω, T ω ≤ C := ⟨R, fun ω => (hTρ ω).trans (hρR ω)⟩
  have hhm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun ω => h ω φ := fun φ =>
    (LQGMetric.measurable_distOn_apply φ).comp S.measurable_field
  have hXm : Measurable (obsX G h hz hc) :=
    (measurable_const.mul (hhm b)).indicator hGm
  have hvT : StronglyMeasurable[hT.measurableSpace] fun ω => varV G r hz hc (T ω) ω :=
    stronglyMeasurable_comp_stoppingTime (S.continuous_varV hz hc) (S.measurable_varV hG0 hz hc) hT
  refine IsCondGaussian.of_condCharFun hT.measurableSpace_le hXm
    ((S.memLp_obsX hG0 hz hc).integrable one_le_two) hvT.measurable
    (fun ω => S.varV_nonneg hz hc (hcr ω)) (fun ω => S.varV_le hz hc (hcr ω)) fun s => ?_
  -- the test function `(s/m) • b`
  set φ : TestOn upperHalfPlaneOpens := (s * m⁻¹) • b with hφdef
  have hlaw := S.law T hT hTb φ
  have hφcoe : ∀ x, φ x = (s * m⁻¹) * b x := fun x => by simp [hφdef]
  have hsupp : ∀ ω ∈ G, Disjoint (tsupport φ) (Z (T ω) ω) := by
    intro ω hω
    refine Set.disjoint_left.2 fun x hx hxZ => ?_
    have h1 : tsupport φ ⊆ tsupport b := by
      have e : (⇑φ : ℂ → ℝ) = fun x => (s * m⁻¹) * b x := funext hφcoe
      rw [e]; exact tsupport_mul_subset_right
    have h2 : x ∈ H \ Z (T ω) ω :=
      hball ω hω ((GFF.tsupport_bumpFun_subset hε) (hbcoe ▸ h1 hx))
    exact h2.2 hxZ
  -- the decomposition of `e^{isX}`
  have hI1 : Integrable (fun ω => cexp (I * (h ω φ : ℂ))) P :=
    Integrable.of_bound ((by fun_prop : Measurable fun x : ℝ => cexp (I * (x : ℂ))).comp
      (hhm φ)).aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_cexp_I_mul_ofReal _).le)
  have hdec : (fun ω => cexp (I * ((s * obsX G h hz hc ω : ℝ) : ℂ))) =
      fun ω => G.indicator (fun ω => cexp (I * (h ω φ : ℂ))) ω +
        Gᶜ.indicator (fun _ => (1 : ℂ)) ω := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [obsX, indicator_of_mem hω, indicator_of_notMem (notMem_compl_iff.2 hω),
        add_zero, hφdef, map_smul, smul_eq_mul, ← hbdef, ← hmdef]
      congr 3; ring
    · simp only [obsX, indicator_of_notMem hω, indicator_of_mem (mem_compl hω),
        zero_add, mul_zero, Complex.ofReal_zero, Complex.exp_zero]
  have hsum : P[fun ω => G.indicator (fun ω => cexp (I * (h ω φ : ℂ))) ω +
      Gᶜ.indicator (fun _ => (1 : ℂ)) ω | hT.measurableSpace] =ᵐ[P]
      fun ω => (P[G.indicator (fun ω => cexp (I * (h ω φ : ℂ))) | hT.measurableSpace]) ω +
        (P[Gᶜ.indicator (fun _ => (1 : ℂ)) | hT.measurableSpace]) ω :=
    condExp_add (hI1.indicator hGm) ((integrable_const (1 : ℂ)).indicator hGm.compl) _
  have hind := condExp_indicator (m := hT.measurableSpace) hI1 hGT
  have hconst : P[Gᶜ.indicator (fun _ => (1 : ℂ)) | hT.measurableSpace] =
      Gᶜ.indicator (fun _ => (1 : ℂ)) :=
    condExp_of_stronglyMeasurable hT.measurableSpace_le
      (stronglyMeasurable_const.indicator hGT.compl) ((integrable_const (1 : ℂ)).indicator hGm.compl)
  rw [hdec]
  filter_upwards [hsum, hind, hlaw] with ω h1 h2 h3
  rw [h1, h2, hconst]
  by_cases hω : ω ∈ G
  · rw [indicator_of_mem hω, indicator_of_notMem (notMem_compl_iff.2 hω), add_zero,
      h3 (hsupp ω hω), indicator_of_mem hω]
    -- the mean and the variance
    have hmean : ∫ x, Hc (T ω) ω x * φ x = s * Hc (T ω) ω z := by
      simp_rw [hφcoe]
      have e : (fun x => Hc (T ω) ω x * (s * m⁻¹ * b x)) =
          fun x => (s * m⁻¹) * (Hc (T ω) ω x * GFF.bumpFun z (bumpRad z c) x) := by
        funext x; rw [hbcoe]; ring
      rw [e, integral_const_mul, GFF.integral_mul_bumpFun_of_harmonic (S.isOpen _ ω)
        (S.harmonic _ ω) hε (hball ω hω)]
      change s * m⁻¹ * (Hc (T ω) ω z * m) = _
      field_simp
    have hvar : zeroGFFTestCov (H \ Z (T ω) ω) φ φ = s ^ 2 * varV G r hz hc (T ω) ω := by
      rw [hφdef, LocalSets.zeroGFFTestCov_smul_self (S.isOpen _ ω) sdiff_subset,
        S.varV_eq hz hc hω (hcr ω hω)]
      ring
    rw [hmean, hvar, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  · rw [indicator_of_notMem hω, indicator_of_mem (mem_compl hω), zero_add, indicator_of_notMem hω]
    simp only [varV, indicator_of_notMem hω, mul_zero, Complex.ofReal_zero,
      Real.exp_zero, Complex.ofReal_one, Complex.exp_zero, mul_one]

theorem isGaussianExploration [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r) {G : Set Ω}
    (hG0 : MeasurableSet[𝓕 0] G) {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) {R : ℝ≥0} (hρR : ∀ ω, ρ ω ≤ R)
    (hcrρ : ∀ ω ∈ G, ∀ t ≤ ρ ω, c ≤ r t ω z) :
    IsGaussianExploration P 𝓕 (obsX G h hz hc) (varV G r hz hc) ρ (varK hz hc) :=
  ⟨hρ, S.continuous_varV hz hc, S.varV_anti hz hc hcrρ, S.measurable_varV hG0 hz hc,
    S.memLp_obsX hG0 hz hc, fun _T hT hTρ => (S.condGaussian_obsX hG0 hz hc hρR hcrρ hT hTρ).1⟩

/-- **Localized time continuity at a point**, general localization: on an `𝓕₀`-event `G`, up to a
bounded stopping time `ρ` before which `r_t(z) ≥ c`, there is a version `M` of `t ↦ 1_G H_{t∧ρ}(z)`
with continuous paths for every `ω`, stopped at `ρ`, equal to `1_G H_σ(z)` at every stopping time
`σ ≤ ρ`; `M` and `M² + v_{·∧ρ}` are martingales (`𝓕₀` containing the null sets). -/
theorem exists_local_versionG [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {G : Set Ω}
    (hG0 : MeasurableSet[𝓕 0] G) {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : 0 < c) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) {R : ℝ≥0} (hρR : ∀ ω, ρ ω ≤ R)
    (hcrρ : ∀ ω ∈ G, ∀ t ≤ ρ ω, c ≤ r t ω z) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => M t ω) ∧ (∀ t, Measurable (M t)) ∧
      (∀ ω t, ρ ω ≤ t → M t ω = M (ρ ω) ω) ∧
      (∀ (σ : Ω → ℝ≥0) (_hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)),
        (∀ ω, σ ω ≤ ρ ω) → (fun ω => M (σ ω) ω) =ᵐ[P] G.indicator (fun ω => Hc (σ ω) ω z)) ∧
      Martingale M 𝓕 P ∧
      Martingale (fun t ω => M t ω ^ 2 + varV G r hz hc (min t (ρ ω)) ω) 𝓕 P ∧
      (∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)),
        (∀ ω, σ ω ≤ ρ ω) → (fun ω => M (σ ω) ω) =ᵐ[P] P[obsX G h hz hc | hσ.measurableSpace]) := by
  have hE := S.isGaussianExploration hG0 hz hc hρ hρR hcrρ
  obtain ⟨M, hMc, hMm, hMstop, hMσ⟩ := hE.exists_continuous_version
  obtain ⟨h1, h2⟩ := hE.martingale_of_version hnull hMm hMstop hMσ
  refine ⟨M, hMc, hMm, hMstop, fun σ hσ hσρ => ?_, h1, h2, hMσ⟩
  exact (hMσ σ hσ hσρ).trans (S.condGaussian_obsX hG0 hz hc hρR hcrρ hσ hσρ).2

/-- **Localized time continuity at a point** (Proposition 6.5 on `{r₀(z) > c}` up to the first time
`r_t(z) ≤ c`, capped at `R`). -/
theorem exists_local_version [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {z : ℂ} (hz : 0 < z.im)
    {c : ℝ} (hc : 0 < c) (R : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => M t ω) ∧ (∀ t, Measurable (M t)) ∧
      (∀ ω t, locTime r z c R ω ≤ t → M t ω = M (locTime r z c R ω) ω) ∧
      (∀ (σ : Ω → ℝ≥0) (_hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)),
        (∀ ω, σ ω ≤ locTime r z c R ω) →
          (fun ω => M (σ ω) ω) =ᵐ[P] (startEv r z c).indicator (fun ω => Hc (σ ω) ω z)) ∧
      Martingale M 𝓕 P ∧
      Martingale (fun t ω => M t ω ^ 2 +
        varV (startEv r z c) r hz hc (min t (locTime r z c R ω)) ω) 𝓕 P :=
  let ⟨M, h1, h2, h3, h4, h5, h6, _⟩ := S.exists_local_versionG hnull (S.measurableSet_startEv hz c)
    hz hc (S.isStoppingTime_locTime hz c R) (fun ω => hitLe_le _ _ _ ω)
    fun _ hω _ ht => S.le_r_of_le_locTime hz hω ht
  ⟨M, h1, h2, h3, h4, h5, h6⟩

end Setting

end InteractingSLE.Sec6.Prop65
