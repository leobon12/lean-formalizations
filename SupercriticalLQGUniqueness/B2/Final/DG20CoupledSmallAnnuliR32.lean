import SupercriticalLQGUniqueness.B2.Final.DG20CoupledGoodCirclesR32
import SupercriticalLQGUniqueness.B2.Final.DG20CoupledSmallAnnuli

 


















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open LQGMetric (DistC normGFFLaw ContMetric)
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.DG20Lim (RatCoords RData RatAnnulus RatCircle finiteRatCoords
  finiteAroundCoords normalizedContLFPP centeredRatAnnulusR32 centeredInnerCircleR32
  centeredOuterCircleR32)

namespace SupercriticalLQGUniqueness.B2.Final

 

theorem smallAnnulusCosts_of_goodR32 (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ))
    (D : LSCMetric) (Zn : ℕ → RatCoords) (Zl : RatCoords) (R : RData) (C : ℝ≥0∞)
    (hZid : ∀ n, Zn n = finiteRatCoords (normalizedContLFPP ξ (a n) (φ n)))
    (hZconv : Tendsto Zn atTop (𝓝 Zl)) (hRa : R.around = Zl.2)
    (hgood : ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
        (∀ n, ∃ (x y r : ℚ) (hr : 0 < r), B n = centeredRatAnnulusR32 x y r hr) ∧
        (∀ n, (B n).inner.Surrounds z ∧
          R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
        (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
        Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) ∧
        ∀ w : ℂ, w ≠ z → D (z, w) < ⊤ →
          Tendsto (fun n => R.across (B n).inner (B n).outer) atTop (𝓝 0) ∧
          Tendsto (fun n => R.around (B n)) atTop (𝓝 0))
    (k : ℕ) :
    PfeWeyl.SmallAnnulusCosts (fun n => PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n)) D
      (closedBall 0 k) (ball 0 ((k : ℝ) + 1)) := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨w, hwz, hw⟩ := hns
  obtain ⟨B, hBshape, hBgood, -, hBrad, hconv⟩ := hgood z
  have hround := (hconv w hwz hw).2
  have hev1 : ∀ᶠ j in atTop, R.around (B j) < ENNReal.ofReal δ :=
    hround.eventually_lt_const (ENNReal.ofReal_pos.2 hδ)
  have hmin : (0 : ℝ) < min (1 / 2) (3 * ρ / 4) := lt_min (by norm_num) (by linarith)
  have hev2 : ∀ᶠ j in atTop, (((B j).outer.radius : ℝ)) < min (1 / 2) (3 * ρ / 4) :=
    hBrad.eventually_lt_const hmin
  obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
  obtain ⟨x, y, r₁, hr₁, hBj⟩ := hBshape j
  set Bj := centeredRatAnnulusR32 x y r₁ hr₁ with hBjdef
  have hsur : Bj.inner.Surrounds z := hBj ▸ (hBgood j).1
  rw [hBj] at hj1 hj2
  set c : ℂ := Complex.mk (x : ℝ) (y : ℝ) with hc
  have hr₁R : (0 : ℝ) < (r₁ : ℝ) := by exact_mod_cast hr₁
  have hcin : Bj.inner.center = c := rfl
  have hrin : ((Bj.inner.radius : ℚ) : ℝ) = (r₁ : ℝ) := rfl
  have hrout : ((Bj.outer.radius : ℚ) : ℝ) = 3 / 2 * (r₁ : ℝ) := by
    change (((3 / 2 * r₁ : ℚ)) : ℝ) = _
    push_cast; ring
  have hzc : dist z c < (r₁ : ℝ) := by
    have := hsur.2
    rw [RatCircle.openDisk, hcin, hrin] at this
    exact this
  have hmax : max (dist z c) (3 / 4 * (r₁ : ℝ)) < (r₁ : ℝ) :=
    max_lt hzc (by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hmax
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hr1
    linarith
  have h34 : 3 / 4 * (r₁ : ℝ) < (r : ℝ) := lt_of_le_of_lt (le_max_right _ _) hr1
  have hzr : dist z c < (r : ℝ) := lt_of_le_of_lt (le_max_left _ _) hr1
  let A : EuclideanAnnulus := ⟨(c, ((r : ℝ), 2 * (r : ℝ))), hrpos, by linarith⟩
  have hAc : A.center = c := rfl
  have hAi : A.innerRadius = (r : ℝ) := rfl
  have hAo : A.outerRadius = 2 * (r : ℝ) := rfl
  have hj2' : 3 / 2 * (r₁ : ℝ) < min (1 / 2) (3 * ρ / 4) := by rw [← hrout]; exact hj2
  have hsmall1 : (r₁ : ℝ) < 1 / 3 := by
    have := lt_of_lt_of_le hj2' (min_le_left _ _); linarith
  have hsmall2 : (r₁ : ℝ) < ρ / 2 := by
    have := lt_of_lt_of_le hj2' (min_le_right _ _); linarith
  have hout : Bj.outer.closedDisk ⊆ ball A.center A.outerRadius := by
    intro u hu
    have hu' : dist u Bj.outer.center ≤ ((Bj.outer.radius : ℚ) : ℝ) := hu
    have hco : Bj.outer.center = c := rfl
    rw [hco, hrout] at hu'
    rw [mem_ball, hAc, hAo]
    linarith
  refine ⟨A, ⟨x, y, r, by exact_mod_cast hrpos, rfl, rfl, rfl⟩, by rw [hAc, hAi]; exact hzr,
    by rw [hAo]; linarith, ?_, ?_⟩
  · intro u hu
    have hu1 : dist u c < 2 * (r : ℝ) := by
      have := hu.1
      rwa [mem_ball, hAc, hAo] at this
    have hz0 : dist z 0 ≤ k := mem_closedBall.1 hz
    have h4 := dist_triangle4 u c z 0
    rw [dist_comm c z] at h4
    rw [mem_ball]
    linarith
  · have hcoord : Tendsto (fun n => (Zn n).2 Bj) atTop (𝓝 (Zl.2 Bj)) :=
      ((continuous_apply Bj).comp continuous_snd).continuousAt.tendsto.comp hZconv
    have hlt : Zl.2 Bj < ENNReal.ofReal δ := by rw [← hRa]; exact hj1
    filter_upwards [hcoord.eventually_lt_const hlt] with n hn
    refine lt_of_le_of_lt ?_ hn
    have hcmp := aroundDist_normalizedLFPP_le_finiteAround ξ (a n) (φ n) Bj A
      (by rw [hAc, hcin]) (by rw [hAi, hrin]; exact hr2) hout
    rw [hZid n]
    exact hcmp

 
theorem coupledSmallAnnuli_of_coords {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate')
    (hB : DG20CouplingData ξ Q m e c V P' h' hN L)
    (hR : CoupledRatCoords ξ m e V P' hN L) : CoupledSmallAnnuli ξ m e V P' hN L := by
  obtain ⟨Z, Zlim, hZm, -, hZid, hZconv, hLink⟩ := hR
  obtain ⟨C, -, hGood⟩ := coupled_good_circlesR32 hS4 hPerc hB Z Zlim hZm hZid hZconv hLink
  intro k
  filter_upwards [hGood, hZid] with ω hG hid
  obtain ⟨R, -, hRa, -, hgood⟩ := hG
  exact smallAnnulusCosts_of_goodR32 (ξ : ℝ) (fun n => m (e n)) (fun n => V (e n) (hN n ω))
    (L ω) (fun n => Z n ω) (Zlim ω) R C hid (hZconv ω) hRa hgood k

 

theorem exists_dg20CouplingData_coords_smallAnnuli (hI : DG20Interfaces)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧ ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      ∃ V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ),
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P') (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC)
        (L : Ω' → LSCMetric),
        DG20CouplingData ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L ∧
        CoupledSmallAnnuli ξ m (fun n => ε (φ₁ n)) V P' hN L ∧
        CoupledRatCoords ξ m (fun n => ε (φ₁ n)) V P' hN L := by
  obtain ⟨hS4, hPerc, hRatio, hRelation, hPositive, hTop⟩ := hI
  obtain ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hR⟩ :=
    exists_dg20CouplingData_coords
      (DG20Lim.dg20LimitSkSBR_of_inputs hS4 hPerc hRatio hRelation hPositive hTop)
      hS4 ξ Q hQ m hm ε hε
  let _ : MeasurableSpace Ω' := M'
  have : IsProbabilityMeasure P' := hP'
  exact ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB,
    coupledSmallAnnuli_of_coords hS4 hPerc hB hR, hR⟩

end SupercriticalLQGUniqueness.B2.Final
