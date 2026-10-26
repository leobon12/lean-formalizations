import HigherDimLQGMetric.Weak.DetLimit
import HigherDimLQGMetric.Weak.DetWeylLoc
import HigherDimLQGMetric.Weak.DetWeylCont

/-!
# Localized Weyl comparison
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The maximum of a locally uniformly vanishing sequence of continuous weights on a fixed
compact ball also vanishes. The chosen maximum is the supremum of the absolute weight on the
ball. -/
theorem exists_vanishing_weight_sup_on_ball
    (ξ R : ℝ) (hR : 0 < R) (u : ℕ → C(Rd d, ℝ))
    (hu : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(u n)) 0 atTop
      (closedBall (0 : Rd d) R)) :
    ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 0) ∧
      ∀ n, 0 ≤ s n ∧
        (∀ x ∈ closedBall (0 : Rd d) R, |ξ * u n x| ≤ s n) ∧
        ∃ x ∈ closedBall (0 : Rd d) R, |ξ * u n x| = s n := by
  classical
  let K : Set (Rd d) := closedBall (0 : Rd d) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨0, mem_closedBall_self hR.le⟩
  have hmax : ∀ n, ∃ z ∈ K, ∀ x ∈ K, |u n x| ≤ |u n z| := by
    intro n
    obtain ⟨z, hz, h⟩ := hK.exists_isMaxOn hKne ((u n).continuous.abs).continuousOn
    exact ⟨z, hz, h⟩
  choose z hz hmax using hmax
  let m : ℕ → ℝ := fun n => |u n (z n)|
  let s : ℕ → ℝ := fun n => |ξ| * m n
  have hm : Tendsto m atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hev := (Metric.tendstoUniformlyOn_iff).1 (hu R hR) ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    apply Filter.eventually_atTop.2
    refine ⟨N, ?_⟩
    intro n hn
    have hval := hN n hn (z n) (hz n)
    have hval' : |u n (z n)| < ε := by simpa [Real.dist_eq] using hval
    simpa [m, Real.dist_eq] using hval'
  have hs : Tendsto s atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => |ξ|) atTop (𝓝 |ξ|)).mul hm
    simpa [s, m] using h
  refine ⟨s, hs, ?_⟩
  intro n
  have hsn : 0 ≤ s n := mul_nonneg (abs_nonneg ξ) (abs_nonneg _)
  refine ⟨hsn, ?_, ?_⟩
  · intro x hx
    have hmax' := hmax n x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hmax' (abs_nonneg ξ)
  · refine ⟨z n, hz n, ?_⟩
    dsimp [s, m]
    rw [abs_mul]

/-- The deterministic Weyl observation from the first paragraph of the proof of Lemma 2.4.
The radius depends only on the compact endpoint set and the proper limit metric. -/
theorem eventually_weyl_metric_local_comparison
    (ξ : ℝ) (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength) (hD : D.IsLength) (hproper : IsProperFn D.1)
    (hconvD : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    (u : ℕ → C(Rd d, ℝ))
    (hconvU : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(u n)) 0 atTop
      (closedBall (0 : Rd d) R))
    {F : Set (Rd d)} (hF : IsCompact F) :
    ∃ R : ℝ, 0 < R ∧ ∃ s : ℕ → ℝ,
      Tendsto s atTop (𝓝 0) ∧
      (∀ n, 0 ≤ s n ∧ ∀ x ∈ closedBall (0 : Rd d) R, |ξ * u n x| ≤ s n) ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F,
        Real.exp (-s n) * (Dn n).1 (x,y) ≤
          (weylMetric ξ (u n) (Dn n) (hDn n)).1 (x,y) ∧
        (weylMetric ξ (u n) (Dn n) (hDn n)).1 (x,y) ≤
          Real.exp (s n) * (Dn n).1 (x,y) ∧
        TendstoUniformlyOn (fun n => ⇑(weylMetric ξ (u n) (Dn n) (hDn n)).1)
          ⇑D.1 atTop (F ×ˢ F) := by
  classical
  obtain ⟨B, hB⟩ := (hF.prod hF).exists_bound_of_continuousOn
    D.1.continuous.continuousOn
  let B' := max B 0
  have hDdiam : ∀ x ∈ F, ∀ y ∈ F, D.1 (x,y) ≤ B' := by
    intro x hx y hy
    exact (Real.le_norm_self _).trans (hB (x,y) ⟨hx,hy⟩ |>.trans (le_max_left _ _))
  let T := B' + 2
  have hT : 2 ≤ T := by dsimp [T]; linarith [le_max_right B 0]
  obtain ⟨r₀, hFball₀⟩ := hF.isBounded.subset_ball (0 : Rd d)
  let r := max r₀ 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hFball : F ⊆ closedBall (0 : Rd d) r := by
    intro x hx
    exact closedBall_subset_closedBall (le_max_left _ _) (ball_subset_closedBall (hFball₀ hx))
  obtain ⟨R, hrR, hbarD⟩ := hproper.exists_sphere_barrier D hr (20 * T + 1)
  have hR : 0 < R := lt_trans hr hrR
  have hFballR : F ⊆ closedBall (0 : Rd d) R := by
    intro x hx
    exact closedBall_subset_closedBall (le_of_lt hrR) (hFball hx)
  obtain ⟨Nclose, hclose⟩ := Filter.eventually_atTop.1
    (eventually_dist_lt_on_closedBall (fun n => (Dn n).1) D.1 hconvD R 1 hR (by norm_num))
  obtain ⟨s, hs, hsprops⟩ := exists_vanishing_weight_sup_on_ball ξ R hR u hconvU
  have hlog : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hsSmall : ∀ᶠ n : ℕ in atTop, s n < Real.log 10 / 2 :=
    hs.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨Ns, hNs⟩ := Filter.eventually_atTop.1 hsSmall
  have hDnCloseF : ∀ᶠ n : ℕ in atTop, ∀ x ∈ F, ∀ y ∈ F,
      |(Dn n).1 (x,y) - D.1 (x,y)| < 1 := by
    have hFballR : F ⊆ closedBall (0 : Rd d) R := by
      intro x hx
      exact closedBall_subset_closedBall (le_of_lt hrR) (hFball hx)
    filter_upwards [Filter.eventually_atTop.2 ⟨Nclose, fun n hn => hclose n hn⟩]
      with n hn x hx y hy
    exact hn x (hFballR hx) y (hFballR hy)
  obtain ⟨Nerr, hNerr⟩ := Filter.eventually_atTop.1 hDnCloseF
  let N := max (max Nclose Ns) Nerr
  obtain ⟨RF₀, hFballRF₀⟩ := hF.isBounded.subset_ball (0 : Rd d)
  let RF := max RF₀ 1
  have hRF : 0 < RF := by dsimp [RF]; positivity
  have hFsubRF : F ⊆ closedBall (0 : Rd d) RF := by
    intro x hx
    exact closedBall_subset_closedBall (le_max_left _ _) (ball_subset_closedBall (hFballRF₀ hx))
  have hWloc : TendstoUniformlyOn
      (fun n (p : Rd d × Rd d) =>
        (weylScale ξ (u n) (Dn n) p.1 p.2).toReal)
      (fun p => (weylScale ξ (0 : C(Rd d, ℝ)) D p.1 p.2).toReal)
      atTop (closedBall (0 : Rd d) RF ×ˢ closedBall (0 : Rd d) RF) :=
    l6d_weylCont d ξ Dn D u 0 hDn hD hproper hconvD hconvU ⟨0, by simp⟩ RF hRF
  have hzero : ∀ p : Rd d × Rd d,
      (weylScale ξ (0 : C(Rd d, ℝ)) D p.1 p.2).toReal = D.1 p := by
    intro p
    rw [weylScale_of_eq_const (a := 0) (fun _ => by simp),
      D.internal_univ_of_isLength hD]
    simp [D.nonneg p.1 p.2]
  have hWloc' : TendstoUniformlyOn
      (fun n => ⇑(weylMetric ξ (u n) (Dn n) (hDn n)).1) ⇑D.1
      atTop (closedBall (0 : Rd d) RF ×ˢ closedBall (0 : Rd d) RF) := by
    convert hWloc using 1
    · funext n p
      exact weylMetric_apply (hDn n) p
    · funext p
      exact (hzero p).symm
  have hWlocF : TendstoUniformlyOn
      (fun n => ⇑(weylMetric ξ (u n) (Dn n) (hDn n)).1) ⇑D.1 atTop (F ×ˢ F) :=
    hWloc'.mono (Set.prod_mono hFsubRF hFsubRF)
  refine ⟨R, hR, s, hs, ?_, ?_⟩
  · intro n
    exact ⟨(hsprops n).1, fun x hx => (hsprops n).2.1 x hx⟩
  refine ⟨N, ?_⟩
  intro n hn x hx y hy
  have hnclose : Nclose ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hns : Ns ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnerr : Nerr ≤ n := le_trans (le_max_right _ _) hn
  have hsbound := hNs n hns
  have hsnonneg := (hsprops n).1
  have hsR : ∀ z ∈ ball (0 : Rd d) R, |ξ * u n z| ≤ s n :=
    fun z hz => (hsprops n).2.1 z (ball_subset_closedBall hz)
  have hxball : x ∈ ball (0 : Rd d) R := by
    exact (closedBall_subset_ball hrR) (hFball hx)
  have hyball : y ∈ ball (0 : Rd d) R := by
    exact (closedBall_subset_ball hrR) (hFball hy)
  have hDnSphere : ∀ z ∈ sphere (0 : Rd d) R, 20 * T ≤ (Dn n).1 (x,z) := by
    intro z hz
    have hDbar := hbarD x (hFball hx) z hz
    have hzR : z ∈ closedBall (0 : Rd d) R := sphere_subset_closedBall hz
    have herr := hclose n hnclose x (hFballR hx) z hzR
    have hstrict := (abs_lt.mp herr).1
    linarith
  have hcompbar := dfl71_le_infEDist_compl_ball (hDn n) hxball hDnSphere
  have hdnerr := hNerr n hnerr x hx y hy
  have hDnBound : (Dn n).1 (x,y) ≤ T := by
    have hupper := (abs_lt.mp hdnerr).2
    have hmetric := hDdiam x hx y hy
    dsimp [T, B']
    linarith [hmetric, le_max_left B 0]
  have hDnNonneg := (Dn n).nonneg x y
  have hball : ∀ z, (Dn n).1 (x,z) < 20 * T → z ∈ ball (0 : Rd d) R := by
    intro z hdist
    by_contra hz
    have hle : Metric.infEDist ((Dn n).pt x)
        ((Dn n).pt '' (ball (0 : Rd d) R)ᶜ) ≤ edist ((Dn n).pt x) ((Dn n).pt z) :=
      Metric.infEDist_le_edist_of_mem
        (s := (Dn n).pt '' (ball (0 : Rd d) R)ᶜ) ⟨z, hz, rfl⟩
    have hcontra : ENNReal.ofReal (20 * T) ≤ ENNReal.ofReal ((Dn n).1 (x,z)) := by
      rw [← (Dn n).edist_pt]
      exact hcompbar.trans hle
    have hreal := (ENNReal.ofReal_le_ofReal_iff ((Dn n).nonneg x z)).mp hcontra
    exact (not_lt_of_ge hreal) hdist
  have hSourceLocal : (Dn n).internal (ball (0 : Rd d) R) x y =
      ENNReal.ofReal ((Dn n).1 (x,y)) := by
    apply (Dn n).internal_eq_of_ball_subset (hDn n) hball
    exact hDnBound.trans_lt (by dsimp [T]; linarith [hT])
  have hweights : ∀ z ∈ ball (0 : Rd d) R,
      -s n ≤ ξ * u n z ∧ ξ * u n z ≤ s n := by
    intro z hz
    have habs := hsR z hz
    exact abs_le.mp habs
  let Dtilde := weylMetric ξ (u n) (Dn n) (hDn n)
  have hIcc := internal_mem_Icc_of_le Dtilde
    (fun z w => weylMetric_spec (hDn n) z w) (isOpen_ball)
    (fun z hz => (hweights z hz).1) (fun z hz => (hweights z hz).2) x y
  rw [weylMetric_internal (hDn n) isOpen_ball] at hIcc
  have hWupper : weylScale ξ (u n) (Dn n) x y ≤ ENNReal.ofReal (Real.exp (s n) * T) := by
    calc weylScale ξ (u n) (Dn n) x y
        ≤ weylScaleOn ξ (u n) (Dn n) (ball (0 : Rd d) R) x y := weylScale_le_weylScaleOn
      _ ≤ ENNReal.ofReal (Real.exp (s n)) * (Dn n).internal (ball (0 : Rd d) R) x y := hIcc.2
      _ = ENNReal.ofReal (Real.exp (s n) * (Dn n).1 (x,y)) := by
        rw [hSourceLocal, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (s n) * T) := by
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hDnBound (Real.exp_pos _).le)
  have hExp : Real.exp (2 * s n) < 10 := by
    calc
      Real.exp (2 * s n) < Real.exp (Real.log 10) := Real.exp_lt_exp.mpr (by
        calc
          2 * s n < 2 * (Real.log 10 / 2) := mul_lt_mul_of_pos_left hsbound (by norm_num)
          _ = Real.log 10 := by ring)
      _ = 10 := Real.exp_log (by norm_num)
  have hratio : Real.exp (s n) * T < Real.exp (-s n) * (20 * T) := by
    have hexp : Real.exp (s n) * Real.exp (s n) = Real.exp (2 * s n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcore : Real.exp (s n) * Real.exp (s n) * T < 20 * T := by
      rw [hexp]
      nlinarith [hExp, hT]
    have hinv : Real.exp (-s n) * Real.exp (s n) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (s n) * T =
          (Real.exp (-s n) * Real.exp (s n)) * (Real.exp (s n) * T) := by
            rw [hinv]
            ring
      _ = Real.exp (-s n) * (Real.exp (s n) * Real.exp (s n) * T) := by ring
      _ < Real.exp (-s n) * (20 * T) :=
        mul_lt_mul_of_pos_left hcore (Real.exp_pos _)
  have hweightedBarrier : ENNReal.ofReal (Real.exp (-s n) * (20 * T)) ≤
      ENNReal.ofReal (Real.exp (-s n)) *
        Metric.infEDist ((Dn n).pt x) ((Dn n).pt '' (ball (0 : Rd d) R)ᶜ) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left hcompbar (by positivity)
  have hlt : weylScale ξ (u n) (Dn n) x y <
      ENNReal.ofReal (Real.exp (-s n)) *
        Metric.infEDist ((Dn n).pt x) ((Dn n).pt '' (ball (0 : Rd d) R)ᶜ) := by
    calc weylScale ξ (u n) (Dn n) x y
        ≤ ENNReal.ofReal (Real.exp (s n) * T) := hWupper
      _ < ENNReal.ofReal (Real.exp (-s n) * (20 * T)) :=
        ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2 hratio
      _ ≤ _ := hweightedBarrier
  have hlocle : weylScaleOn ξ (u n) (Dn n) (ball (0 : Rd d) R) x y ≤
      weylScale ξ (u n) (Dn n) x y :=
    weylScaleOn_le_weylScale_of_lt isOpen_ball (Set.Subset.refl _)
      (fun z hz => (hweights z hz).1) hlt
  have hlocge : weylScale ξ (u n) (Dn n) x y ≤
      weylScaleOn ξ (u n) (Dn n) (ball (0 : Rd d) R) x y := weylScale_le_weylScaleOn
  have hWeq : weylScaleOn ξ (u n) (Dn n) (ball (0 : Rd d) R) x y =
      weylScale ξ (u n) (Dn n) x y := le_antisymm hlocle hlocge
  have hIccLower := hIcc.1
  rw [hSourceLocal] at hIccLower
  have hscaleLower : ENNReal.ofReal (Real.exp (-s n)) *
      ENNReal.ofReal ((Dn n).1 (x,y)) ≤ weylScale ξ (u n) (Dn n) x y :=
    hIccLower.trans_eq hWeq
  have hIccUpper := hIcc.2
  rw [hSourceLocal, hWeq] at hIccUpper
  have hscaleUpper : weylScale ξ (u n) (Dn n) x y ≤ ENNReal.ofReal (Real.exp (s n)) *
      ENNReal.ofReal ((Dn n).1 (x,y)) := hIccUpper
  have hrealLower : Real.exp (-s n) * (Dn n).1 (x,y) ≤ Dtilde.1 (x,y) := by
    have hh : ENNReal.ofReal (Real.exp (-s n) * (Dn n).1 (x,y)) ≤
        ENNReal.ofReal (Dtilde.1 (x,y)) := by
      calc
        ENNReal.ofReal (Real.exp (-s n) * (Dn n).1 (x,y)) =
            ENNReal.ofReal (Real.exp (-s n)) * ENNReal.ofReal ((Dn n).1 (x,y)) :=
          ENNReal.ofReal_mul (Real.exp_pos _).le
        _ ≤ weylScale ξ (u n) (Dn n) x y := hscaleLower
        _ = ENNReal.ofReal (Dtilde.1 (x,y)) :=
          (weylMetric_spec (ξ := ξ) (f := u n) (D := Dn n) (hDn n) x y).symm
    exact (ENNReal.ofReal_le_ofReal_iff (Dtilde.nonneg x y)).mp hh
  have hrealUpper : Dtilde.1 (x,y) ≤ Real.exp (s n) * (Dn n).1 (x,y) := by
    have hh : ENNReal.ofReal (Dtilde.1 (x,y)) ≤
        ENNReal.ofReal (Real.exp (s n) * (Dn n).1 (x,y)) := by
      calc
        ENNReal.ofReal (Dtilde.1 (x,y)) = weylScale ξ (u n) (Dn n) x y :=
          weylMetric_spec (ξ := ξ) (f := u n) (D := Dn n) (hDn n) x y
        _ ≤ ENNReal.ofReal (Real.exp (s n)) * ENNReal.ofReal ((Dn n).1 (x,y)) := hscaleUpper
        _ = ENNReal.ofReal (Real.exp (s n) * (Dn n).1 (x,y)) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.exp_pos _).le ((Dn n).nonneg x y))).mp hh
  exact ⟨hrealLower, hrealUpper, hWlocF⟩

end HigherDimLFPPAS.Det
