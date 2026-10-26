import HigherDimLFPPAS.Shell.Lemma26
import HigherDimLFPPAS.Windows.Scales
import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.Sharp.GridNear

/-!
# Abstract good-radius covering estimate

This module formalizes the finite-scale probability estimate in Lemma 3.3. It
uses only the shell tail bound, the deterministic scale window, and a finite
count of lattice points in a bounded ball.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLFPPAS

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

def d7ScaleRadius (k : ℤ) : ℝ := (256 : ℝ) ^ (-k)

private def d7IndexAt (S : Finset ℤ) (hS : 0 < S.card) (i : ℕ) : ℤ :=
  if hi : i < S.card then
    S.orderEmbOfFin rfl ⟨i, hi⟩
  else
    S.orderEmbOfFin rfl ⟨S.card - 1, by omega⟩ + (i - S.card + 1 : ℕ)

private theorem d7IndexAt_mem (S : Finset ℤ) (hS : 0 < S.card) {i : ℕ}
    (hi : i < S.card) : d7IndexAt S hS i ∈ S := by
  simp [d7IndexAt, hi, Finset.orderEmbOfFin_mem]

private theorem d7IndexAt_strict (S : Finset ℤ) (hS : 0 < S.card) (i : ℕ) :
    d7IndexAt S hS i < d7IndexAt S hS (i + 1) := by
  by_cases hi : i + 1 < S.card
  · have hi' : i < S.card := by omega
    simp only [d7IndexAt, hi', hi, dite_true]
    exact (S.orderEmbOfFin (rfl : S.card = S.card)).strictMono
      (Fin.mk_lt_mk.mpr (by omega))
  · by_cases hlt : i < S.card
    · have heq : i + 1 = S.card := by omega
      have hiVal : i = S.card - 1 := by omega
      have hfi : (⟨i, hlt⟩ : Fin S.card) = ⟨S.card - 1, by omega⟩ := by
        apply Fin.ext
        exact hiVal
      have hlast :
          S.orderEmbOfFin (rfl : S.card = S.card) ⟨i, hlt⟩ =
            S.orderEmbOfFin (rfl : S.card = S.card) ⟨S.card - 1, by omega⟩ := by
        rw [hfi]
      simp only [d7IndexAt, hlt, hi, dite_true, dite_false]
      rw [hlast]
      have htail : i + 1 - S.card + 1 = 1 := by omega
      rw [htail]
      omega
    · have hi' : S.card ≤ i := by omega
      have hnat : i + 1 - S.card + 1 = i - S.card + 1 + 1 := by omega
      simp only [d7IndexAt, hlt, hi, dite_false]
      rw [hnat]
      omega

private def d7RadiusAt (S : Finset ℤ) (hS : 0 < S.card) (i : ℕ) : ℝ :=
  d7ScaleRadius (d7IndexAt S hS i)

private theorem d7RadiusAt_pos (S : Finset ℤ) (hS : 0 < S.card) (i : ℕ) :
    0 < d7RadiusAt S hS i := by
  exact zpow_pos (by norm_num : (0 : ℝ) < 256) _

private theorem d7RadiusAt_ratio (S : Finset ℤ) (hS : 0 < S.card) (i : ℕ) :
    d7RadiusAt S hS (i + 1) ≤ (1 / 256 : ℝ) * d7RadiusAt S hS i := by
  have hk := d7IndexAt_strict S hS i
  have hpow : -d7IndexAt S hS (i + 1) ≤ -d7IndexAt S hS i - 1 := by omega
  have hmono := zpow_le_zpow_right₀ (a := (256 : ℝ))
    (by norm_num : (1 : ℝ) ≤ 256) hpow
  have he : -d7IndexAt S hS i - 1 = -d7IndexAt S hS i + (-1 : ℤ) := by omega
  calc
    d7RadiusAt S hS (i + 1) ≤ (256 : ℝ) ^ (-d7IndexAt S hS i - 1) := by
      exact hmono
    _ = (256 : ℝ) ^ (-d7IndexAt S hS i) * (256 : ℝ) ^ (-1 : ℤ) := by
      rw [he, zpow_add₀ (by norm_num : (256 : ℝ) ≠ 0)]
    _ = (1 / 256 : ℝ) * d7RadiusAt S hS i := by
      simp [d7RadiusAt, d7ScaleRadius, zpow_neg]
      ring

private theorem d7_window_count_strong {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hu : 0 < u) (hlarge : 4 ≤ Windows.winIndexLower ε u) :
    (Windows.winRadiusWindow ε u).ncard ≥ Windows.winIndexLower ε u / 2 := by
  have hlog256 : 0 < Real.log (256 : ℝ) := Real.log_pos (by norm_num)
  have hinj : Function.Injective (fun k : ℤ => (256 : ℝ) ^ (-k)) := by
    intro k l hkl
    have hlogs := congrArg Real.log hkl
    rw [Real.log_zpow, Real.log_zpow] at hlogs
    have hcast : (k : ℝ) = l := by
      apply (mul_right_cancel₀ hlog256.ne')
      simpa using hlogs
    exact Int.cast_injective hcast
  have hceil : (Windows.winIndexLower ε u : ℝ) ≤
      (⌈Windows.winIndexLower ε u⌉ : ℤ) := by
    exact_mod_cast Int.le_ceil _
  have hceil_lt : (⌈Windows.winIndexLower ε u⌉ : ℝ) <
      Windows.winIndexLower ε u + 1 := Int.ceil_lt_add_one _
  have hfloor : 2 * Windows.winIndexLower ε u - 1 <
      (⌊2 * Windows.winIndexLower ε u⌋ : ℤ) := Int.sub_one_lt_floor _
  have hfloor_le : (⌈Windows.winIndexLower ε u⌉ : ℤ) ≤
      (⌊2 * Windows.winIndexLower ε u⌋ : ℤ) + 1 := by
    calc
      (⌈Windows.winIndexLower ε u⌉ : ℤ) ≤
          (⌊Windows.winIndexLower ε u⌋ : ℤ) + 1 := Int.ceil_le_floor_add_one _
      _ ≤ (⌊2 * Windows.winIndexLower ε u⌋ : ℤ) + 1 := by
        exact Int.add_le_add_right
          (Int.floor_mono (by linarith [hlarge])) 1
  have hcardInt :
      ((Finset.Icc (⌈Windows.winIndexLower ε u⌉)
        (⌊2 * Windows.winIndexLower ε u⌋)).card : ℤ) =
        (⌊2 * Windows.winIndexLower ε u⌋ : ℤ) + 1 -
          (⌈Windows.winIndexLower ε u⌉ : ℤ) := Int.card_Icc_of_le _ _ hfloor_le
  have hcardReal : ((Windows.winRadiusWindow ε u).ncard : ℝ) =
      (⌊2 * Windows.winIndexLower ε u⌋ : ℝ) + 1 -
        (⌈Windows.winIndexLower ε u⌉ : ℝ) := by
    rw [Windows.winRadiusWindow, Windows.winRadiusIndices_eq_Icc hε0 hε1 hu,
      Set.ncard_image_of_injective _ hinj, Set.ncard_Icc]
    exact_mod_cast hcardInt
  have hfloor' : 2 * Windows.winIndexLower ε u - 1 <
      (⌊2 * Windows.winIndexLower ε u⌋ : ℝ) := by
    exact_mod_cast hfloor
  have hceil' : (⌈Windows.winIndexLower ε u⌉ : ℝ) <
      Windows.winIndexLower ε u + 1 := hceil_lt
  rw [hcardReal]
  linarith

private theorem d7_grid_box_count {d : ℕ} (hd : 2 ≤ d) {ε u B : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hu : 0 < u) (hB : 0 ≤ B) :
    ((HigherDimLQGMetric.shellGridBox d
      (⌈B / (ε ^ u / (100 * (d : ℝ)))⌉₊ + 1)
      (ε ^ u / (100 * (d : ℝ)))).card : ℝ) * ε ^ (u * (d : ℝ)) ≤
        (200 * d * B + 5) ^ d := by
  let x : ℝ := ε ^ u
  let s : ℝ := x / (100 * (d : ℝ))
  let N : ℕ := ⌈B / s⌉₊ + 1
  let F : Finset (Rd d) := HigherDimLQGMetric.shellGridBox d N s
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx0 : 0 < x := by dsimp [x]; exact Real.rpow_pos_of_pos hε0 _
  have hx1 : x ≤ 1 := by
    dsimp [x]
    calc
      ε ^ u ≤ ε ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
      _ = 1 := by simp
  have hs : 0 < s := by dsimp [s]; positivity
  have hN : (N : ℝ) < B / s + 2 := by
    dsimp [N]
    push_cast
    have hceil : (⌈B / s⌉₊ : ℝ) < B / s + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hB hs.le)
    linarith
  have hNx : (N : ℝ) * x < 100 * d * B + 2 * x := by
    have hmul := mul_lt_mul_of_pos_right hN hx0
    have hquot : (B / s + 2) * x = 100 * d * B + 2 * x := by
      dsimp [s]
      field_simp
    rw [hquot] at hmul
    exact hmul
  have hgridBase : (2 * (N : ℝ) + 1) * x ≤ 200 * d * B + 5 := by
    have hmul := mul_lt_mul_of_pos_left hNx (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hcard := HigherDimLQGMetric.card_shellGridBox_le d N s
  have hcardR :
      (F.card : ℝ) ≤
        (2 * (N : ℝ) + 1) ^ d := by exact_mod_cast hcard
  have hxpow : ε ^ (u * (d : ℝ)) = x ^ d := by
    dsimp [x]
    exact Real.rpow_mul_natCast (le_of_lt hε0) u d
  have hpow : ((2 * (N : ℝ) + 1) * x) ^ d ≤ (200 * d * B + 5) ^ d :=
    pow_le_pow_left₀ (by positivity) hgridBase d
  change (F.card : ℝ) * ε ^ (u * (d : ℝ)) ≤
    (200 * d * B + 5) ^ d
  calc
    (F.card : ℝ) * ε ^ (u * (d : ℝ))
        ≤ (2 * (N : ℝ) + 1) ^ d * x ^ d := by
          rw [← hxpow]
          exact mul_le_mul_of_nonneg_right hcardR (Real.rpow_nonneg (le_of_lt hε0) _)
    _ = ((2 * (N : ℝ) + 1) * x) ^ d := by rw [mul_pow]
    _ ≤ (200 * d * B + 5) ^ d := hpow

/-- The audited mesh spacing puts a grid point within `ε^u / 100` of every
point of `B_R`, and keeps that grid point inside `B_{R+1}` for small `ε`. -/
theorem d7_mesh_point_near {d : ℕ} (hd : 2 ≤ d) {ε u R : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hu : 0 < u)
    {x : Rd d} (hx : x ∈ Metric.ball (0 : Rd d) R) :
    ∃ z ∈ HigherDimLQGMetric.gridPts (ε ^ u / (100 * (d : ℝ))) ∩
        Metric.ball (0 : Rd d) (R + 1), dist x z ≤ ε ^ u / 100 := by
  let s : ℝ := ε ^ u / (100 * (d : ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have hxpow1 : ε ^ u ≤ 1 := by
    calc
      ε ^ u ≤ ε ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
      _ = 1 := by simp
  obtain ⟨z, hzgrid, hnear⟩ :=
    HigherDimLQGMetric.exists_gridPt_near hs x
  have hdist : dist x z ≤ ε ^ u / 100 := by
    rw [dist_eq_norm]
    calc
      ‖x - z‖ ≤ (d : ℝ) * s := hnear
      _ = ε ^ u / 100 := by
        dsimp [s]
        field_simp
  have hxnorm : ‖x‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hztri : ‖z‖ ≤ ‖x‖ + dist x z := by
    have hrepr : z = x + (z - x) := by abel
    calc
      ‖z‖ = ‖x + (z - x)‖ := by rw [← hrepr]
      _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
      _ = ‖x‖ + dist x z := by rw [dist_eq_norm]; simp [norm_sub_rev]
  have hzball : z ∈ Metric.ball (0 : Rd d) (R + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    have hsmall : ε ^ u / 100 < 1 := by nlinarith [hxpow1]
    linarith
  refine ⟨z, ⟨?_, hzball⟩, hdist⟩
  simpa [s] using hzgrid

/-- Abstract Lemma 3.3. The selected deterministic radii are represented by
their integer lattice indices. The threshold `p` is the one supplied by
`lemma26_shell_independence` at the paper's fixed parameters. -/
theorem lemma33_good_radius_cover {d : ℕ} (hd : 2 ≤ d) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → HigherDimLQGMetric.DistRd d),
        HigherDimLQGMetric.IsNormalizedLGF h P →
        ∀ u q₀ R : ℝ, 0 < u → u < q₀ → q₀ < 1 →
        ∀ E : ℝ → Rd d → ℝ → Set Ω,
          (∀ ε, 0 < ε → ∀ z k, k ∈ Windows.winRadiusIndices ε u →
            MeasurableSet[
              HigherDimLQGMetric.fieldSigmaRd
                (fun ω => HigherDimLQGMetric.addConst (h ω)
                  (-HigherDimLQGMetric.sphereAvg (h ω) (d7ScaleRadius k) z))
                (HigherDimLQGMetric.shellOpen z
                  ((8 : ℝ)⁻¹ * d7ScaleRadius k) (8 * d7ScaleRadius k))]
              (E ε z (d7ScaleRadius k))) →
          (∀ ε, 0 < ε → ∀ z k, k ∈ Windows.winRadiusIndices ε u →
            ENNReal.ofReal p ≤ P (E ε z (d7ScaleRadius k))) →
          ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
            ∀ ε, 0 < ε → ε < ε₀ →
              ∀ S : Finset ℤ,
                (∀ k ∈ S, k ∈ Windows.winRadiusIndices ε u) →
                (Windows.winRadiusWindow ε u).ncard ≤ 4 * S.card →
                P {ω | ∃ z ∈ HigherDimLQGMetric.gridPts
                    (ε ^ u / (100 * (d : ℝ))) ∩
                      Metric.ball (0 : Rd d) (R + 1),
                    ∀ k ∈ S, ω ∉ E ε z (d7ScaleRadius k)} ≤
                  ENNReal.ofReal (C * ε ^ u) := by
  classical
  let A₀ : ℝ := 32 * ((d : ℝ) + 2) * Real.log 256
  have hA₀ : 0 < A₀ := by
    dsimp [A₀]
    positivity
  obtain ⟨p, hp0, hp1, h26⟩ :=
    lemma26_shell_independence hd (1 / 256 : ℝ) 8 (by norm_num) (by norm_num)
      (by norm_num) A₀ (1 / 2 : ℝ) hA₀ (by norm_num) (by norm_num)
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω _ P _ h hh u q₀ R hu huq hq₀ E hE hprob
  let B : ℝ := max (R + 1) 0
  let C : ℝ := (200 * (d : ℝ) * B + 5) ^ d
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let ε₀ : ℝ := Real.exp (-(8 * Real.log 256 / u))
  have hε₀pos : 0 < ε₀ := Real.exp_pos _
  have hε₀lt : ε₀ < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hquot : 0 < 8 * Real.log 256 / u := div_pos (by positivity) hu
    linarith
  refine ⟨C, hC, ε₀, hε₀pos, hε₀lt, ?_⟩
  intro ε hε0 hεsmall S hS hsize
  have hε1 : ε < 1 := lt_trans hεsmall hε₀lt
  have hlog256 : 0 < Real.log (256 : ℝ) := Real.log_pos (by norm_num)
  have hlogε : Real.log ε < -(8 * Real.log 256 / u) := by
    calc
      Real.log ε < Real.log ε₀ := Real.log_lt_log hε0 hεsmall
      _ = -(8 * Real.log 256 / u) := by simp [ε₀]
  have hlarge : 4 < Windows.winIndexLower ε u := by
    have hmul : 8 * Real.log 256 < u * (-Real.log ε) := by
      have h := mul_lt_mul_of_pos_left hlogε hu
      have hcancel : u * (8 * Real.log 256 / u) = 8 * Real.log 256 := by
        field_simp
      nlinarith [h, hcancel]
    unfold Windows.winIndexLower
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log 256)).2
    nlinarith
  have hwindow := d7_window_count_strong hε0 hε1 hu (le_of_lt hlarge)
  have hsizeR : ((Windows.winRadiusWindow ε u).ncard : ℝ) ≤
      4 * (S.card : ℝ) := by exact_mod_cast hsize
  have hncount : u * Real.log (ε⁻¹) / (16 * Real.log 256) ≤ (S.card : ℝ) := by
    have htarget : Windows.winIndexLower ε u / 8 =
        u * Real.log (ε⁻¹) / (16 * Real.log 256) := by
      unfold Windows.winIndexLower
      rw [Real.log_inv]
      ring
    rw [← htarget]
    have hwindow' : Windows.winIndexLower ε u / 2 ≤
        (Windows.winRadiusWindow ε u).ncard := hwindow
    linarith
  have hnpos : 0 < S.card := by
    have hlogInv : 0 < Real.log (ε⁻¹) := by
      apply Real.log_pos
      exact (one_lt_inv₀ hε0).2 hε1
    have hden : 0 < 16 * Real.log 256 := by positivity
    have hpositive : 0 < u * Real.log (ε⁻¹) / (16 * Real.log 256) :=
      div_pos (mul_pos hu hlogInv) hden
    have hnReal : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hpositive hncount
    exact_mod_cast hnReal
  let r : ℕ → ℝ := d7RadiusAt S hnpos
  have hr : ∀ i, 0 < r i := d7RadiusAt_pos S hnpos
  have hratio : ∀ i, r (i + 1) ≤ (1 / 256 : ℝ) * r i :=
    d7RadiusAt_ratio S hnpos
  let F : Finset (Rd d) := HigherDimLQGMetric.shellGridBox d
    (⌈B / (ε ^ u / (100 * (d : ℝ)))⌉₊ + 1)
    (ε ^ u / (100 * (d : ℝ)))
  have hmesh : 0 < ε ^ u / (100 * (d : ℝ)) := by positivity
  have hbox : ∀ z ∈ HigherDimLQGMetric.gridPts
      (ε ^ u / (100 * (d : ℝ))) ∩ Metric.ball (0 : Rd d) (R + 1), z ∈ F := by
    intro z hz
    have hB : 0 ≤ B := by dsimp [B]; exact le_max_right _ _
    have hle : R + 1 ≤ B := by dsimp [B]; exact le_max_left _ _
    have hzball : z ∈ Metric.ball (0 : Rd d) B :=
      Metric.ball_subset_ball hle hz.2
    exact HigherDimLQGMetric.grid_ball_subset_shellGridBox hmesh hB ⟨hz.1, hzball⟩
  have hcenter (z : Rd d) :
      P {ω | ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} ≤
        ENNReal.ofReal (Real.exp (-A₀ * S.card)) := by
    let E' : ℕ → Set Ω := fun i => if i < S.card then E ε z (r i) else univ
    have hmeas : ∀ i, MeasurableSet[
        HigherDimLQGMetric.fieldSigmaRd
          (fun ω => HigherDimLQGMetric.addConst (h ω)
            (-HigherDimLQGMetric.sphereAvg (h ω) (r i) z))
          (HigherDimLQGMetric.shellOpen z ((8 : ℝ)⁻¹ * r i) (8 * r i))]
          (E' i) := by
      intro i
      by_cases hi : i < S.card
      · have hk := d7IndexAt_mem S hnpos hi
        have hkw := hS (d7IndexAt S hnpos i) hk
        have hm := hE ε hε0 z (d7IndexAt S hnpos i) hkw
        simp [E', hi]
        dsimp [r, d7RadiusAt]
        exact hm
      · simp [E', hi]
    have hprob' : ∀ i, ENNReal.ofReal p ≤ P (E' i) := by
      intro i
      by_cases hi : i < S.card
      · have hk := d7IndexAt_mem S hnpos hi
        have hkw := hS (d7IndexAt S hnpos i) hk
        simpa [E', hi, r, d7RadiusAt, d7ScaleRadius] using
          hprob ε hε0 z (d7IndexAt S hnpos i) hkw
      · have hpUniv : ENNReal.ofReal p ≤ P univ := by
          rw [measure_univ]
          calc
            ENNReal.ofReal p ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (le_of_lt hp1)
            _ = 1 := by simp
        simpa [E', hi] using hpUniv
    have htail := h26 P h hh z r hr hratio E' hmeas hprob' S.card
    have hcount (ω : Ω) : shellSuccessCount E' S.card ω =
        (((Finset.range S.card).filter (fun i => ω ∈ E' i)).card : ℝ) := by
      simp [shellSuccessCount, Finset.sum_boole]
    have hsubset :
        {ω | ∀ i ∈ Finset.range S.card, ω ∉ E' i} ⊆
          {ω | shellSuccessCount E' S.card ω < (1 / 2 : ℝ) * S.card} := by
      intro ω hω
      change shellSuccessCount E' S.card ω < (1 / 2 : ℝ) * S.card
      rw [hcount]
      have hempty :
          (Finset.range S.card).filter (fun i => ω ∈ E' i) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi
        have hfail := hω i hi
        have hi' : i < S.card := Finset.mem_range.mp hi
        simpa [E', hi'] using hfail
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      have hnR : (0 : ℝ) < S.card := by exact_mod_cast hnpos
      nlinarith
    have hbadEq :
        {ω | ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} =
          {ω | ∀ i ∈ Finset.range S.card, ω ∉ E' i} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Finset.mem_range]
      constructor
      · intro hω i hi
        simpa [E', hi] using hω i hi
      · intro hω i hi
        have hfail := hω i hi
        simpa [E', hi] using hfail
    calc
      P {ω | ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} =
          P {ω | ∀ i ∈ Finset.range S.card, ω ∉ E' i} := by rw [hbadEq]
      _ ≤
          P {ω | shellSuccessCount E' S.card ω < (1 / 2 : ℝ) * S.card} :=
        measure_mono hsubset
      _ ≤ ENNReal.ofReal (Real.exp (-A₀ * S.card)) := htail
  have hfinite :
      P {ω | ∃ z ∈ F, ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} ≤
        (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A₀ * S.card)) := by
    calc
      P {ω | ∃ z ∈ F, ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} =
          P (⋃ z ∈ F, {ω | ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)}) := by
            congr 1
            ext ω
            simp only [mem_ofPred_eq, mem_iUnion]
            constructor
            · rintro ⟨z, hz, hω⟩
              exact ⟨z, hz, hω⟩
            · rintro ⟨z, hz, hω⟩
              exact ⟨z, hz, hω⟩
      _ ≤ ∑ z ∈ F, P {ω | ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ F, ENNReal.ofReal (Real.exp (-A₀ * S.card)) := by
        exact Finset.sum_le_sum fun z hz => hcenter z
      _ = (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A₀ * S.card)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hsub :
      {ω | ∃ z ∈ HigherDimLQGMetric.gridPts
          (ε ^ u / (100 * (d : ℝ))) ∩ Metric.ball (0 : Rd d) (R + 1),
          ∀ k ∈ S, ω ∉ E ε z (d7ScaleRadius k)} ⊆
        {ω | ∃ z ∈ F, ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} := by
    rintro ω ⟨z, hz, hω⟩
    refine ⟨z, hbox z hz, ?_⟩
    intro i hi
    have himem : i < S.card := Finset.mem_range.mp hi
    have hki := d7IndexAt_mem S hnpos himem
    have hfail := hω (d7IndexAt S hnpos i) hki
    simpa [r, d7RadiusAt, d7ScaleRadius] using hfail
  have hB : 0 ≤ B := by dsimp [B]; exact le_max_right _ _
  have hgridCount := d7_grid_box_count hd hε0 hε1 hu hB
  have hgridCount' : (F.card : ℝ) * ε ^ (u * (d : ℝ)) ≤ C := by
    dsimp [F, C]
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hgridCount
  have hlogInv : 0 < Real.log (ε⁻¹) := by
    apply Real.log_pos
    exact (one_lt_inv₀ hε0).2 hε1
  have hcountExp :
      Real.exp (-A₀ * S.card) ≤ ε ^ (2 * ((d : ℝ) + 2) * u) := by
    have hAcount : 2 * ((d : ℝ) + 2) * u * Real.log (ε⁻¹) ≤ A₀ * S.card := by
      have hmul := mul_le_mul_of_nonneg_left hncount
        (by positivity : (0 : ℝ) ≤ 32 * ((d : ℝ) + 2) * Real.log 256)
      have hcancel :
          (32 * ((d : ℝ) + 2) * Real.log 256) *
              (u * Real.log (ε⁻¹) / (16 * Real.log 256)) =
            2 * ((d : ℝ) + 2) * u * Real.log (ε⁻¹) := by
        field_simp
        ring
      rw [hcancel] at hmul
      change 2 * ((d : ℝ) + 2) * u * Real.log (ε⁻¹) ≤
        32 * ((d : ℝ) + 2) * Real.log 256 * S.card
      exact hmul
    have hAcount' := hAcount
    rw [Real.log_inv] at hAcount'
    rw [Real.rpow_def_of_pos hε0]
    apply Real.exp_le_exp.mpr
    nlinarith [hAcount']
  have hrestExponent : u ≤ ((d : ℝ) + 4) * u := by
    have hd4 : (1 : ℝ) ≤ (d : ℝ) + 4 := by exact_mod_cast (by omega : 1 ≤ d + 4)
    nlinarith [mul_le_mul_of_nonneg_right hd4 hu.le]
  have hrest : ε ^ (((d : ℝ) + 4) * u) ≤ ε ^ u :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hrestExponent
  have hreal : (F.card : ℝ) * Real.exp (-A₀ * S.card) ≤ C * ε ^ u := by
    calc
      (F.card : ℝ) * Real.exp (-A₀ * S.card) ≤
          (F.card : ℝ) * ε ^ (2 * ((d : ℝ) + 2) * u) :=
        mul_le_mul_of_nonneg_left hcountExp (by positivity)
      _ = ((F.card : ℝ) * ε ^ (u * (d : ℝ))) *
          ε ^ (((d : ℝ) + 4) * u) := by
        have hexp : 2 * ((d : ℝ) + 2) * u =
            u * (d : ℝ) + ((d : ℝ) + 4) * u := by ring
        rw [hexp, Real.rpow_add hε0]
        ring
      _ ≤ C * ε ^ u := by
        exact mul_le_mul hgridCount' hrest (by positivity) (by positivity)
  have hcast : (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A₀ * S.card)) =
      ENNReal.ofReal ((F.card : ℝ) * Real.exp (-A₀ * S.card)) := by
    rw [ENNReal.ofReal_mul (p := (F.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
  calc
    P {ω | ∃ z ∈ HigherDimLQGMetric.gridPts
        (ε ^ u / (100 * (d : ℝ))) ∩ Metric.ball (0 : Rd d) (R + 1),
        ∀ k ∈ S, ω ∉ E ε z (d7ScaleRadius k)} ≤
      P {ω | ∃ z ∈ F, ∀ i ∈ Finset.range S.card, ω ∉ E ε z (r i)} :=
        measure_mono hsub
    _ ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A₀ * S.card)) := hfinite
    _ = ENNReal.ofReal ((F.card : ℝ) * Real.exp (-A₀ * S.card)) := hcast
    _ ≤ ENNReal.ofReal (C * ε ^ u) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLFPPAS
