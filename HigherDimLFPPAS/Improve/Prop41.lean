import HigherDimLFPPAS.Improve.Step1
import HigherDimLFPPAS.Improve.Step3
import Mathlib.Tactic

/-!
# Proposition 4.1: deterministic comparison upgrade

This file assembles the closed-ball greedy crossings from Step 1, the summed gap estimate from
Step 2, and the finite replacement chain from Step 3.
-/

set_option autoImplicit false
-- This proof contains a finite greedy construction followed by an explicit four-edge chain.
set_option maxHeartbeats 600000

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Improve

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The forward deterministic implication, with the two scale inequalities of MA2 written
explicitly. The auxiliary small-scale theorem below supplies these inequalities using a threshold
depending only on `(u,q₀)`. -/
theorem d4_prop41_forward_small
    {u q₀ η A R ε C m : ℝ}
    (hu : 0 < u) (huq : u < q₀) (hq₀ : q₀ < 1)
    (hη : 0 < η) (hA : 1 ≤ A) (hR : 2 ≤ R)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hE1 : 8 * ε ^ q₀ ≤ 6 * ε ^ (u / 2))
    (hE2 : ε ^ u / 100 + 2 * ε ^ (u / 2) < 1)
    (D M : ContMetric d) (mesh : Finset (Rd d)) (radii : Finset ℝ) (c : ℝ → ℝ)
    (hm : ∀ r ∈ radii, c r ≤ m)
    (hcover : d4CoveringHalf D M R (ε ^ u) (ε ^ (u / 2)) η A (8 * ε ^ q₀)
      mesh radii c)
    (hcompare : d4Comparison D M R ε q₀ C) :
    d4Comparison D M R ε (u / 2)
      (A / (A + 1) * max C m + (1 - A / (A + 1) + 3 * η) * m) := by
  classical
  let rmin : ℝ := ε ^ u
  let rmax : ℝ := ε ^ (u / 2)
  let b : ℝ := 8 * ε ^ q₀
  let V : Set (Rd d) := Metric.ball 0 (R + 2)
  let θ : ℝ := d4Theta A
  let Cstar : ℝ := max C m
  let Cnew : ℝ := θ * Cstar + (1 - θ + 3 * η) * m
  have hrmin : 0 < rmin := by dsimp [rmin]; exact Real.rpow_pos_of_pos hε u
  have hrmax : 0 < rmax := by dsimp [rmax]; exact Real.rpow_pos_of_pos hε (u / 2)
  have hrange : rmin ≤ rmax := by
    dsimp [rmin, rmax]
    exact Real.rpow_le_rpow_of_exponent_ge hε (le_of_lt hε1) (by linarith)
  have hθpos : 0 < θ := by
    dsimp [θ, d4Theta]
    positivity
  have hθlt : θ < 1 := by
    dsimp [θ, d4Theta]
    have hden : 0 < A + 1 := by linarith
    rw [div_lt_one hden]
    linarith
  have hmpos : 0 < m := by
    have hx : (0 : Rd d) ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_self]
      linarith
    obtain ⟨z, hz, _⟩ := hcover.1 0 hx
    obtain ⟨r', hr', _, _, hgood⟩ := hcover.2.2 z hz
    rcases hgood with ⟨_, hc, _, _, _, _, _, _⟩
    have hmr := hm r' hr'
    linarith
  have hCstar_nonneg : 0 ≤ Cstar := by dsimp [Cstar]; exact le_trans (le_of_lt hmpos) (le_max_right C m)
  have hC_le : C ≤ Cstar := by dsimp [Cstar]; exact le_max_left C m
  have hCnew_nonneg : 0 ≤ Cnew := by
    dsimp [Cnew]
    positivity
  intro P T hgeo hpath
  rcases hgeo with ⟨hT, hcont, hDmap, hdist, hlen⟩
  have hgeo : d4InternalGeodesic D (Metric.ball 0 (R + 1)) P T :=
    ⟨hT, hcont, hDmap, hdist, hlen⟩
  let x : Rd d := P 0
  let y : Rd d := P T
  have hxR : x ∈ Metric.ball 0 R := hpath ⟨by linarith, by linarith⟩
  have hyR : y ∈ Metric.ball 0 R := hpath ⟨by linarith, le_rfl⟩
  by_cases hclose : dist x y < 16 * rmax
  · have hzero : setDistIn M V (Metric.ball x (8 * rmax)) (Metric.ball y (8 * rmax)) = 0 := by
      apply d4_midpoint_setDistIn_zero M (by linarith) hxR hyR
      nlinarith
    calc
      setDistIn M V (Metric.ball x (8 * ε ^ (u / 2))) (Metric.ball y (8 * ε ^ (u / 2))) = 0 := by
        simpa [rmax, x, y, V] using hzero
      _ ≤ ENNReal.ofReal Cnew * D.len P 0 T := bot_le
  · have hfar : 4 * rmax < dist x y := by
      have hle : 16 * rmax ≤ dist x y := le_of_not_gt hclose
      have hlt : 4 * rmax < 16 * rmax := by nlinarith only [hrmax]
      exact hlt.trans_le hle
    obtain ⟨t₀, Ty, ht₀, hTy, ht₀pos, ht₀Ty, hxt₀, hyTy, hfirstY, hlastX⟩ :=
      d4_endpoint_separation_times (P := P) (T := T) (ρ := 2 * rmax) (x := x) (y := y)
        hT hcont rfl rfl (by linarith [hrmax]) (by nlinarith [hfar])
    have hnohitY : ∀ t ∈ Ico 0 Ty, P t ∉ Metric.closedBall y (2 * rmax) := by
      intro t ht
      simpa [y] using hfirstY t ht
    have houtsideStart : 2 * rmax ≤ dist (P t₀) y := by
      by_contra hbad
      have hmem : P t₀ ∈ Metric.closedBall y (2 * rmax) := by
        rw [Metric.mem_closedBall]
        exact le_of_lt (lt_of_not_ge hbad)
      exact hnohitY t₀ ⟨ht₀.1, ht₀Ty⟩ hmem
    obtain ⟨times, htimes0, htimes0Ty, htimesBounds, hstop, htimesMono, hstep⟩ :=
      d4_greedy_sequence_reaches hcover hrmin hrange hcont hpath rfl ht₀.1 ht₀.2 ht₀Ty
        hTy.2 hnohitY
    rcases hstop with ⟨N, hTyN, hNbefore⟩
    have hNpos : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      exact (not_lt_of_ge hTyN) (by simpa [htimes0] using htimes0Ty)
    let steps : ∀ i : Fin N,
        D4CrossingData (D := D) (M := M) (R := R) (rmin := rmin) (rmax := rmax)
          (η := η) (A := A) (b := b) (mesh := mesh) (radii := radii) (c := c)
          (P := P) (T := T) (a := times i.val) := fun i =>
      Classical.choose (hstep i.val (hNbefore i.val i.isLt))
    have hstepTime (i : Fin N) : (steps i).t = times (i.val + 1) :=
      Classical.choose_spec (hstep i.val (hNbefore i.val i.isLt))
    have htimeMono : Monotone times := monotone_nat_of_le_succ htimesMono
    have htimeStart (i : Fin N) : t₀ ≤ times i.val := by
      rw [← htimes0]
      exact htimeMono (Nat.zero_le _)
    have htimeBefore (i : Fin N) : times i.val < Ty := hNbefore i.val i.isLt
    have houtsideX (i : Fin N) : 2 * rmax ≤ dist (P (times i.val)) x := by
      by_cases heq : times i.val = t₀
      · rw [heq]
        simpa [x] using hxt₀.ge
      · have ht₀i : t₀ < times i.val := lt_of_le_of_ne (htimeStart i) (Ne.symm heq)
        have hnot := hlastX (times i.val) ⟨ht₀i, (htimeBefore i).le⟩
        by_contra hbad
        have hmem : P (times i.val) ∈ Metric.closedBall x (2 * rmax) := by
          rw [Metric.mem_closedBall]
          exact le_of_lt (lt_of_not_ge hbad)
        exact hnot hmem
    have hBgap (i : Fin N) : 0 ≤ (steps i).s - times i.val := by
      linarith [(steps i).hast]
    have hGgap (i : Fin N) : 0 ≤ times (i.val + 1) - (steps i).s := by
      rw [← hstepTime i]
      linarith [(steps i).hst]
    let Bf : Fin N → ℝ := fun i => (steps i).s - times i.val
    let Gf : Fin N → ℝ := fun i => times (i.val + 1) - (steps i).s
    let Bsum : ℝ := ∑ i : Fin N, Bf i
    let Gsum : ℝ := ∑ i : Fin N, Gf i
    have hfrac : Bsum ≤ θ * (Bsum + Gsum) := by
      dsimp [Bsum, Gsum, θ]
      apply d4_step2_sum A Bf Gf (by linarith)
      intro i
      have w := steps i
      have hcurrent : dist (P (times i.val)) (steps i).z < 3 * (steps i).r / 4 := by
        have := (steps i).hnear
        have := (steps i).hrmin
        have := (steps i).hgood.1
        nlinarith
      have hstart : 3 * (steps i).r / 4 < dist x (steps i).z := by
        have htri := dist_triangle (P (times i.val)) (steps i).z x
        have hdistComm := dist_comm x (steps i).z
        have hrad := houtsideX i
        have hnear := (steps i).hnear
        dsimp [rmin] at hnear
        nlinarith [hrmax, hrmin, (steps i).hrmin, (steps i).hrmax, hdistComm]
      obtain ⟨q, hq, hqdist⟩ := d4_prior_inner_sphere_hit hcont (htimesBounds i.val).1
        (htimesBounds i.val).2 hstart hcurrent
      have hU : d4U (steps i).z (steps i).r ⊆ Metric.ball 0 (R + 1) := by
        apply d4U_subset_ball_R1 (steps i).hrmax
        · exact (steps i).hzcenter
        · dsimp [rmin, rmax] at hE2 ⊢
          exact hE2
      have hqSphere : P q ∈ Metric.sphere (steps i).z (3 * (steps i).r / 4) := by
        rw [Metric.mem_sphere]
        exact hqdist
      have hsSphere : P (steps i).s ∈ Metric.sphere (steps i).z (3 * (steps i).r / 4) := by
        rw [Metric.mem_sphere]
        exact (steps i).hsphere
      have htSphere : P (steps i).t ∈ Metric.sphere (steps i).z (steps i).r := by
        rw [Metric.mem_sphere]
        exact (steps i).htsphere
      have hgap := d4_gap_bound hgeo hq.1 (steps i).htT hq.2
        (steps i).hast (steps i).hst hqSphere hsSphere htSphere hU (steps i).hgood (steps i).hF
      simpa [Bf, Gf, hstepTime i] using hgap
    have hBnonneg : 0 ≤ Bsum := by
      dsimp [Bsum]
      exact Finset.sum_nonneg fun i _ => hBgap i
    have hGnonneg : 0 ≤ Gsum := by
      dsimp [Gsum]
      exact Finset.sum_nonneg fun i _ => hGgap i
    have htotal : Bsum + Gsum ≤ T := by
      have htel : Bsum + Gsum = times N - times 0 := by
        dsimp [Bsum, Gsum]
        rw [← Finset.sum_add_distrib]
        calc
          (∑ i : Fin N, (Bf i + Gf i)) =
              ∑ i : Fin N, (times (i.val + 1) - times i.val) := by
                apply Finset.sum_congr rfl
                intro i hi
                dsimp [Bf, Gf]
                ring
          _ = ∑ i ∈ Finset.range N, (times (i + 1) - times i) := by
                simpa using (Fin.sum_univ_eq_sum_range
                  (fun n : ℕ => times (n + 1) - times n) N)
          _ = times N - times 0 := Finset.sum_range_sub times N
      rw [htel]
      have htimeN := htimesBounds N
      have htime0 := htimesBounds 0
      rw [htimes0] at htime0
      linarith
    have hgoal : setDistIn M V (Metric.ball x (8 * rmax)) (Metric.ball y (8 * rmax)) ≤
        ENNReal.ofReal Cnew * D.len P 0 T := by
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro δ hδ hfinite
      let δR : ℝ := (δ : ℝ)
      have hδR : 0 < δR := by exact_mod_cast hδ
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
      let σ : ℝ := δR / N
      have hσ : 0 < σ := by dsimp [σ]; exact div_pos hδR hNreal
      have hsumσ : (∑ i : Fin N, σ) = δR := by
        rw [Finset.sum_const, Finset.card_fin]
        rw [nsmul_eq_mul]
        dsimp [σ]
        field_simp [ne_of_gt hNreal]
      let pairExists : ∀ i : Fin N, ∃ p : Rd d × Rd d,
          p.1 ∈ Metric.ball (P (times i.val)) b ∧
          p.2 ∈ Metric.ball (P ((steps i).s)) b ∧
          M.internal V p.1 p.2 <
            ENNReal.ofReal (Cstar * Bf i) + ENNReal.ofReal σ := by
        intro i
        let Q : ℝ → Rd d := fun s => P (times i.val + s)
        have hQgeo : d4InternalGeodesic D (Metric.ball 0 (R + 1)) Q (Bf i) := by
          apply d4InternalGeodesic_restrict D hgeo
          · exact (htimesBounds i.val).1
          · exact (steps i).hast
          · exact (steps i).hst.trans (steps i).htT
        have hQpath : MapsTo Q (Icc 0 (Bf i)) (Metric.ball 0 R) := by
          intro s hs
          rcases hs with ⟨hs0, hs1⟩
          have hs' : times i.val + s ∈ Icc 0 T := by
            constructor
            · linarith [(htimesBounds i.val).1, hs0]
            · have hseg : times i.val + s ≤ (steps i).s := by
                dsimp [Bf] at hs1
                linarith
              exact hseg.trans ((steps i).hst.trans (steps i).htT)
          exact hpath hs'
        have hcmp := hcompare Q (Bf i) hQgeo hQpath
        have hQlen : D.len Q 0 (Bf i) = ENNReal.ofReal (Bf i) := by
          rcases hQgeo with ⟨hQT, hQc, hQmap, hQdist, hQl⟩
          have hBi : 0 ≤ Bf i := hBgap i
          simpa using hQl 0 ⟨le_rfl, hBi⟩ (Bf i) ⟨hBi, le_rfl⟩ hBi
        have hcmp' : setDistIn M V (Metric.ball (P (times i.val)) b)
            (Metric.ball (P ((steps i).s)) b) ≤
            ENNReal.ofReal C * ENNReal.ofReal (Bf i) := by
          have hcmpLen : setDistIn M V (Metric.ball (P (times i.val)) b)
              (Metric.ball (P ((steps i).s)) b) ≤ ENNReal.ofReal C * D.len Q 0 (Bf i) := by
            have hQstart : Q 0 = P (times i.val) := by simp [Q]
            have hQend : Q (Bf i) = P ((steps i).s) := by
              simp [Q, Bf]
            have hcmp' := hcmp
            rw [hQstart, hQend] at hcmp'
            simpa [b, V] using hcmp'
          rw [hQlen] at hcmpLen
          exact hcmpLen
        have hcmpBase : ENNReal.ofReal C * ENNReal.ofReal (Bf i) ≤
            ENNReal.ofReal (Cstar * Bf i) := by
          calc
            ENNReal.ofReal C * ENNReal.ofReal (Bf i) ≤
                ENNReal.ofReal Cstar * ENNReal.ofReal (Bf i) := by
                  gcongr
            _ = ENNReal.ofReal (Cstar * Bf i) :=
              (ENNReal.ofReal_mul hCstar_nonneg).symm
        have hslackPos : ENNReal.ofReal σ ≠ 0 :=
          (ENNReal.ofReal_pos.mpr hσ).ne'
        have hsetlt : setDistIn M V (Metric.ball (P (times i.val)) b)
            (Metric.ball (P ((steps i).s)) b) <
            ENNReal.ofReal (Cstar * Bf i) + ENNReal.ofReal σ :=
          lt_of_le_of_lt (hcmp'.trans hcmpBase)
            (ENNReal.lt_add_right ENNReal.ofReal_ne_top hslackPos)
        obtain ⟨p, hp₁, q, hq₂, hpq⟩ := d4_setDistIn_exists_pair_lt M hsetlt
        exact ⟨(p, q), hp₁, hq₂, hpq⟩
      let pairs : ∀ i : Fin N, Rd d × Rd d := fun i => Classical.choose (pairExists i)
      have hpairs (i : Fin N) :
          (pairs i).1 ∈ Metric.ball (P (times i.val)) b ∧
          (pairs i).2 ∈ Metric.ball (P ((steps i).s)) b ∧
          M.internal V (pairs i).1 (pairs i).2 <
            ENNReal.ofReal (Cstar * Bf i) + ENNReal.ofReal σ :=
        Classical.choose_spec (pairExists i)
      have hpairsV (i : Fin N) : (pairs i).1 ∈ V ∧ (pairs i).2 ∈ V := by
        have hne : M.internal V (pairs i).1 (pairs i).2 ≠ ⊤ := by
          intro htop
          have hlt := (hpairs i).2.2
          rw [htop] at hlt
          exact (not_lt_of_ge le_top) hlt
        exact d4_internal_finite_mem (D := M) (V := V) hne
      let aSeq : ℕ → Rd d := fun n => if hn : n < N then (pairs ⟨n, hn⟩).1 else P (times n)
      let bSeq : ℕ → Rd d := fun n => if hn : n < N then (pairs ⟨n, hn⟩).2 else P (times n)
      let sSeq : ℕ → ℝ := fun n => if hn : n < N then (steps ⟨n, hn⟩).s else times n
      let cSeq : ℕ → Rd d := fun n => if hn : n < N then P ((steps ⟨n, hn⟩).s) else P (times n)
      let eSeq : ℕ → Rd d := fun n => P (times (n + 1))
      let Bn : ℕ → ℝ := fun n => if hn : n < N then Bf ⟨n, hn⟩ else 0
      let Gn : ℕ → ℝ := fun n => if hn : n < N then Gf ⟨n, hn⟩ else 0
      let w₁ : ℕ → ℝ≥0∞ := fun n => if hn : n < N then
        ENNReal.ofReal (Cstar * Bf ⟨n, hn⟩ + σ) else 0
      let w₂ : ℕ → ℝ≥0∞ := fun n => if hn : n < N then
        ENNReal.ofReal (η * m * Gf ⟨n, hn⟩) else 0
      let w₃ : ℕ → ℝ≥0∞ := fun n => if hn : n < N then
        ENNReal.ofReal ((1 + η) * m * Gf ⟨n, hn⟩) else 0
      let w₄ : ℕ → ℝ≥0∞ := fun n => if hn : n < N then
        ENNReal.ofReal (η * m * Gf ⟨n, hn⟩) else 0
      let cost : ℕ → ℝ := fun n => if hn : n < N then
        Cstar * Bf ⟨n, hn⟩ + σ + η * m * Gf ⟨n, hn⟩ +
          (1 + η) * m * Gf ⟨n, hn⟩ + η * m * Gf ⟨n, hn⟩ else 0
      have hP_in_V (t : ℝ) (ht : t ∈ Icc 0 T) : P t ∈ V := by
        have hp := hpath ht
        rw [Metric.mem_ball] at hp ⊢
        exact hp.trans (by linarith)
      have haSeqV : ∀ n ≤ N, aSeq n ∈ V := by
        intro n hn
        by_cases hlt : n < N
        · simpa [aSeq, hlt] using (hpairsV ⟨n, hlt⟩).1
        · have heq : n = N := by omega
          subst n
          simp [aSeq]
          exact hP_in_V (times N) (htimesBounds N)
      have hqSeq : ∀ n < N,
          bSeq n ∈ V ∧ cSeq n ∈ V ∧ eSeq n ∈ V ∧ aSeq (n + 1) ∈ V := by
        intro n hn
        let i : Fin N := ⟨n, hn⟩
        have hsn : (steps i).s ∈ Icc 0 T := by
          constructor
          · exact le_trans (htimesBounds n).1 (steps i).hast
          · exact (steps i).hst.trans (steps i).htT
        have htn : times (n + 1) ∈ Icc 0 T := htimesBounds (n + 1)
        have hnext : aSeq (n + 1) ∈ V := by
          by_cases hnext : n + 1 < N
          · simpa [aSeq, hnext] using (hpairsV ⟨n + 1, hnext⟩).1
          · have heq : n + 1 = N := by omega
            simp [aSeq, hnext]
            exact hP_in_V (times (n + 1)) (htimesBounds (n + 1))
        simp only [bSeq, dite_eq_left hn, cSeq, eSeq]
        exact ⟨(hpairsV i).2, hP_in_V (steps i).s hsn,
          hP_in_V (times (n + 1)) htn, hnext⟩
      have hchain1 (n : ℕ) (hn : n < N) :
          M.internal V (aSeq n) (bSeq n) ≤ w₁ n := by
        let i : Fin N := ⟨n, hn⟩
        have hpairMem := hpairs i
        have hpairBound : M.internal V (pairs i).1 (pairs i).2 ≤
            ENNReal.ofReal (Cstar * Bf i + σ) := by
          calc
            M.internal V (pairs i).1 (pairs i).2 ≤
                ENNReal.ofReal (Cstar * Bf i) + ENNReal.ofReal σ := hpairMem.2.2.le
            _ = ENNReal.ofReal (Cstar * Bf i + σ) :=
              (ENNReal.ofReal_add (mul_nonneg hCstar_nonneg (hBgap i)) hσ.le).symm
        simpa [aSeq, bSeq, w₁, hn] using hpairBound
      have hcrossD (i : Fin N) : d4Crossing D (steps i).z (steps i).r ≤
          ENNReal.ofReal (Gf i) := by
        have hsSphere : P (steps i).s ∈ Metric.sphere (steps i).z (3 * (steps i).r / 4) := by
          rw [Metric.mem_sphere]
          exact (steps i).hsphere
        have htSphere : P (steps i).t ∈ Metric.sphere (steps i).z (steps i).r := by
          rw [Metric.mem_sphere]
          exact (steps i).htsphere
        calc
          d4Crossing D (steps i).z (steps i).r ≤
              D.internal (d4F (steps i).z (steps i).r) (P (steps i).s) (P (steps i).t) := by
                unfold d4Crossing setDistIn
                exact (iInf₂_le _ hsSphere).trans (iInf₂_le _ htSphere)
          _ ≤ D.len P (steps i).s (steps i).t := by
                apply D.internal_le_len (steps i).hst
                · exact hcont.mono (Icc_subset_Icc
                    (le_trans (htimesBounds i.val).1 (steps i).hast) (steps i).htT)
                · exact (steps i).hF
          _ = ENNReal.ofReal (Gf i) := by
                rw [hlen (steps i).s
                  ⟨le_trans (htimesBounds i.val).1 (steps i).hast,
                    (steps i).hst.trans (steps i).htT⟩
                  (steps i).t ⟨le_trans (le_trans (htimesBounds i.val).1 (steps i).hast)
                    (steps i).hst, (steps i).htT⟩ (steps i).hst]
                rw [hstepTime i]
      have hUinV (i : Fin N) : d4U (steps i).z (steps i).r ⊆ V := by
        have hU := d4U_subset_ball_R1 (steps i).hrmax (steps i).hzcenter (by
          dsimp [rmin, rmax] at hE2 ⊢
          exact hE2)
        intro z hz
        have hz' := hU hz
        change dist z 0 < R + 2
        rw [Metric.mem_ball] at hz'
        exact hz'.trans (by linarith)
      have hchain2 (n : ℕ) (hn : n < N) :
          M.internal V (bSeq n) (cSeq n) ≤ w₂ n := by
        let i : Fin N := ⟨n, hn⟩
        rcases (steps i).hgood with ⟨hr, hc, hη', hA', hb', hcmpF, hdiamD, hshort⟩
        have hsF : P (steps i).s ∈ d4F (steps i).z (steps i).r := by
          change 3 * (steps i).r / 4 ≤ ‖P (steps i).s - (steps i).z‖ ∧
            ‖P (steps i).s - (steps i).z‖ ≤ (steps i).r
          have heq : ‖P (steps i).s - (steps i).z‖ = 3 * (steps i).r / 4 := by
            rw [← dist_eq_norm]
            exact (steps i).hsphere
          rw [heq]
          constructor
          · rfl
          · linarith [hr]
        have hcoef : 0 ≤ η * (c (steps i).r) := mul_nonneg hη.le hc.le
        have hcoefle : η * (c (steps i).r) ≤ η * m :=
          mul_le_mul_of_nonneg_left (hm (steps i).r (steps i).hr) hη.le
        have hshort' := hshort (P (steps i).s) hsF (pairs i).2 (hpairs i).2.1
        have hcrossCost : M.internal (d4U (steps i).z (steps i).r)
            (P (steps i).s) (pairs i).2 ≤ ENNReal.ofReal (η * m * Gf i) := by
          calc
            _ ≤ ENNReal.ofReal (η * c (steps i).r) * d4Crossing D (steps i).z (steps i).r := hshort'
            _ ≤ ENNReal.ofReal (η * c (steps i).r) * ENNReal.ofReal (Gf i) :=
              mul_le_mul_of_nonneg_left (hcrossD i) bot_le
            _ = ENNReal.ofReal (η * c (steps i).r * Gf i) :=
              (ENNReal.ofReal_mul hcoef).symm
            _ ≤ ENNReal.ofReal (η * m * Gf i) := ENNReal.ofReal_le_ofReal (by
              calc
                η * c (steps i).r * Gf i = (η * c (steps i).r) * Gf i := by ring
                _ ≤ (η * m) * Gf i := mul_le_mul_of_nonneg_right hcoefle (hGgap i)
                _ = η * m * Gf i := by ring)
        have hbEq : bSeq n = (pairs i).2 := by simp [bSeq, i, hn]
        have hcEq : cSeq n = P (steps i).s := by simp [cSeq, i, hn]
        have hfi : (⟨n, hn⟩ : Fin N) = i := rfl
        have hw₂ : w₂ n = ENNReal.ofReal (η * m * Gf i) := by
          simp only [w₂, dite_eq_left hn]
          rw [hfi]
        calc
          M.internal V (bSeq n) (cSeq n) = M.internal V (pairs i).2 (P (steps i).s) := by
            rw [hbEq, hcEq]
          _ = M.internal V (P (steps i).s) (pairs i).2 := M.internal_comm V _ _
          _ ≤ M.internal (d4U (steps i).z (steps i).r) (P (steps i).s) (pairs i).2 :=
            M.internal_anti (hUinV i) _ _
          _ ≤ ENNReal.ofReal (η * m * Gf i) := hcrossCost
          _ = w₂ n := hw₂.symm
      have hchain3 (n : ℕ) (hn : n < N) :
          M.internal V (cSeq n) (eSeq n) ≤ w₃ n := by
        let i : Fin N := ⟨n, hn⟩
        have hfi : (⟨n, hn⟩ : Fin N) = i := rfl
        have hsSphere : P (steps i).s ∈ Metric.sphere (steps i).z (3 * (steps i).r / 4) := by
          rw [Metric.mem_sphere]
          exact (steps i).hsphere
        have htSphere : P (steps i).t ∈ Metric.sphere (steps i).z (steps i).r := by
          rw [Metric.mem_sphere]
          exact (steps i).htsphere
        have hbound := d4_crossing_bound_forward hgeo
          (le_trans (htimesBounds n).1 (steps i).hast)
          (steps i).htT (steps i).hst hsSphere htSphere (steps i).hgood (steps i).hF
        rcases (steps i).hgood with ⟨hr, hc, hη', hA', hb', hcmpF, hdiamD, hshort⟩
        have hcoef : 0 ≤ (1 + η) * c (steps i).r := by positivity
        have hcoefle : (1 + η) * c (steps i).r ≤ (1 + η) * m := by
          exact mul_le_mul_of_nonneg_left (hm (steps i).r (steps i).hr) (by linarith)
        have hbound' : M.internal (d4U (steps i).z (steps i).r)
            (P (steps i).s) (P (steps i).t) ≤
              ENNReal.ofReal ((1 + η) * m * Gf i) := by
          calc
            _ ≤ ENNReal.ofReal ((1 + η) * c (steps i).r * Gf i) := by
              simpa [Gf, hstepTime i] using hbound
            _ ≤ ENNReal.ofReal ((1 + η) * m * Gf i) :=
              ENNReal.ofReal_le_ofReal (by
                calc
                  ((1 + η) * c (steps i).r) * Gf i ≤ ((1 + η) * m) * Gf i :=
                    mul_le_mul_of_nonneg_right hcoefle (hGgap i)
                  _ = (1 + η) * m * Gf i := by ring)
        have hcEq : cSeq n = P (steps i).s := by simp [cSeq, i, hn]
        have htimeEq : (steps i).t = times (n + 1) := by
          simpa [i] using hstepTime i
        have heEq : eSeq n = P (steps i).t := by
          simp [eSeq]
          rw [← htimeEq]
        calc
          M.internal V (cSeq n) (eSeq n) =
              M.internal V (P (steps i).s) (P (steps i).t) := by
                rw [hcEq, heEq]
          _ ≤ M.internal (d4U (steps i).z (steps i).r)
                (P (steps i).s) (P (steps i).t) := M.internal_anti (hUinV i) _ _
          _ ≤ ENNReal.ofReal ((1 + η) * m * Gf i) := hbound'
          _ = w₃ n := by
            simp only [w₃, dite_eq_left hn]
            rw [hfi]
      have hchain4 (n : ℕ) (hn : n < N) :
          M.internal V (eSeq n) (aSeq (n + 1)) ≤ w₄ n := by
        let i : Fin N := ⟨n, hn⟩
        have hfi : (⟨n, hn⟩ : Fin N) = i := rfl
        by_cases hnext : n + 1 < N
        ·
          have htimeEq : (steps i).t = times (n + 1) := by
            simpa [i] using hstepTime i
          have hcloseNext : (pairs ⟨n + 1, hnext⟩).1 ∈
              Metric.ball (P (steps i).t) b := by
            simpa [htimeEq] using (hpairs ⟨n + 1, hnext⟩).1
          rcases (steps i).hgood with ⟨hr, hc, hη', hA', hb', hcmpF, hdiamD, hshort⟩
          have htF : P (steps i).t ∈ d4F (steps i).z (steps i).r := by
            change 3 * (steps i).r / 4 ≤ ‖P (steps i).t - (steps i).z‖ ∧
              ‖P (steps i).t - (steps i).z‖ ≤ (steps i).r
            have heq : ‖P (steps i).t - (steps i).z‖ = (steps i).r := by
              rw [← dist_eq_norm]
              exact (steps i).htsphere
            rw [heq]
            constructor
            · linarith [hr]
            · linarith [hr]
          have hshort' := hshort (P (steps i).t) htF (pairs ⟨n + 1, hnext⟩).1 hcloseNext
          have hcoef : 0 ≤ η * c (steps i).r := mul_nonneg hη.le hc.le
          have hcoefle : η * c (steps i).r ≤ η * m :=
            mul_le_mul_of_nonneg_left (hm (steps i).r (steps i).hr) hη.le
          have hcost' : M.internal (d4U (steps i).z (steps i).r)
              (P (steps i).t) (pairs ⟨n + 1, hnext⟩).1 ≤ ENNReal.ofReal (η * m * Gf i) := by
            calc
              _ ≤ ENNReal.ofReal (η * c (steps i).r) * d4Crossing D (steps i).z (steps i).r := hshort'
              _ ≤ ENNReal.ofReal (η * c (steps i).r) * ENNReal.ofReal (Gf i) :=
                mul_le_mul_of_nonneg_left (hcrossD i) bot_le
              _ = ENNReal.ofReal (η * c (steps i).r * Gf i) :=
                (ENNReal.ofReal_mul hcoef).symm
              _ ≤ ENNReal.ofReal (η * m * Gf i) := ENNReal.ofReal_le_ofReal (by
                calc
                  η * c (steps i).r * Gf i = (η * c (steps i).r) * Gf i := by ring
                  _ ≤ (η * m) * Gf i := mul_le_mul_of_nonneg_right hcoefle (hGgap i)
                  _ = η * m * Gf i := by ring)
          calc
            M.internal V (eSeq n) (aSeq (n + 1)) =
                M.internal V (P (steps i).t) (pairs ⟨n + 1, hnext⟩).1 := by
                  have heqLeft : eSeq n = P (steps i).t := by
                    change P (times (n + 1)) = P (steps i).t
                    rw [← htimeEq]
                  have heqRight : aSeq (n + 1) = (pairs ⟨n + 1, hnext⟩).1 := by
                    simp [aSeq, hnext]
                  rw [heqLeft, heqRight]
            _ ≤ M.internal (d4U (steps i).z (steps i).r)
                  (P (steps i).t) (pairs ⟨n + 1, hnext⟩).1 := M.internal_anti (hUinV i) _ _
            _ ≤ ENNReal.ofReal (η * m * Gf i) := hcost'
            _ = w₄ n := by
              simp only [w₄, dite_eq_left hn]
              rw [hfi]
        · have hEq : n + 1 = N := by omega
          have hsame : eSeq n = aSeq (n + 1) := by
            simp [eSeq, aSeq, hnext]
          have hterm : aSeq (n + 1) = P (times (n + 1)) := by
            simp [aSeq, hnext]
          rw [hsame, hterm]
          rw [M.internal_self (hP_in_V (times (n + 1)) (htimesBounds (n + 1)))]
          have hw : w₄ n = ENNReal.ofReal (η * m * Gf ⟨n, hn⟩) := by
            simp [w₄, hn]
          rw [hw]
          exact bot_le
      let i0 : Fin N := ⟨0, hNpos⟩
      have ha0 : aSeq 0 = (pairs i0).1 := by
        simp [aSeq, i0, hNpos]
      have hstartBall : aSeq 0 ∈ Metric.ball x (8 * rmax) := by
        rw [Metric.mem_ball]
        have hp := (hpairs i0).1
        rw [Metric.mem_ball] at hp
        have hpPair : dist (pairs i0).1 (P (times 0)) < b := by
          simpa only [i0, Fin.val_mk] using hp
        have hp0 : dist (aSeq 0) (P (times 0)) < b := by
          rw [ha0]
          exact hpPair
        have hcenter : dist (P (times 0)) x = 2 * rmax := by
          rw [htimes0]
          exact hxt₀
        calc
          dist (aSeq 0) x ≤ dist (aSeq 0) (P (times 0)) + dist (P (times 0)) x :=
            dist_triangle _ _ _
          _ < b + 2 * rmax := by
            calc
              dist (aSeq 0) (P (times 0)) + dist (P (times 0)) x =
                  dist (P (times 0)) x + dist (aSeq 0) (P (times 0)) := by ring
              _ < dist (P (times 0)) x + b :=
                add_lt_add_right hp0 (dist (P (times 0)) x)
              _ = b + 2 * rmax := by rw [hcenter]; ring
          _ ≤ 8 * rmax := by dsimp [b, rmax] at hE1 ⊢; linarith
      let iLast : Fin N := ⟨N - 1, by omega⟩
      have htimeLast : (steps iLast).t = times N := by
        calc
          (steps iLast).t = times (iLast.val + 1) := hstepTime iLast
          _ = times N := congrArg times (by simp [iLast]; omega)
      have hTyInLast : times (N - 1) ≤ Ty ∧ Ty ≤ (steps iLast).t := by
        constructor
        · exact (hNbefore (N - 1) (by omega)).le
        · rw [htimeLast]
          exact hTyN
      have hTyDist : dist (P Ty) (steps iLast).z ≤ (steps iLast).r := by
        by_cases heq : Ty = (steps iLast).t
        · rw [heq]
          exact (steps iLast).htsphere.le
        · have hTylt : Ty < (steps iLast).t := lt_of_le_of_ne hTyInLast.2 heq
          exact (steps iLast).hbefore Ty ⟨hTyInLast.1, hTylt⟩ |>.le
      have hlastBall : P (times N) ∈ Metric.ball y (8 * rmax) := by
        rw [Metric.mem_ball]
        have hNdist : dist (P (times N)) (steps iLast).z = (steps iLast).r := by
          rw [← htimeLast]
          exact (steps iLast).htsphere
        have hbetween : dist (P (times N)) (P Ty) ≤ 2 * (steps iLast).r := by
          have htri := dist_triangle (P (times N)) (steps iLast).z (P Ty)
          rw [hNdist] at htri
          have hcomm : dist (steps iLast).z (P Ty) = dist (P Ty) (steps iLast).z := dist_comm _ _
          rw [hcomm] at htri
          linarith [hTyDist]
        have hyend : dist (P Ty) y = 2 * rmax := hyTy
        calc
          dist (P (times N)) y ≤ dist (P (times N)) (P Ty) + dist (P Ty) y :=
            dist_triangle _ _ _
          _ ≤ 2 * (steps iLast).r + 2 * rmax := add_le_add hbetween (le_of_eq hyend)
          _ ≤ 4 * rmax := by linarith [(steps iLast).hrmax]
          _ < 8 * rmax := by nlinarith [hrmax]
      have haN : aSeq N = P (times N) := by simp [aSeq]
      have hchain : M.internal V (aSeq 0) (aSeq N) ≤
          ∑ n ∈ Finset.range N, (w₁ n + w₂ n + w₃ n + w₄ n) :=
        d4_internal_chain_four M aSeq bSeq cSeq eSeq w₁ w₂ w₃ w₄ N
          haSeqV hqSeq hchain1 hchain2 hchain3 hchain4
      have hcostStep (n : ℕ) (hn : n < N) :
          w₁ n + w₂ n + w₃ n + w₄ n = ENNReal.ofReal (cost n) := by
        let i : Fin N := ⟨n, hn⟩
        have hfi : (⟨n, hn⟩ : Fin N) = i := rfl
        have h0 : 0 ≤ Cstar * Bf i := mul_nonneg hCstar_nonneg (hBgap i)
        have h1 : 0 ≤ σ := hσ.le
        have h2 : 0 ≤ η * m * Gf i := mul_nonneg (mul_nonneg hη.le hmpos.le) (hGgap i)
        have h3 : 0 ≤ (1 + η) * m * Gf i :=
          mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + η) hmpos.le) (hGgap i)
        simp only [w₁, w₂, w₃, w₄, cost, dite_eq_left hn]
        rw [hfi]
        rw [← ENNReal.ofReal_add (add_nonneg h0 h1) h2,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg h0 h1) h2) h3,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h2]
      have hcostNonneg : ∀ n, n ∈ Finset.range N → 0 ≤ cost n := by
        intro n hn
        have hn' : n < N := Finset.mem_range.mp hn
        have hB := hBgap (⟨n, hn'⟩ : Fin N)
        have hG := hGgap (⟨n, hn'⟩ : Fin N)
        simp only [cost, dite_eq_left hn']
        positivity
      have hbudget :
          (∑ n ∈ Finset.range N, (w₁ n + w₂ n + w₃ n + w₄ n)) =
            ENNReal.ofReal (∑ n ∈ Finset.range N, cost n) := by
        calc
          _ = ∑ n ∈ Finset.range N, ENNReal.ofReal (cost n) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hcostStep n (Finset.mem_range.mp hn)
          _ = ENNReal.ofReal (∑ n ∈ Finset.range N, cost n) := by
            rw [ENNReal.ofReal_sum_of_nonneg hcostNonneg]
      have hcostSum : (∑ n ∈ Finset.range N, cost n) =
          Cstar * Bsum + δR + η * m * Gsum + (1 + η) * m * Gsum + η * m * Gsum := by
        rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ => cost n) N]
        simp [cost, Finset.sum_add_distrib, ← Finset.mul_sum, hsumσ, Bsum, Gsum]
      have hmax : max Cstar m = Cstar := by
        dsimp [Cstar]
        exact max_eq_left (le_max_right C m)
      have hmainCost : Cstar * Bsum + m * Gsum + 3 * η * m * Gsum ≤
          (θ * Cstar + (1 - θ + 3 * η) * m) * (Bsum + Gsum) := by
        have h := d4_step3_cost_bound (C := Cstar) (m := m) (η := η) (θ := θ)
          (B := Bsum) (G := Gsum) hmpos.le hη.le hBnonneg hfrac
        rw [hmax] at h
        exact h
      have hcostBound : (∑ n ∈ Finset.range N, cost n) ≤ Cnew * T + δR := by
        rw [hcostSum]
        calc
          Cstar * Bsum + δR + η * m * Gsum + (1 + η) * m * Gsum + η * m * Gsum =
              (Cstar * Bsum + m * Gsum + 3 * η * m * Gsum) + δR := by ring
          _ ≤ (θ * Cstar + (1 - θ + 3 * η) * m) * (Bsum + Gsum) + δR :=
            add_le_add hmainCost le_rfl
          _ ≤ Cnew * T + δR := by
            have hprod := mul_le_mul_of_nonneg_left htotal hCnew_nonneg
            calc
              (θ * Cstar + (1 - θ + 3 * η) * m) * (Bsum + Gsum) + δR =
                  Cnew * (Bsum + Gsum) + δR := rfl
              _ ≤ Cnew * T + δR := add_le_add hprod le_rfl
      have hchainSet : setDistIn M V (Metric.ball x (8 * rmax))
          (Metric.ball y (8 * rmax)) ≤ M.internal V (aSeq 0) (aSeq N) := by
        exact d4_setDistIn_le_pair M hstartBall (by simpa [haN] using hlastBall)
      have hsetSlack : setDistIn M V (Metric.ball x (8 * rmax))
          (Metric.ball y (8 * rmax)) ≤ ENNReal.ofReal (Cnew * T + δR) := by
        calc
          _ ≤ M.internal V (aSeq 0) (aSeq N) := hchainSet
          _ ≤ ∑ n ∈ Finset.range N, (w₁ n + w₂ n + w₃ n + w₄ n) := hchain
          _ = ENNReal.ofReal (∑ n ∈ Finset.range N, cost n) := hbudget
          _ ≤ ENNReal.ofReal (Cnew * T + δR) := ENNReal.ofReal_le_ofReal hcostBound
      have hlenT : D.len P 0 T = ENNReal.ofReal T := by
        simpa only [sub_zero] using hlen 0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩ hT
      have hslackEq : ENNReal.ofReal (Cnew * T + δR) =
          ENNReal.ofReal Cnew * D.len P 0 T + δ := by
        calc
          _ = ENNReal.ofReal (Cnew * T) + ENNReal.ofReal δR :=
            ENNReal.ofReal_add (mul_nonneg hCnew_nonneg hT) hδR.le
          _ = ENNReal.ofReal Cnew * ENNReal.ofReal T + ENNReal.ofReal δR := by
            rw [← ENNReal.ofReal_mul hCnew_nonneg]
          _ = ENNReal.ofReal Cnew * D.len P 0 T + δ := by
            rw [hlenT]
            simp [δR]
      calc
        setDistIn M V (Metric.ball x (8 * rmax)) (Metric.ball y (8 * rmax)) ≤
            ENNReal.ofReal (Cnew * T + δR) := hsetSlack
        _ = ENNReal.ofReal Cnew * D.len P 0 T + δ := hslackEq
    exact hgoal

/-- The two scale restrictions used in the closed-ball endpoint argument hold below a threshold
depending only on `u` and `q₀`. -/
theorem d4_prop41_small_epsilon {u q₀ : ℝ}
    (hu : 0 < u) (huq : u < q₀) (hq₀ : q₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        8 * ε ^ q₀ ≤ 6 * ε ^ (u / 2) ∧ ε ^ u / 100 + 2 * ε ^ (u / 2) < 1 := by
  have hv : 0 < u / 2 := by linarith
  let α : ℝ := q₀ - u / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have htend_rpow (a : ℝ) (ha : 0 < a) :
      Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hαtend := htend_rpow α hα
  have hevα : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ α < 3 / 4 :=
    hαtend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 3 / 4))
  obtain ⟨εα, hεα, Hα⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hevα
  have htu := htend_rpow u hu
  have htv := htend_rpow (u / 2) hv
  have htE2 : Tendsto (fun ε : ℝ => ε ^ u / 100 + 2 * ε ^ (u / 2))
      (𝓝[>] 0) (𝓝 0) := by
    have hleft : Tendsto (fun ε : ℝ => ε ^ u / 100) (𝓝[>] 0) (𝓝 0) := by
      simpa [div_eq_mul_inv] using htu.mul_const (100⁻¹ : ℝ)
    have hright : Tendsto (fun ε : ℝ => 2 * ε ^ (u / 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using htv.const_mul 2
    simpa using hleft.add hright
  have hevE2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ u / 100 + 2 * ε ^ (u / 2) < 1 :=
    htE2.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨εE2, hεE2, HE2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hevE2
  refine ⟨min εα εE2, lt_min hεα hεE2, ?_⟩
  intro ε hε
  have hεα' : ε ∈ Ioo (0 : ℝ) εα :=
    ⟨hε.1, hε.2.trans_le (min_le_left εα εE2)⟩
  have hεE2' : ε ∈ Ioo (0 : ℝ) εE2 :=
    ⟨hε.1, hε.2.trans_le (min_le_right εα εE2)⟩
  have hpow : ε ^ α < 3 / 4 := Hα hεα'
  have hqdecomp : q₀ = u / 2 + α := by dsimp [α]; ring
  have hpowEq : ε ^ q₀ = ε ^ (u / 2) * ε ^ α := by
    rw [hqdecomp, Real.rpow_add hε.1]
  have hE1 : 8 * ε ^ q₀ ≤ 6 * ε ^ (u / 2) := by
    rw [hpowEq]
    have hmul := mul_le_mul_of_nonneg_left hpow.le
      (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num)
        (Real.rpow_nonneg hε.1.le (u / 2)))
    calc
      8 * (ε ^ (u / 2) * ε ^ α) = (8 * ε ^ (u / 2)) * ε ^ α := by ring
      _ ≤ (8 * ε ^ (u / 2)) * (3 / 4) := hmul
      _ = 6 * ε ^ (u / 2) := by ring
  exact ⟨hE1, HE2 hεE2'⟩

/-- A chosen smallness threshold from `d4_prop41_small_epsilon`; its only mathematical inputs are
the exponents `u` and `q₀`. -/
noncomputable def d4_prop41_epsilon0 {u q₀ : ℝ}
    (hu : 0 < u) (huq : u < q₀) (hq₀ : q₀ < 1) : ℝ :=
  Classical.choose (d4_prop41_small_epsilon hu huq hq₀)

/-- The forward proposition with the MA2 threshold built into the statement. -/
theorem d4_prop41_forward
    {u q₀ η A R ε C m : ℝ}
    (hu : 0 < u) (huq : u < q₀) (hq₀ : q₀ < 1)
    (hη : 0 < η) (hA : 1 ≤ A) (hR : 2 ≤ R)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hεsmall : ε < d4_prop41_epsilon0 hu huq hq₀)
    (D M : ContMetric d) (mesh : Finset (Rd d)) (radii : Finset ℝ) (c : ℝ → ℝ)
    (hm : ∀ r ∈ radii, c r ≤ m)
    (hcover : d4CoveringHalf D M R (ε ^ u) (ε ^ (u / 2)) η A (8 * ε ^ q₀)
      mesh radii c)
    (hcompare : d4Comparison D M R ε q₀ C) :
    d4Comparison D M R ε (u / 2)
      (A / (A + 1) * max C m + (1 - A / (A + 1) + 3 * η) * m) := by
  have hthreshold := Classical.choose_spec (d4_prop41_small_epsilon hu huq hq₀)
  have hscale := hthreshold.2 ε ⟨hε, hεsmall⟩
  exact d4_prop41_forward_small hu huq hq₀ hη hA hR hε hε1 hscale.1 hscale.2
    D M mesh radii c hm hcover hcompare

/-- The forward implication specialized to the full good-annulus condition of Definition 3.1. -/
theorem d4_prop41_forward_full
    {u q₀ η A R ε C m : ℝ}
    (hu : 0 < u) (huq : u < q₀) (hq₀ : q₀ < 1)
    (hη : 0 < η) (hA : 1 ≤ A) (hR : 2 ≤ R)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hεsmall : ε < d4_prop41_epsilon0 hu huq hq₀)
    (D M : ContMetric d) (mesh : Finset (Rd d)) (radii : Finset ℝ) (c : ℝ → ℝ)
    (hm : ∀ r ∈ radii, c r ≤ m)
    (hcover : d4Covering D M R (ε ^ u) (ε ^ (u / 2)) η A (8 * ε ^ q₀)
      mesh radii c)
    (hcompare : d4Comparison D M R ε q₀ C) :
    d4Comparison D M R ε (u / 2)
      (A / (A + 1) * max C m + (1 - A / (A + 1) + 3 * η) * m) := by
  have hcoverHalf : d4CoveringHalf D M R (ε ^ u) (ε ^ (u / 2)) η A (8 * ε ^ q₀)
      mesh radii c := by
    refine ⟨hcover.1, hcover.2.1, ?_⟩
    intro z hz
    obtain ⟨r, hr, hrmin, hrmax, hgood⟩ := hcover.2.2 z hz
    exact ⟨r, hr, hrmin, hrmax, d4GoodAt_toGoodHalf hgood⟩
  exact d4_prop41_forward hu huq hq₀ hη hA hR hε hε1 hεsmall
    D M mesh radii c hm hcoverHalf hcompare

/-- The reverse proposition follows by exchanging the metrics and inverting every scale ratio. -/
theorem d4_prop41_reverse
    {u q₀ η A R ε C m : ℝ}
    (hu : 0 < u) (huq : u < q₀) (hq₀ : q₀ < 1)
    (hη : 0 < η) (hA : 1 ≤ A) (hR : 2 ≤ R)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hεsmall : ε < d4_prop41_epsilon0 hu huq hq₀)
    (D M : ContMetric d) (mesh : Finset (Rd d)) (radii : Finset ℝ) (c : ℝ → ℝ)
    (hmInv : ∀ r ∈ radii, (c r)⁻¹ ≤ m)
    (hcover : d4Covering D M R (ε ^ u) (ε ^ (u / 2)) η A (8 * ε ^ q₀)
      mesh radii c)
    (hcompare : d4Comparison M D R ε q₀ C) :
    d4Comparison M D R ε (u / 2)
      (A / (A + 1) * max C m + (1 - A / (A + 1) + 3 * η) * m) := by
  have hcover' : d4CoveringHalf M D R (ε ^ u) (ε ^ (u / 2)) η A (8 * ε ^ q₀)
      mesh radii (fun r => (c r)⁻¹) := by
    refine ⟨hcover.1, hcover.2.1, ?_⟩
    intro z hz
    obtain ⟨r, hr, hrmin, hrmax, hgood⟩ := hcover.2.2 z hz
    exact ⟨r, hr, hrmin, hrmax, d4GoodAt_toGoodHalf (d4GoodAt_symm hgood)⟩
  exact d4_prop41_forward hu huq hq₀ hη hA hR hε hε1 hεsmall
    M D mesh radii (fun r => (c r)⁻¹) hmInv hcover' hcompare

end HigherDimLFPPAS.Improve

end
