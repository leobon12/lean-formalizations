import MatedCRTHarmonic.MesoGrid.Core

/-!
# Uniform constants for the mesoscopic-control construction

This exposes the scalar-only constants constructed in the deterministic proof before quantifying
all graph and edge types, so one pair serves every sample-dependent mated-CRT edge type.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoGrid

theorem mesoscopicControlWith_of_scaledGridControl_uniform :
    ∀ a ρ p χ β q : ℝ, 0 < a → 0 < ρ → ρ < 1 → 0 < p → 0 < β → β < χ → β < q → β < a →
      ∃ σ ν : ℝ, 0 < σ ∧ 0 < ν ∧
        ∀ {V E : Type*} (G : LFMultigraph V E) (o : V) (H : CellularEmbedding G o)
          (R : ℕ → ℝ), (∀ k, 0 < R k) →
          Tendsto (fun k : ℕ => Real.logb 2 (R k) / k) atTop (𝓝 a) →
          (∀ᶠ k : ℕ in atTop, H.ScaledGridControl (R k) ((2 : ℝ) ^ (-(k : ℝ))) χ β q ρ p) →
          (∀ᶠ k : ℕ in atTop,
            (verticesMeeting H.cell (ball 0 (R k))).encard ≤ (2 : ℕ∞) ^ (2 * k)) →
          H.MesoscopicControlWith (min p (1 / 2)) σ ν := by
  classical
  intro a rho p chi beta q ha hrho hrhoOne hp hbeta hchi hq hba
  have hbaPos : 0 < a - beta := sub_pos.mpr hba
  have hrecip : 1 / a < 1 / (a - beta) := by
    apply (div_lt_div_iff₀ ha hbaPos).2
    nlinarith
  let lam : ℝ := ((1 / a) + (1 / (a - beta))) / 2
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hLamLo : 1 / a < lam := by dsimp [lam]; linarith
  have hLamHi : lam < 1 / (a - beta) := by dsimp [lam]; linarith
  have hLamProdLo : 1 < lam * a := by
    have h := (div_lt_iff₀ ha).mp hLamLo
    nlinarith
  have hLamProdHi : lam * (a - beta) < 1 := by
    have h := (lt_div_iff₀ hbaPos).mp hLamHi
    nlinarith
  let sigma : ℝ := (1 - lam * (a - beta)) / 2
  let nu : ℝ := 1 / (2 * lam)
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hLamSigma : lam * (a - beta) < 1 - sigma := by
    dsimp [sigma]
    linarith
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hp' : 0 < min p (1 / 2) := lt_min hp (by norm_num)
  have hp'lt : min p (1 / 2) < 1 := lt_of_le_of_lt (min_le_right p (1 / 2)) (by norm_num)
  refine ⟨sigma, nu, hsigma, hnu, ?_⟩
  intro V E G o H R hR hlim hScaled hCount
  obtain ⟨Kscaled, hScaled⟩ := Filter.eventually_atTop.mp hScaled
  obtain ⟨Kcount, hCount⟩ := Filter.eventually_atTop.mp hCount
  let K : ℕ := max Kscaled Kcount
  have hKscaled : ∀ k, K ≤ k → H.ScaledGridControl (R k) ((2 : ℝ) ^ (-(k : ℝ))) chi beta q rho p := by
    intro k hk
    exact hScaled k (le_trans (Nat.le_max_left Kscaled Kcount) hk)
  have hKcount : ∀ k, K ≤ k → (verticesMeeting H.cell (ball 0 (R k))).encard ≤ (2 : ℕ∞) ^ (2 * k) := by
    intro k hk
    exact hCount k (le_trans (Nat.le_max_right Kscaled Kcount) hk)
  have hLarge := exists_large_scale_bounds ha hrho hrhoOne hsigma hlam hbeta hchi hba hR hlim
    hLamProdLo hLamSigma K
  obtain ⟨R0, hBounds⟩ := hLarge
  let mfun : ℝ → ℝ := fun D => R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ beta
  let efun : ℝ → ℝ := fun D => 6 * (R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ chi)
  let dfun : ℝ → ℝ := fun D => R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ q
  have hpos : ∀ D, R0 ≤ D → 0 < mfun D ∧ 0 < efun D ∧ 0 < dfun D := by
    intro D hD
    rcases hBounds D hD with ⟨hk, hRbig, hDltR, hmle, hsmall, h3s⟩
    let k := scaleIndex lam D
    have heps : 0 < meshEpsilon k := by dsimp [meshEpsilon]; positivity
    constructor
    · dsimp [mfun]
      exact mul_pos (hR k) (Real.rpow_pos_of_pos heps beta)
    constructor
    · dsimp [efun]
      exact mul_pos (by norm_num) (mul_pos (hR k) (Real.rpow_pos_of_pos heps chi))
    · dsimp [dfun]
      exact mul_pos (hR k) (Real.rpow_pos_of_pos heps q)
  have hmgrowth : ∀ D, R0 ≤ D → mfun D ≤ D ^ (1 - sigma) := by
    intro D hD
    exact (hBounds D hD).2.2.2.1
  have hratio : Tendsto (fun D => (efun D + dfun D) / mfun D) atTop (𝓝 0) := by
    have hdecχ := tendsto_two_neg_mul_scaleIndex (lam := lam) (gap := chi - beta) hlam (sub_pos.mpr hchi)
    have hdecq := tendsto_two_neg_mul_scaleIndex (lam := lam) (gap := q - beta) hlam (sub_pos.mpr hq)
    have hεχ : Tendsto (fun D : ℝ => (meshEpsilon (scaleIndex lam D)) ^ (chi - beta)) atTop (𝓝 0) := by
      refine hdecχ.congr ?_
      intro D
      symm
      dsimp [meshEpsilon]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; ring
    have hεq : Tendsto (fun D : ℝ => (meshEpsilon (scaleIndex lam D)) ^ (q - beta)) atTop (𝓝 0) := by
      refine hdecq.congr ?_
      intro D
      symm
      dsimp [meshEpsilon]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; ring
    have hlimSum := (hεχ.const_mul 6).add hεq
    have hlimSum' : Tendsto (fun D => 6 * (meshEpsilon (scaleIndex lam D)) ^ (chi - beta) +
        (meshEpsilon (scaleIndex lam D)) ^ (q - beta)) atTop (𝓝 0) := by
      simpa using hlimSum
    refine hlimSum'.congr ?_
    intro D
    have hRpos := hR (scaleIndex lam D)
    have hepspos : 0 < meshEpsilon (scaleIndex lam D) := by
      dsimp [meshEpsilon]
      exact Real.rpow_pos_of_pos (by norm_num) _
    dsimp [mfun, efun, dfun]
    rw [Real.rpow_sub hepspos chi beta, Real.rpow_sub hepspos q beta]
    field_simp [ne_of_gt hRpos, ne_of_gt (Real.rpow_pos_of_pos hepspos beta)]
  have hdiam : ∀ D, R0 ≤ D → ∀ x, (H.cell x ∩ ball 0 (4 * D)).Nonempty → diam (H.cell x) ≤ dfun D := by
    intro D hD x hx
    rcases hBounds D hD with ⟨hk, hRbig, hDltR, hmle, hsmall, h3s⟩
    obtain ⟨y, hycell, hyball⟩ := hx
    have hywide : y ∈ ball (0 : ℂ) (rho * R (scaleIndex lam D)) := by
      have hdist : dist y 0 < 4 * D := by simpa [Metric.mem_ball] using hyball
      rw [Metric.mem_ball]
      exact lt_trans hdist (by nlinarith [hRbig])
    have hcontrol : H.ScaledGridControl (R (scaleIndex lam D))
        ((2 : ℝ) ^ (-(scaleIndex lam D : ℝ))) chi beta q rho p := by
      exact hKscaled (scaleIndex lam D) hk
    have hdiam' := hcontrol.1 x ⟨y, hycell, hywide⟩
    simpa [dfun, meshEpsilon] using hdiam'
  have hnets : ∀ D, R0 ≤ D → ∃ (Z : Finset ℂ) (Q : Finset ℝ),
      (∀ z ∈ Z, z ∈ ball (0 : ℂ) (2 * D)) ∧
      (∀ w ∈ ball (0 : ℂ) (2 * D), ∃ z ∈ Z, dist w z ≤ efun D) ∧
      (∀ r ∈ Q, r ∈ Set.Icc (mfun D) (D / 100)) ∧
      (∀ s ∈ Set.Icc (mfun D) (D / 100), ∃ r ∈ Q, dist s r ≤ efun D) ∧
      ∀ z ∈ Z, ∀ r ∈ Q, ∀ x ∈ verticesMeeting H.cell (sphere z r),
        ENNReal.ofReal (min p (1 / 2)) ≤ G.walkLaw x {ω | G.AnnularEvent H.cell z r (G.vertexPath ω)} := by
    intro D hD
    rcases hBounds D hD with ⟨hk, hRbig, hDltR, hmle, hsmall, h3s⟩
    let k := scaleIndex lam D
    let eps := meshEpsilon k
    let s := R k * eps ^ chi
    have heps : 0 < eps := by dsimp [eps, meshEpsilon]; positivity
    have hs : 0 < s := mul_pos (hR k) (Real.rpow_pos_of_pos heps chi)
    have hcontrol : H.ScaledGridControl (R k) ((2 : ℝ) ^ (-(k : ℝ))) chi beta q rho p := by
      exact hKscaled k hk
    have hsum : R k * eps ^ beta + R k * eps ^ chi < D / 100 := by
      simpa [k, eps, meshEpsilon] using hsmall
    have h3s' : 3 * s < 2 * D := by simpa [s, eps] using h3s
    refine ⟨gridBallFinset s (2 * D), gridIntervalFinset s (mfun D) (D / 100), ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      simpa [Metric.mem_ball] using hz'
    · intro w hw
      obtain ⟨z, hz, hdist⟩ := gridBallFinset_isNet hs h3s' w hw
      refine ⟨z, hz, ?_⟩
      have hedist : dist w z ≤ 6 * s := hdist
      refine le_trans hedist ?_
      dsimp [efun]
      simp [k, s, eps, meshEpsilon]
    · intro r hr
      obtain ⟨j, hj, hreq, hr'⟩ := gridIntervalFinset_mem_index hr
      simpa [mfun, k, eps, meshEpsilon] using hr'
    · intro t ht
      have hwidth : mfun D + s ≤ D / 100 := by
        have := hsum
        dsimp [mfun, k, eps] at *
        dsimp [s]
        linarith
      obtain ⟨r, hr, hdist⟩ := gridIntervalFinset_isNet hs hwidth t ht
      refine ⟨r, hr, ?_⟩
      have hedist : dist t r ≤ 6 * s := by
        calc
          dist t r ≤ s := hdist
          _ ≤ 6 * s := by nlinarith [hs]
      simpa [efun, k, s, eps, meshEpsilon] using hedist
    · intro z hz r hr x hx
      obtain ⟨im, in_, him, hin, hzEq, hzball⟩ := gridBallFinset_mem_indices hz
      obtain ⟨ir, hir, hrEq, hrange⟩ := gridIntervalFinset_mem_index hr
      have hcenter : (((R k * eps ^ chi : ℝ) : ℂ) * ((im : ℂ) + (in_ : ℂ) * Complex.I)) = z := by
        calc
          _ = (s : ℂ) * ((im : ℂ) + (in_ : ℂ) * Complex.I) := by simp [s]
          _ = gridPoint s im in_ := (gridPoint_eq_scaledInt s im in_).symm
          _ = z := hzEq
      have hrval : R k * eps ^ chi * (ir : ℝ) = r := by simpa [s] using hrEq
      have hcenterMem : (((R k * eps ^ chi : ℝ) : ℂ) * ((im : ℂ) + (in_ : ℂ) * Complex.I)) ∈
          ball (0 : ℂ) (rho * R k) := by
        rw [hcenter]
        exact Metric.ball_subset_ball (by linarith [hRbig]) hzball
      have hlowm : R k * eps ^ beta ≤ r := by
        simpa [mfun, k, eps, meshEpsilon] using hrange.1
      have hlow : R k * eps ^ beta ≤ R k * eps ^ chi * (ir : ℝ) := by
        calc
          R k * eps ^ beta ≤ r := hlowm
          _ = R k * eps ^ chi * (ir : ℝ) := hrval.symm
      have hup : R k * eps ^ chi * (ir : ℝ) ≤ rho * R k := by
        rw [hrval]
        have hDpos : 0 < D := by linarith [hD]
        have hrle : r ≤ D / 100 := hrange.2
        nlinarith [hRbig]
      have hballsub : ball z (2 * (R k * eps ^ chi * (ir : ℝ))) ⊆ ball (0 : ℂ) (rho * R k) := by
        rw [hrval]
        intro w hw
        have hw' : dist w z < 2 * r := by simpa [Metric.mem_ball] using hw
        have hz' : dist z 0 < 2 * D := by simpa [Metric.mem_ball] using hzball
        have htriangle : dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
        have hrle : r ≤ D / 100 := hrange.2
        have hDpos : 0 < D := by linarith [hD]
        have htarget : 2 * r + 2 * D < rho * R k := by
          have : 2 * r + 2 * D ≤ (2 : ℝ) * (D / 100) + 2 * D := add_le_add (mul_le_mul_of_nonneg_left hrle (by norm_num)) le_rfl
          nlinarith [hRbig]
        have hwzero : dist w 0 < rho * R k := lt_of_le_of_lt htriangle (lt_of_lt_of_le (add_lt_add hw' hz') (by linarith))
        simpa [Metric.mem_ball] using hwzero
      let centerControl : ℂ := (((R k * ((2 : ℝ) ^ (-(k : ℝ))) ^ chi : ℝ) : ℂ) *
        ((im : ℂ) + (in_ : ℂ) * Complex.I))
      let radiusControl : ℝ := R k * ((2 : ℝ) ^ (-(k : ℝ))) ^ chi * (ir : ℝ)
      have hcenterControl : centerControl = z := by
        simpa [centerControl, eps, meshEpsilon] using hcenter
      have hradiusControl : radiusControl = r := by
        simpa [radiusControl, eps, meshEpsilon] using hrval
      have hcenterEq' : (((R k * ((2 : ℝ) ^ (-(k : ℝ))) ^ chi : ℝ) : ℂ) *
          ((im : ℂ) + (in_ : ℂ) * Complex.I)) = z := by
        simpa [eps, meshEpsilon] using hcenter
      have hradiusEq' : R k * ((2 : ℝ) ^ (-(k : ℝ))) ^ chi * (ir : ℝ) = r := by
        simpa [eps, meshEpsilon] using hrval
      have hballsub' : ball centerControl (2 * radiusControl) ⊆ ball (0 : ℂ) (rho * R k) := by
        rw [hcenterControl]
        simpa [centerControl, radiusControl, eps, meshEpsilon] using hballsub
      have hxcontrol : x ∈ verticesMeeting H.cell (sphere centerControl radiusControl) := by
        simpa [centerControl, radiusControl, hcenterEq', hradiusEq'] using hx
      have hcenterMem' : centerControl ∈ ball (0 : ℂ) (rho * R k) := by
        simpa [centerControl, eps, meshEpsilon] using hcenterMem
      have hprob := hcontrol.2 im in_ ir hcenterMem' hlow hup hballsub' x hxcontrol
      have hprob' : ENNReal.ofReal p ≤ G.walkLaw x
          {ω | G.AnnularEvent H.cell z r (G.vertexPath ω)} := by
        have hprob2 : ENNReal.ofReal p ≤ G.walkLaw x
            {ω | G.AnnularEvent H.cell centerControl radiusControl (G.vertexPath ω)} := by
          simpa [centerControl, radiusControl] using hprob
        simpa [hcenterControl, hradiusControl] using hprob2
      exact (ENNReal.ofReal_le_ofReal (min_le_left p (1 / 2))).trans hprob'
  refine ⟨hp', hp'lt, hsigma, hnu, ?_⟩
  refine ⟨R0, mfun, efun, dfun, hpos, hmgrowth, hratio, hdiam, hnets, ?_⟩
  let S : Set V := {x | (H.cell x ∩ closedBall (0 : ℂ) R0).Nonempty}
  have hSF : S.Finite := by
    simpa [S] using H.locallyFinite_cell.finite_nonempty_inter_compact
      (isCompact_closedBall (0 : ℂ) R0)
  letI : Fintype S := hSF.fintype
  let F : Finset V := hSF.toFinset
  let cvol : ℝ := ((4 : ℝ) ^ nu)⁻¹ / 2
  have hcvol : 0 < cvol := by
    dsimp [cvol]
    positivity
  have hNatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    apply (tendsto_natCast_atTop_iff).2
    exact tendsto_id
  have hPowNat : Tendsto (fun n : ℕ => (n : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp hNatCast
  have hcpos : 0 < ((4 : ℝ) ^ nu)⁻¹ := by positivity
  have hPowScaled : Tendsto (fun n : ℕ => ((4 : ℝ) ^ nu)⁻¹ * (n : ℝ) ^ nu) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcpos hPowNat
  obtain ⟨Npow, hNpow⟩ := Filter.eventually_atTop.mp
    (hPowScaled.eventually (eventually_ge_atTop (2 : ℝ)))
  let N : ℕ := max (F.card + 1) Npow
  refine ⟨cvol, hcvol, N, ?_⟩
  intro A hoA hAconn hN
  have hdiamGt : R0 < planeDiam H.cell A := by
    by_contra hnot
    have hdiamLe : planeDiam H.cell A ≤ R0 := le_of_not_gt hnot
    have hsubF : A ⊆ F := by
      intro x hx
      obtain ⟨y, hy⟩ := H.interior_cell_nonempty x
      have hycell : y ∈ H.cell x := interior_subset hy
      have hynorm := CellularFacts.norm_le_planeDiam H hoA hx hycell
      have hyclosed : y ∈ closedBall (0 : ℂ) R0 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hynorm.trans hdiamLe
      have hxS : x ∈ S := ⟨y, hycell, hyclosed⟩
      exact Set.mem_toFinset.mpr hxS
    have hcardF : A.card ≤ F.card := Finset.card_le_card hsubF
    have hNlocal : F.card + 1 ≤ A.card := le_trans (le_max_left (F.card + 1) Npow) hN
    omega
  let D : ℝ := planeDiam H.cell A + 1
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have : 0 ≤ planeDiam H.cell A := diam_nonneg
    linarith
  have hRD : R0 ≤ D := by dsimp [D]; linarith
  rcases hBounds D hRD with ⟨hk, hRbig, hDltR, hmle, hsmall, h3s⟩
  let k : ℕ := scaleIndex lam D
  have hAsub : (A : Set V) ⊆ verticesMeeting H.cell (ball (0 : ℂ) (R k)) := by
    intro x hx
    obtain ⟨y, hy⟩ := H.interior_cell_nonempty x
    have hycell : y ∈ H.cell x := interior_subset hy
    have hynorm := CellularFacts.norm_le_planeDiam H hoA hx hycell
    have hyball : y ∈ ball (0 : ℂ) (R k) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hynorm (lt_trans (by dsimp [D]; linarith) hDltR)
    exact ⟨y, hycell, hyball⟩
  have hcountEn : (A.card : ℕ∞) ≤ (2 : ℕ∞) ^ (2 * k) := by
    calc
      (A.card : ℕ∞) = (A : Set V).encard := by simp
      _ ≤ (verticesMeeting H.cell (ball (0 : ℂ) (R k))).encard := Set.encard_mono hAsub
      _ ≤ (2 : ℕ∞) ^ (2 * k) := by simpa [k] using hKcount (scaleIndex lam D) hk
  have hcountReal : (A.card : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have htop : ((2 : ℕ∞) ^ (2 * k)) ≠ ⊤ := by simp
    have hcountNat : A.card ≤ 2 ^ (2 * k) := by exact_mod_cast hcountEn
    exact_mod_cast hcountNat
  have hkupper : (k : ℝ) < lam * Real.logb 2 D + 1 := by
    exact scaleIndex_lt_add_one hlam hD1
  have hexp : 2 * (k : ℝ) < 2 * (lam * Real.logb 2 D + 1) := by nlinarith
  have hpowcast : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * (k : ℝ)) := by
    calc
      (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ ((2 * k : ℕ) : ℝ) :=
        (Real.rpow_natCast (2 : ℝ) (2 * k)).symm
      _ = (2 : ℝ) ^ (2 * (k : ℝ)) := by congr 1; norm_num
  have hpowbound : (2 : ℝ) ^ (2 * k) < 4 * D ^ (2 * lam) := by
    rw [hpowcast]
    calc
      (2 : ℝ) ^ (2 * (k : ℝ)) < (2 : ℝ) ^ (2 * (lam * Real.logb 2 D + 1)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
      _ = 4 * D ^ (2 * lam) := by
        rw [show 2 * (lam * Real.logb 2 D + 1) = 2 + (2 * lam) * Real.logb 2 D by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hmul : (2 : ℝ) ^ ((2 * lam) * Real.logb 2 D) =
            ((2 : ℝ) ^ Real.logb 2 D) ^ (2 * lam) := by
          calc
            _ = (2 : ℝ) ^ (Real.logb 2 D * (2 * lam)) := by congr 1; ring
            _ = ((2 : ℝ) ^ Real.logb 2 D) ^ (2 * lam) := Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
        rw [hmul, Real.rpow_logb (by norm_num) (by norm_num) (by linarith [hRD])]
        norm_num
  have hcardBound : (A.card : ℝ) ≤ 4 * D ^ (2 * lam) := hcountReal.trans hpowbound.le
  have hcardPos : 0 < (A.card : ℝ) := by
    have hcardNat : 0 < A.card := Finset.card_pos.mpr ⟨o, hoA⟩
    exact_mod_cast hcardNat
  have hcardRpow : (A.card : ℝ) ^ nu ≤ (4 * D ^ (2 * lam)) ^ nu :=
    Real.rpow_le_rpow hcardPos.le hcardBound hnu.le
  have hboundRpow : (4 * D ^ (2 * lam)) ^ nu = (4 : ℝ) ^ nu * D := by
    rw [Real.mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) (by positivity),
      ← Real.rpow_mul (by positivity : 0 ≤ D)]
    have hExp : (2 * lam) * nu = 1 := by dsimp [nu]; field_simp
    rw [hExp, Real.rpow_one]
  let X : ℝ := ((4 : ℝ) ^ nu)⁻¹ * (A.card : ℝ) ^ nu
  have hXle : X ≤ D := by
    dsimp [X]
    calc
      ((4 : ℝ) ^ nu)⁻¹ * (A.card : ℝ) ^ nu ≤
          ((4 : ℝ) ^ nu)⁻¹ * ((4 * D ^ (2 * lam)) ^ nu) :=
        mul_le_mul_of_nonneg_left hcardRpow (by positivity)
      _ = D := by rw [hboundRpow]; field_simp
  have hXge : 2 ≤ X := by
    dsimp [X, N] at hN ⊢
    have hNpowA : Npow ≤ A.card := le_trans (le_max_right (F.card + 1) Npow) hN
    exact hNpow A.card hNpowA
  have hvol : cvol * (A.card : ℝ) ^ nu ≤ planeDiam H.cell A := by
    dsimp [D] at hXle
    dsimp [cvol]
    dsimp [X] at hXge
    nlinarith [hXle, hXge]
  exact hvol

end MatedCRTHarmonic.MesoGrid
