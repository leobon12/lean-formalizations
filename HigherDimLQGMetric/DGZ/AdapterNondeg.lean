import HigherDimLQGMetric.DGZ.AdapterFixed
import HigherDimLQGMetric.DGZ.TightNondegCross

/-! Comparison of Euclidean sphere distances with finitely many dyadic box crossings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}

/-- A finite family of box shells has uniform crossing constants. -/
theorem adapter_nondeg_finite (h : DGZHyp d κ ξ Q)
    (hNondeg : NondegShape d κ ξ Q) (Y : Finset (Rd d))
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) :
    ∃ δ > 0, ∃ N : ℕ,
      ∀ y ∈ Y, ∀ {Ω : Type} [MeasurableSpace Ω]
        {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
          P {ω | acrossDist ξ (fun z => H n z ω) y (2 * ρ) ρ ≤
            δ * aQ P H ξ n 2⁻¹} ≤ ENNReal.ofReal θ := by
  classical
  induction Y using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, 0, ?_⟩
      intro y hy
      simp at hy
  | @insert y Y hy ih =>
      obtain ⟨δy, hδy, Ny, hboundy⟩ := hNondeg h y (2 * ρ) ρ hρ
        (by linarith) θ hθ
      obtain ⟨δY, hδY, NY, hboundY⟩ := ih
      refine ⟨min δy δY, lt_min hδy hδY, max Ny NY, ?_⟩
      intro z hz Ω _ P W H hH n hn
      have hd : 0 < d := by have hh := h.dim; omega
      have hq : 0 ≤ aQ P H ξ n 2⁻¹ := by
        unfold aQ
        exact ((hH.band n).lowerQuantile_lfppDistance_pos hd
          hH.whiteNoise ξ (by norm_num) (by norm_num)).le
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have hsub : {ω | acrossDist ξ (fun z => H n z ω) z (2 * ρ) ρ ≤
            min δy δY * aQ P H ξ n 2⁻¹} ⊆
          {ω | acrossDist ξ (fun z => H n z ω) z (2 * ρ) ρ ≤
            δy * aQ P H ξ n 2⁻¹} := by
          intro ω hω
          exact hω.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq)
        exact (measure_mono hsub).trans
          (hboundy (Ω := Ω) P W H hH n (le_trans (le_max_left _ _) hn))
      · have hsub : {ω | acrossDist ξ (fun z => H n z ω) z (2 * ρ) ρ ≤
            min δy δY * aQ P H ξ n 2⁻¹} ⊆
          {ω | acrossDist ξ (fun z => H n z ω) z (2 * ρ) ρ ≤
            δY * aQ P H ξ n 2⁻¹} := by
          intro ω hω
          exact hω.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq)
        exact (measure_mono hsub).trans
          (hboundY z hz hH n (le_trans (le_max_right _ _) hn))

/-- After scaling by `s⁻¹`, the inner sphere stays in one fixed compact ball. -/
private theorem adapter_scaled_inner_mem {c : Rd d} {r₂ s : ℝ}
    (hr₂ : 0 < r₂) (hs : 1 / 2 < s)
    {x : Rd d} (hx : x ∈ Metric.sphere c r₂) :
    s⁻¹ • x ∈ Metric.closedBall (0 : Rd d) (2 * (‖c‖ + r₂)) := by
  have hs0 : 0 < s := by linarith
  have hsi : s⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hs0).2 (by linarith)
  have hxnorm : ‖x‖ ≤ ‖c‖ + r₂ := by
    have hxc : ‖x - c‖ = r₂ := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
    have hh := norm_add_le (x - c) c
    rw [sub_add_cancel] at hh
    linarith
  have hsum : 0 ≤ ‖c‖ + r₂ := by positivity
  change dist (s⁻¹ • x) 0 ≤ 2 * (‖c‖ + r₂)
  rw [dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
  exact (mul_le_mul hsi hxnorm (norm_nonneg _) (by norm_num))

/-- Every point on the scaled outer sphere leaves a box of radius `2ρ` around a point
whose `ρ` box contains a point on the scaled inner sphere. -/
private theorem adapter_scaled_outer_not_obox {c v x y : Rd d} {r₁ r₂ s ρ : ℝ}
    (hd : 0 < d) (hr : r₂ < r₁)
    (hs : 1 / 2 < s) (hs1 : s ≤ 1)
    (hρ : ρ = (r₁ - r₂) / (8 * (Real.sqrt d + 1)))
    (hx : x ∈ Metric.sphere c r₂) (hy : y ∈ Metric.sphere c r₁)
    (hcover : s⁻¹ • x ∈ obox v ρ) :
    s⁻¹ • y ∉ obox v (2 * ρ) := by
  have hs0 : 0 < s := by linarith
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hden : 0 < 8 * (Real.sqrt d + 1) := by positivity
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos (by linarith) hden
  have hdiff : r₁ - r₂ ≤ ‖s⁻¹ • x - s⁻¹ • y‖ := by
    have hxy : r₁ - r₂ ≤ ‖x - y‖ := by
      have hyc : dist y c = r₁ := hy
      have hxc : dist x c = r₂ := hx
      have hh := dist_triangle y x c
      rw [hyc, hxc, dist_comm y x, dist_eq_norm] at hh
      linarith
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    have hsi : 1 ≤ s⁻¹ := by simpa only [one_div] using (one_le_div hs0).2 hs1
    nlinarith [mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hsi), norm_nonneg (x-y)]
  intro hout
  have hnear₁ : ‖s⁻¹ • x - v‖ ≤ Real.sqrt d * ρ := by
    simpa only [norm_sub_rev] using (tn_norm_sub_le hcover)
  have hnear₂ : ‖v - s⁻¹ • y‖ ≤ Real.sqrt d * (2 * ρ) := tn_norm_sub_le hout
  have htri : ‖s⁻¹ • x - s⁻¹ • y‖ ≤
      ‖s⁻¹ • x - v‖ + ‖v - s⁻¹ • y‖ := by
    calc
      _ = ‖(s⁻¹ • x - v) + (v - s⁻¹ • y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hbound : Real.sqrt d * ρ + Real.sqrt d * (2 * ρ) < r₁ - r₂ := by
    have hK : 0 < Real.sqrt d + 1 := by positivity
    have hA : 3 * Real.sqrt d < 8 * (Real.sqrt d + 1) := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hA (by linarith : 0 < r₁ - r₂)
    have ht : 3 * Real.sqrt d * ρ < r₁ - r₂ := by
      rw [hρ]
      have heq : 3 * Real.sqrt d * ((r₁ - r₂) / (8 * (Real.sqrt d + 1))) =
          (3 * Real.sqrt d * (r₁ - r₂)) / (8 * (Real.sqrt d + 1)) := by ring
      rw [heq]
      exact (div_lt_iff₀ hden).2 (by nlinarith [hmul])
    nlinarith
  linarith

/-- One finite box cover works for all scale ratios `s ∈ (1/2,1]`. -/
theorem adapter_sphere_cover {c : Rd d} {r₂ ρ : ℝ}
    (hr₂ : 0 < r₂) (hρ : 0 < ρ) :
    ∃ Y : Finset (Rd d),
      (∀ v ∈ Y, v ∈ Metric.closedBall (0 : Rd d) (2 * (‖c‖ + r₂))) ∧
      ∀ {s : ℝ}, 1 / 2 < s → ∀ {x : Rd d}, x ∈ Metric.sphere c r₂ →
        ∃ v ∈ Y, s⁻¹ • x ∈ obox v ρ := by
  let S := Metric.closedBall (0 : Rd d) (2 * (‖c‖ + r₂))
  obtain ⟨Y, hY, hcover⟩ :=
    tn_exists_obox_cover (S := S) (isCompact_closedBall _ _) hρ
  refine ⟨Y, hY, ?_⟩
  intro s hs x hx
  have hp : s⁻¹ • x ∈ S := adapter_scaled_inner_mem hr₂ hs hx
  simpa only [Set.mem_iUnion, exists_prop] using hcover hp

/-- A good finite family of dyadic crossings forces every scaled pair between the Euclidean
spheres to have large real-band distance. -/
theorem adapter_sphere_pair_cross {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W W' : WN d → Ω → ℝ} {G : ℝ → Rd d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} {B : Rd d → Ω → ℝ}
    {ε s r₁ r₂ ρ L δ : ℝ} {c : Rd d} {N : ℕ}
    (hd : 0 < d) (hξ : 0 < ξ) (hr : r₂ < r₁)
    (hs : 1 / 2 < s) (hs1 : s ≤ 1)
    (hρ : ρ = (r₁ - r₂) / (8 * (Real.sqrt d + 1)))
    (hG : IsBandVersion P W κ ε 1 (G ε))
    (hH : IsDyadicRealization κ P W' H)
    (heq : ∀ z ω, G ε (s • z) ω = H N z ω + B z ω)
    (Y : Finset (Rd d))
    (hY : ∀ v ∈ Y, v ∈ Metric.closedBall (0 : Rd d) (2 * (‖c‖ + r₂)))
    (hcover : ∀ {t : ℝ}, 1 / 2 < t → ∀ {x : Rd d}, x ∈ Metric.sphere c r₂ →
      ∃ v ∈ Y, t⁻¹ • x ∈ obox v ρ)
    (ω : Ω)
    (hBg : ¬ ∃ z ∈ cbox (0 : Rd d) (2 * (‖c‖ + r₂) + 2 * ρ + 1),
      L < |B z ω|)
    (hcross : ∀ v ∈ Y, δ * aQ P H ξ N 2⁻¹ <
      acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ)
    {x y : Rd d} (hx : x ∈ Metric.sphere c r₂)
    (hy : y ∈ Metric.sphere c r₁) :
    δ * aQ P H ξ N 2⁻¹ <
      Real.exp (ξ * L) * lfppMetric ξ (fun z => G ε (s • z) ω)
        (s⁻¹ • x) (s⁻¹ • y) := by
  obtain ⟨v, hvY, hpv⟩ := hcover hs hx
  have hρ0 : 0 < ρ := by
    rw [hρ]
    have : 0 < Real.sqrt d + 1 := by positivity
    exact div_pos (by linarith) (by positivity)
  have hp : s⁻¹ • x ∈ cbox v ρ := HigherDimLFPP.DGZ.obox_subset_cbox _ _ hpv
  have hq : s⁻¹ • y ∉ obox v (2 * ρ) :=
    adapter_scaled_outer_not_obox hd hr hs hs1 hρ hx hy hpv
  have hvn : ‖v‖ ≤ 2 * (‖c‖ + r₂) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hY v hvY
  have hvbox : v ∈ cbox (0 : Rd d) (2 * (‖c‖ + r₂)) := by
    intro i
    simpa only [PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm v i).trans hvn
  have hBc : ∀ z ∈ cbox v (2 * ρ) \ obox v ρ,
      |H N z ω - G ε (s • z) ω| ≤ L := by
    intro z hz
    have hz' : z ∈ obox v (2 * ρ + 1) :=
      cbox_subset_obox (by linarith : 2 * ρ < 2 * ρ + 1) hz.1
    have hzS : z ∈ cbox (0 : Rd d) (2 * (‖c‖ + r₂) + 2 * ρ + 1) := by
      convert tn_obox_subset_cbox hvbox hz' using 1
      ring_nf
    have hh := le_of_not_gt (fun ht => hBg ⟨z, hzS, ht⟩)
    rw [heq]
    simpa only [sub_add_cancel_left, abs_neg] using hh
  have hXc : Continuous (fun z => G ε (s • z) ω) :=
    (hG.continuous ω).comp (continuous_id.const_smul s)
  have hcomp : acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ ≤
      Real.exp (ξ * L) * acrossDist ξ (fun z => G ε (s • z) ω) v (2 * ρ) ρ := by
    have hh := acrossDist_le_exp_mul (ξ := ξ) (c := v) (r₁ := 2 * ρ)
      (r₂ := ρ) ((hH.band N).continuous ω) hXc (by linarith) hBc
    rwa [abs_of_pos hξ] at hh
  exact (hcross v hvY).trans_le (hcomp.trans
    (mul_le_mul_of_nonneg_left
      (acrossDist_le_lfppMetric_of_mem hXc (by linarith) hp hq)
      (Real.exp_pos _).le))

/-- Finite union bound with a per-centre budget of `θ/(2(|Y|+1))`. -/
private theorem adapter_finite_bad_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Finset (Rd d)} {E : Rd d → Set Ω} {θ : ℝ}
    (hθ : 0 < θ)
    (hE : ∀ v ∈ Y, P (E v) ≤ ENNReal.ofReal (θ / (2 * (Y.card + 1)))) :
    P {ω | ∃ v ∈ Y, ω ∈ E v} ≤ ENNReal.ofReal (θ / 2) := by
  have hreal : (Y.card : ℝ) * (θ / (2 * (Y.card + 1))) ≤ θ / 2 := by
    have hc : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
    have hden : 0 < (2 : ℝ) * (Y.card + 1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hh : (Y.card : ℝ) / (Y.card + 1) ≤ 1 :=
      (div_le_iff₀ (by linarith)).2 (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hh hθ.le
    calc
      (Y.card : ℝ) * (θ / (2 * (Y.card + 1))) * 2
          = θ * ((Y.card : ℝ) / (Y.card + 1)) := by field_simp
      _ ≤ θ := by nlinarith
  have hsum : (∑ v ∈ Y, ENNReal.ofReal (θ / (2 * (Y.card + 1)))) ≤
      ENNReal.ofReal (θ / 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    P {ω | ∃ v ∈ Y, ω ∈ E v} = P (⋃ v ∈ Y, E v) := by congr 1; ext ω; simp
    _ ≤ ∑ v ∈ Y, P (E v) := measure_biUnion_finset_le Y E
    _ ≤ ∑ v ∈ Y, ENNReal.ofReal (θ / (2 * (Y.card + 1))) :=
      Finset.sum_le_sum fun v hv => hE v hv
    _ ≤ ENNReal.ofReal (θ / 2) := hsum

/-- Uniform margin in the comparison from dyadic crossings to real-band set distance. -/
private theorem adapter_nondeg_numeric {ξ L δ C a ah DX D s : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (ha : 0 < a)
    (hs : 1 / 2 < s) (hmed : ah ≤ C * a)
    (hcross : δ * a < Real.exp (ξ * L) * DX)
    (hD : D = s * DX) :
    2 * (Real.exp (-(ξ * L)) * δ / (8 * C)) * ah < D := by
  have hs0 : 0 < s := by linarith
  have hq : ah / C ≤ a := (div_le_iff₀ hC).2 (by nlinarith [hmed])
  have hDX : Real.exp (-(ξ * L)) * (δ * a) < DX := by
    have hh : δ * a < DX * Real.exp (ξ * L) := by
      simpa only [mul_comm] using hcross
    have hh' := (div_lt_iff₀ (Real.exp_pos (ξ * L))).2 hh
    rwa [div_eq_mul_inv, ← Real.exp_neg, mul_comm] at hh'
  have hfirst : 2 * (Real.exp (-(ξ * L)) * δ / (8 * C)) * ah ≤
      (1 / 4 : ℝ) * Real.exp (-(ξ * L)) * δ * a := by
    calc
      2 * (Real.exp (-(ξ * L)) * δ / (8 * C)) * ah =
          (1 / 4 : ℝ) * Real.exp (-(ξ * L)) * δ * (ah / C) := by
            field_simp
            ring
      _ ≤ (1 / 4 : ℝ) * Real.exp (-(ξ * L)) * δ * a :=
        mul_le_mul_of_nonneg_left hq (by positivity)
  calc
    _ ≤ (1 / 4 : ℝ) * Real.exp (-(ξ * L)) * δ * a := hfirst
    _ < s * (Real.exp (-(ξ * L)) * (δ * a)) := by
      have hfac : 0 < Real.exp (-(ξ * L)) * (δ * a) := by positivity
      have hss : (1 / 4 : ℝ) < s := by linarith
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right hss hfac
    _ < s * DX := mul_lt_mul_of_pos_left hDX hs0
    _ = D := hD.symm

/-- The Euclidean sphere nondegeneracy clause of `RealEpsAdapterShape`. -/
theorem adapter_nondeg_real (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) (hNondeg : NondegShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {G : ℝ → Rd d → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε))
    (c : Rd d) (r₁ r₂ θ : ℝ) (hr₂ : 0 < r₂) (hr : r₂ < r₁) (hθ : 0 < θ) :
    ∃ δ > 0, ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | lfppSetDist ξ (fun z => G ε z ω) univ
          (Metric.sphere c r₂) (Metric.sphere c r₁) ≤ δ * aHat P G ξ ε} ≤
        ENNReal.ofReal θ := by
  classical
  have hd : 0 < d := by have hh := h.dim; omega
  let ρ : ℝ := (r₁ - r₂) / (8 * (Real.sqrt d + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    positivity
  obtain ⟨Y, hY, hcover⟩ := adapter_sphere_cover hr₂ hρ (c := c)
  let θ' : ℝ := θ / (2 * (Y.card + 1))
  have hθ' : 0 < θ' := by dsimp [θ']; positivity
  obtain ⟨δF, hδF, NF, hF⟩ :=
    adapter_nondeg_finite h hNondeg Y hρ hθ'
  obtain ⟨L₀, hL₀, M₀, hM₀, δ₀, hδ₀, N₀, hmed⟩ :=
    adapter_median_bounds_coupled h hHolder hNondeg hβ0 hβ
  let C : ℝ := Real.exp (ξ * L₀) * M₀ * (2 : ℝ) ^ β
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < M₀ := by linarith
    positivity
  obtain ⟨L, hL, hBbound⟩ := adapter_exists_upperBand_sup_bound hd h.kernel
    (R := 2 * (‖c‖ + r₂) + 2 * ρ + 1) (θ := θ / 2)
    (by positivity) (by positivity)
  let δ : ℝ := Real.exp (-(ξ * L)) * δF / (8 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let ε₀ : ℝ := (2 : ℝ)⁻¹ ^ (max NF N₀)
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hε₀1 : ε₀ ≤ 1 := by
    dsimp [ε₀]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹ : ℝ) ≤ 1)
  refine ⟨δ, hδ, ε₀, hε₀, ?_⟩
  intro ε hε
  have hε1 : ε < 1 := hε.2.trans_le hε₀1
  obtain ⟨N, s, hs, hs1, hεeq⟩ := adapter_exists_dyadic_scale hε.1 hε1.le
  have hs0 : 0 < s := by linarith
  have hN : max NF N₀ ≤ N := adapter_index_ge_of_eps_lt hs hεeq hε.2
  obtain ⟨H, hH, B, hB, heq⟩ := adapter_realScale_coupling h.kernel hW hε.1
    (hG ε ⟨hε.1, hε1⟩) N hs0 hs1 hεeq
  have hN₀ : N₀ ≤ N := (le_max_right _ _).trans hN
  have hNF : NF ≤ N := (le_max_left _ _).trans hN
  have hb1 : 1 ≤ 1 / s := (one_le_div hs0).2 hs1
  have hb2 : 1 / s ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
  have hmedup : aHat P G ξ ε ≤ C * aQ P H ξ N 2⁻¹ := by
    exact (hmed hW (hG ε ⟨hε.1, hε1⟩) hH hB hs hs1 hN₀ heq).2
  have haQpos : 0 < aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact (hH.band N).lowerQuantile_lfppDistance_pos hd hH.whiteNoise ξ
      (by norm_num) (by norm_num)
  have haHatpos : 0 < aHat P G ξ ε := aHat_pos hd hW (hG ε ⟨hε.1, hε1⟩) ξ
  have hBbad : P {ω | ∃ z ∈ cbox (0 : Rd d)
      (2 * (‖c‖ + r₂) + 2 * ρ + 1), L < |B z ω|} ≤
      ENNReal.ofReal (θ / 2) := hBbound hH.whiteNoise hb1 hb2 hB
  have hFbad : P {ω | ∃ v ∈ Y,
      acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ ≤
        δF * aQ P H ξ N 2⁻¹} ≤ ENNReal.ofReal (θ / 2) := by
    apply adapter_finite_bad_bound hθ
    intro v hv
    exact hF v hv hH N hNF
  have hsphere (r : ℝ) (hr : 0 ≤ r) : (Metric.sphere c r).Nonempty := by
    refine ⟨c + r • e₁ d, ?_⟩
    change dist (c + r • e₁ d) c = r
    rw [dist_eq_norm]
    have hh : c + r • e₁ d - c = r • e₁ d := by abel
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, norm_e₁ hd, mul_one]
  have hsub : {ω | lfppSetDist ξ (fun z => G ε z ω) univ
      (Metric.sphere c r₂) (Metric.sphere c r₁) ≤ δ * aHat P G ξ ε} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) (2 * (‖c‖ + r₂) + 2 * ρ + 1),
        L < |B z ω|} ∪
      {ω | ∃ v ∈ Y, acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ ≤
        δF * aQ P H ξ N 2⁻¹} := by
    intro ω hω
    by_cases hBg : ∃ z ∈ cbox (0 : Rd d) (2 * (‖c‖ + r₂) + 2 * ρ + 1),
        L < |B z ω|
    · exact Or.inl hBg
    · right
      by_contra hCg
      have hpair : ∀ x ∈ Metric.sphere c r₂, ∀ y ∈ Metric.sphere c r₁,
          2 * δ * aHat P G ξ ε < lfppMetric ξ (fun z => G ε z ω) x y := by
        intro x hx y hy
        have hcross := adapter_sphere_pair_cross hd h.xi_pos hr hs hs1 (rfl : ρ = _)
          (hG ε ⟨hε.1, hε1⟩) hH heq Y hY hcover ω hBg
          (fun v hv => lt_of_not_ge (fun hh => hCg ⟨v, hv, hh⟩)) hx hy
        have hscale : lfppMetric ξ (fun z => G ε z ω) x y =
            s * lfppMetric ξ (fun z => G ε (s • z) ω) (s⁻¹ • x) (s⁻¹ • y) := by
          have hh := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ
            (fun z => G ε z ω) hs0 (s⁻¹ • x) (s⁻¹ • y)
          simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, smul_smul,
            mul_inv_cancel₀ hs0.ne', one_smul] using hh
        exact adapter_nondeg_numeric hδF hC haQpos hs hmedup hcross hscale
      have hset : 2 * δ * aHat P G ξ ε ≤
          lfppSetDist ξ (fun z => G ε z ω) univ
            (Metric.sphere c r₂) (Metric.sphere c r₁) := by
        apply le_lfppSetDist (hsphere r₂ hr₂.le) (hsphere r₁ (by linarith))
        intro x hx y hy
        exact (hpair x hx y hy).le
      have hmargin : δ * aHat P G ξ ε < 2 * δ * aHat P G ξ ε := by
        nlinarith [mul_pos hδ haHatpos]
      exact (not_le_of_gt (hmargin.trans_le hset)) hω
  calc
    P {ω | lfppSetDist ξ (fun z => G ε z ω) univ
        (Metric.sphere c r₂) (Metric.sphere c r₁) ≤ δ * aHat P G ξ ε}
        ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d)
            (2 * (‖c‖ + r₂) + 2 * ρ + 1), L < |B z ω|} ∪
          {ω | ∃ v ∈ Y, acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ ≤
            δF * aQ P H ξ N 2⁻¹}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
      (measure_union_le _ _).trans (add_le_add hBbad hFbad)
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end HigherDimLQGMetric.DGZ
