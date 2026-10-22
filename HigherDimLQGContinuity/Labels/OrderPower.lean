import HigherDimLQGContinuity.Labels.OrderBasic

/-!
# Reusable power bounds for the polynomial clause of the site order
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- A function is comparable to `v^q` throughout `0 < v ≤ 1`. -/
def SitePowerBounds (f : ℝ → ℝ) (q : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ v : ℝ, 0 < v → v ≤ 1 → c * v ^ q ≤ f v ∧ f v ≤ C * v ^ q

theorem sitePowerBounds_congr {f g : ℝ → ℝ} {q : ℝ}
    (hf : SitePowerBounds f q)
    (hfg : ∀ v, 0 < v → v ≤ 1 → f v = g v) :
    SitePowerBounds g q := by
  obtain ⟨c, C, hc, hC, h⟩ := hf
  refine ⟨c, C, hc, hC, ?_⟩
  intro v hv hv1
  rw [← hfg v hv hv1]
  exact h v hv hv1

theorem sitePowerBounds_const {c : ℝ} (hc : 0 < c) :
    SitePowerBounds (fun _ => c) 0 := by
  refine ⟨c, c, hc, hc, ?_⟩
  intro v _ _
  simp

theorem sitePowerBounds_monomial (q : ℝ) :
    SitePowerBounds (fun v => v ^ q) q := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro v _ _
  simp

theorem sitePowerBounds_scale {f : ℝ → ℝ} {q c : ℝ}
    (hf : SitePowerBounds f q) (hc : 0 < c) :
    SitePowerBounds (fun v => c * f v) q := by
  obtain ⟨a, b, ha, hb, h⟩ := hf
  refine ⟨c * a, c * b, mul_pos hc ha, mul_pos hc hb, ?_⟩
  intro v hv hv1
  obtain ⟨hl, hu⟩ := h v hv hv1
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl hc.le]
  · nlinarith [mul_le_mul_of_nonneg_left hu hc.le]

theorem sitePowerBounds_div_const {f : ℝ → ℝ} {q c : ℝ}
    (hf : SitePowerBounds f q) (hc : 0 < c) :
    SitePowerBounds (fun v => f v / c) q := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (sitePowerBounds_scale hf (inv_pos.mpr hc))

theorem sitePowerBounds_mul {f g : ℝ → ℝ} {q p : ℝ}
    (hf : SitePowerBounds f q) (hg : SitePowerBounds g p) :
    SitePowerBounds (fun v => f v * g v) (q + p) := by
  obtain ⟨cf, Cf, hcf, hCf, hf⟩ := hf
  obtain ⟨cg, Cg, hcg, hCg, hg⟩ := hg
  refine ⟨cf * cg, Cf * Cg, mul_pos hcf hcg, mul_pos hCf hCg, ?_⟩
  intro v hv hv1
  obtain ⟨hfl, hfu⟩ := hf v hv hv1
  obtain ⟨hgl, hgu⟩ := hg v hv hv1
  have hvl : 0 ≤ v ^ q := (Real.rpow_pos_of_pos hv _).le
  have hpl : 0 ≤ v ^ p := (Real.rpow_pos_of_pos hv _).le
  have hfn : 0 ≤ f v := le_trans (mul_nonneg hcf.le hvl) hfl
  have hgn : 0 ≤ g v := le_trans (mul_nonneg hcg.le hpl) hgl
  rw [Real.rpow_add hv]
  constructor
  · nlinarith [mul_le_mul hfl hgl (mul_nonneg hcg.le hpl) hfn]
  · nlinarith [mul_le_mul hfu hgu hgn (mul_nonneg hCf.le hvl)]

theorem sitePowerBounds_rpow {f : ℝ → ℝ} {q a : ℝ}
    (hf : SitePowerBounds f q) (ha : 0 < a) :
    SitePowerBounds (fun v => (f v) ^ a) (q * a) := by
  obtain ⟨c, C, hc, hC, hf⟩ := hf
  refine ⟨c ^ a, C ^ a, Real.rpow_pos_of_pos hc _, Real.rpow_pos_of_pos hC _, ?_⟩
  intro v hv hv1
  obtain ⟨hl, hu⟩ := hf v hv hv1
  have hvq : 0 ≤ v ^ q := (Real.rpow_pos_of_pos hv _).le
  have hcv : 0 ≤ c * v ^ q := mul_nonneg hc.le hvq
  have hfv : 0 ≤ f v := hcv.trans hl
  have hCv : 0 ≤ C * v ^ q := mul_nonneg hC.le hvq
  rw [Real.rpow_mul hv.le, ← Real.mul_rpow hc.le hvq,
    ← Real.mul_rpow hC.le hvq]
  exact ⟨Real.rpow_le_rpow hcv hl ha.le, Real.rpow_le_rpow hfv hu ha.le⟩

theorem sitePowerBounds_min {f g : ℝ → ℝ} {q p : ℝ}
    (hf : SitePowerBounds f q) (hg : SitePowerBounds g p) :
    SitePowerBounds (fun v => min (f v) (g v)) (max q p) := by
  obtain ⟨cf, Cf, hcf, hCf, hf⟩ := hf
  obtain ⟨cg, Cg, hcg, hCg, hg⟩ := hg
  refine ⟨min cf cg, max Cf Cg, lt_min hcf hcg,
    lt_of_lt_of_le hCf (le_max_left _ _), ?_⟩
  intro v hv hv1
  obtain ⟨hfl, hfu⟩ := hf v hv hv1
  obtain ⟨hgl, hgu⟩ := hg v hv hv1
  have hvq : v ^ max q p ≤ v ^ q :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (le_max_left _ _)
  have hvp : v ^ max q p ≤ v ^ p :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (le_max_right _ _)
  constructor
  · apply le_min
    · calc
        min cf cg * v ^ max q p ≤ cf * v ^ q :=
          (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_pos_of_pos hv _).le).trans
            (mul_le_mul_of_nonneg_left hvq hcf.le)
        _ ≤ f v := hfl
    · calc
        min cf cg * v ^ max q p ≤ cg * v ^ p :=
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_pos_of_pos hv _).le).trans
            (mul_le_mul_of_nonneg_left hvp hcg.le)
        _ ≤ g v := hgl
  · rcases le_total q p with hqp | hpq
    · rw [max_eq_right hqp]
      exact (min_le_right _ _).trans (hgu.trans
        (mul_le_mul_of_nonneg_right (le_max_right Cf Cg) (Real.rpow_pos_of_pos hv _).le))
    · rw [max_eq_left hpq]
      exact (min_le_left _ _).trans (hfu.trans
        (mul_le_mul_of_nonneg_right (le_max_left Cf Cg) (Real.rpow_pos_of_pos hv _).le))

theorem sitePowerBounds_min_const {f : ℝ → ℝ} {q c : ℝ}
    (hf : SitePowerBounds f q) (hc : 0 < c) (hq : 0 ≤ q) :
    SitePowerBounds (fun v => min (f v) c) q := by
  simpa only [max_eq_left hq] using sitePowerBounds_min hf (sitePowerBounds_const hc)

theorem sitePowerBounds_comp {f g : ℝ → ℝ} {p q : ℝ}
    (hf : SitePowerBounds f p) (hg : SitePowerBounds g q)
    (hp : 0 < p)
    (hgrange : ∀ v, 0 < v → v ≤ 1 → 0 < g v ∧ g v ≤ 1) :
    SitePowerBounds (fun v => f (g v)) (q * p) := by
  obtain ⟨cf, Cf, hcf, hCf, hf⟩ := hf
  obtain ⟨cg, Cg, hcg, hCg, hgpow⟩ := sitePowerBounds_rpow hg hp
  refine ⟨cf * cg, Cf * Cg, mul_pos hcf hcg, mul_pos hCf hCg, ?_⟩
  intro v hv hv1
  obtain ⟨hgp, hg1⟩ := hgrange v hv hv1
  obtain ⟨hfl, hfu⟩ := hf (g v) hgp hg1
  obtain ⟨hgl, hgu⟩ := hgpow v hv hv1
  have hvq : 0 ≤ v ^ (q * p) := (Real.rpow_pos_of_pos hv _).le
  constructor
  · calc
      (cf * cg) * v ^ (q * p) = cf * (cg * v ^ (q * p)) := by ring
      _ ≤ cf * (g v) ^ p := mul_le_mul_of_nonneg_left hgl hcf.le
      _ ≤ f (g v) := hfl
  · calc
      f (g v) ≤ Cf * (g v) ^ p := hfu
      _ ≤ Cf * (Cg * v ^ (q * p)) := mul_le_mul_of_nonneg_left hgu hCf.le
      _ = (Cf * Cg) * v ^ (q * p) := by ring

/-- A finite family of positive power bounds has one shared polynomial lower
bound and one shared smallness threshold. -/
theorem sitePowerBounds_finite {ι : Type} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 < q i)
    (hb : ∀ i, SitePowerBounds (f i) (q i)) :
    ∃ ε c K : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧ 0 < K ∧
      ∀ v, 0 < v → v ≤ ε → ∀ i, c * v ^ K ≤ f i v ∧ f i v ≤ 1 := by
  classical
  choose c C hc hC hbounds using hb
  let U : Finset ι := Finset.univ
  have hU : U.Nonempty := Finset.univ_nonempty
  let K : ℝ := U.sup' hU q
  let c₀ : ℝ := U.inf' hU c
  let ε₀ : ℝ := U.inf' hU (fun i => min 1 ((1 / C i) ^ (1 / q i)))
  have hK : 0 < K := lt_of_lt_of_le (hq (Classical.choice inferInstance))
    (Finset.le_sup' q (Finset.mem_univ _))
  have hc₀ : 0 < c₀ := by
    apply (Finset.lt_inf'_iff hU).2
    intro i _
    exact hc i
  have hε₀ : 0 < ε₀ := by
    apply (Finset.lt_inf'_iff hU).2
    intro i _
    apply lt_min (by norm_num)
    have hCi : 0 < 1 / C i := by positivity [hC i]
    exact Real.rpow_pos_of_pos hCi _
  have hε₀one : ε₀ ≤ 1 := by
    have i := Classical.choice (inferInstance : Nonempty ι)
    exact (Finset.inf'_le (f := fun i => min 1 ((1 / C i) ^ (1 / q i)))
      (Finset.mem_univ i)).trans (min_le_left _ _)
  refine ⟨ε₀, c₀, K, hε₀, hε₀one, hc₀, hK, ?_⟩
  intro v hv hvε i
  have hv1 : v ≤ 1 := hvε.trans hε₀one
  have hqi : q i ≤ K := Finset.le_sup' q (Finset.mem_univ i)
  have hci : c₀ ≤ c i := Finset.inf'_le c (Finset.mem_univ i)
  have hεi : ε₀ ≤ min 1 ((1 / C i) ^ (1 / q i)) :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have hvi : v ≤ (1 / C i) ^ (1 / q i) :=
    hvε.trans (hεi.trans (min_le_right _ _))
  obtain ⟨hlo, hhi⟩ := hbounds i v hv hv1
  constructor
  · calc
      c₀ * v ^ K ≤ c i * v ^ (q i) :=
        (mul_le_mul_of_nonneg_right hci (Real.rpow_pos_of_pos hv _).le).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hv hv1 hqi) (hc i).le)
      _ ≤ f i v := hlo
  · have hbase : 0 < 1 / C i := by positivity [hC i]
    have hvpow : v ^ (q i) ≤ ((1 / C i) ^ (1 / q i)) ^ (q i) :=
      Real.rpow_le_rpow hv.le hvi (hq i).le
    have hroot : ((1 / C i) ^ (1 / q i)) ^ (q i) = 1 / C i := by
      rw [← Real.rpow_mul hbase.le]
      have hi : (1 / q i) * q i = 1 := by
        field_simp [ne_of_gt (hq i)]
      rw [hi, Real.rpow_one]
    rw [hroot] at hvpow
    have hCmul := mul_le_mul_of_nonneg_left hvpow (hC i).le
    have hCancel : C i * (1 / C i) = 1 := by
      field_simp [ne_of_gt (hC i)]
    exact hhi.trans (by simpa only [hCancel] using hCmul)

/-- Any positive power-bounded scale eventually lies below a prescribed
positive fixed threshold. -/
theorem sitePowerBounds_small {f : ℝ → ℝ} {q B : ℝ}
    (hf : SitePowerBounds f q) (hq : 0 < q) (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ v, 0 < v → v ≤ ε → f v ≤ B := by
  obtain ⟨ε, c, K, hε, hε1, hc, hK, h⟩ := sitePowerBounds_finite
    (fun _ : Fin 1 => fun v => f v / B) (fun _ : Fin 1 => q)
    (fun _ => hq) (fun _ => sitePowerBounds_div_const hf hB)
  refine ⟨ε, hε, hε1, ?_⟩
  intro v hv hvε
  have hle := (h v hv hvε 0).2
  simpa only [one_mul] using (div_le_iff₀ hB).1 hle

theorem siteConsts_t₀_power {d : ℕ} (S : SiteData d) (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).t₀) (siteTExponent S) := by
  change SitePowerBounds (fun v => siteTCoeff S * v ^ siteTExponent S)
    (siteTExponent S)
  exact sitePowerBounds_scale (sitePowerBounds_monomial _) (siteTCoeff_pos S)

theorem siteConsts_uLead_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).uLead)
      (siteTExponent S * S.seed.β⁻¹) := by
  have hA : 0 < 2 * S.seed.A := by linarith [S.seed.A_ge]
  have hL : 0 < S.boxHalfSide / 8 := by positivity [S.boxHalfSide_pos hd]
  have hq : 0 ≤ siteTExponent S * S.seed.β⁻¹ := by
    exact mul_nonneg (siteTExponent_pos S).le (inv_pos.mpr S.seed.β_pos).le
  have ht := sitePowerBounds_div_const (siteConsts_t₀_power S Cnet) hA
  have hpow := sitePowerBounds_rpow ht (inv_pos.mpr S.seed.β_pos)
  have hmin := sitePowerBounds_min_const hpow hL hq
  change SitePowerBounds (fun v => min
    (((siteConsts S Cnet v).t₀ / (2 * S.seed.A)) ^ S.seed.β⁻¹)
    (S.boxHalfSide / 8)) (siteTExponent S * S.seed.β⁻¹)
  exact hmin

theorem siteConsts_r_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).r)
      ((siteTExponent S * S.seed.β⁻¹) * ((S.seed.α * S.seed.β) ^ 2)⁻¹) := by
  have hA : 0 < 2 * S.seed.A := by linarith [S.seed.A_ge]
  have hc : 0 < Topology.polygonalClearanceConst (2 * S.seed.A)
      S.seed.α S.seed.β / 10 := by
    have hp := Topology.polygonalClearanceConst_pos (α := S.seed.α) (β := S.seed.β) hA
    positivity
  have hαβ : 0 < (S.seed.α * S.seed.β) ^ 2 := by
    have hα := S.seed.α_pos
    have hβ := S.seed.β_pos
    positivity
  have hu := siteConsts_uLead_power S hd Cnet
  have hp := sitePowerBounds_rpow hu (inv_pos.mpr hαβ)
  have hscaled := sitePowerBounds_scale hp hc
  change SitePowerBounds (fun v => Topology.polygonalClearanceConst
    (2 * S.seed.A) S.seed.α S.seed.β *
    (siteConsts S Cnet v).uLead ^ ((S.seed.α * S.seed.β) ^ 2)⁻¹ / 10) _
  convert hscaled using 1
  ext v
  ring_nf

theorem siteRExponent_formula {d : ℕ} (S : SiteData d) :
    (siteTExponent S * S.seed.β⁻¹) * ((S.seed.α * S.seed.β) ^ 2)⁻¹ =
      siteRExponent S := by
  unfold siteRExponent
  have hα := ne_of_gt S.seed.α_pos
  have hβ := ne_of_gt S.seed.β_pos
  field_simp

theorem siteConsts_r_power_corrected {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).r) (siteRExponent S) := by
  simpa only [siteRExponent_formula] using siteConsts_r_power S hd Cnet

theorem siteConsts_barν_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).barν)
      (siteNuExponent S) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : 0 < (3 * d + 2 : ℝ) := by positivity
  have hH : 0 < 1000 * S.Hup := by linarith [S.Hup_ge]
  have hHE : 0 < 1000 * S.seed.HE := by linarith [S.seed.HE_ge]
  have hD : 0 < S.seed.d₀ / (1000 * S.Hup) := by positivity [S.seed.d₀_pos]
  have hE : 0 < S.seed.d₀ / (1000 * S.seed.HE) := by positivity [S.seed.d₀_pos]
  have hsInv : 0 < 1 / S.s := by positivity [S.s_pos]
  have hsEInv : 0 < 1 / S.seed.sE := by positivity [S.seed.sE_pos]
  have hr := sitePowerBounds_rpow (siteConsts_r_power_corrected S hd Cnet) hdpos
  have hDpow := sitePowerBounds_rpow
    (sitePowerBounds_scale (sitePowerBounds_monomial 1) hD) hsInv
  have hEpow := sitePowerBounds_rpow
    (sitePowerBounds_scale (sitePowerBounds_monomial 1) hE) hsEInv
  have hmin := sitePowerBounds_min hr (sitePowerBounds_min hDpow hEpow)
  have hscaled := sitePowerBounds_scale hmin (siteNuCoeff_pos S hd1)
  have hcast : (3 * (d : ℝ) + 2) = ((3 * d + 2 : ℕ) : ℝ) := by norm_cast
  rw [hcast] at hscaled
  change SitePowerBounds (fun v => siteNuCoeff S *
    min ((siteConsts S Cnet v).r ^ (3 * d + 2))
      (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
        ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE))))
    (siteNuExponent S)
  unfold siteNuExponent
  rw [hcast]
  simpa only [Real.rpow_one, one_mul, Real.rpow_natCast,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem siteNuExponent_pos {d : ℕ} (S : SiteData d) :
    0 < siteNuExponent S := by
  unfold siteNuExponent
  have hs : 0 < 1 / S.s := by positivity [S.s_pos]
  exact lt_of_lt_of_le hs ((le_max_left _ _).trans (le_max_right _ _))

theorem siteConsts_ν_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).ν)
      (siteNuExponent S) := by
  obtain ⟨c, C, hc, hC, hbar⟩ := siteConsts_barν_power S hd Cnet
  have hq : 0 < (sitePortDenom S : ℝ) := by
    exact_mod_cast sitePortDenom_pos S (by omega)
  let c' := c / (1 + (sitePortDenom S : ℝ) * C)
  have hD : 0 < 1 + (sitePortDenom S : ℝ) * C := by positivity
  refine ⟨c', C, div_pos hc hD, hC, ?_⟩
  intro v hv hv1
  obtain ⟨hlo, hhi⟩ := hbar v hv hv1
  have hvq : 0 < v ^ siteNuExponent S := Real.rpow_pos_of_pos hv _
  have hvq1 : v ^ siteNuExponent S ≤ 1 :=
    Real.rpow_le_one hv.le hv1 (siteNuExponent_pos S).le
  have hbar0 := siteConsts_barν_pos S hd Cnet v hv
  have hbarC : (siteConsts S Cnet v).barν ≤ C := by
    nlinarith [mul_le_mul_of_nonneg_left hvq1 hC.le]
  have hden : 0 < 1 + (sitePortDenom S : ℝ) * (siteConsts S Cnet v).barν := by
    positivity
  have hdenle : 1 + (sitePortDenom S : ℝ) * (siteConsts S Cnet v).barν ≤
      1 + (sitePortDenom S : ℝ) * C := by
    nlinarith [mul_le_mul_of_nonneg_left hbarC hq.le]
  have hquant := siteConsts_barν_div_le_ν S hd Cnet v hv
  constructor
  · calc
      c' * v ^ siteNuExponent S ≤
          (siteConsts S Cnet v).barν /
            (1 + (sitePortDenom S : ℝ) * (siteConsts S Cnet v).barν) := by
        have heq : c' * v ^ siteNuExponent S =
            (c * v ^ siteNuExponent S) /
              (1 + (sitePortDenom S : ℝ) * C) := by
          dsimp [c']
          ring
        rw [heq]
        apply (div_le_div_iff₀ hD hden).2
        have hm1 := mul_le_mul_of_nonneg_right hlo hD.le
        have hm2 := mul_le_mul_of_nonneg_left hdenle (mul_nonneg hc.le hvq.le)
        nlinarith
      _ ≤ (siteConsts S Cnet v).ν := hquant
  · exact (siteConsts_ν_le_barν S hd Cnet v hv).trans hhi

theorem siteDeltaFromNu_power :
    SitePowerBounds siteDeltaFromNu 3 := by
  have hc : 0 < Routing.gpC1 4 / 4 := by
    have h := Routing.gpC1_pos (show (0 : ℝ) ≤ 4 by norm_num)
    positivity
  have h := sitePowerBounds_scale (sitePowerBounds_monomial (3 : ℝ)) hc
  convert h using 1
  ext ν
  simp only [siteDeltaFromNu]
  rw [← Real.rpow_natCast]
  ring_nf

theorem siteThetaNumerator_power {d : ℕ} (S : SiteData d) :
    SitePowerBounds (siteThetaNumerator S) (3 * S.b) := by
  have hhalf := sitePowerBounds_div_const siteDeltaFromNu_power
    (show (0 : ℝ) < 2 by norm_num)
  have hpow := sitePowerBounds_rpow hhalf (by linarith [S.b_ge] : 0 < S.b)
  have hHlo : 0 < S.Hlo⁻¹ := by
    apply inv_pos.mpr
    linarith [S.Hlo_ge]
  have hscaled := sitePowerBounds_scale hpow hHlo
  have hmin := sitePowerBounds_min
    (sitePowerBounds_const (siteData_eps0_pos S)) hscaled
  have hq : max 0 (3 * S.b) = 3 * S.b := max_eq_right (by linarith [S.b_ge])
  rw [hq] at hmin
  change SitePowerBounds (fun ν => min (siteEps0 S.mc S.Hlo)
    (S.Hlo⁻¹ * (siteDeltaFromNu ν / 2) ^ S.b)) (3 * S.b)
  exact hmin

theorem siteThetaFromNu_eq {d : ℕ} (S : SiteData d) {Cnet ν : ℝ}
    (hCnet : 0 < Cnet) (hν : 0 < ν) :
    siteThetaFromNu S Cnet ν =
      (1 / (4 * Cnet * S.Hup)) * siteThetaNumerator S ν *
        ν ^ (8 * d : ℝ) := by
  have hH : 0 < S.Hup := by linarith [S.Hup_ge]
  have hpow : 0 < ν ^ (8 * d : ℝ) := Real.rpow_pos_of_pos hν _
  unfold siteThetaFromNu siteAnetFromNu
  rw [Real.rpow_neg hν.le]
  field_simp

theorem siteThetaFromNu_power {d : ℕ} (S : SiteData d) (Cnet : ℝ)
    (hCnet : 0 < Cnet) :
    SitePowerBounds (siteThetaFromNu S Cnet) (siteThetaExponent S) := by
  have hH : 0 < S.Hup := by linarith [S.Hup_ge]
  have hc : 0 < 1 / (4 * Cnet * S.Hup) := by positivity
  have hmul := sitePowerBounds_mul (siteThetaNumerator_power S)
    (sitePowerBounds_monomial (8 * d : ℝ))
  have hscaled := sitePowerBounds_scale hmul hc
  obtain ⟨c, C, hc0, hC0, h⟩ := hscaled
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro ν hν hν1
  have hEq := siteThetaFromNu_eq S hCnet hν
  have hq : siteThetaExponent S = 3 * S.b + 8 * d := by
    unfold siteThetaExponent
    ring
  rw [hq, hEq]
  simpa only [mul_assoc] using h ν hν hν1

theorem siteConsts_θ_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).θ)
      (siteNuExponent S * siteThetaExponent S) := by
  have hcomp := sitePowerBounds_comp (siteThetaFromNu_power S Cnet hCnet)
    (siteConsts_ν_power S hd Cnet)
    (by unfold siteThetaExponent; positivity [S.b_ge])
    (fun v hv _ => ⟨siteConsts_ν_pos S hd Cnet v,
      siteConsts_ν_le_one S hd Cnet v⟩)
  change SitePowerBounds (fun v => siteThetaFromNu S Cnet
    (siteConsts S Cnet v).ν) (siteNuExponent S * siteThetaExponent S)
  exact hcomp

/-- The intrinsic `θ ≍ ν^(8d+3b)` part of ruling N29, with fixed comparison
constants independent of the tolerance. -/
theorem siteConsts_θ_nu_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ v, 0 < v → v ≤ 1 →
        c * (siteConsts S Cnet v).ν ^ siteThetaExponent S ≤
          (siteConsts S Cnet v).θ ∧
        (siteConsts S Cnet v).θ ≤
          C * (siteConsts S Cnet v).ν ^ siteThetaExponent S := by
  obtain ⟨c, C, hc, hC, h⟩ := siteThetaFromNu_power S Cnet hCnet
  refine ⟨c, C, hc, hC, ?_⟩
  intro v hv hv1
  exact h (siteConsts S Cnet v).ν
    (siteConsts_ν_pos S hd Cnet v) (siteConsts_ν_le_one S hd Cnet v)

end HigherDimLQGContinuity
