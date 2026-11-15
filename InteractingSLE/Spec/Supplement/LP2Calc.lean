import InteractingSLE.Spec.Ito.Observable

/-!
# Lemma LP2: the Lyapunov function of the passive-point gap (calculus)

Packet PROVE-LP16. Specification §6.2, Lemma LP2 (`source/spec/p433-480.md` L1124–L1160,
`source/spec/p481-528.md` L1–L18): for `k > 4` and `−2 < ρ < c = k/2 − 2`, in the canonical single-right-seed
driving law every passive point `x > 0` is swallowed at a finite time.

The source proves LP2 by one-dimensional diffusion theory for the ratio `U = (V − W)/(g(x) − W)` (scale and
speed, the ergodic or renewal theorem, the time-change reconstruction). We use instead a Lyapunov function of the
pair `X = g_t(x) − W_t`, `D = g_t(x) − V_t` (so `R = V − W = X − D ≥ 0`):

  `F(X, D) = X^a D^e + θ X^{λ − 2} (X − D)²`, `e = aρ/2`, `λ = a + e`.

Along the evolution, `dX = (2/X + ρ/R) dt − √k dB`, `dD = (2/X − 2/R) dt`, and the Itô drift of `F` is
`X^{λ−2} G(D/X)` with

  `G(u) = −c₁ u^e + θ P(1 − u)`, `c₁ = a (c − k a / 2)`, `P(U) = A U² + B U + C`,

where the singular terms `1/R` cancel exactly in the first summand (this is why `e = aρ/2`). For small `a > 0`,
`c₁ > 0` and `P(1) = λ (ρ − c + kλ/2) < 0`; for small `θ > 0`, `G ≤ −γ < 0` on `(0, 1]` and `F ≥ m X^λ` when
`0 < D ≤ X`. The probabilistic part (`LP2Loc.lean`, `LP2.lean`) turns this into finite swallowing.

This file is deterministic:

* `lyap`, `lyapX`, `lyapD`, `lyapXX` and their derivative lemmas;
* the coordinates `gapX`, `gapD` of a point `((Λ₁, Λ₂), b)` (with `Λ₁ = g(x)`, `Λ₂ = V`, `b = B`), the observable
  `obs` and its region `region` (`X > 0`, `D > 0`);
* `itoGen_obs`: the Itô generator of `obs`;
* `exists_lyapParams`: the constants, with the drift bound `itoGen_obs_le`, the lower bound `obs_ge` and the
  initial value `obs_init`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.LP.LP2

/-! ### The scalar function and its derivatives -/

/-- The Lyapunov function `F(X, D) = X^a D^e + θ X^{a+e−2} (X − D)²`. -/
def lyap (a e θ X D : ℝ) : ℝ := X ^ a * D ^ e + θ * (X ^ (a + e - 2) * (X - D) ^ 2)

/-- `∂_X F`. -/
def lyapX (a e θ X D : ℝ) : ℝ :=
  a * X ^ (a - 1) * D ^ e +
    θ * ((a + e - 2) * X ^ (a + e - 2 - 1) * (X - D) ^ 2 + X ^ (a + e - 2) * (2 * (X - D)))

/-- `∂_D F`. -/
def lyapD (a e θ X D : ℝ) : ℝ :=
  X ^ a * (e * D ^ (e - 1)) - θ * (X ^ (a + e - 2) * (2 * (X - D)))

/-- `∂²_X F`. -/
def lyapXX (a e θ X D : ℝ) : ℝ :=
  a * (a - 1) * X ^ (a - 1 - 1) * D ^ e +
    θ * ((a + e - 2) * (a + e - 2 - 1) * X ^ (a + e - 2 - 1 - 1) * (X - D) ^ 2 +
      4 * (a + e - 2) * X ^ (a + e - 2 - 1) * (X - D) + 2 * X ^ (a + e - 2))

variable {a e θ : ℝ}

/-- The derivative of `F` along a line. -/
theorem hasDerivAt_lyap_line {X₀ D₀ α β t₀ : ℝ} (hX : 0 < X₀ + t₀ * α) (hD : 0 < D₀ + t₀ * β) :
    HasDerivAt (fun t : ℝ => lyap a e θ (X₀ + t * α) (D₀ + t * β))
      (lyapX a e θ (X₀ + t₀ * α) (D₀ + t₀ * β) * α + lyapD a e θ (X₀ + t₀ * α) (D₀ + t₀ * β) * β) t₀ := by
  have hx : HasDerivAt (fun t : ℝ => X₀ + t * α) α t₀ := by
    simpa using ((hasDerivAt_id t₀).mul_const α).const_add X₀
  have hd : HasDerivAt (fun t : ℝ => D₀ + t * β) β t₀ := by
    simpa using ((hasDerivAt_id t₀).mul_const β).const_add D₀
  have h1 := hx.rpow_const (p := a) (Or.inl hX.ne')
  have h2 := hd.rpow_const (p := e) (Or.inl hD.ne')
  have h3 := hx.rpow_const (p := a + e - 2) (Or.inl hX.ne')
  have h4 := (hx.sub hd).pow 2
  have h := (h1.mul h2).add ((h3.mul h4).const_mul θ)
  refine h.congr_deriv ?_
  simp only [lyapX, lyapD, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
  norm_num
  ring

/-- The derivative of `∂_X F` in `X`. -/
theorem hasDerivAt_lyapX_line {X₀ D₀ α t₀ : ℝ} (hX : 0 < X₀ + t₀ * α) :
    HasDerivAt (fun t : ℝ => lyapX a e θ (X₀ + t * α) D₀) (lyapXX a e θ (X₀ + t₀ * α) D₀ * α) t₀ := by
  have hx : HasDerivAt (fun t : ℝ => X₀ + t * α) α t₀ := by
    simpa using ((hasDerivAt_id t₀).mul_const α).const_add X₀
  have h1 := hx.rpow_const (p := a - 1) (Or.inl hX.ne')
  have h2 := hx.rpow_const (p := a + e - 2 - 1) (Or.inl hX.ne')
  have h3 := hx.rpow_const (p := a + e - 2) (Or.inl hX.ne')
  have h4 := (hx.sub_const D₀).pow 2
  have h5 := hx.sub_const D₀
  have h := ((h1.const_mul a).mul_const (D₀ ^ e)).add
    ((((h2.const_mul (a + e - 2)).mul h4).add (h3.mul (h5.const_mul 2))).const_mul θ)
  refine h.congr_deriv ?_
  simp only [lyapXX, Nat.cast_ofNat]
  norm_num
  ring

/-- `F` is smooth on `X > 0`, `D > 0`. -/
theorem contDiffAt_lyap {n : WithTop ℕ∞} {p : ℝ × ℝ} (hX : 0 < p.1) (hD : 0 < p.2) :
    ContDiffAt ℝ n (fun q : ℝ × ℝ => lyap a e θ q.1 q.2) p := by
  have h1 : ContDiffAt ℝ n (fun q : ℝ × ℝ => q.1 ^ a) p :=
    contDiffAt_fst.rpow_const_of_ne hX.ne'
  have h2 : ContDiffAt ℝ n (fun q : ℝ × ℝ => q.2 ^ e) p :=
    contDiffAt_snd.rpow_const_of_ne hD.ne'
  have h3 : ContDiffAt ℝ n (fun q : ℝ × ℝ => q.1 ^ (a + e - 2)) p :=
    contDiffAt_fst.rpow_const_of_ne hX.ne'
  have h4 : ContDiffAt ℝ n (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) p :=
    (contDiffAt_fst.sub contDiffAt_snd).pow 2
  exact (h1.mul h2).add ((h3.mul h4).const_smul θ)

/-! ### The observable on the Itô coordinates -/

/-- The gap `X = g_t(x) − W_t` of a coordinate point `((g_t(x), V_t), B_t)`: along the single-seed evolution
`W = √k B − (ρ/2) V`. -/
def gapX (κ ρ : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := p.1.1 + ρ / 2 * p.1.2 - Real.sqrt κ * p.2

/-- The gap `D = g_t(x) − V_t`. -/
def gapD (p : (ℝ × ℝ) × ℝ) : ℝ := p.1.1 - p.1.2

/-- The Lyapunov observable `F(X, D)` on the coordinates. -/
def obs (κ ρ a e θ : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := lyap a e θ (gapX κ ρ p) (gapD p)

/-- The region `X > 0`, `D > 0`. -/
def region (κ ρ : ℝ) : Set ((ℝ × ℝ) × ℝ) := {p | 0 < gapX κ ρ p ∧ 0 < gapD p}

variable {κ ρ : ℝ}

theorem continuous_gapX : Continuous (gapX κ ρ) := by
  unfold gapX; fun_prop

theorem continuous_gapD : Continuous gapD := by
  unfold gapD; fun_prop

theorem isOpen_region : IsOpen (region κ ρ) :=
  (isOpen_lt continuous_const continuous_gapX).inter (isOpen_lt continuous_const continuous_gapD)

theorem contDiff_gap {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ => (gapX κ ρ p, gapD p)) := by
  unfold gapX gapD; fun_prop

theorem contDiffAt_obs {n : WithTop ℕ∞} {p : (ℝ × ℝ) × ℝ} (hp : p ∈ region κ ρ) :
    ContDiffAt ℝ n (obs κ ρ a e θ) p :=
  (contDiffAt_lyap (p := (gapX κ ρ p, gapD p)) hp.1 hp.2).comp p contDiff_gap.contDiffAt

theorem contDiffOn_obs {n : WithTop ℕ∞} : ContDiffOn ℝ n (obs κ ρ a e θ) (region κ ρ) :=
  fun _ hp => (contDiffAt_obs hp).contDiffWithinAt

theorem obs_line_fst (p : (ℝ × ℝ) × ℝ) (v : ℝ × ℝ) (t : ℝ) :
    obs κ ρ a e θ (p.1 + t • v, p.2) =
      lyap a e θ (gapX κ ρ p + t * (v.1 + ρ / 2 * v.2)) (gapD p + t * (v.1 - v.2)) := by
  simp only [obs, gapX, gapD, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring_nf

theorem obs_line_snd (p : (ℝ × ℝ) × ℝ) (y : ℝ) :
    obs κ ρ a e θ (p.1, y) =
      lyap a e θ ((p.1.1 + ρ / 2 * p.1.2) + y * (-Real.sqrt κ)) (gapD p + y * 0) := by
  simp only [obs, gapX, gapD]
  ring_nf

theorem partialSnd_obs {p : (ℝ × ℝ) × ℝ} (hp : p ∈ region κ ρ) :
    Ito.partialSnd (obs κ ρ a e θ) p = lyapX a e θ (gapX κ ρ p) (gapD p) * (-Real.sqrt κ) := by
  refine Ito.partialSnd_eq_of_hasDerivAt (contDiffAt_obs (n := 1) hp).differentiableAt_one ?_
  have hX : 0 < (p.1.1 + ρ / 2 * p.1.2) + p.2 * (-Real.sqrt κ) := by
    have := hp.1; simp only [gapX] at this; linarith
  have hD : 0 < gapD p + p.2 * 0 := by simpa using hp.2
  have h := hasDerivAt_lyap_line (a := a) (e := e) (θ := θ) hX hD
  have hfun : (fun y : ℝ => obs κ ρ a e θ (p.1, y)) = fun y : ℝ =>
      lyap a e θ ((p.1.1 + ρ / 2 * p.1.2) + y * (-Real.sqrt κ)) (gapD p + y * 0) :=
    funext fun y => obs_line_snd p y
  have hgX : (p.1.1 + ρ / 2 * p.1.2) + p.2 * (-Real.sqrt κ) = gapX κ ρ p := by
    simp only [gapX]; ring
  rw [hfun]
  refine h.congr_deriv ?_
  rw [hgX, mul_zero, add_zero, mul_zero, add_zero]

theorem partialSndSnd_obs (hκ : 0 ≤ κ) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ region κ ρ) :
    Ito.partialSndSnd (obs κ ρ a e θ) p = κ * lyapXX a e θ (gapX κ ρ p) (gapD p) := by
  set c := p.1.1 + ρ / 2 * p.1.2 with hc
  refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_obs hp)
    (g := fun y => lyapX a e θ (c + y * (-Real.sqrt κ)) (gapD p) * (-Real.sqrt κ)) ?_ ?_
  · have hopen : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : (ℝ × ℝ) × ℝ) ∈ region κ ρ := by
      have hc' : Continuous fun y : ℝ => ((p.1, y) : (ℝ × ℝ) × ℝ) := by fun_prop
      exact hc'.continuousAt.preimage_mem_nhds (isOpen_region.mem_nhds (by simpa using hp))
    filter_upwards [hopen] with y hy
    rw [partialSnd_obs hy]
    congr 2
    simp only [gapX, hc]; ring
  · have hX : 0 < c + p.2 * (-Real.sqrt κ) := by
      have := hp.1; simp only [gapX] at this; rw [hc]; linarith
    have h := (hasDerivAt_lyapX_line (a := a) (e := e) (θ := θ) (D₀ := gapD p) hX).mul_const
      (-Real.sqrt κ)
    have hgX : c + p.2 * (-Real.sqrt κ) = gapX κ ρ p := by simp only [gapX, hc]; ring
    refine h.congr_deriv ?_
    rw [hgX]
    have hs : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
    linear_combination (lyapXX a e θ (gapX κ ρ p) (gapD p)) * hs

/-- **The Itô generator of the observable**: `∂_Λ F · v + ½ ∂²_b F = F_X (v₁ + (ρ/2) v₂) + F_D (v₁ − v₂)
+ (k/2) F_XX`. -/
theorem itoGen_obs (hκ : 0 ≤ κ) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ region κ ρ) (v : ℝ × ℝ) :
    Ito.itoGen (obs κ ρ a e θ) p v =
      lyapX a e θ (gapX κ ρ p) (gapD p) * (v.1 + ρ / 2 * v.2) +
        lyapD a e θ (gapX κ ρ p) (gapD p) * (v.1 - v.2) +
          κ / 2 * lyapXX a e θ (gapX κ ρ p) (gapD p) := by
  have hfst : Ito.partialFst (obs κ ρ a e θ) p v =
      lyapX a e θ (gapX κ ρ p) (gapD p) * (v.1 + ρ / 2 * v.2) +
        lyapD a e θ (gapX κ ρ p) (gapD p) * (v.1 - v.2) := by
    refine Ito.partialFst_eq_of_hasDerivAt (contDiffAt_obs (n := 1) hp).differentiableAt_one ?_
    have hX : 0 < gapX κ ρ p + 0 * (v.1 + ρ / 2 * v.2) := by simpa using hp.1
    have hD : 0 < gapD p + 0 * (v.1 - v.2) := by simpa using hp.2
    have h := hasDerivAt_lyap_line (a := a) (e := e) (θ := θ) hX hD
    have hfun : (fun t : ℝ => obs κ ρ a e θ (p.1 + t • v, p.2)) = fun t : ℝ =>
        lyap a e θ (gapX κ ρ p + t * (v.1 + ρ / 2 * v.2)) (gapD p + t * (v.1 - v.2)) :=
      funext fun t => obs_line_fst p v t
    rw [hfun]
    refine h.congr_deriv ?_
    simp only [zero_mul, add_zero]
  rw [Ito.itoGen, hfst, partialSndSnd_obs hκ hp]
  ring

/-! ### The drift identity -/

/-- **The drift of `F` along the evolution.** With `v = (2/X, 2/R)`, `R = X − D > 0`, and `e = aρ/2`, the Itô drift is
`−c₁ X^a D^e / X² + θ X^{λ−2} (A (R/X)² + B (R/X) + C)` with `p = λ − 2`, `c₁ = a (k/2 − 2 − k a/2)`,
`A = 2p + k p (p − 1)/2`, `B = p (ρ + 2k)`, `C = 2ρ + 4 + k`. The reciprocal `1/R` cancels in the first term. -/
theorem drift_eq {X D : ℝ} (hX : 0 < X) (hD : 0 < D) (hR : 0 < X - D) :
    lyapX a (a * ρ / 2) θ X D * (2 / X + ρ / 2 * (2 / (X - D))) +
        lyapD a (a * ρ / 2) θ X D * (2 / X - 2 / (X - D)) +
          κ / 2 * lyapXX a (a * ρ / 2) θ X D =
      -(a * (κ / 2 - 2 - κ * a / 2)) * (X ^ a * D ^ (a * ρ / 2)) / X ^ 2 +
        θ * X ^ (a + a * ρ / 2 - 2) *
          ((2 * (a + a * ρ / 2 - 2) + κ * (a + a * ρ / 2 - 2) * (a + a * ρ / 2 - 2 - 1) / 2) *
              ((X - D) / X) ^ 2 +
            (a + a * ρ / 2 - 2) * (ρ + 2 * κ) * ((X - D) / X) + (2 * ρ + 4 + κ)) := by
  have hX0 := hX.ne'
  have hD0 := hD.ne'
  have hR0 := hR.ne'
  simp only [lyapX, lyapD, lyapXX, Real.rpow_sub_one hX0, Real.rpow_sub_one hD0]
  generalize X ^ a = Xa
  generalize D ^ (a * ρ / 2) = De
  generalize X ^ (a + a * ρ / 2 - 2) = Xp
  field_simp
  ring

/-- The first term in the variable `u = D/X`: `X^a D^e / X² = X^{λ−2} u^e`. -/
theorem rpow_mul_rpow_div_sq {X D : ℝ} (hX : 0 < X) (hD : 0 < D) :
    X ^ a * D ^ e / X ^ 2 = X ^ (a + e - 2) * (D / X) ^ e := by
  rw [Real.div_rpow hD.le hX.le, Real.rpow_sub hX, Real.rpow_add hX, Real.rpow_two]
  field_simp

/-! ### The constants -/

theorem one_min_le_rpow {u δ e : ℝ} (hδ : 0 < δ) (hδu : δ ≤ u) (hu1 : u ≤ 1) :
    min 1 (δ ^ e) ≤ u ^ e := by
  rcases le_or_gt 0 e with he | he
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow hδ.le hδu he)
  · exact (min_le_left _ _).trans
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hδ.trans_le hδu) hu1 he.le)

/-- **The constants of the drift and lower bounds.** If `c₁ > 0` and `P(1) = A + B + C < 0`, then for some
`θ, γ, m > 0`, on `0 < u ≤ 1`: `−c₁ u^e + θ P(1 − u) ≤ −γ` and `u^e + θ (1 − u)² ≥ m`. -/
theorem exists_drift_consts {c₁ e A B C : ℝ} (hc₁ : 0 < c₁) (hP : A + B + C < 0) :
    ∃ θ γ m : ℝ, 0 < θ ∧ 0 < γ ∧ 0 < m ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      -c₁ * u ^ e + θ * (A * (1 - u) ^ 2 + B * (1 - u) + C) ≤ -γ ∧
        m ≤ u ^ e + θ * (1 - u) ^ 2 := by
  set p₁ := -(A + B + C) with hp₁
  have hp₁0 : 0 < p₁ := by linarith
  set L := 2 * |A| + |B| + 1 with hL
  have hL0 : 0 < L := by positivity
  set δ := min 1 (p₁ / (2 * L)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδL : δ * L ≤ p₁ / 2 := by
    have : δ ≤ p₁ / (2 * L) := min_le_right _ _
    calc δ * L ≤ p₁ / (2 * L) * L := mul_le_mul_of_nonneg_right this hL0.le
      _ = p₁ / 2 := by field_simp
  set q := min 1 (δ ^ e) with hq
  have hq0 : 0 < q := lt_min one_pos (Real.rpow_pos_of_pos hδ0 e)
  set MP := |A| + |B| + |C| + 1 with hMP
  have hMP0 : 0 < MP := by positivity
  set θ := c₁ * q / (2 * MP) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθMP : θ * MP = c₁ * q / 2 := by rw [hθ]; field_simp
  set γ := min (θ * p₁ / 2) (c₁ * q / 2) with hγ
  have hγ0 : 0 < γ := lt_min (by positivity) (by positivity)
  set m := min (min 1 ((1 / 2 : ℝ) ^ e)) (θ / 4) with hm
  have hm0 : 0 < m :=
    lt_min (lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) e)) (by positivity)
  refine ⟨θ, γ, m, hθ0, hγ0, hm0, fun u hu hu1 => ⟨?_, ?_⟩⟩
  · have hue : 0 < u ^ e := Real.rpow_pos_of_pos hu e
    rcases le_or_gt u δ with huδ | huδ
    · -- near `u = 0`: `P(1 − u) ≤ −p₁/2`
      have hA2 : A * (u - 2) ≤ 2 * |A| := by
        rcases le_or_gt 0 A with hA | hA
        · nlinarith [abs_nonneg A]
        · rw [abs_of_neg hA]; nlinarith
      have hBu : -B ≤ |B| := neg_le_abs B
      have hPu : A * (1 - u) ^ 2 + B * (1 - u) + C ≤ -p₁ + u * L := by
        have : A * (1 - u) ^ 2 + B * (1 - u) + C = (A + B + C) + u * (A * (u - 2) - B) := by ring
        rw [this, hp₁, neg_neg]
        have : u * (A * (u - 2) - B) ≤ u * L := mul_le_mul_of_nonneg_left (by linarith) hu.le
        linarith
      have huL : u * L ≤ p₁ / 2 := (mul_le_mul_of_nonneg_right huδ hL0.le).trans hδL
      have h1 : θ * (A * (1 - u) ^ 2 + B * (1 - u) + C) ≤ θ * (-(p₁ / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hθ0.le
      have h2 : γ ≤ θ * p₁ / 2 := min_le_left _ _
      nlinarith
    · -- away from `u = 0`: `u^e ≥ q`
      have hqu : q ≤ u ^ e := one_min_le_rpow hδ0 huδ.le hu1
      have hPM : A * (1 - u) ^ 2 + B * (1 - u) + C ≤ MP := by
        have h1u : 0 ≤ 1 - u := by linarith
        have h1u' : 1 - u ≤ 1 := by linarith
        have hsq : (1 - u) ^ 2 ≤ 1 := by nlinarith
        have ha : A * (1 - u) ^ 2 ≤ |A| := by
          calc A * (1 - u) ^ 2 ≤ |A| * (1 - u) ^ 2 :=
                mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg _)
            _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left hsq (abs_nonneg A)
            _ = |A| := mul_one _
        have hb : B * (1 - u) ≤ |B| := by
          calc B * (1 - u) ≤ |B| * (1 - u) := mul_le_mul_of_nonneg_right (le_abs_self B) h1u
            _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h1u' (abs_nonneg B)
            _ = |B| := mul_one _
        have hc : C ≤ |C| := le_abs_self C
        linarith
      have h1 : θ * (A * (1 - u) ^ 2 + B * (1 - u) + C) ≤ θ * MP :=
        mul_le_mul_of_nonneg_left hPM hθ0.le
      have h2 : c₁ * q ≤ c₁ * u ^ e := mul_le_mul_of_nonneg_left hqu hc₁.le
      have h3 : γ ≤ c₁ * q / 2 := min_le_right _ _
      nlinarith
  · have hue : 0 < u ^ e := Real.rpow_pos_of_pos hu e
    rcases le_or_gt (1 / 2) u with hu2 | hu2
    · have h1 : min 1 ((1 / 2 : ℝ) ^ e) ≤ u ^ e := one_min_le_rpow (by norm_num) hu2 hu1
      have h2 : m ≤ min 1 ((1 / 2 : ℝ) ^ e) := min_le_left _ _
      have h3 : 0 ≤ θ * (1 - u) ^ 2 := by positivity
      linarith
    · have hsq : 1 / 4 ≤ (1 - u) ^ 2 := by nlinarith
      have h1 : θ / 4 ≤ θ * (1 - u) ^ 2 := by nlinarith
      have h2 : m ≤ θ / 4 := min_le_right _ _
      linarith

/-! ### The parameters -/

/-- A small exponent `a > 0`: `c₁ = a (c − k a/2) > 0`, `0 < λ = a (1 + ρ/2) < 1` and `λ (ρ − c + kλ/2) < 0`. -/
theorem exists_exponent (hκ : 4 < κ) (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) :
    ∃ a : ℝ, 0 < a ∧ 0 < a * (κ / 2 - 2 - κ * a / 2) ∧ 0 < a + a * ρ / 2 ∧ a + a * ρ / 2 < 1 ∧
      (a + a * ρ / 2) * (ρ - (κ / 2 - 2) + κ * (a + a * ρ / 2) / 2) < 0 := by
  have hc : 0 < κ / 2 - 2 := by linarith
  have hcρ : 0 < κ / 2 - 2 - ρ := by linarith
  have hρ2 : 0 < 1 + ρ / 2 := by linarith
  have hκ0 : 0 < κ := by linarith
  set a := min ((κ / 2 - 2) / κ) ((κ / 2 - 2 - ρ) / (κ * (1 + ρ / 2))) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have ha1 : a ≤ (κ / 2 - 2) / κ := min_le_left _ _
  have ha2 : a ≤ (κ / 2 - 2 - ρ) / (κ * (1 + ρ / 2)) := min_le_right _ _
  have hκa : a * κ ≤ κ / 2 - 2 := (le_div_iff₀ hκ0).1 ha1
  have hkl : a * (κ * (1 + ρ / 2)) ≤ κ / 2 - 2 - ρ := (le_div_iff₀ (by positivity)).1 ha2
  have hl : a + a * ρ / 2 = a * (1 + ρ / 2) := by ring
  refine ⟨a, ha0, ?_, ?_, ?_, ?_⟩
  · have : 0 < κ / 2 - 2 - κ * a / 2 := by linarith
    positivity
  · rw [hl]; positivity
  · rw [hl]
    have : κ * (a * (1 + ρ / 2)) < κ * 1 := by nlinarith
    exact lt_of_mul_lt_mul_left this hκ0.le
  · rw [hl]
    have h1 : 0 < a * (1 + ρ / 2) := by positivity
    have h2 : ρ - (κ / 2 - 2) + κ * (a * (1 + ρ / 2)) / 2 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg h1 h2

/-- `F` in the variable `u = D/X`: `F = X^λ (u^e + θ (1 − u)²)`. -/
theorem lyap_eq {X D : ℝ} (hX : 0 < X) (hD : 0 < D) :
    lyap a e θ X D = X ^ (a + e - 2) * X ^ 2 * ((D / X) ^ e + θ * (1 - D / X) ^ 2) := by
  have h1 : X ^ a * D ^ e = X ^ (a + e - 2) * X ^ 2 * (D / X) ^ e := by
    have h := rpow_mul_rpow_div_sq (a := a) (e := e) hX hD
    rw [div_eq_iff (by positivity)] at h
    rw [h]; ring
  rw [lyap, h1]
  field_simp

theorem rpow_sub_two_mul_sq {X : ℝ} (hX : 0 < X) (l : ℝ) : X ^ (l - 2) * X ^ 2 = X ^ l := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hX]; norm_num

/-- **The Lyapunov parameters.** For `k > 4` and `−2 < ρ < k/2 − 2` there are `a, θ, γ, m` with
`0 < λ = a + aρ/2 < 1` such that, with `F = obs k ρ a (aρ/2) θ`:
* the drift along `v = (2/X, 2/R)` (`R = X − D > 0`) is at most `−γ X^{λ−2}`;
* `F ≥ m X^λ` when `0 < D ≤ X`;
* `F ≥ 0` on the region. -/
theorem exists_lyapParams (hκ : 4 < κ) (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) :
    ∃ a θ γ m : ℝ, 0 < a + a * ρ / 2 ∧ a + a * ρ / 2 < 1 ∧ 0 < θ ∧ 0 < γ ∧ 0 < m ∧
      (∀ p ∈ region κ ρ, 0 < gapX κ ρ p - gapD p →
        Ito.itoGen (obs κ ρ a (a * ρ / 2) θ) p (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) ≤
          -γ * gapX κ ρ p ^ (a + a * ρ / 2 - 2)) ∧
      (∀ p ∈ region κ ρ, gapD p ≤ gapX κ ρ p →
        m * gapX κ ρ p ^ (a + a * ρ / 2) ≤ obs κ ρ a (a * ρ / 2) θ p) ∧
      (∀ p ∈ region κ ρ, 0 ≤ obs κ ρ a (a * ρ / 2) θ p) := by
  obtain ⟨a, ha0, hc₁, hl0, hl1, hP1⟩ := exists_exponent hκ hρ hρc
  have hABC : (2 * (a + a * ρ / 2 - 2) + κ * (a + a * ρ / 2 - 2) * (a + a * ρ / 2 - 2 - 1) / 2) +
      (a + a * ρ / 2 - 2) * (ρ + 2 * κ) + (2 * ρ + 4 + κ) < 0 := by
    have h : (2 * (a + a * ρ / 2 - 2) + κ * (a + a * ρ / 2 - 2) * (a + a * ρ / 2 - 2 - 1) / 2) +
        (a + a * ρ / 2 - 2) * (ρ + 2 * κ) + (2 * ρ + 4 + κ) =
        (a + a * ρ / 2) * (ρ - (κ / 2 - 2) + κ * (a + a * ρ / 2) / 2) := by ring
    rw [h]; exact hP1
  obtain ⟨θ, γ, m, hθ, hγ, hm, hbd⟩ := exists_drift_consts (e := a * ρ / 2) hc₁ hABC
  refine ⟨a, θ, γ, m, hl0, hl1, hθ, hγ, hm, fun p hp hR => ?_, fun p hp hDX => ?_, fun p hp => ?_⟩
  · have hX : 0 < gapX κ ρ p := hp.1
    have hD : 0 < gapD p := hp.2
    rw [itoGen_obs (by linarith) hp]
    dsimp only
    rw [drift_eq hX hD hR, mul_div_assoc, rpow_mul_rpow_div_sq hX hD]
    have hu : 0 < gapD p / gapX κ ρ p := div_pos hD hX
    have hu1 : gapD p / gapX κ ρ p ≤ 1 := (div_le_one hX).2 (by linarith)
    have hRX : (gapX κ ρ p - gapD p) / gapX κ ρ p = 1 - gapD p / gapX κ ρ p := by
      field_simp
    rw [hRX]
    have h1 := (hbd _ hu hu1).1
    have hXp : 0 < gapX κ ρ p ^ (a + a * ρ / 2 - 2) := Real.rpow_pos_of_pos hX _
    have h2 := mul_le_mul_of_nonneg_left h1 hXp.le
    linarith
  · have hX : 0 < gapX κ ρ p := hp.1
    have hD : 0 < gapD p := hp.2
    have hu : 0 < gapD p / gapX κ ρ p := div_pos hD hX
    have hu1 : gapD p / gapX κ ρ p ≤ 1 := (div_le_one hX).2 hDX
    have h1 := (hbd _ hu hu1).2
    rw [obs, lyap_eq hX hD, rpow_sub_two_mul_sq hX, mul_comm m]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hX _).le
  · have hX : 0 < gapX κ ρ p := hp.1
    have hD : 0 < gapD p := hp.2
    rw [obs, lyap]
    have h1 : 0 ≤ gapX κ ρ p ^ a := (Real.rpow_pos_of_pos hX _).le
    have h2 : 0 ≤ gapD p ^ (a * ρ / 2) := (Real.rpow_pos_of_pos hD _).le
    have h3 : 0 ≤ gapX κ ρ p ^ (a + a * ρ / 2 - 2) := (Real.rpow_pos_of_pos hX _).le
    positivity

/-- **The initial value**: at `X = D = x`, `F = x^λ`. -/
theorem lyap_self {x : ℝ} (hx : 0 < x) : lyap a e θ x x = x ^ (a + e) := by
  rw [lyap, sub_self, Real.rpow_add hx]; ring

end InteractingSLE.LP.LP2
