import HigherDimLQGMetric.DGZ.CompareDisc
import HigherDimLQGMetric.DGZ.Cover

/-!
# DGZ Proposition 5.13, first inequality (packet L4c)

Source: [2] Prop 5.13 (TeX l. 2702–2716), first inequality only, as in MA7 Details (a) **D-5.13**
and blueprint Part C `r2:prop:513`.

**Statement** (`prop513`, deterministic, path form). On `𝒥₁ ∩ 𝒥₂′` (and DGZ's parameter regime,
written as explicit numerical conditions), every piecewise `C¹` path `P` in `B₂(0)` from `x` to `y`
with `y ∉ B̄_{10 s_m}(x)` yields a piecewise `C¹` path `γ'` in `B₂(0)` from `B̄_{10 s_m}(x)` to
`B̄_{10 s_m}(y)` with `len(γ'; h_n) ≤ C 2^{(1-ξQ+ε)k} len(P; h_{n+k})`, `C = prop513Const d ξ L`
(`= 2·4√d·41^d e^{2ξ(L+1)}·L`). The set-distance form of [2] (`prop513_setDist`):
`D_n(B̄_{10s_m}(x), B̄_{10s_m}(y); B₂(0)) ≤ C 2^{(1-ξQ+ε)k} D_{n+k}(x, y; B₂(0))`.

**Proof** (D-5.13). L4b1's `exists_bypassCover` gives the cover `𝒳` with (A″), (C) outside
`𝒰`; Lemma 5.12(1) (`lemma512`, `s = s₀ = 2^{-n}`, `T = L⁻¹ 2^{-n-(1-ξQ+ε)k}`, so
`s₀/T = L 2^{(1-ξQ+ε)k}`) gives the polygon `γ̃`; L4b2's `bypass` gives `γ'` with
`len(γ') ≤ 2 len_{B₂(0)\𝒰}(γ̃)`.

Two adaptations (beyond MA7, both bookkeeping): `bypass` needs `40R s_j ≤ s_{j+1}` for **all** `j`,
while `s_j = 2^{-(n-a_j)}` is constant `= 1` once `a_j ≥ n`; the scales are therefore continued
geometrically beyond `m` (`cmpScale`), and the cover is restricted to the levels `1 ≤ j < m`
(`cmp_isBypassCover_restrict`); neither changes `𝒰` (`cmp_coverU_congr`). Lemma 5.12(1) needs `𝒰` to
be saturated on the lattice `s₀ ℤ^d` (`cmp_coverU_saturated`, D-5.12 (a)): the centres of `𝒳_j`
are lattice points of `s_j ℤ^d ⊆ s₀ ℤ^d` and `R s_j ∈ s₀ ℕ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## Scales and lattices -/

/-- `s_j = 2^{a_j} s₀` when `a₀ = 0` and `a_j ≤ n`. -/
theorem cmp_s_eq (p : NiceParams) (ha0 : p.a 0 = 0) {j : ℕ} (hj : p.a j ≤ p.n) :
    p.s j = (2 : ℝ) ^ p.a j * p.s 0 := by
  unfold NiceParams.s
  rw [ha0, Nat.sub_zero]
  conv_rhs => rw [show p.n = (p.n - p.a j) + p.a j by omega, pow_add]
  rw [mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]

/-- The lattice `s_j ℤ^d` inside `s₀ ℤ^d`. -/
theorem cmp_latPt_s_eq (p : NiceParams) (ha0 : p.a 0 = 0) {j : ℕ} (hj : p.a j ≤ p.n)
    (u : Zd d) : latPt (p.s j) u = latPt (p.s 0) ((2 : ℤ) ^ p.a j • u) := by
  ext k
  rw [latPt_apply, latPt_apply, cmp_s_eq p ha0 hj]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  ring

/-- **D-5.12 (a)**: the cover `𝒰` is saturated on the lattice `s₀ ℤ^d`: a lattice point of `𝒰`
carries its open `s₀`-box inside `𝒰`. -/
theorem cmp_coverU_saturated (p : NiceParams) (ha0 : p.a 0 = 0) (hmono : Monotone p.a)
    {m : ℕ} (ham : p.a m ≤ p.n) {R : ℕ} {X : ℕ → Set (Rd d)}
    (hX : ∀ j, ∀ z ∈ X j, ∃ u : Zd d, z = latPt (p.s j) u) (x : Zd d)
    (hx : latPt (p.s 0) x ∈ coverU (R : ℝ) m p.s X) :
    obox (latPt (p.s 0) x) (p.s 0) ⊆ coverU (R : ℝ) m p.s X := by
  obtain ⟨j, hj1, hjm, z, hz, hxz⟩ := mem_coverU_iff.1 hx
  obtain ⟨u, rfl⟩ := hX j z hz
  have hjn : p.a j ≤ p.n := (hmono hjm.le).trans ham
  have hs0 : 0 < p.s 0 := p.s_pos 0
  set c : Zd d := (2 : ℤ) ^ p.a j • u with hcdef
  set N : ℕ := R * 2 ^ p.a j with hNdef
  have hRs : (R : ℝ) * p.s j = p.s 0 * N := by
    rw [cmp_s_eq p ha0 hjn, hNdef]
    push_cast
    ring
  have hlat := cmp_latPt_s_eq p ha0 hjn u
  rw [hlat, hRs] at hxz
  have hwi : WithinInf ((N : ℤ) - 1) x c := by
    intro i
    have h1 := hxz i
    rw [latPt_apply, latPt_apply, ← mul_sub, abs_mul, abs_of_pos hs0] at h1
    have h2 : |((x i - c i : ℤ) : ℝ)| < N := by
      push_cast
      exact lt_of_mul_lt_mul_left h1 hs0.le
    have h3 : |x i - c i| < (N : ℤ) := by exact_mod_cast h2
    omega
  intro v hv
  refine mem_coverU_iff.2 ⟨j, hj1, hjm, latPt (p.s j) u, hz, ?_⟩
  rw [hlat, hRs]
  exact obox_latPt_subset hs0 hwi hv

/-- The cover changes only through the levels `1 ≤ j < m`. -/
theorem cmp_coverU_congr {R : ℝ} {m : ℕ} {s s' : ℕ → ℝ} {X X' : ℕ → Set (Rd d)}
    (hs : ∀ j, 1 ≤ j → j < m → s' j = s j) (hX : ∀ j, 1 ≤ j → j < m → X' j = X j) :
    coverU R m s' X' = coverU R m s X := by
  ext v
  simp only [mem_coverU_iff]
  constructor
  · rintro ⟨j, hj1, hjm, z, hz, hv⟩
    rw [hX j hj1 hjm] at hz
    rw [hs j hj1 hjm] at hv
    exact ⟨j, hj1, hjm, z, hz, hv⟩
  · rintro ⟨j, hj1, hjm, z, hz, hv⟩
    rw [← hX j hj1 hjm] at hz
    rw [← hs j hj1 hjm] at hv
    exact ⟨j, hj1, hjm, z, hz, hv⟩

/-- A bypass cover restricted to the levels `1 ≤ j < m`, with scales changed only above `m`. -/
theorem cmp_isBypassCover_restrict {ξ : ℝ} {φ : Rd d → ℝ} {R : ℝ} {m : ℕ} {s s' w : ℕ → ℝ}
    {X : ℕ → Set (Rd d)} (h : IsBypassCover ξ φ R m s w X) (hs : ∀ j, j ≤ m → s' j = s j) :
    IsBypassCover ξ φ R m s' w (fun j => if 1 ≤ j ∧ j < m then X j else ∅) where
  finite j := by
    split_ifs
    · exact h.finite j
    · exact finite_empty
  sub j := by
    split_ifs
    · exact h.sub j
    · exact empty_subset _
  sep j z hz z' hz' hne := by
    split_ifs at hz hz' with hj
    · rw [hs (j + 1) (by omega)]
      exact h.sep j z hz z' hz' hne
    · exact absurd hz (notMem_empty z)
  ctrl j hj1 hjm z hz := by
    rw [ite_eq_left ⟨hj1, hjm⟩] at hz
    rw [hs j hjm.le, hs (j + 1) (by omega)]
    exact h.ctrl j hj1 hjm z hz

/-- The scales `s_0, …, s_m`, continued geometrically (ratio `40R`) beyond `m`. -/
def cmpScale (s : ℕ → ℝ) (m : ℕ) (R : ℝ) (j : ℕ) : ℝ :=
  if j ≤ m then s j else (40 * R) ^ (j - m) * s m

theorem cmpScale_of_le {s : ℕ → ℝ} {m : ℕ} {R : ℝ} {j : ℕ} (hj : j ≤ m) :
    cmpScale s m R j = s j := by
  unfold cmpScale
  rw [ite_eq_left hj]

theorem cmpScale_pos {s : ℕ → ℝ} {m : ℕ} {R : ℝ} (hs : ∀ j, 0 < s j) (hR : 0 < R) (j : ℕ) :
    0 < cmpScale s m R j := by
  unfold cmpScale
  split_ifs
  · exact hs j
  · exact mul_pos (pow_pos (by linarith) _) (hs m)

theorem cmpScale_gap {s : ℕ → ℝ} {m : ℕ} {R : ℝ}
    (hgap : ∀ j, j < m → 40 * R * s j ≤ s (j + 1)) (j : ℕ) :
    40 * R * cmpScale s m R j ≤ cmpScale s m R (j + 1) := by
  unfold cmpScale
  rcases Nat.lt_or_ge j m with hj | hj
  · rw [ite_eq_left hj.le, ite_eq_left (by omega : j + 1 ≤ m)]
    exact hgap j hj
  · rcases hj.eq_or_lt with hjm | hjm
    · subst hjm
      rw [ite_eq_left le_rfl, ite_eq_right (by omega), Nat.add_sub_cancel_left, pow_one]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        show j + 1 - m = (j - m) + 1 by omega, pow_succ]
      ring_nf
      exact le_rfl

/-- `s₀ / T = L 2^c` for `s₀ = 2^{-n}`, `T = L⁻¹ 2^{-n-c}`. -/
theorem cmp_s0_div (n : ℕ) {L : ℝ} (hL : 0 < L) (c : ℝ) :
    (2 : ℝ)⁻¹ ^ n / (L⁻¹ * (2 : ℝ) ^ (-(n : ℝ) - c)) = L * (2 : ℝ) ^ c := by
  have h2 : (0 : ℝ) < 2 := two_pos
  rw [Real.rpow_sub h2, Real.rpow_neg h2.le, Real.rpow_natCast, inv_pow]
  have hc : 0 < (2 : ℝ) ^ c := Real.rpow_pos_of_pos h2 c
  have hn : 0 < (2 : ℝ) ^ n := pow_pos h2 n
  field_simp

/-! ## Proposition 5.13, first inequality -/

/-- The constant of Proposition 5.13 (first inequality) in the form proved here:
`2 · lemma512Const · L`. -/
def prop513Const (d : ℕ) (ξ L : ℝ) : ℝ := 2 * lemma512Const d ξ L * L

/-- **DGZ Proposition 5.13, first inequality, path form** (MA7 D-5.13; blueprint
`r2:prop:513`), deterministic: on `𝒥₁ ∩ 𝒥₂′` and under the numerical conditions of DGZ's
parameter regime, a piecewise `C¹` path `P` in `B₂(0)` from `x` to `y` (`y ∉ B̄_{10 s_m}(x)`) is
replaced by a piecewise `C¹` path `γ'` in `B₂(0)` from `B̄_{10 s_m}(x)` to `B̄_{10 s_m}(y)` with
`len(γ'; h_n) ≤ prop513Const · 2^{(1-ξQ+ε)k} len(P; h_{n+k})`. -/
theorem prop513 (hd : 2 ≤ d) {ξ Q θ : ℝ} (hξ : 0 < ξ) (hθ : 0 < θ) {R : ℕ} (hR : 100 ≤ R) :
    ∃ N₀ : ℕ, ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) → ∀ m : ℕ, 1 ≤ m →
      ∀ {lam : ℝ}, 0 ≤ lam → lam ≤ 3 → 2 ≤ p.K → p.a = dgzSeq lam p.K →
      ∀ {g : ℕ}, 3 ≤ g → (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4 →
      p.a m ≤ p.n → N₀ ≤ p.a 1 → 4 * R ≤ 2 ^ (p.n - p.a m + 1) →
      (∀ j, j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1)) →
      6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) →
      Real.log 2 ≤ lam * (p.K : ℝ) ^ 3 / 3 → 8 * (41 : ℝ) ^ d ≤ Real.exp ((p.K : ℝ) ^ 3) →
      p.s m ≤ 1 / 100 → 0 < p.L →
      EventJ1 p H m → EventJ2' p H m →
      ∀ {P : ℝ → Rd d} {x y : Rd d}, IsPcwC1Path P x y → MapsTo P (Icc 0 1) (obox (0 : Rd d) 2) →
        y ∉ cbox x (10 * p.s m) →
        ∃ γ' : ℝ → Rd d, IsPcwC1Path γ' (γ' 0) (γ' 1) ∧
          MapsTo γ' (Icc 0 1) (obox (0 : Rd d) 2) ∧
          γ' 0 ∈ cbox x (10 * p.s m) ∧ γ' 1 ∈ cbox y (10 * p.s m) ∧
          lfppLength ξ (H p.n) γ' ≤
            prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
              lfppLength ξ (H (p.n + p.k)) P := by
  obtain ⟨N₀, hcov⟩ := exists_bypassCover hd hξ hθ (by omega : 1 ≤ R)
  refine ⟨N₀, ?_⟩
  intro p hpξ hpQ hpθ hpR H hc m hm lam hlam0 hlam3 hK ha g hg3 hg ham hN hCube hgap hKm hr hc8
    hsm hL hJ1 hJ2 P x y hP hPB hxy
  obtain ⟨X, hXlat, hXcov, hsite⟩ := hcov p hpξ hpQ hpθ hpR H hc m hm hlam0 hK ha hg3 hg ham hN
    hCube (fun j _ hjm => hgap j hjm) hKm hJ1 hJ2
  have hmono : Monotone p.a := by
    rw [ha]
    exact dgzSeq_monotone hlam0 (by omega)
  have ha0 : p.a 0 = 0 := by
    rw [ha]
    rfl
  have hs0 : 0 < p.s 0 := p.s_pos 0
  have hRpos : (0 : ℝ) < p.R := by
    rw [hpR]
    exact_mod_cast (by omega : 0 < R)
  -- Lemma 5.12(1) for `P`
  set U : Set (Rd d) := coverU (p.R : ℝ) m p.s X with hUdef
  set T : ℝ := p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - ξ * Q + p.ε) * p.k) with hTdef
  have hT : 0 < T := mul_pos (inv_pos.2 hL) (Real.rpow_pos_of_pos two_pos _)
  have hUo : IsOpen U :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
      HigherDimLFPP.DGZ.isOpen_obox _ _
  have hUsat : ∀ x : Zd d, latPt (p.s 0) x ∈ U → obox (latPt (p.s 0) x) (p.s 0) ⊆ U :=
    cmp_coverU_saturated p ha0 hmono ham hXlat
  have hA : ∀ w : Zd d, obox (latPt (p.s 0) w) (p.s 0) ⊆ obox (0 : Rd d) 2 →
      latPt (p.s 0) w ∉ U →
      (∀ v ∈ cbox (latPt (p.s 0) w) (2 * p.s 0), ∀ v' ∈ cbox (latPt (p.s 0) w) (2 * p.s 0),
        |H p.n v - H p.n v'| ≤ p.L + 1) ∧
      T < acrossDist ξ (fun v => H (p.n + p.k) v - H p.n v) (latPt (p.s 0) w) (2 * p.s 0)
        (p.s 0) := by
    intro w h1 h2
    have := hsite w h1 h2
    rw [hpξ, hpQ] at this
    exact this
  have hN1 : 1 ≤ 2 ^ (p.n - p.a 0 + 1) := Nat.one_le_two_pow
  have hsN : p.s 0 * ((2 ^ (p.n - p.a 0 + 1) : ℕ) : ℝ) = 2 := p.s_mul_two_pow 0
  have hsm0 : p.s 0 ≤ p.s m := p.s_le_s hmono (Nat.zero_le m)
  have hxy4 : y ∉ cbox x (4 * p.s 0) := fun h => hxy fun i => (h i).trans (by linarith)
  obtain ⟨γt, hγt, hγtB, hγtlen⟩ := lemma512 hξ.le (hc p.n) (hc (p.n + p.k)) hs0 hN1 hsN hUo
    hUsat hT hA hP hPB hxy4
  -- the bypass
  set s' : ℕ → ℝ := cmpScale p.s m (p.R : ℝ) with hs'def
  set X' : ℕ → Set (Rd d) := fun j => if 1 ≤ j ∧ j < m then X j else ∅ with hX'def
  have hs'le : ∀ j, j ≤ m → s' j = p.s j := fun j hj => cmpScale_of_le hj
  have hXcov' : IsBypassCover ξ (H p.n) (p.R : ℝ) m s' (coverWeight p) X' := by
    have := cmp_isBypassCover_restrict hXcov hs'le
    rwa [hpξ] at this
  have hU' : coverU (p.R : ℝ) m s' X' = U :=
    cmp_coverU_congr (fun j _ hjm => hs'le j hjm.le) fun j hj1 hjm => by
      simp only [hX'def]
      rw [ite_eq_left ⟨hj1, hjm⟩]
  have hweights : (∑ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * coverWeight p j) ≤ 1 / 2 := by
    unfold coverWeight
    rw [ha]
    exact dgz_weights_le hlam0 hlam3 (by omega : 1 ≤ p.K) hr d hc8 m
  have hR100 : (100 : ℝ) ≤ p.R := by
    rw [hpR]
    exact_mod_cast hR
  have hs'm : s' m = p.s m := hs'le m le_rfl
  have hγt0 : γt 0 = x := hγt.source
  have hγt1 : γt 1 = y := hγt.target
  obtain ⟨γ', hγ', hγ'B, hγ'0, hγ'1, hγ'len⟩ := bypass d hd ξ (H p.n) (hc p.n) (p.R : ℝ) m s'
    (coverWeight p) X' hR100 (cmpScale_pos (fun j => p.s_pos j) hRpos)
    (cmpScale_gap hgap) (fun j => (Real.exp_pos _).le) hweights (by rw [hs'm]; exact hsm)
    hXcov' γt (by rw [hγt0, hγt1]; exact hγt) hγtB (by rw [hγt0, hγt1, hs'm]; exact hxy)
  rw [hγt0, hs'm] at hγ'0
  rw [hγt1, hs'm] at hγ'1
  rw [hU'] at hγ'len
  refine ⟨γ', hγ', fun t ht => (hγ'B ht).1, hγ'0, hγ'1, ?_⟩
  have hs0eq : p.s 0 = (2 : ℝ)⁻¹ ^ p.n := by
    unfold NiceParams.s
    rw [ha0, Nat.sub_zero]
  have hratio : p.s 0 / T = p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) := by
    rw [hs0eq, hTdef]
    exact cmp_s0_div p.n hL _
  calc lfppLength ξ (H p.n) γ' ≤ 2 * lfppLengthIn ξ (H p.n) γt (obox 0 2 \ U) := hγ'len
    _ ≤ 2 * (lemma512Const d ξ p.L * (p.s 0 / T) * lfppLength ξ (H (p.n + p.k)) P) :=
        mul_le_mul_of_nonneg_left hγtlen (by norm_num)
    _ = prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
          lfppLength ξ (H (p.n + p.k)) P := by
        rw [hratio, prop513Const]
        ring

theorem prop513Const_nonneg (d : ℕ) (ξ : ℝ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ prop513Const d ξ L :=
  mul_nonneg (mul_nonneg (by norm_num) (lemma512Const_nonneg d ξ L)) hL

/-- **DGZ Proposition 5.13, first inequality, the set-distance form of [2]** (blueprint
`r2:prop:513`): on `𝒥₁ ∩ 𝒥₂′`, for `x, y ∈ B₂(0)` with `y ∉ B̄_{10 s_m}(x)`,
`D_n(B̄_{10 s_m}(x), B̄_{10 s_m}(y); B₂(0)) ≤ C 2^{(1-ξQ+ε)k} D_{n+k}(x, y; B₂(0))`. -/
theorem prop513_setDist (hd : 2 ≤ d) {ξ Q θ : ℝ} (hξ : 0 < ξ) (hθ : 0 < θ) {R : ℕ}
    (hR : 100 ≤ R) :
    ∃ N₀ : ℕ, ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) → ∀ m : ℕ, 1 ≤ m →
      ∀ {lam : ℝ}, 0 ≤ lam → lam ≤ 3 → 2 ≤ p.K → p.a = dgzSeq lam p.K →
      ∀ {g : ℕ}, 3 ≤ g → (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4 →
      p.a m ≤ p.n → N₀ ≤ p.a 1 → 4 * R ≤ 2 ^ (p.n - p.a m + 1) →
      (∀ j, j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1)) →
      6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) →
      Real.log 2 ≤ lam * (p.K : ℝ) ^ 3 / 3 → 8 * (41 : ℝ) ^ d ≤ Real.exp ((p.K : ℝ) ^ 3) →
      p.s m ≤ 1 / 100 → 0 < p.L →
      EventJ1 p H m → EventJ2' p H m →
      ∀ {x y : Rd d}, x ∈ obox (0 : Rd d) 2 → y ∈ obox (0 : Rd d) 2 →
        y ∉ cbox x (10 * p.s m) →
        lfppSetDist ξ (H p.n) (obox (0 : Rd d) 2) (cbox x (10 * p.s m)) (cbox y (10 * p.s m)) ≤
          prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
            lfppDistOn ξ (H (p.n + p.k)) (obox (0 : Rd d) 2) x y := by
  obtain ⟨N₀, h⟩ := prop513 hd hξ hθ hR
  refine ⟨N₀, fun p hpξ hpQ hpθ hpR H hc m hm lam hlam0 hlam3 hK ha g hg3 hg ham hN hCube hgap
    hKm hr hc8 hsm hL hJ1 hJ2 x y hx hy hxy => ?_⟩
  have hC : 0 ≤ prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) :=
    mul_nonneg (prop513Const_nonneg d ξ hL.le) (Real.rpow_pos_of_pos two_pos _).le
  refine le_mul_lfppDistOn_of_forall
    (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 2) hx hy) hC fun P hP hPB => ?_
  obtain ⟨γ', hγ', hγ'B, hγ'0, hγ'1, hlen⟩ := h p hpξ hpQ hpθ hpR H hc m hm hlam0 hlam3 hK ha
    hg3 hg ham hN hCube hgap hKm hr hc8 hsm hL hJ1 hJ2 hP hPB hxy
  calc lfppSetDist ξ (H p.n) (obox (0 : Rd d) 2) (cbox x (10 * p.s m)) (cbox y (10 * p.s m))
      ≤ lfppDistOn ξ (H p.n) (obox (0 : Rd d) 2) (γ' 0) (γ' 1) := lfppSetDist_le hγ'0 hγ'1
    _ ≤ lfppLength ξ (H p.n) γ' := lfppDistOn_le_lfppLength hγ' hγ'B
    _ ≤ _ := hlen

end DGZ

end HigherDimLQGMetric
