import InteractingSLE.Spec.Supplement.LP2Loc

/-!
# Lemma LP2: finite swallowing of a passive point

Packet PROVE-LP16. Specification §6.2, Lemma LP2 (`source/spec/p433-480.md` L1124–L1160,
`source/spec/p481-528.md` L1–L18): **for `k > 4` and `−2 < ρ < c = k/2 − 2`, in the canonical single-right-seed
driving law every fixed passive point `x > 0` is swallowed at a finite time almost surely** (`lp2`).

Proof (a Lyapunov argument replacing the source's one-dimensional diffusion theory; see `LP2Calc.lean`). Let
`F = X^a D^{aρ/2} + θ X^{λ−2} (X − D)²` be the observable of `exists_lyapParams` (`F ≥ m X^λ` when `0 < D ≤ X`, Itô
drift `≤ −γ X^{λ−2}`), and let `σ_n` be the localizing times of `LP2Loc.lean` at upper level `M > x`. By
`lyap_markov`, `P(σ_n ≥ T) ≤ x^λ/(γ M^{λ−2} T)` and `P(F(σ_n) ≥ m M^λ) ≤ x^λ/(m M^λ)` for every large `n`.

On a good path along which `x` is never swallowed, fix `T`. On `[0, T]` the gaps `X, D` are bounded below
(`vR_lt_of_isForwardSol`), so for large `n` the tamed coordinates are the true ones and the path stays inside the
level-`n` region. Either `X < M` on `[0, T]`, and then `σ_n ≥ T` (`le_lyapStop`), or `X` reaches `M` before `T`, and
then the path exits through `X = M`, so `F(σ_n) ≥ m M^λ` (`eventually_of_alive`). Hence the never-swallowed paths
have probability at most `x^λ/(γ M^{λ−2} T) + x^λ/(m M^λ)`; letting `T`, then `M`, grow gives `0`. The lifetime is
infinite almost surely (`Sec7.ae_lifetime_eq_top_oneForceRight`), so the swallowing time is before `ζ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.LP.LP2

open QuantumZipper QuantumZipper.RS

section Path

open scoped Classical

variable {Ω : Type*} {κ ρ : ℝ} {xL ρL : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {x M : ℝ} {n : ℕ}

/-- A path that avoids the exit set on `[0, T]`, `T ≤ n`, has `T ≤ σ_n`. -/
theorem le_lyapStop {ω : Ω} (hω : ω ∈ G) (hc : Continuous (lyapPath G W VR B x n · ω)) {T : ℝ≥0}
    (hTn : (T : ℝ) ≤ n)
    (havoid : ∀ t ∈ Icc 0 T, lyapPath G W VR B x n t ω ∉ Zhan.exitSet (region κ ρ) (gapX κ ρ) M n) :
    T ≤ lyapStop κ ρ G W VR B x M n ω := by
  simp only [lyapStop, Zhan.locStop, hω, ↓reduceIte]
  by_contra hcon
  push Not at hcon
  have hTn' : T ≤ (n : ℝ≥0) := by exact_mod_cast hTn
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) n,
      lyapPath G W VR B x n j ω ∈ Zhan.exitSet (region κ ρ) (gapX κ ρ) M n := by
    by_contra hno
    have h : hittingBtwn (Zhan.pathX (coordΛ G W VR (1 / ((n : ℝ) + 1)) x) (modProc G B))
        (Zhan.exitSet (region κ ρ) (gapX κ ρ) M n) 0 n ω = n := by
      simp only [hittingBtwn, hno, ↓reduceIte]
    rw [h] at hcon
    exact absurd hTn' (not_le.2 hcon)
  have hmem := Zhan.mem_of_hittingBtwn hc (Zhan.isClosed_exitSet continuous_gapX.continuousOn) hex
  exact havoid _ ⟨zero_le, hcon.le⟩ hmem

variable (hgood : ∀ ω ∈ G, IsGood κ ρ xL ρL W VL VR B ζ ω)
include hgood

/-- With the taming level below the true gap, the level-`n` coordinates are the true ones. -/
theorem lyapPath_eq_of_isForwardSol {ω : Ω} (hω : ω ∈ G) {T : ℝ≥0} {u : ℝ → ℂ}
    (hu : IsForwardSol (fun t : ℝ => W t.toNNReal ω) (x : ℂ) T u) {c₀ : ℝ}
    (hc₀ : ∀ t ∈ Icc (0 : ℝ) T, c₀ ≤ (u t).re) (hn : 1 / ((n : ℝ) + 1) ≤ c₀) {t : ℝ≥0}
    (ht : t ∈ Icc (0 : ℝ≥0) T) :
    lyapPath G W VR B x n t ω = (((u t).re + W t ω, VR 0 t ω), B t ω) := by
  have hW : Continuous fun t : ℝ => W t.toNNReal ω :=
    (hgood ω hω).continuous_w.comp continuous_real_toNNReal
  have hW0 : (fun t : ℝ => W t.toNNReal ω) 0 = 0 := by simp [(hgood ω hω).2.2.1]
  have hdrv : sDrive 1 (modProc G W) ω = fun t : ℝ => W t.toNNReal ω := by
    funext s; simp [sDrive, modProc_of_mem hω]
  have htT : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
  have hX := realTamed_eq_re_of_isForwardSol hW hW0 (one_div_succ_pos n) hu
    (fun s hs => hn.trans (hc₀ s hs)) t htT
  show ((tGap G W (1 / ((n : ℝ) + 1)) x t ω + modProc G W t ω, modProc G (VR 0) t ω),
    modProc G B t ω) = _
  rw [tGap, hdrv, hX, modProc_of_mem hω, modProc_of_mem hω, modProc_of_mem hω]

/-- **The dichotomy on a never-swallowed good path.** For every `T`, either eventually (in `n`) `σ_n ≥ T`, or
eventually `F(σ_n) ≥ m M^λ`. -/
theorem eventually_of_alive {ω : Ω} (hω : ω ∈ G) (hx : 0 < x)
    (halive : ∀ T : ℝ≥0, LP3.Alive (fun t => W t.toNNReal ω) x T) (T : ℝ≥0) {a e θ m : ℝ}
    (hl : 0 < a + e) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hlow : ∀ p ∈ region κ ρ, gapD p ≤ gapX κ ρ p → m * gapX κ ρ p ^ (a + e) ≤ obs κ ρ a e θ p) :
    (∃ N : ℕ, ∀ n ≥ N, T ≤ lyapStop κ ρ G W VR B x M n ω) ∨
      ∃ N : ℕ, ∀ n ≥ N, m * M ^ (a + e) ≤
        obs κ ρ a e θ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω) := by
  have hg := hgood ω hω
  obtain ⟨u, hu⟩ := halive T
  have hW : Continuous fun t : ℝ => W t.toNNReal ω := hg.continuous_w.comp continuous_real_toNNReal
  have hW0 : (fun t : ℝ => W t.toNNReal ω) 0 = 0 := by simp [hg.2.2.1]
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx T.coe_nonneg hu
  set q : ℝ≥0 → (ℝ × ℝ) × ℝ := fun t => (((u t).re + W t ω, VR 0 t ω), B t ω) with hqdef
  have hmapsT : MapsTo (fun t : ℝ≥0 => (t : ℝ)) (Icc 0 T) (Icc (0 : ℝ) T) := fun t ht =>
    ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
  have hqc : ContinuousOn q (Icc 0 T) := by
    have hu' : ContinuousOn (fun t : ℝ≥0 => u t) (Icc 0 T) :=
      hu.1.comp NNReal.continuous_coe.continuousOn hmapsT
    exact (((Complex.continuous_re.comp_continuousOn hu').add hg.continuous_w.continuousOn).prodMk
      hg.continuous_v.continuousOn).prodMk hg.2.1.continuousOn
  have hgX : ∀ t, gapX κ ρ (q t) = (u t).re := fun t => by
    simp only [hqdef, gapX]
    rw [w_eq_of_path hg.2.2 t]; ring
  have hgD : ∀ t, gapD (q t) = (u t).re + W t ω - VR 0 t ω := fun t => by simp [hqdef, gapD]
  have hqU : ∀ t ∈ Icc 0 T, q t ∈ region κ ρ := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hgX]; exact hc₀.trans_le (hc₀le t (hmapsT ht))
    · rw [hgD]
      have h := vR_lt_of_isForwardSol hg.2.2 hx T.coe_nonneg hu t (hmapsT ht)
      simp only [Real.toNNReal_coe] at h
      linarith
  have hUc : (region κ ρ)ᶜ.Nonempty := ⟨((0, 0), 0), fun h => by
    have := h.1; simp [gapX] at this⟩
  obtain ⟨n₁, hn₁⟩ := Zhan.exists_level_of_continuousOn hUc isOpen_region hqc hqU
  obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hc₀
  have hlev : ∀ n ≥ max n₁ n₂, 1 / ((n : ℝ) + 1) ≤ c₀ := fun n hn => by
    have h : (n₂ : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hn₂.le
  have heq : ∀ n ≥ max n₁ n₂, ∀ t ∈ Icc (0 : ℝ≥0) T, lyapPath G W VR B x n t ω = q t :=
    fun n hn t ht => lyapPath_eq_of_isForwardSol hgood hω hu hc₀le (hlev n hn) ht
  have hcont : ∀ n : ℕ, Continuous (lyapPath G W VR B x n · ω) := fun n =>
    Zhan.continuous_pathX (continuous_coordΛ hgood (one_div_succ_pos n)) (continuous_modB hgood) ω
  by_cases hcase : ∀ t ∈ Icc (0 : ℝ≥0) T, (u t).re < M
  · left
    refine ⟨max n₁ n₂, fun n hn => le_lyapStop hω (hcont n) (hn₁ n (le_of_max_le_left hn)).1
      fun t ht hmem => ?_⟩
    rw [heq n hn t ht] at hmem
    obtain ⟨h1, h2⟩ := (hn₁ n (le_of_max_le_left hn)).2 t ht
    rcases hmem with h | h | h
    · linarith
    · linarith
    · have := h.2; rw [hgX] at this; linarith [hcase t ht]
  · right
    push Not at hcase
    obtain ⟨t₁, ht₁, hMt₁⟩ := hcase
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    have hn1 := hn₁ n (le_of_max_le_left hn)
    have ht₁n : (t₁ : ℝ) ≤ n := (show (t₁ : ℝ) ≤ T by exact_mod_cast ht₁.2).trans hn1.1
    have hsub : ∀ t ∈ Icc 0 t₁, t ∈ Icc (0 : ℝ≥0) T := fun t ht => ⟨zero_le, ht.2.trans ht₁.2⟩
    have hU1 : lyapPath G W VR B x n t₁ ω ∈ region κ ρ := by
      rw [heq n hn t₁ ht₁]; exact hqU t₁ ht₁
    have hL : M ≤ gapX κ ρ (lyapPath G W VR B x n t₁ ω) := by
      rw [heq n hn t₁ ht₁, hgX]; exact hMt₁
    have hgood' : ∀ t ∈ Icc 0 t₁, 1 / ((n : ℝ) + 1) < infDist (lyapPath G W VR B x n t ω) (region κ ρ)ᶜ ∧
        ‖lyapPath G W VR B x n t ω‖ < n := fun t ht => by
      rw [heq n hn t (hsub t ht)]; exact hn1.2 t (hsub t ht)
    have hge := Zhan.le_Φ_hittingBtwn (X := fun t ω => lyapPath G W VR B x n t ω) (hcont n)
      continuous_gapX.continuousOn hU1 hL ht₁n hgood'
    -- the hitting time is at most `t₁ ≤ T`
    have hσle : lyapStop κ ρ G W VR B x M n ω ≤ t₁ := by
      simp only [lyapStop, Zhan.locStop, hω, ↓reduceIte]
      exact hittingBtwn_le_of_mem zero_le (by exact_mod_cast ht₁n) (Or.inr (Or.inr ⟨hU1, hL⟩))
    have hσT : lyapStop κ ρ G W VR B x M n ω ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hσle.trans ht₁.2⟩
    have hge' : M ≤ gapX κ ρ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω) := by
      simpa only [lyapStop, Zhan.locStop, hω, ↓reduceIte] using hge
    rw [heq n hn _ hσT] at hge' ⊢
    have hqσ := hqU _ hσT
    have hDX : gapD (q (lyapStop κ ρ G W VR B x M n ω)) ≤ gapX κ ρ (q (lyapStop κ ρ G W VR B x M n ω)) := by
      rw [hgD, hgX]; linarith [hg.w_le_v (lyapStop κ ρ G W VR B x M n ω)]
    have hlow' := hlow _ hqσ hDX
    have hpow : M ^ (a + e) ≤ gapX κ ρ (q (lyapStop κ ρ G W VR B x M n ω)) ^ (a + e) :=
      Real.rpow_le_rpow hM hge' hl.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hm]

end Path

/-! ### Lemma LP2 -/

section Final

/-- `P(A) ≤ x^λ/(γ M^{λ−2} T) + x^λ/(m M^λ)` for the never-swallowed good paths `A`, every `M > x`, `T > 0`. -/
theorem measure_alive_le {κ ρ : ℝ} (hκ : 0 < κ) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {xL ρL : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL (fun _ => 0) ρL (fun _ => ρ) P 𝓕 W VL VR B ζ) {G : Set Ω}
    (hG : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGood κ ρ xL ρL W VL VR B ζ ω)
    {x : ℝ} (hx : 0 < x) {a e θ γ m : ℝ} (hl0 : 0 < a + e) (hl2 : a + e < 2) (hγ : 0 < γ) (hm : 0 < m)
    (hdrift : ∀ p ∈ region κ ρ, 0 < gapX κ ρ p - gapD p →
      Ito.itoGen (obs κ ρ a e θ) p (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) ≤
        -γ * gapX κ ρ p ^ (a + e - 2))
    (hlow : ∀ p ∈ region κ ρ, gapD p ≤ gapX κ ρ p → m * gapX κ ρ p ^ (a + e) ≤ obs κ ρ a e θ p)
    (hnn : ∀ p ∈ region κ ρ, 0 ≤ obs κ ρ a e θ p) {M : ℝ} (hxM : x < M) {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    P {ω | ω ∈ G ∧ ∀ T : ℝ≥0, LP3.Alive (fun t => W t.toNNReal ω) x T} ≤
      ENNReal.ofReal (x ^ (a + e) / (γ * M ^ (a + e - 2)) / T) +
        ENNReal.ofReal (x ^ (a + e) / (m * M ^ (a + e))) := by
  have hM : 0 < M := hx.trans hxM
  have hp0U : (((x, 0), 0) : (ℝ × ℝ) × ℝ) ∈ region κ ρ := ⟨by simp [gapX, hx], by simp [gapD, hx]⟩
  have hUc : (region κ ρ)ᶜ.Nonempty := ⟨((0, 0), 0), fun h => by have := h.1; simp [gapX] at this⟩
  obtain ⟨n₀, hn₀⟩ := Zhan.exists_level_of_continuousOn
    (x := fun _ : ℝ≥0 => (((x, 0), 0) : (ℝ × ℝ) × ℝ)) (T := 0) hUc isOpen_region continuousOn_const
    fun _ _ => hp0U
  have hX0 : ∀ n ≥ n₀, (((x, 0), 0) : (ℝ × ℝ) × ℝ) ∉ Zhan.exitSet (region κ ρ) (gapX κ ρ) M n := by
    intro n hn h
    obtain ⟨h1, h2⟩ := (hn₀ n hn).2 0 ⟨le_rfl, le_rfl⟩
    rcases h with h | h | h
    · linarith
    · linarith
    · have := h.2; simp [gapX] at this; linarith
  set S1 : ℕ → Set Ω := fun N => {ω | ∀ n ≥ N, T ≤ lyapStop κ ρ G W VR B x M n ω} with hS1
  set S2 : ℕ → Set Ω := fun N => {ω | ∀ n ≥ N, m * M ^ (a + e) ≤
    obs κ ρ a e θ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω)} with hS2
  have hsub : {ω | ω ∈ G ∧ ∀ T : ℝ≥0, LP3.Alive (fun t => W t.toNNReal ω) x T} ⊆
      (⋃ N, S1 N) ∪ ⋃ N, S2 N := by
    intro ω hω
    rcases eventually_of_alive hgood hω.1 hx hω.2 T hl0 hm.le hM.le hlow with ⟨N, hN⟩ | ⟨N, hN⟩
    · exact Or.inl (mem_iUnion.2 ⟨N, hN⟩)
    · exact Or.inr (mem_iUnion.2 ⟨N, hN⟩)
  have h1 : P (⋃ N, S1 N) ≤ ENNReal.ofReal (x ^ (a + e) / (γ * M ^ (a + e - 2)) / T) := by
    have hmono : Monotone S1 := fun N N' hNN' ω hω n hn => hω n (hNN'.trans hn)
    refine le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun N => ?_
    have hN := (lyap_markov hκ hE hG hGc hgood (hX0 (max N n₀) (le_max_right _ _)) hl2 hγ hm hM hx
      hdrift hnn hT).1
    refine (measure_mono fun ω hω => ?_).trans hN
    have := hω (max N n₀) (le_max_left _ _)
    show (T : ℝ) ≤ _
    exact_mod_cast this
  have h2 : P (⋃ N, S2 N) ≤ ENNReal.ofReal (x ^ (a + e) / (m * M ^ (a + e))) := by
    have hmono : Monotone S2 := fun N N' hNN' ω hω n hn => hω n (hNN'.trans hn)
    refine le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun N => ?_
    have hN := (lyap_markov hκ hE hG hGc hgood (hX0 (max N n₀) (le_max_right _ _)) hl2 hγ hm hM hx
      hdrift hnn hT).2
    refine (measure_mono fun ω hω => ?_).trans hN
    simp only [hS2, mem_ofPred_eq] at hω
    exact hω (max N n₀) (le_max_left _ _)
  calc P {ω | ω ∈ G ∧ ∀ T : ℝ≥0, LP3.Alive (fun t => W t.toNNReal ω) x T}
      ≤ P ((⋃ N, S1 N) ∪ ⋃ N, S2 N) := measure_mono hsub
    _ ≤ P (⋃ N, S1 N) + P (⋃ N, S2 N) := measure_union_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Lemma LP2** (finite swallowing of a passive point; Specification §6.2, p. 480). Let `k > 4` and
`−2 < ρ < k/2 − 2`. For the canonical single-right-seed evolution (no left mark, one right mark of weight `ρ` at
the seed `0`) and every passive point `x > 0`, almost surely `x` is swallowed at a finite time before the lifetime:
there is `T < ζ` at which `x` has no forward solution on `[0, T]`. -/
theorem lp2 {κ ρ : ℝ} (hκ : 4 < κ) (hρ : -2 < ρ) (hρc : ρ < κ / 2 - 2) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {xL ρL : Fin 0 → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL (fun _ => 0) ρL (fun _ => ρ) P 𝓕 W VL VR B ζ) {x : ℝ}
    (hx : 0 < x) :
    ∀ᵐ ω ∂P, ∃ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω ∧ ¬ LP3.Alive (fun t => W t.toNNReal ω) x T := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hκ0 : 0 < κ := by linarith
  obtain ⟨G, hG, hGc, hgood⟩ := exists_measurableSet_subset_of_ae (ae_isGood hκ0 hρ hE)
  obtain ⟨a, θ, γ, m, hl0, hl1, -, hγ, hm, hdrift, hlow, hnn⟩ := exists_lyapParams hκ hρ hρc
  set l := a + a * ρ / 2 with hldef
  set A : Set Ω := {ω | ω ∈ G ∧ ∀ T : ℝ≥0, LP3.Alive (fun t => W t.toNNReal ω) x T} with hAdef
  suffices hA : P A = 0 by
    have hGae : ∀ᵐ ω ∂P, ω ∈ G :=
      (measure_eq_zero_iff_ae_notMem.1 hGc).mono fun ω h => by simpa using h
    have hAae : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 hA
    filter_upwards [hGae, hAae] with ω hωG hωA
    have hnot : ¬ ∀ T : ℝ≥0, LP3.Alive (fun t => W t.toNNReal ω) x T := fun h => hωA ⟨hωG, h⟩
    push Not at hnot
    obtain ⟨T, hT⟩ := hnot
    exact ⟨T, by rw [(hgood ω hωG).1]; exact ENNReal.coe_lt_top, hT⟩
  have hxl : 0 < x ^ l := Real.rpow_pos_of_pos hx l
  -- for every `δ > 0`, `P(A) ≤ δ`
  have hδ : ∀ δ : ℝ, 0 < δ → P A ≤ ENNReal.ofReal δ := by
    intro δ hδ
    set K := x ^ l * (1 + 2 / (m * δ)) with hK
    have hK0 : 0 < K := by positivity
    set M := K ^ (1 / l) with hMdef
    have hM0 : 0 < M := Real.rpow_pos_of_pos hK0 _
    have hMl : M ^ l = K := by
      rw [hMdef, ← Real.rpow_mul hK0.le, one_div_mul_cancel hl0.ne', Real.rpow_one]
    have hxM : x < M := by
      have hlt : x ^ l < M ^ l := by
        rw [hMl, hK]
        have : 0 < 2 / (m * δ) := by positivity
        nlinarith
      exact (Real.rpow_lt_rpow_iff hx.le hM0.le hl0).1 hlt
    have hMp : 0 < γ * M ^ (l - 2) := mul_pos hγ (Real.rpow_pos_of_pos hM0 _)
    set T : ℝ≥0 := (2 * x ^ l / (γ * M ^ (l - 2) * δ)).toNNReal with hTdef
    have hT : (T : ℝ) = 2 * x ^ l / (γ * M ^ (l - 2) * δ) :=
      Real.coe_toNNReal _ (by positivity)
    have hTpos : 0 < (T : ℝ) := by rw [hT]; positivity
    have hb := measure_alive_le hκ0 hE hG hGc hgood hx hl0 (by linarith) hγ hm hdrift hlow hnn hxM hTpos
    have he1 : x ^ l / (γ * M ^ (l - 2)) / T = δ / 2 := by
      rw [hT]; field_simp
    have he2 : x ^ l / (m * M ^ l) ≤ δ / 2 := by
      have h : x ^ l / (m * M ^ l) = δ / (m * δ + 2) := by
        rw [hMl, hK]; field_simp
      rw [h]
      exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by nlinarith)
    calc P A ≤ ENNReal.ofReal (x ^ l / (γ * M ^ (l - 2)) / T) +
          ENNReal.ofReal (x ^ l / (m * M ^ l)) := hb
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
          rw [he1]; exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal he2)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have := hδ ε hε
  rwa [ENNReal.ofReal_coe_nnreal] at this

end Final

end InteractingSLE.LP.LP2
