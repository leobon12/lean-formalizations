import HigherDimLFPP.Upper.ChainUnion
import HigherDimLFPP.Upper.TreeInequality
import HigherDimLFPP.Frozen.A

/-!
# Simultaneity over all admissible paths: HA3 D7 (packet P-U3 target T3)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.4, (4.20)–(4.23) and the paragraph before
(4.24) ("the resulting family includes every field-dependent path and every one of its chains"),
as corrected by the planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D6 (iv) and
D7 ("Claim", "Counting", "Simultaneity"); HA3 §4 "Simultaneity over all paths".

* `GoodRecordMeanBound d κ` — **the good-record mean bound, D6 (iv)**, stated exactly: there is
  `C_*` such that for every white-noise model, every `n ≥ 3` and `τ, u ∈ (0,1)` there is `δ₀ > 0`
  with `E max_{c ∈ F} Y(c) ≤ b*_n + (1 - τ)(k + 1)` for all `δ ∈ (0, δ₀)`, all cutoffs
  `ε ∈ (0,1)`, all valid good records in bin `k` and all finite nonempty `F ⊆ Φ(ρ)`, where
  `b*_n = (1+u)^{2/3}(1-τ)^{-1/3} A_{n,d} + C_* u^{-1/2} + 1` (`bStar`).  It is the conclusion of
  Lemma 4.3 (HA3 D5) for records; it is the only hypothesis of the upper comparison beyond the
  frozen white-noise model, and it is supplied by the Lemma 4.3 packet.
* `log_lfpp_ge_of_chains` — the deterministic step: if every chain record of length at most
  `M_ε = ⌊log(1/ε)/log(2K/3)⌋ + 1` has `Σ_i (Y_i(c_i) - cost(ρ_i)) ≤ T₀`, then for **every**
  admissible path `γ`, `log ∫_γ e^{ζφ} ≥ ζ H_root - ζ ω(5ε) - δ² T₀` (`ζ = δ^{3/2}`), and the same
  bound holds for `log D^ζ`.  It combines the tree (`pathTreeExists`), the tree inequality
  (`treeInequality`), the leaf depth bound (`chainLengthBound`) and the record assignment
  (`chainRecord_assignment`).
* `exists_exceptional_event` (local form) and **`chainUnionBound`** (target T3): on the complement
  of an exceptional event `𝒜` with `P(𝒜) ≤ e^{-2M_ε}`,
  `log D^ζ_{ε,d} ≥ ζ H_root - ζ ω - δ² T₀` simultaneously for all admissible paths, with
  `T₀ = (M_ε/t)(log(1 + Z_g + Z_b) + 2)`.

2D source: `LQGDimension/LFPP/UpperAssembly.lean` (`det_bound`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

attribute [local instance] isFiniteMeasure_polyMeasure

/-! ## Parameters -/

/-- `M_ε = ⌊log(1/ε)/log(2K/3)⌋ + 1`, `K = 2ⁿ`: an upper bound for the number of internal nodes
on a root-to-leaf chain (HA3 D1). -/
def Mchain (n : ℕ) (ε : ℝ) : ℕ := ⌊Real.log (1 / ε) / Real.log (2 * (2 : ℝ) ^ n / 3)⌋₊ + 1

/-- The threshold `T₀ = (M/t)(log(1 + Z) + 2)` of HA3 D7. -/
def Tzero (M : ℕ) (t Z : ℝ) : ℝ := (M : ℝ) / t * (Real.log (1 + Z) + 2)

/-- `b*_n = (1+u)^{2/3}(1-τ)^{-1/3} A_{n,d} + C_* u^{-1/2} + 1` (HA3 D6 (iv)). -/
def bStar (d n : ℕ) (τ u Cstar : ℝ) : ℝ :=
  (1 + u) ^ (2 / 3 : ℝ) * (1 - τ) ^ (-(1 / 3 : ℝ)) * (A n d).toReal + Cstar * u ^ (-(1 / 2 : ℝ)) + 1

theorem one_le_Mchain (n : ℕ) (ε : ℝ) : 1 ≤ Mchain n ε := Nat.le_add_left 1 _

/-- The depth of every leaf of the tree of an admissible path is at most `M_ε`. -/
theorem length_le_Mchain {d : ℕ} [NeZero d] {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    {γ : ℝ → Rd d} (hγ : IsAdmissiblePath d γ) {T : CutTree}
    (hT : T.WF γ (2 ^ n) ε (2 * Real.sqrt d)) {v : List ℕ} (hv : v ∈ T.leaves) :
    v.length ≤ Mchain n ε := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h := chainLengthBound d γ hγ (2 ^ n) h8 ε hε T hT v hv
  push_cast at h
  have hK : (8 : ℝ) ≤ 2 ^ n := by exact_mod_cast h8
  have hlog : 0 < Real.log (2 * (2 : ℝ) ^ n / 3) := Real.log_pos (by linarith)
  have hL : 0 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos hε.1.le hε.2.le)
  unfold Mchain
  rcases Nat.eq_zero_or_pos v.length with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hle : ((v.length - 1 : ℕ) : ℝ) ≤ Real.log (1 / ε) / Real.log (2 * (2 : ℝ) ^ n / 3) := by
    rw [Nat.cast_sub hpos]
    push_cast
    linarith
  have := Nat.le_floor hle
  omega

/-! ## The deterministic step: simultaneity over paths -/

section Deterministic

variable {d : ℕ} [NeZero d]

/-- The segment `t ↦ t e₁` is an admissible path (so the infimum in `D^ζ` is over a nonempty
set). -/
theorem isAdmissiblePath_segment (d : ℕ) : IsAdmissiblePath d fun t : ℝ => t • e₁ d where
  source := zero_smul _ _
  target := one_smul _ _
  mapsTo := by
    intro t ht i
    have he : (e₁ d) i = if (i : ℕ) = 0 then (1 : ℝ) else 0 := rfl
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [he]
    split_ifs
    · rw [mul_one, abs_of_nonneg ht.1]; linarith [ht.2]
    · rw [mul_zero, abs_zero]; norm_num
  continuousOn := (continuous_id.smul continuous_const).continuousOn
  piecewise_contDiff := by
    refine ⟨1, fun i => ((i : ℕ) : ℝ), ?_, by simp, by simp, fun i => ?_⟩
    · intro a b hab
      simp only
      exact_mod_cast hab
    · exact (contDiff_id.smul contDiff_const).contDiffOn

/-- **Simultaneity over all admissible paths** (HA3 D7, "Simultaneity"; 2D `det_bound`): if every
chain record of the finite record set of the cutoff `ε` with length at most `M_ε` satisfies
`Σ_i (Y_i(c_i) - cost(ρ_i)) ≤ T₀` for all `c_i ∈ Φ(ρ_i)`, then for every admissible path `γ`,
`ζ H_root - ζ ω(5ε) - δ² T₀ ≤ log ∫_γ e^{ζφ}` with `ζ = δ^{3/2}`, and the same lower bound holds
for `log D^ζ`. -/
theorem log_lfpp_ge_of_chains {n : ℕ} (hn : 3 ≤ n) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) {φ : Rd d → ℝ} (hφ : Continuous φ) {T₀ : ℝ}
    (hchains : ∀ l ≤ Mchain n ε, ∀ ρ : Fin l → recSet d n δ ε,
      IsChainRec δ (fun i => (ρ i).1) → ∀ c : Fin l → Config d,
      (∀ i, c i ∈ family n δ (ρ i).1) →
        ∑ i, (cfgVal δ φ (c i) - (ρ i).1.cost n δ) ≤ T₀) :
    (∀ γ : ℝ → Rd d, IsAdmissiblePath d γ →
      δ ^ (3 / 2 : ℝ) * segAvg φ 0 (e₁ d) - δ ^ (3 / 2 : ℝ) * osc φ (5 * ε) - δ ^ 2 * T₀ ≤
        Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ)) ∧
    δ ^ (3 / 2 : ℝ) * segAvg φ 0 (e₁ d) - δ ^ (3 / 2 : ℝ) * osc φ (5 * ε) - δ ^ 2 * T₀ ≤
      Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) φ) := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn1 : 1 ≤ n := by omega
  set bound := δ ^ (3 / 2 : ℝ) * segAvg φ 0 (e₁ d) - δ ^ (3 / 2 : ℝ) * osc φ (5 * ε) -
    δ ^ 2 * T₀ with hbound
  have hpath : ∀ γ : ℝ → Rd d, IsAdmissiblePath d γ →
      bound ≤ Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ) ∧
        0 < lfppLength (δ ^ (3 / 2 : ℝ)) φ γ := by
    intro γ hγ
    obtain ⟨T, hT⟩ := pathTreeExists d γ hγ (2 ^ n) h8 ε hε
    obtain ⟨hpos, hineq, hflow0, hflow1⟩ :=
      treeInequality d γ hγ (2 ^ n) h8 ε hε T hT (a0 n) (a0_pos n).le φ hφ δ hδ
    have hH : T.H γ φ [] = segAvg φ 0 (e₁ d) := by
      simp only [CutTree.H, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2, hγ.source,
        hγ.target]
    have hS : ∀ v ∈ T.leaves, ∑ j ∈ Finset.range v.length,
        (δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take j) - T.bcost γ (a0 n) δ (v.take j)) ≤ T₀ := by
      intro v hv
      obtain ⟨ρ, c, hch, hc, hsum⟩ := chainRecord_assignment hn1 hδ hε.1 hγ hT hφ hv
      exact hsum.trans (hchains v.length (length_le_Mchain hn hε hγ hT hv) ρ hch c
        fun i => (hc i).1)
    have hsum : ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        (δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take j) - T.bcost γ (a0 n) δ (v.take j)) ≤ T₀ := by
      calc _ ≤ ∑ v ∈ T.leaves, T.flow γ v * T₀ :=
            Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (hS v hv) (hflow0 v hv)
        _ = T₀ := by rw [← Finset.sum_mul, hflow1, one_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg δ)
    rw [hH] at hineq
    exact ⟨by linarith, hpos⟩
  refine ⟨fun γ hγ => (hpath γ hγ).1, ?_⟩
  have hne : Nonempty {γ : ℝ → Rd d // IsAdmissiblePath d γ} :=
    ⟨⟨_, isAdmissiblePath_segment d⟩⟩
  have hD : Real.exp bound ≤ lfppDistance d (δ ^ (3 / 2 : ℝ)) φ := by
    unfold lfppDistance
    refine le_ciInf fun γ => ?_
    obtain ⟨h1, h2⟩ := hpath γ.1 γ.2
    calc Real.exp bound ≤ Real.exp (Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ.1)) :=
          Real.exp_le_exp.2 h1
      _ = lfppLength (δ ^ (3 / 2 : ℝ)) φ γ.1 := Real.exp_log h2
  calc bound = Real.log (Real.exp bound) := (Real.log_exp _).symm
    _ ≤ Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) φ) := Real.log_le_log (Real.exp_pos _) hD

end Deterministic

/-! ## The exceptional event -/

section Exceptional

variable {d : ℕ} {κ : Rd d → ℝ}

/-- **HA3 D7, local form**: for fixed `n ≥ 3`, `δ ∈ (0, 1]`, `τ, t > 0`, cutoff `ε ∈ (0,1)` and a
version `H` of `H_{ε,1}`, given the good-record mean bound (D6 (iv)) at these parameters, the
bad-record mean bound (D6 (ii)) and the variance bound (D6 (iii)), there is an event `𝒜` with
`P(𝒜) ≤ e^{-2M_ε}` off which `log D^ζ ≥ ζ H_root - ζ ω(5ε) - δ² T₀` for every admissible path. -/
theorem exists_exceptional_event [NeZero d] (hκ : IsLFPPKernel κ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ ε 1 H) {n : ℕ}
    (hn : 3 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t τ bstar Cbad CV CV' : ℝ} (ht : 0 < t)
    (hτ : 0 < τ)
    (hgood : ∀ g : GoodRec d, RecValid n δ (Sum.inl g) → ∀ F : Finset (Config d),
      ↑F ⊆ goodFam n δ g → F.Nonempty →
        ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ bstar + (1 - τ) * ((g.bin : ℝ) + 1))
    (hbad : ∀ (br : BadRec d) (F : Finset (Config d)), ↑F ⊆ badFam n δ br →
      ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ Cbad)
    (hvar : ∀ {l : ℕ} (ρ : Fin l → Record d), IsChainRec δ ρ → (∀ i, RecValid n δ (ρ i)) →
      ∀ c : Fin l → Config d, (∀ i, c i ∈ family n δ (ρ i)) →
        ‖∑ i, cfgVec κ ε 1 δ (c i)‖ ^ 2 ≤ ∑ i, recVar CV CV' δ (ρ i)) :
    ∃ 𝒜 : Set Ω, P 𝒜 ≤ ENNReal.ofReal (Real.exp (-2 * (Mchain n ε : ℝ))) ∧
      ∀ ω ∉ 𝒜,
        (∀ γ : ℝ → Rd d, IsAdmissiblePath d γ →
          δ ^ (3 / 2 : ℝ) * segAvg (fun z => H z ω) 0 (e₁ d) -
              δ ^ (3 / 2 : ℝ) * osc (fun z => H z ω) (5 * ε) -
              δ ^ 2 * Tzero (Mchain n ε) t (Zsum d n δ t τ bstar Cbad CV CV') ≤
            Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) (fun z => H z ω) γ)) ∧
        δ ^ (3 / 2 : ℝ) * segAvg (fun z => H z ω) 0 (e₁ d) -
            δ ^ (3 / 2 : ℝ) * osc (fun z => H z ω) (5 * ε) -
            δ ^ 2 * Tzero (Mchain n ε) t (Zsum d n δ t τ bstar Cbad CV CV') ≤
          Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H z ω)) := by
  set M := Mchain n ε with hM
  set Z := Zsum d n δ t τ bstar Cbad CV CV' with hZ
  set T₀ := Tzero M t Z with hT₀
  have hZ0 : 0 ≤ Z :=
    add_nonneg (tsum_nonneg fun k => mul_nonneg (Ng_nonneg d n k) (wGood_pos _ _ _ _ _).le)
      (mul_nonneg (Nb_nonneg d n hδ) (wBad_pos _ _ _ _ _).le)
  refine ⟨excEvent d n δ ε H M T₀, ?_, fun ω hω => ?_⟩
  · refine (measure_excEvent_le hκ hW hH hε hδ hδ1 ht hτ hgood hbad
      (fun ρ hch hv c hc => hvar ρ hch hv c hc) M T₀).trans (le_of_eq ?_)
    rw [hT₀, Tzero, exp_mul_pow_eq ht hZ0 M]
  · refine log_lfpp_ge_of_chains hn hδ hε (hH.continuous ω) fun l hl ρ hch c hc => ?_
    by_contra hlt
    refine hω ?_
    simp only [excEvent, mem_iUnion, Finset.mem_range]
    exact ⟨l, Nat.lt_succ_of_le hl, ρ, hch, c, hc, lt_of_not_ge hlt⟩

end Exceptional

/-! ## The good-record mean bound and the target statement -/

section Target

variable {d : ℕ}

/-- **The good-record mean bound** (HA3 D6 (iv); the conclusion of Lemma 4.3, HA3 D5, for the
records of §4.3).  There is `C_*` such that for every white-noise model `(Ω, P, W)` with
continuous versions `H ε` of `H_{ε,1}`, every `n ≥ 3` and `τ, u ∈ (0,1)` there is `δ₀ > 0` with:
for every `δ ∈ (0, δ₀)`, every cutoff `ε ∈ (0,1)`, every valid good record `ρ` in bin `k` and every
finite nonempty `F ⊆ Φ(ρ)`,
`E max_{c ∈ F} Y(c) ≤ b*_n + (1 - τ)(k + 1)`, `b*_n = (1+u)^{2/3}(1-τ)^{-1/3} A_{n,d} + C_* u^{-1/2} + 1`,
where `Y(c) = δ^{-1/2} ⟨H_{ε,1}, ν_{[x,y]} - ν_Q⟩` is the record variable (`cfgVal`). -/
def GoodRecordMeanBound (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∃ Cstar : ℝ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
    ∀ n : ℕ, 3 ≤ n → ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∃ δ₀ > 0,
      ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ g : GoodRec d, RecValid n δ (Sum.inl g) →
        ∀ F : Finset (Config d), ↑F ⊆ goodFam n δ g → F.Nonempty →
          ∫ ω, (⨆ c : F, cfgVal δ (fun z => H ε z ω) c) ∂P ≤
            bStar d n τ u Cstar + (1 - τ) * ((g.bin : ℝ) + 1)

/-- The good-record mean bound can always be used with a nonnegative constant `C_*`. -/
theorem GoodRecordMeanBound.exists_nonneg {κ : Rd d → ℝ} (h : GoodRecordMeanBound d κ) :
    ∃ Cstar : ℝ, 0 ≤ Cstar ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
    ∀ n : ℕ, 3 ≤ n → ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∃ δ₀ > 0,
      ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ g : GoodRec d, RecValid n δ (Sum.inl g) →
        ∀ F : Finset (Config d), ↑F ⊆ goodFam n δ g → F.Nonempty →
          ∫ ω, (⨆ c : F, cfgVal δ (fun z => H ε z ω) c) ∂P ≤
            bStar d n τ u Cstar + (1 - τ) * ((g.bin : ℝ) + 1) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, le_max_right _ _, fun Ω _ P W hW H hH n hn τ hτ u hu => ?_⟩
  obtain ⟨δ₀, hδ₀, hb⟩ := hC Ω P W hW H hH n hn τ hτ u hu
  refine ⟨δ₀, hδ₀, fun δ hδ ε hε g hg F hF hne => (hb δ hδ ε hε g hg F hF hne).trans ?_⟩
  have hu0 : 0 ≤ u ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu.1.le _
  have : C * u ^ (-(1 / 2 : ℝ)) ≤ max C 0 * u ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hu0
  simp only [bStar]
  linarith

/-- **The chain union bound and simultaneity** (HA3 D7; packet P-U3 target T3), conditional on
the good-record mean bound `GoodRecordMeanBound` (HA3 D6 (iv)).  There are `C_* ≥ 0` and
`C_V ≥ 0` (independent of `n`) such that for every `n ≥ 3` there are `C_bad, C'_V ≥ 0` with: for
every white-noise model and `τ, u ∈ (0,1)` there is `δ₀ > 0` such that for all `δ ∈ (0, δ₀)`,
`t > 0` and cutoffs `ε ∈ (0,1)` there is an exceptional event `𝒜` with `P(𝒜) ≤ e^{-2M_ε}` off
which, **simultaneously for all admissible paths** `γ`,
`log ∫_γ e^{ζ H_{ε,1}} ≥ ζ H_root - ζ ω(5ε) - δ² T₀`, and hence
`log D^ζ_{ε,d} ≥ ζ H_root - ζ ω(5ε) - δ² T₀`, where `ζ = δ^{3/2}`, `ω(5ε)` is the oscillation of
`H_{ε,1}` on `Ū` at distance `5ε`, `T₀ = (M_ε/t)(log(1 + Z_g + Z_b) + 2)` and
`Z_g + Z_b = Zsum d n δ t τ b*_n C_bad C_V C'_V`. -/
theorem chainUnionBound [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hG : GoodRecordMeanBound d κ) :
    ∃ Cstar CV : ℝ, 0 ≤ Cstar ∧ 0 ≤ CV ∧ ∀ n : ℕ, 3 ≤ n → ∃ Cbad CV' : ℝ, 0 ≤ Cbad ∧ 0 ≤ CV' ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ t > 0,
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        ∃ 𝒜 : Set Ω, P 𝒜 ≤ ENNReal.ofReal (Real.exp (-2 * (Mchain n ε : ℝ))) ∧
          ∀ ω ∉ 𝒜,
            (∀ γ : ℝ → Rd d, IsAdmissiblePath d γ →
              δ ^ (3 / 2 : ℝ) * segAvg (fun z => H ε z ω) 0 (e₁ d) -
                  δ ^ (3 / 2 : ℝ) * osc (fun z => H ε z ω) (5 * ε) -
                  δ ^ 2 * Tzero (Mchain n ε) t
                    (Zsum d n δ t τ (bStar d n τ u Cstar) Cbad CV CV') ≤
                Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω) γ)) ∧
            δ ^ (3 / 2 : ℝ) * segAvg (fun z => H ε z ω) 0 (e₁ d) -
                δ ^ (3 / 2 : ℝ) * osc (fun z => H ε z ω) (5 * ε) -
                δ ^ 2 * Tzero (Mchain n ε) t
                  (Zsum d n δ t τ (bStar d n τ u Cstar) Cbad CV CV') ≤
              Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)) := by
  obtain ⟨Cstar, hCstar0, hG'⟩ := hG.exists_nonneg
  obtain ⟨CV, hCV0, hCV⟩ := exists_chain_variance_bound (d := d) hκ
  refine ⟨Cstar, CV, hCstar0, hCV0, fun n hn => ?_⟩
  obtain ⟨CV', hCV'0, hvar⟩ := hCV n hn
  obtain ⟨Cbad, hCbad0, hbad⟩ := exists_badRecord_mean_bound (d := d) hκ n
  refine ⟨Cbad, CV', hCbad0, hCV'0, fun Ω _ P W hW H hH τ hτ u hu => ?_⟩
  obtain ⟨δ₀, hδ₀, hgood⟩ := hG' Ω P W hW H hH n hn τ hτ u hu
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ t ht ε hε => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδδ₀ : δ ∈ Ioo (0 : ℝ) δ₀ := ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩
  have hδ1 : δ ≤ 1 := (hδ.2.trans_le (min_le_right _ _)).le
  exact exists_exceptional_event hκ hW hε (hH ε hε) hn hδ0 hδ1 ht hτ.1
    (fun g hg F hF hne => hgood δ hδδ₀ ε hε g hg F hF hne)
    (fun br F hF => hbad hW hε.1 hε.2.le (hH ε hε) hδ0 br F hF)
    (fun ρ hch hv c hc => hvar hε.1 hε.2.le hδ0 ρ hch hv c hc)

end Target

end HigherDimLFPP.Upper
