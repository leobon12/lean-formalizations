import QuantumZipper.Proofs.Thm11.AddendumMartPath

/-!
# Theorem 1.1 addendum, AD-4: the frozen kernel converges to `V_T`

Blueprint `blueprint/THM11_BLUEPRINT.md` §9, AD-4 (second half): `V^{δ_n}_T → ∬ ρρ V_T`, a
monotone limit (FD-3, `K3.tendsto_vtKer_VTe`) along the times `t_n = T ∧ σ_n(a) ∧ σ_n(b)`,
which increase to `T ∧ τ(a) ∧ τ(b)` (`AddendumMartPath`), dominated by `|ρ||ρ| G`
(as in `MainMart.tendsto_fieldV`).  Deterministic, for every continuous driving path.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm11Asm

open FwdHolo FwdClock FrozenMart FieldMart NonSwallow MainMart Thm11Add

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {δn : ℕ → ℝ}

theorem fzZ_eq_fwdMap_of_le_sigN (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ}
    (hδpos : ∀ n, 0 < δn n) {a : ℂ} (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (ω : Ω) (n : ℕ)
    {t : ℝ≥0} (ht : t ≤ sigN κ δn T B a ω n) :
    fzZ κ (δn n / 2) B a t ω = fwdMap (drive κ B ω) t a := by
  have := congrArg Prod.fst (fzU_eq_true hBc (by linarith [hδpos n]) (by linarith [hδpos n])
    (hδa n) ω ht)
  simpa [fzU] using this

/-- **Pathwise AD-4 (kernel).** `K^{δ_n}_T(a,b) → V_T(a,b)` for `a ≠ b`. -/
theorem tendsto_frozenKernel_VT (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ}
    (hδpos : ∀ n, 0 < δn n) (hδanti : StrictAnti δn) (hδlim : Tendsto δn atTop (𝓝 0))
    {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hδa : ∀ n, δn n ≤ a.im) (hδb : ∀ n, δn n ≤ b.im)
    (hab : a ≠ b) (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => frozenKernel κ (δn n / 2) (δn n) T B a b T ω) atTop
      (𝓝 (K3.VT (drive κ B ω) T a b)) := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  set W := drive κ B ω with hWdef
  set t : ℕ → ℝ≥0 := fun n => min T (min (sigN κ δn T B a ω n) (sigN κ δn T B b ω n)) with ht
  have hta : ∀ n, t n ≤ sigN κ δn T B a ω n := fun n =>
    (min_le_right _ _).trans (min_le_left _ _)
  have htb : ∀ n, t n ≤ sigN κ δn T B b ω n := fun n =>
    (min_le_right _ _).trans (min_le_right _ _)
  have hK : ∀ n, frozenKernel κ (δn n / 2) (δn n) T B a b T ω = (K3.vtKer W (t n) a b).toReal :=
    fun n => by
      have h0 := frozenKernel_nonneg (κ := κ) (B := B) hBc (c := δn n / 2) (δ := δn n)
        (by linarith [hδpos n]) (by linarith [hδpos n]) (hδa n) (hδb n) hab T T ω
      rw [K3.vtKer, ENNReal.toReal_ofReal]
      · unfold frozenKernel
        rw [← fzZ_eq_fwdMap_of_le_sigN hBc hδpos hδa T ω n (hta n),
          ← fzZ_eq_fwdMap_of_le_sigN hBc hδpos hδb T ω n (htb n)]
      · rw [← fzZ_eq_fwdMap_of_le_sigN hBc hδpos hδa T ω n (hta n),
          ← fzZ_eq_fwdMap_of_le_sigN hBc hδpos hδb T ω n (htb n)]
        exact h0
  have hmono : Monotone (fun n => (t n : ℝ)) := fun m n hmn => by
    have h1 := sigN_monotone (κ := κ) hBc hδpos hδanti hδa T ω hmn
    have h2 := sigN_monotone (κ := κ) hBc hδpos hδanti hδb T ω hmn
    exact_mod_cast min_le_min le_rfl (min_le_min h1 h2)
  have hmem : ∀ n, (t n : ℝ) ∈ K3.vtIdx W T a b := fun n =>
    ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_left _ _,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by exact_mod_cast hta n))
        (sigN_lt_swallowTime hBc hδpos hδa T ω n),
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by exact_mod_cast htb n))
        (sigN_lt_swallowTime hBc hδpos hδb T ω n)⟩
  have hcof : ∀ s ∈ K3.vtIdx W T a b, ∃ n, s ≤ t n := fun s hs => by
    obtain ⟨n, hn1, hn2⟩ := ((eventually_le_sigN hBc hδpos hδlim ha hδa T ω hs.1 hs.2.2.1
      hs.2.1).and (eventually_le_sigN hBc hδpos hδlim hb hδb T ω hs.1 hs.2.2.2 hs.2.1)).exists
    refine ⟨n, ?_⟩
    simp only [ht, NNReal.coe_min]
    exact le_min hs.2.1 (le_min hn1 hn2)
  obtain ⟨-, hlim⟩ := K3.tendsto_vtKer_VTe hW ha hb hmono hmem hcof
  have hfin : K3.VTe W T a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le _ (hmem 0))
  simp only [hK]
  exact (ENNReal.tendsto_toReal hfin).comp hlim

/-- **AD-4 (kernel part).** `V^{δ_n}_T → ∬ ρρ V_T` for every continuous driving path. -/
theorem tendsto_fieldV_ext (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    {κ : ℝ} {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hρδ₀ : ∀ a : ℂ, a.im < δ₀ → ρ a = 0) (hδpos : ∀ n, 0 < δn n)
    (hδle : ∀ n, δn n ≤ δ₀) (hδanti : StrictAnti δn) (hδlim : Tendsto δn atTop (𝓝 0))
    (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => fieldV κ (δn n / 2) (δn n) T B ρ T ω) atTop
      (𝓝 (∫ a, ∫ b, ρ a * ρ b * K3.VT (drive κ B ω) T a b)) := by
  set Lf : ℂ × ℂ → ℝ := fun p => ρ p.1 * ρ p.2 * K3.VT (drive κ B ω) T p.1 p.2 with hLf
  set bnd : ℂ × ℂ → ℝ := fun p => |ρ p.1| * |ρ p.2| * greenH p.1 p.2 with hbnd
  have hbi : Integrable bnd ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    integrable_rho_rho_greenH hρc hρs hδ₀ hρδ₀
  have hmeasF : ∀ n, AEStronglyMeasurable (fun p : ℂ × ℂ =>
      ρ p.1 * ρ p.2 * frozenKernel κ (δn n / 2) (δn n) T B p.1 p.2 T ω)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := fun n =>
    (((hρc.measurable.comp measurable_fst).mul (hρc.measurable.comp measurable_snd)).mul
      ((measurable_frozenKernel_amb (κ := κ) (δ := δn n) hBc (bmFilt hBm) (bmFilt_adapted hBm)
        (by linarith [hδpos n] : 0 < δn n / 2) T T).comp
          (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)),
      ‖ρ p.1 * ρ p.2 * frozenKernel κ (δn n / 2) (δn n) T B p.1 p.2 T ω‖ ≤ bnd p := by
    intro n
    filter_upwards [ae_ne_diag] with p hp
    by_cases h1 : ρ p.1 = 0
    · simp [hbnd, h1]
    by_cases h2 : ρ p.2 = 0
    · simp [hbnd, h2]
    have i1 : δn n ≤ p.1.im := (hδle n).trans (not_lt.1 fun h => h1 (hρδ₀ _ h))
    have i2 : δn n ≤ p.2.im := (hδle n).trans (not_lt.1 fun h => h2 (hρδ₀ _ h))
    have hc : 0 < δn n / 2 := by linarith [hδpos n]
    have hcδ : δn n / 2 ≤ δn n := by linarith [hδpos n]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (frozenKernel_nonneg (κ := κ) hBc hc hcδ i1 i2 hp T T ω)]
    exact mul_le_mul_of_nonneg_left (frozenKernel_le_greenH (κ := κ) hBc hc hcδ i1 i2 hp T T ω)
      (by positivity)
  have hlim : ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)), Tendsto
      (fun n => ρ p.1 * ρ p.2 * frozenKernel κ (δn n / 2) (δn n) T B p.1 p.2 T ω) atTop
      (𝓝 (Lf p)) := by
    filter_upwards [ae_ne_diag] with p hne
    by_cases h1 : ρ p.1 = 0
    · simp [hLf, h1]
    by_cases h2 : ρ p.2 = 0
    · simp [hLf, h2]
    have i1 : δ₀ ≤ p.1.im := not_lt.1 fun h => h1 (hρδ₀ _ h)
    have i2 : δ₀ ≤ p.2.im := not_lt.1 fun h => h2 (hρδ₀ _ h)
    exact (tendsto_frozenKernel_VT (κ := κ) hBc hδpos hδanti hδlim
      (show p.1 ∈ H from hδ₀.trans_le i1) (show p.2 ∈ H from hδ₀.trans_le i2)
      (fun n => (hδle n).trans i1) (fun n => (hδle n).trans i2) hne T ω).const_mul _
  have hLi : Integrable Lf ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    refine Integrable.mono' hbi (aestronglyMeasurable_of_tendsto_ae atTop hmeasF hlim) ?_
    filter_upwards [hlim, ae_all_iff.2 hbound] with p hp hb
    exact le_of_tendsto' hp.norm hb
  have hEq : ∫ p, Lf p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) =
      ∫ a, ∫ b, ρ a * ρ b * K3.VT (drive κ B ω) T a b :=
    integral_prod Lf hLi
  rw [← hEq]
  exact tendsto_integral_of_dominated_convergence bnd hmeasF hbi hbound hlim

end Thm11Asm
end QuantumZipper
