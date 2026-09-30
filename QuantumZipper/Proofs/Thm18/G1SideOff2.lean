import QuantumZipper.Proofs.Thm18.G1SideOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (8): the wedge family transport, uniformly over the dilated test functions

`ae_wedge_offset_uniform`: almost surely, for the wedge field and a finite-parameter family of
class maps, for every continuous compactly supported `f` whose dilates `f(c ·)`, `c ∈ [1,2]`, all
vanish off a fixed `[a', b'] ⊂ (a, b)`, the transport of `G1Side.ae_wedge_transport_family` holds
uniformly in the map `q ∈ K` and in `c ∈ [1,2]`. See G1SideOff.lean for the sources.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

set_option maxHeartbeats 800000 in
/-- **Uniform transport over the dilated test functions, a.s.** -/
theorem ae_wedge_offset_uniform {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m : ℚ}
    {L R : ℝ} {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : (a : ℝ) < b) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) (hK : IsCompact K) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar) :
    ∀ᵐ ω ∂P', ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → ∀ a' b' : ℝ,
      (a : ℝ) < a' → b' < b → (∀ c ∈ Icc (1 : ℝ) 2, ∀ u, u ∉ Icc a' b' → f (c * u) = 0) →
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ K, ∀ c ∈ Icc (1 : ℝ) 2,
        |∫ u, f (c * u) ∂bdryApprox γ (coordChange (wedgeField (lateralPart (X ω))
            (fun t => A t ω) (Qc γ)) (Ψ q) (Qc γ)) k -
          ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
            f (c * Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u)
              ∂qBoundaryMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))| ≤
          η := by
  filter_upwards [ae_wedge_transport_family hγ hγ2 hα hX hA hI Ψ K hab hρ hm hL hcl hlip hπ hπK
      hπid hR hKR hK hc₀ hsep hHb,
    ae_wedge_family_exact hγ hγ2 hα hX hA hab hρ hm hL hcl hlip hπ hπK hπid hc₀ hsep hHb,
    WedgeBdry.ae_bReg_wedgeField hγ hγ2 hα hX hA hI]
    with ω hT hE hW f hf hfc a' b' ha' hb' hvan η hη
  set W := wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ) with hWdef
  set ν0 := qBoundaryMeasure γ W with hν0
  have hW' := Thm18Asm.G1Z3.isVagueLimitR_of_good_z3 hW.1
  haveI := hW'.1
  have hsub : Icc a' b' ⊆ Ioo (a : ℝ) b := Icc_subset_Ioo ha' hb'
  -- the bump
  obtain ⟨φc, hφs, hφ1, hφ01⟩ := exists_tsupport_one_of_isOpen_isClosed (X := ℝ) isOpen_Ioo
    (by rw [closure_Ioo hab.ne]; exact isCompact_Icc) isClosed_Icc hsub
  set φ : ℝ → ℝ := ⇑φc with hφdef
  have hφc : Continuous φ := φc.continuous
  have hφcs : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hφs.trans Ioo_subset_Icc_self)
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => (hφ01 x).1
  have hφle1 : ∀ x, φ x ≤ 1 := fun x => (hφ01 x).2
  have hφK : ∀ x ∈ Icc a' b', 1 ≤ φ x := fun x hx => le_of_eq (hφ1 hx).symm
  -- mass bound for the limit functional
  set Mφ : ℝ := ν0.real (Icc (-(M : ℝ)) M) with hMφ
  have hthk : ∀ t ∈ Icc (a : ℝ) b, ((t : ℝ) : ℂ) ∈ thickening (ρ : ℝ) (segC a b) :=
    fun t ht => self_subset_thickening hρ _ (ofReal_mem_segC ht)
  have hre : ∀ q ∈ K, ∀ t ∈ Icc (a : ℝ) b, (Ψ q t).re ∈ Icc (-(M : ℝ)) M := fun q hq t ht => by
    have h1 := (hcl q hq).2.1 _ (hthk t ht)
    have h2 := abs_le.1 ((Complex.abs_re_le_norm (Ψ q t)).trans h1)
    exact ⟨h2.1, h2.2⟩
  have hLφ : ∀ q ∈ K, ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
      φ (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u) ∂ν0 ≤ Mφ := by
    intro q hq
    have hsub' : Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re ⊆ Icc (-(M : ℝ)) M :=
      Icc_subset_Icc (hre q hq a ⟨le_rfl, hab.le⟩).1 (hre q hq b ⟨hab.le, le_rfl⟩).2
    have hfin : ν0 (Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re) ≠ ⊤ :=
      isCompact_Icc.measure_lt_top.ne
    calc _ ≤ ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re, (1 : ℝ) ∂ν0 :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => hφ0 _)
            (integrableOn_const hfin) (Eventually.of_forall fun u => hφle1 _)
      _ = ν0.real (Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re) := by simp
      _ ≤ Mφ := measureReal_mono hsub' isCompact_Icc.measure_lt_top.ne
  -- the family of test functions
  set F : Set (ℝ → ℝ) := (fun c : ℝ => fun u => f (c * u)) '' Icc 1 2 with hF
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hFK : ∀ h ∈ F, ∀ x ∉ Icc a' b', h x = 0 := by
    rintro _ ⟨c, hc, rfl⟩ x hx; exact hvan c hc x hx
  have hFc : ∀ h ∈ F, Continuous h := by
    rintro _ ⟨c, hc, rfl⟩; exact hf.comp (continuous_const.mul continuous_id)
  have hFts : ∀ h ∈ F, tsupport h ⊆ Icc a' b' := fun h hh =>
    closure_minimal (fun x hx => by by_contra hn; exact hx (hFK h hh x hn)) isClosed_Icc
  have hFb : ∀ h ∈ F, ∃ C, ∀ x, |h x| ≤ C := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨Cf, fun x => by simpa [Real.norm_eq_abs] using hCf (c * x)⟩
  -- per test function: the transport, as an index over `K`
  let ι := {q // q ∈ K}
  let μ : ι → ℕ → Measure ℝ := fun i k => bdryApprox γ (coordChange W (Ψ i.1) (Qc γ)) k
  let Lf : ι → (ℝ → ℝ) → ℝ := fun i h => ∫ u in Icc (Ψ i.1 (a : ℝ)).re (Ψ i.1 (b : ℝ)).re,
    h (Function.invFunOn (fun t : ℝ => (Ψ i.1 t).re) (Icc (a : ℝ) b) u) ∂ν0
  have hconvT : ∀ h : ℝ → ℝ, Continuous h → tsupport h ⊆ Icc a' b' →
      ∀ η > 0, ∀ᶠ k in atTop, ∀ i : ι, |∫ x, h x ∂μ i k - Lf i h| ≤ η := by
    intro h hc hts η hη
    have hcs : HasCompactSupport h := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
    filter_upwards [hT h hc hcs (hts.trans hsub) η hη] with k hk i
    exact hk i.1 i.2
  have hφconv : ∀ η > 0, ∀ᶠ k in atTop, ∀ i : ι, |∫ x, φ x ∂μ i k - Lf i φ| ≤ η := by
    intro η hη
    filter_upwards [hT φ hφc hφcs hφs η hη] with k hk i
    exact hk i.1 i.2
  have hφint : ∀ᶠ k in atTop, ∀ i : ι, Integrable φ (μ i k) := by
    filter_upwards [hE] with k hk i
    exact integrable_bdryApprox_of_continuousOn γ (hk i.1 i.2).2 hφc fun u hu =>
      image_eq_zero_of_notMem_tsupport fun h => hu (Ioo_subset_Icc_self (hφs h))
  have hconvF : ∀ h ∈ F, ∀ η > 0, ∀ᶠ k in atTop, ∀ i : ι, |∫ x, h x ∂μ i k - Lf i h| ≤ η :=
    fun h hh => hconvT h (hFc h hh) (hFts h hh)
  have hLlip : ∀ i : ι, ∀ f₁ ∈ F, ∀ f₂ ∈ F, ∀ ε : ℝ, 0 ≤ ε → (∀ x, |f₁ x - f₂ x| ≤ ε) →
      |Lf i f₁ - Lf i f₂| ≤ |Mφ| * ε := by
    intro i f₁ hf₁ f₂ hf₂ ε hε hsup
    obtain ⟨C₁, hC₁⟩ := hFb f₁ hf₁
    obtain ⟨C₂, hC₂⟩ := hFb f₂ hf₂
    have key := abs_sub_le_of_limits (μ := μ i) hε hφ0 hφK (hFK f₁ hf₁) (hFK f₂ hf₂)
      (hFc f₁ hf₁).stronglyMeasurable (hFc f₂ hf₂).stronglyMeasurable hC₁ hC₂ hsup
      (hφint.mono fun k hk => hk i)
      (fun η hη => (hconvF f₁ hf₁ η hη).mono fun k hk => hk i)
      (fun η hη => (hconvF f₂ hf₂ η hη).mono fun k hk => hk i)
      (fun η hη => (hφconv η hη).mono fun k hk => hk i)
    calc _ ≤ ε * _ := key
      _ ≤ ε * Mφ := mul_le_mul_of_nonneg_left (hLφ i.1 i.2) hε
      _ ≤ |Mφ| * ε := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hε
  have hU := unif_testFamily (μ := μ) (L := Lf) (K := Icc a' b') (Mφ := Mφ) (D := |Mφ|)
    (F := F) hφ0 hφK hφint hφconv (fun i => hLφ i.1 i.2) hFK
    (fun h hh => (hFc h hh).stronglyMeasurable) hFb hLlip (exists_net_dilate hf hfc) hconvF
  filter_upwards [hU η hη] with k hk q hq c hc
  exact hk ⟨q, hq⟩ _ ⟨c, hc, rfl⟩

end G1Side
end QuantumZipper
