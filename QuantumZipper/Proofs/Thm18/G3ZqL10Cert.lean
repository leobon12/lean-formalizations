import QuantumZipper.Proofs.Thm18.G3ZqL5LocA
import QuantumZipper.Proofs.Thm18.G3ZrDil
import QuantumZipper.Proofs.Thm18.G3ZqL8Body
import QuantumZipper.Proofs.Thm18.G3ZqL9Palm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (10): zoom locality at quantum-typical points from the fixed Palm points

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (pp. 65–66): the statement is proved at a fixed
Palm point `x` ("once we condition on `x` …") and transferred to quantum-typical points by the
rooted-measure (Palm) formula (Duplantier–Sheffield, arXiv:0808.1560, §3.3).

* `LocCertC γ c`: a **measurable** certificate on the dyadic coordinates `c` of the pulled-back
  zoomed field. It asks for uniformly Cauchy raw circle averages near `0` at all small dyadic
  radii (countable form: for fixed levels `n, n'` the pair of dyadic roundings of `z` takes
  countably many values), and a positive limit of the smoothed areas of rational half-balls
  (`measurableSet_locCertC`).
* `locAreaQ_of_locCertC`, `g3zoomLawM_bump_iffQ`: the certificate gives the bump locality of the
  zoom through the local map.
* **`g3ZqLZoomLocAEMapStmt_of_palm : G3ZqLPalmCertStmt → G3ZqLZoomLocAEMapStmt`**: by the Palm null
  transfer `ae_hν_of_palm_null` (G3ZqL9Palm), the certificate at the Palm field of Lebesgue-a.e.
  fixed point `x` gives it at `ν_h`-a.e. point of the free field.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "X₀" => gffBase.X

namespace G3ZqL

open Prop16Area.G Factorization G3Z2b2 G3Zp G3Zq LQGMeas LocalRule

/-- The raw circle average of the rebuilt field `reconstruct c` at the level-`n` dyadic rounding of
`z`, radius `r_k`. -/
def rawAt (c : ℕ → ℝ) (n k : ℕ) (z : ℂ) : ℝ :=
  reconstruct c (foldedCircle (dyadicRoundC n z) (radius k))

/-- **Measurable certificate of local area positivity.** -/
def LocCertC (γ : ℝ) (c : ℕ → ℝ) : Prop :=
  ∃ ρ : ℚ, 0 < (ρ : ℝ) ∧ ∃ k₀ : ℕ,
    (∀ k : ℕ, k₀ ≤ k → ∀ ε : ℚ, 0 < (ε : ℝ) → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ n' : ℕ, N ≤ n' →
      ∀ z ∈ ball (0 : ℂ) ρ ∩ H, |rawAt c n k z - rawAt c n' k z| ≤ ε) ∧
    ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ρ → ∃ n : ℕ,
      (∃ l : ℝ, Tendsto (fun k => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z
        ∂areaApprox γ (reconstruct c) k) atTop (𝓝 l)) ∧
      0 < liminf (fun k => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z
        ∂areaApprox γ (reconstruct c) k) atTop

theorem countable_range_dyadicRoundC_L (n : ℕ) : (Set.range (dyadicRoundC n)).Countable := by
  have hsub : Set.range (dyadicRoundC n) ⊆
      Set.range (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  exact (Set.countable_range _).mono hsub

/-- The Cauchy clause at fixed levels is a countable intersection. -/
theorem measurableSet_cauchyAt (S : Set ℂ) (n n' k : ℕ) (ε : ℝ) :
    MeasurableSet {c : ℕ → ℝ | ∀ z ∈ S, |rawAt c n k z - rawAt c n' k z| ≤ ε} := by
  set g : ℂ → ℂ × ℂ := fun z => (dyadicRoundC n z, dyadicRoundC n' z) with hg
  have hcount : (g '' S).Countable :=
    ((countable_range_dyadicRoundC_L n).prod (countable_range_dyadicRoundC_L n')).mono (by
        rintro _ ⟨z, -, rfl⟩; exact ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩)
  set T : ℂ × ℂ → Set (ℕ → ℝ) := fun p => {c | |reconstruct c (foldedCircle p.1 (radius k)) -
        reconstruct c (foldedCircle p.2 (radius k))| ≤ ε} with hT
  have e : {c : ℕ → ℝ | ∀ z ∈ S, |rawAt c n k z - rawAt c n' k z| ≤ ε} = ⋂ p ∈ g '' S, T p := by
    refine Set.ext fun c => ⟨fun h => mem_iInter₂.2 fun p hp => ?_, fun h z hz => ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hp
      exact h z hz
    · exact mem_iInter₂.1 h (g z) (mem_image_of_mem g hz)
  rw [e]
  refine MeasurableSet.biInter hcount fun p _ => ?_
  have h1 : Measurable fun c : ℕ → ℝ => reconstruct c (foldedCircle p.1 (radius k)) :=
    measurable_pi_iff.1 measurable_reconstruct _
  have h2 : Measurable fun c : ℕ → ℝ => reconstruct c (foldedCircle p.2 (radius k)) :=
    measurable_pi_iff.1 measurable_reconstruct _
  exact measurableSet_le (continuous_abs.measurable.comp (h1.sub h2)) measurable_const

theorem measurable_bumpInt (γ : ℝ) (q : ℝ) (n k : ℕ) :
    Measurable fun c : ℕ → ℝ => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z
      ∂areaApprox γ (reconstruct c) k :=
  Prop16Area.Meas.measurable_integral_areaApprox_param γ k measurable_reconstruct
    (g := fun _ z => openBump (ball (0 : ℂ) q ∩ H) n z)
    ((continuous_openBump _ n).measurable.comp measurable_snd)

/-- **The certificate is measurable.** -/
theorem measurableSet_locCertC (γ : ℝ) : MeasurableSet {c : ℕ → ℝ | LocCertC γ c} := by
  refine measurableSet_setOf.2 ?_
  unfold LocCertC
  refine Measurable.exists fun ρ => measurable_const.and (Measurable.exists fun k₀ =>
    Measurable.and ?_ ?_)
  · refine Measurable.forall fun k => measurable_const.imp (Measurable.forall fun ε =>
      measurable_const.imp (Measurable.exists fun N => Measurable.forall fun n =>
        measurable_const.imp (Measurable.forall fun n' => measurable_const.imp ?_)))
    exact measurableSet_setOf.1 (measurableSet_cauchyAt _ n n' k ε)
  · refine Measurable.forall fun q => measurable_const.imp (measurable_const.imp
      (Measurable.exists fun n => Measurable.and ?_ ?_))
    · exact measurableSet_setOf.1 (StronglyMeasurable.measurableSet_exists_tendsto fun k =>
        (measurable_bumpInt γ q n k).stronglyMeasurable)
    · exact measurableSet_setOf.1 (measurableSet_lt measurable_const
        (Measurable.liminf fun k => measurable_bumpInt γ q n k))

/-- Local area positivity with rational radii. -/
def LocAreaQ (γ : ℝ) (u : FieldSample) : Prop :=
  ∃ ρ : ℚ, 0 < (ρ : ℝ) ∧ ∃ k₀ : ℕ, (∀ k : ℕ, k₀ ≤ k → ∀ z ∈ ball (0 : ℂ) ρ ∩ H, ∃ l : ℝ,
      Tendsto (fun n => u (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) ∧
    ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ρ → ∃ (n : ℕ) (v : ℝ), 0 < v ∧
      Tendsto (fun k => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z ∂areaApprox γ u k) atTop (𝓝 v)

theorem locAreaQ_of_locCertC {γ : ℝ} {c : ℕ → ℝ} (h : LocCertC γ c) :
    LocAreaQ γ (reconstruct c) := by
  obtain ⟨ρ, hρ, k₀, hC, hP⟩ := h
  refine ⟨ρ, hρ, k₀, fun k hk z hz => ?_, fun q hq hqρ => ?_⟩
  · refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨ε', hε'0, hε'⟩ := exists_rat_btwn hε
    obtain ⟨N, hN⟩ := hC k hk ε' hε'0
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hN n hn N le_rfl z hz) hε'
  · obtain ⟨n, ⟨l, hl⟩, hpos⟩ := hP q hq hqρ
    refine ⟨n, l, ?_, hl⟩
    rwa [hl.liminf_eq] at hpos

/-- **Bump locality of the zooms through a local map, rational local area form.** -/
theorem g3zoomLawM_bump_iffQ {s : Set LawD} (hs : s ∈ lawCyl) {γ : ℝ} (hγ : 0 < γ)
    {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {left : Bool} {y : FieldSample} {f : ℂ → ℝ} {a : ℝ≥0 → ℝ}
    {b x r : ℝ} (hr : 0 < r) (hf : ∀ z ∈ ball (x : ℂ) r, f z = 0)
    {ρ : ℝ} (hρ : 0 < ρ) {Φ : ℂ → ℂ} (hc : ContinuousOn Φ (closedBall 0 ρ ∩ Hbar))
    (hmt : MapsTo Φ (closedBall 0 ρ ∩ Hbar) Hbar)
    (heq : EqOn (g3mapP Ψ left (y, a, b, x)) Φ (closedBall 0 ρ ∩ H))
    (hm : Measurable (g3mapP Ψ left (y, a, b, x))) (h0 : Φ 0 = 0)
    (hloc : LocAreaQ γ (reconstruct (g3coordsM γ 0 Ψ left (y, a, b, x)))) :
    ∀ᶠ L in atTop,
      (g3zoomLawM γ L Ψ left (y + ofFun f, a, b, x) ∈ s ↔ g3zoomLawM γ L Ψ left (y, a, b, x) ∈ s) := by
  have hfc : FcAgree ((fun z => z + (x : ℂ)) ⁻¹' ball (x : ℂ) r)
      (translate (y + ofFun f) (x : ℂ)) (translate y (x : ℂ)) :=
    fcAgree_translate isOpen_ball (fcAgree_add_ofFun_zero y hf).circAgree x
  have hpre : (fun z => z + (x : ℂ)) ⁻¹' ball (x : ℂ) r = ball 0 r := by
    ext z; simp [dist_eq_norm]
  rw [hpre] at hfc
  obtain ⟨R, hR, Hm⟩ := g3zoomLawM_mem_iff_of_agree hs
  obtain ⟨ρ', hρ', hK⟩ := exists_small_of_ext hρ hc hmt heq hm h0 isOpen_ball (mem_ball_self hr)
  obtain ⟨ρ₁, hρ₁, k₀, hraw, hpos⟩ := hloc
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨q₀, hq₀, hq₀'⟩ := exists_rat_btwn (lt_min (div_pos hρ' hR0) hρ₁)
  have hq₀R : (q₀ : ℝ) * R < ρ' := by
    have := lt_of_lt_of_le hq₀' (min_le_left _ _)
    rwa [lt_div_iff₀ hR0] at this
  have hq₀ρ : (q₀ : ℝ) < ρ₁ := lt_of_lt_of_le hq₀' (min_le_right _ _)
  obtain ⟨n, v, hv, ht⟩ := hpos q₀ hq₀ hq₀ρ
  have hraw' : ∀ k : ℕ, k₀ ≤ k → ∀ z ∈ ball (0 : ℂ) q₀ ∩ H, ∃ l : ℝ, Tendsto
      (fun n => reconstruct (g3coordsM γ 0 Ψ left (y, a, b, x))
        (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l) := fun k hk z hz =>
    hraw k hk z ⟨ball_subset_ball hq₀ρ.le hz.1, hz.2⟩
  have hev := eventually_one_le_areaProxy_addConst_of_loc hγ hraw' hv ht
  have htL : Tendsto (fun L : ℝ => L / γ) atTop atTop := tendsto_id.atTop_div_const hγ
  filter_upwards [htL.eventually hev] with L hL
  refine Hm γ L Ψ left (y + ofFun f) y a b x (ball 0 r) (ball 0 ρ') isOpen_ball isOpen_ball
    hfc.circAgree hK q₀ hq₀ (fun u hu => mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu.1) hq₀R))
    ?_
  have e : areaProxy γ (reconstruct (g3coordsM γ L Ψ left (y, a, b, x))) q₀ =
      areaProxy γ (addConst (reconstruct (g3coordsM γ 0 Ψ left (y, a, b, x))) (L / γ)) q₀ := by
    rw [g3coordsM_level]
    unfold areaProxy LQGMeas.areaFun
    rw [Factorization.areaApprox_congr (avgReg_reconstruct_add_const _ _)]
  rw [e]
  exact hL

/-- The pulled-back coordinates only see the regularized averages of the field. -/
theorem g3coordsM_reconstruct_coords (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool)
    (y : FieldSample) (a : ℝ≥0 → ℝ) (x : ℝ) :
    g3coordsM γ L Ψ left (reconstruct (coords y), a, 1, x) = g3coordsM γ L Ψ left (y, a, 1, x) := by
  funext i
  simp only [g3coordsM, g3mapP]
  rw [translate_congr (avgReg_reconstruct_coords y)]

/-- The bad event of the Palm transfer: `x` on the side half-line and no certificate. -/
def badSet (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (side : Bool) (a : ℝ≥0 → ℝ) :
    Set ((ℕ → ℝ) × ℝ) :=
  {p | p.2 ∈ g1SideHalf side ∧ ¬ LocCertC γ (g3coordsM γ 0 Ψ side (reconstruct p.1, a, 1, p.2))}

theorem measurableSet_badSet {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    (side : Bool) (a : ℝ≥0 → ℝ) : MeasurableSet (badSet γ Ψ side a) := by
  have hm : Measurable fun p : (ℕ → ℝ) × ℝ => g3coordsM γ 0 Ψ side (reconstruct p.1, a, 1, p.2) :=
    (measurable_g3coordsM hsel 0 side).comp ((measurable_reconstruct.comp measurable_fst).prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  exact (measurable_snd (measurableSet_g1SideHalf side)).inter
    ((measurableSet_locCertC γ).preimage hm).compl

/-- **Node (fixed Palm points): the certificate for the pulled-back Palm field.** For a good path,
at Lebesgue-a.e. point `x ∈ (−1, 1)` of the side half-line, a.s. the pulled-back zoomed Palm field
`normField γ (xPalm γ x)` through the local map at `x` satisfies `LocCertC`. -/
def G3ZqLPalmCertStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a → ∀ side : Bool,
    ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), x ∈ g1SideHalf side →
      ∀ᵐ ω ∂gffBase.P, LocCertC γ (g3coordsM γ 0 Ψ side (normField γ (xPalm γ x) ω, a, 1, x))

/-- **Zoom locality at quantum-typical points from the fixed Palm points.** -/
theorem g3ZqLZoomLocAEMapStmt_of_palm (hP : G3ZqLPalmCertStmt) : G3ZqLZoomLocAEMapStmt := by
  intro γ hγ hγ2 Ψ hsel a ha side s hs φ hφ r hr
  have hab : Icc (-1 : ℝ) 1 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by simp
  have hPal : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), ∀ᵐ ω ∂gffBase.P,
      (coords (normField γ (xPalm γ x) ω), x) ∉ badSet γ Ψ side a := by
    filter_upwards [hP γ hγ hγ2 Ψ hsel a ha side] with x hx
    by_cases hxs : x ∈ g1SideHalf side
    · filter_upwards [hx hxs] with ω hω
      intro hb
      exact hb.2 (by rw [g3coordsM_reconstruct_coords]; exact hω)
    · exact Eventually.of_forall fun ω hb => hxs hb.1
  have hT := ae_hν_of_palm_null hγ hγ2 (measurableSet_badSet hsel side a) hab hPal
  filter_upwards [g2ZoomLocStmt_holds hγ hγ2 s hs φ hφ r hr, hT] with ω hpl hbad
  rw [ae_restrict_iff' measurableSet_Ioo] at hbad
  filter_upwards [hbad] with x hxb hxI hx0 b
  by_cases hxs : x ∈ g1SideHalf side
  · have hcert : LocCertC γ (g3coordsM γ 0 Ψ side (normField γ X₀ ω, a, 1, x)) := by
      by_contra hn
      exact hxb hxI ⟨hxs, by rw [g3coordsM_reconstruct_coords]; exact hn⟩
    obtain ⟨φ₀, hφ₀, hΨa⟩ := hsel.2.2 a ha.1 ha.2 side
    obtain ⟨Φo, hR⟩ := G1Z2.sideReflChordStmt_holds _ ha.2 side φ₀ hφ₀
    rw [← hΨa] at hR
    have hψH : MapsTo (Ψ side a) H H := (G1RC.psiGood_of_sel hsel ha.1 ha.2 side).2.2.2.1
    obtain ⟨ρ, hρ, Φ₁, hc, hmt, heq, h0⟩ :=
      G3Zp.g3mapP_ext hψH hR hxs (normField γ gffBase.X ω)
    have hm : Measurable (g3mapP Ψ side (normField γ gffBase.X ω, a, 1, x)) :=
      (g3mapB_props hsel ha.1 ha.2 side one_pos (x / 1)).2.2
    have hev := g3zoomLawM_bump_iffQ hs hγ (f := fun z => b * φ z) hr
      (fun z hz => by rw [hx0 z hz, mul_zero]) hρ hc hmt heq hm h0 (locAreaQ_of_locCertC hcert)
    have e1 : ∀ (C : ℝ) (y : FieldSample),
        g3zMapZ γ Ψ side a C y x = g3zoomLawM γ C Ψ side (y, a, 1, x) := fun C y => by
      unfold g3zMapZ
      exact ite_eq_left hxs
    filter_upwards [hev] with C hC
    rw [e1, e1]
    exact hC
  · have e1 : ∀ (C : ℝ) (y : FieldSample), g3zMapZ γ Ψ side a C y x = zoomLaw γ C y x :=
      fun C y => by
        unfold g3zMapZ
        exact ite_eq_right hxs
    filter_upwards [hpl x hx0 b] with C hC
    rw [e1, e1]
    exact hC

/-- **The map mixing body from the fixed-Palm-point certificate alone.** -/
theorem g3FixMixBody_mapPalm (hP : G3ZqLPalmCertStmt)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → FieldSample) (hW : IsQuantumWedge γ γ Y' P') :
    R18.G3FixMixBody (g2WedgeLaw P' Y') (g2WedgeLaw P' Y') (g3PalmLaw γ) (g3X γ) (g3R γ)
      (g3UfZ (g3zMapZ γ Ψ true a) γ) (g3VfZ (g3zMapZ γ Ψ false a) γ) :=
  g3FixMixBody_mapAE (g3ZqLZoomLocAEMapStmt_of_palm hP) hγ hγ2 hsel ha P' Y' hW

end G3ZqL
end Thm18Asm
end QuantumZipper
