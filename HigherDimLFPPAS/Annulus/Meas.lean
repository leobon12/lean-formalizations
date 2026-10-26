import HigherDimLFPPAS.Core.Interfaces
import HigherDimLQGMetric.Sec4.Lemma43Meas
import HigherDimLQGMetric.ShellDec.Sigma
import HigherDimLQGMetric.Select.Internal
import HigherDimLQGMetric.Locality.TruncInternal
import HigherDimLQGMetric.Limits.JointInternalMeas
import HigherDimLQGMetric.Events.ScaledEvent
import HigherDimLQGMetric.Sharp.CountableShell
import HigherDimLQGMetric.Metric.WeylBasic
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Field.LGFPlusCont

/-! Measurability and recentring for the good annulus event in Lemma 3.2. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter Topology Metric TopologicalSpace
open scoped ENNReal

namespace HigherDimLFPPAS.Annulus

open HigherDimLFPPAS.Core HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem measurable_restrict_sigmaOn {Ω : Type} [MeasurableSpace Ω]
    {h : Ω → DistRd d} {W : Set (Rd d)} {U : Opens (Rd d)} (hUW : (U : Set (Rd d)) ⊆ W) :
    Measurable[fieldSigmaOn h W] (fun ω => restrictTo U (h ω)) := by
  apply (@measurable_distOn_iff d U Ω (fieldSigmaOn h W)
    (fun ω => restrictTo U (h ω))).2
  intro φ
  let ψ : {θ : TestRd d // tsupport (θ : Rd d → ℝ) ⊆ W} :=
    ⟨testIncl U φ, (by simpa only [coe_testIncl] using
      (show tsupport (φ : Rd d → ℝ) ⊆ (U : Set (Rd d)) from φ.tsupport_subset).trans hUW)⟩
  have hsrc : Measurable[fieldSigmaOn h W]
      (fun ω (ψ : {θ : TestRd d // tsupport (θ : Rd d → ℝ) ⊆ W}) => h ω ψ.1) :=
    Measurable.of_comap_le le_rfl
  have hp : Measurable[fieldSigmaOn h W] (fun ω => h ω ψ.1) :=
    (measurable_pi_apply ψ).comp hsrc
  simpa only [restrictTo_apply, ψ] using hp

private theorem goodAnnulus_smul_iff (G H : ContMetric d) (a η c₀ b s : ℝ)
    (z : Rd d) (r : ℝ) (hs : 0 < s) :
    GoodAnnulus (G.smul s hs) (H.smul s hs) a η c₀ b z r ↔
      GoodAnnulus G H a η c₀ b z r := by
  -- The event is homogeneous in the two metrics; the ratio parameter is held fixed.
  have hk : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have htop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel (x y k : ℝ≥0∞) :
      ENNReal.ofReal s * x ≤ k * (ENNReal.ofReal s * y) ↔ x ≤ k * y := by
    have heq : k * (ENNReal.ofReal s * y) = ENNReal.ofReal s * (k * y) := by ac_rfl
    rw [heq]
    exact ENNReal.mul_le_mul_iff_right hk htop
  unfold GoodAnnulus
  simp_rw [ContMetric.internal_smul hs, setDistIn_smul hs, hcancel]

private theorem fieldLfppMetric_locField_addConst {κ : Rd d → ℝ} {ε ξ : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hrad : 0 < locRad ε) (hZ : locMass κ ε (locRad ε) ≠ 0)
    (g : DistRd d) (c : ℝ) :
    fieldLfppMetric ξ (Core.locFieldC κ ε (addConst g c)) =
      (fieldLfppMetric ξ (Core.locFieldC κ ε g)).smul (Real.exp (ξ * c)) (Real.exp_pos _) := by
  have hc₁ := continuous_locField hK hrad (addConst g c)
  have hc₀ := continuous_locField hK hrad g
  have hlocC : Core.locFieldC κ ε (addConst g c) =
      Core.locFieldC κ ε g + ContinuousMap.const (Rd d) c := by
    ext x
    simp only [Core.locFieldC, dif_pos hc₁, dif_pos hc₀, ContinuousMap.coe_mk,
      ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact locField_addConst hK hrad hZ g c x
  have hlocFun : (Core.locFieldC κ ε (addConst g c) : Rd d → ℝ) =
      (fun x => Core.locFieldC κ ε g x + c) := by
    funext x
    have hx := congrArg (fun φ : C(Rd d, ℝ) => φ x) hlocC
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply] using hx
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  simp only [ContMetric.smul_apply, fieldLfppMetric_apply]
  rw [fieldLfpp_eq_lfppDistOn (Core.locFieldC κ ε (addConst g c)).continuous,
    fieldLfpp_eq_lfppDistOn (Core.locFieldC κ ε g).continuous, hlocFun]
  exact HigherDimLFPP.lfppDistOn_add_const ξ (Core.locFieldC κ ε g) c univ p.1 p.2

private theorem Meps_addConst {κ : Rd d → ℝ} {ε ξ : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hrad : 0 < locRad ε) (hZ : locMass κ ε (locRad ε) ≠ 0)
    (ha : 0 < aEps κ ξ ε) (g : DistRd d) (c : ℝ) :
    Core.Meps κ ξ ε (addConst g c) =
      (Core.Meps κ ξ ε g).smul (Real.exp (ξ * c)) (Real.exp_pos _) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  simp only [Core.Meps, dif_pos ha, ContMetric.smul_apply]
  rw [fieldLfppMetric_locField_addConst hK hrad hZ g c]
  simp only [ContMetric.smul_apply]
  ring_nf

private theorem pairLe_of_dense {f g : Rd d × Rd d → ℝ≥0∞} {S : Set (Rd d × Rd d)}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    {ι : Type*} {q : ι → Rd d × Rd d} (hq : ∀ n, q n ∈ S)
    (hdense : S ⊆ closure (range q)) (hseq : ∀ n, f (q n) ≤ g (q n))
    {p : Rd d × Rd d} (hp : p ∈ S) : f p ≤ g p := by
  let H : Rd d × Rd d → ℝ≥0∞ × ℝ≥0∞ := fun p => (f p, g p)
  have hH : ContinuousOn H S := hf.prodMk hg
  have hqS : range q ⊆ S := by
    rintro x ⟨n, rfl⟩
    exact hq n
  have hmem : H p ∈ closure (H '' range q) :=
    ContinuousWithinAt.mem_closure_image ((hH p hp).mono hqS) (hdense hp)
  have hclosed : IsClosed {x : ℝ≥0∞ × ℝ≥0∞ | x.1 ≤ x.2} :=
    isClosed_le continuous_fst continuous_snd
  have hrel : H p ∈ {x : ℝ≥0∞ × ℝ≥0∞ | x.1 ≤ x.2} := by
    apply closure_minimal ?_ hclosed hmem
    rintro _ ⟨x, ⟨n, rfl⟩, rfl⟩
    exact hseq n
  exact hrel

private theorem continuousOn_ennreal_constMul {X : Type*} [TopologicalSpace X]
    {S : Set X} (a : ℝ≥0∞) (ha : a ≠ ⊤) {f : X → ℝ≥0∞}
    (hf : ContinuousOn f S) : ContinuousOn (fun x => a * f x) S := by
  exact (ENNReal.continuous_const_mul ha).continuousOn.comp hf (mapsTo_univ _ _)

private theorem closedBall_cut_subset_ann {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hslt : s < r / 16) (z x : Rd d)
    (hlo : 7 * r / 32 < ‖x - z‖) (hhi : ‖x - z‖ < 95 * r / 32) :
    closedBall x s ⊆ ann z (r / 8) (8 * r) := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  have htri₁ : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    calc
      ‖x - z‖ = ‖(x - y) + (y - z)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y - z‖ := norm_add_le _ _
  have htri₂ : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
    calc
      ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
  constructor <;> nlinarith [norm_sub_rev y x]

private theorem exists_denseSeq_pair {S : Set (Rd d × Rd d)} (hS : S.Nonempty) :
    ∃ q : ℕ → Rd d × Rd d, (∀ n, q n ∈ S) ∧ S ⊆ closure (range q) := by
  letI : Nonempty S := hS.to_subtype
  refine ⟨fun n => (TopologicalSpace.denseSeq S n : Rd d × Rd d),
    fun n => (TopologicalSpace.denseSeq S n).2, ?_⟩
  intro p hp
  rw [_root_.mem_closure_iff]
  intro o ho hpo
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_mem_open
    (ho.preimage continuous_subtype_val) ⟨⟨p, hp⟩, hpo⟩
  exact ⟨_, hn, n, rfl⟩

private theorem goodAnnulus_of_dense_control {G G' : ContMetric d}
    (A η c b : ℝ) (z : Rd d) (r : ℝ)
    (hUopen : IsOpen (ann z (r / 4) (2 * r)))
    (hVopen : IsOpen (ann z (r / 2) (3 * r / 2)))
    (hGlen : G.IsLength) (hG'len : G'.IsLength)
    {qI qO : ℕ → Rd d} {q3 : ℕ → Rd d × Rd d}
    (hqI : ∀ n, qI n ∈ (sphere z (3 * r / 4))) (hqO : ∀ n, qO n ∈ (sphere z r))
    (hq3 : ∀ n, (q3 n).1 ∈ annCl z (3 * r / 4) r ∧ (q3 n).2 ∈ ball (q3 n).1 b)
    (hdenseI : (sphere z (3 * r / 4)) ⊆ closure (range qI)) (hdenseO : (sphere z r) ⊆ closure (range qO))
    (hdense3 : {p : Rd d × Rd d | p.1 ∈ annCl z (3 * r / 4) r ∧ p.2 ∈ ball p.1 b} ⊆ closure (range q3))
    (hSiU : (sphere z (3 * r / 4)) ⊆ ann z (r / 4) (2 * r)) (hSoU : (sphere z r) ⊆ ann z (r / 4) (2 * r))
    (hSiV : (sphere z (3 * r / 4)) ⊆ ann z (r / 2) (3 * r / 2)) (hSoV : (sphere z r) ⊆ ann z (r / 2) (3 * r / 2))
    (hFU : {p : Rd d × Rd d | p.1 ∈ annCl z (3 * r / 4) r ∧ p.2 ∈ ball p.1 b} ⊆
      ann z (r / 4) (2 * r) ×ˢ ann z (r / 4) (2 * r))
    (hcross1 : ∀ i o, G'.internal (ann z (r / 4) (2 * r)) (qI i) (qO o) ≤
      ENNReal.ofReal ((1 + η) * c) * G.internal (ann z (r / 2) (3 * r / 2)) (qI i) (qO o))
    (hcross2 : ∀ i o, G.internal (ann z (r / 4) (2 * r)) (qI i) (qO o) ≤
      ENNReal.ofReal ((1 + η) / c) * G'.internal (ann z (r / 2) (3 * r / 2)) (qI i) (qO o))
    (hdiam1 : ∀ i j, G.internal (ann z (r / 4) (2 * r)) (qI i) (qI j) ≤
      ENNReal.ofReal A * setDistIn G (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r))
    (hdiam2 : ∀ i j, G'.internal (ann z (r / 4) (2 * r)) (qI i) (qI j) ≤
      ENNReal.ofReal A * setDistIn G' (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r))
    (hconn1 : ∀ n, G'.internal (ann z (r / 4) (2 * r)) (q3 n).1 (q3 n).2 ≤
      ENNReal.ofReal (η * c) * setDistIn G (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r))
    (hconn2 : ∀ n, G.internal (ann z (r / 4) (2 * r)) (q3 n).1 (q3 n).2 ≤
      ENNReal.ofReal (η / c) * setDistIn G' (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r)) :
    GoodAnnulus G G' A η c b z r := by
  let U := ann z (r / 4) (2 * r)
  let V := ann z (r / 2) (3 * r / 2)
  have hcrossDense : (sphere z (3 * r / 4)) ×ˢ (sphere z r) ⊆ closure (range (Prod.map qI qO)) := by
    intro p hp
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hdenseI hp.1, hdenseO hp.2⟩
  have hdiamDense : (sphere z (3 * r / 4)) ×ˢ (sphere z (3 * r / 4)) ⊆ closure (range (Prod.map qI qI)) := by
    intro p hp
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hdenseI hp.1, hdenseI hp.2⟩
  have hcrossSetU : (sphere z (3 * r / 4)) ×ˢ (sphere z r) ⊆ U ×ˢ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hSiU hx, hSoU hy⟩
  have hcrossSetV : (sphere z (3 * r / 4)) ×ˢ (sphere z r) ⊆ V ×ˢ V := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hSiV hx, hSoV hy⟩
  have hdiamSetU : (sphere z (3 * r / 4)) ×ˢ (sphere z (3 * r / 4)) ⊆ U ×ˢ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hSiU hx, hSiU hy⟩
  have hDUcont : ContinuousOn (fun p : Rd d × Rd d => G.internal U p.1 p.2) (U ×ˢ U) :=
    G.continuousOn_internal hGlen hUopen
  have hDVcont : ContinuousOn (fun p : Rd d × Rd d => G.internal V p.1 p.2) (V ×ˢ V) :=
    G.continuousOn_internal hGlen hVopen
  have hG'Ucont : ContinuousOn (fun p : Rd d × Rd d => G'.internal U p.1 p.2) (U ×ˢ U) :=
    G'.continuousOn_internal hG'len hUopen
  have hG'Vcont : ContinuousOn (fun p : Rd d × Rd d => G'.internal V p.1 p.2) (V ×ˢ V) :=
    G'.continuousOn_internal hG'len hVopen
  unfold GoodAnnulus
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    constructor
    · exact @pairLe_of_dense d _ _ _ (hG'Ucont.mono hcrossSetU)
        ((continuousOn_ennreal_constMul _ ENNReal.ofReal_ne_top hDVcont).mono hcrossSetV)
        (ℕ × ℕ) (Prod.map qI qO)
        (fun p => ⟨hqI p.1, hqO p.2⟩) hcrossDense
        (fun p => hcross1 p.1 p.2) (x, y) ⟨hx, hy⟩
    · exact @pairLe_of_dense d _ _ _ (hDUcont.mono hcrossSetU)
        ((continuousOn_ennreal_constMul _ ENNReal.ofReal_ne_top hG'Vcont).mono hcrossSetV)
        (ℕ × ℕ) (Prod.map qI qO)
        (fun p => ⟨hqI p.1, hqO p.2⟩) hcrossDense
        (fun p => hcross2 p.1 p.2) (x, y) ⟨hx, hy⟩
  · intro x hx y hy
    constructor
    · exact @pairLe_of_dense d _ _ _ (hDUcont.mono hdiamSetU) continuousOn_const
        (ℕ × ℕ) (Prod.map qI qI)
        (fun p => ⟨hqI p.1, hqI p.2⟩) hdiamDense
        (fun p => hdiam1 p.1 p.2) (x, y) ⟨hx, hy⟩
    · exact @pairLe_of_dense d _ _ _ (hG'Ucont.mono hdiamSetU) continuousOn_const
        (ℕ × ℕ) (Prod.map qI qI)
        (fun p => ⟨hqI p.1, hqI p.2⟩) hdiamDense
        (fun p => hdiam2 p.1 p.2) (x, y) ⟨hx, hy⟩
  · intro x hx w hw
    have hpF : (x, w) ∈ {p : Rd d × Rd d | p.1 ∈ annCl z (3 * r / 4) r ∧ p.2 ∈ ball p.1 b} :=
      ⟨hx, hw⟩
    constructor
    · exact @pairLe_of_dense d _ _ _ (hG'Ucont.mono hFU) continuousOn_const
        ℕ q3 hq3 hdense3 hconn1 (x, w) hpF
    · exact @pairLe_of_dense d _ _ _ (hDUcont.mono hFU) continuousOn_const
        ℕ q3 hq3 hdense3 hconn2 (x, w) hpF

private theorem l32m_aeEventIn_fixed {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (A η c b : ℝ) (z : Rd d) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrad : 0 < locRad ε) (hb : 0 < b)
    (hZ : locMass κ ε (locRad ε) ≠ 0)
    (hsmall : locRad ε + b < r / 16) :
    AEEventIn P (fieldSigma0 h (ann z (r / 8) (8 * r)))
      {ω | GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η c b z r} := by
  let W : Set (Rd d) := ann z (r / 8) (8 * r)
  let U : Set (Rd d) := ann z (r / 4) (2 * r)
  let V : Set (Rd d) := ann z (r / 2) (3 * r / 2)
  have hWopen : IsOpen W := isOpen_ann _ _ _
  have hUopen : IsOpen U := isOpen_ann _ _ _
  have hVopen : IsOpen V := isOpen_ann _ _ _
  have hUW : U ⊆ W := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hVW : V ⊆ W := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let Uo : Opens (Rd d) := ⟨U, hUopen⟩
  let Vo : Opens (Rd d) := ⟨V, hVopen⟩
  let h' : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) r z)
  have hcmeas : Measurable (fun ω => -sphereAvg (h ω) r z) :=
    (measurable_sphereAvg_left r z).comp hS.field.1.measurable |>.neg
  have hh'whole : IsWholeSpaceLGF h' P := hS.field.1.addConst hcmeas
  have hh' : IsLGFPlusCont h' P := hh'whole.isLGFPlusCont
  obtain ⟨FU, hFUm, hUae⟩ := hS.strong.locality P h' hh' Uo
  obtain ⟨FV, hFVm, hVae⟩ := hS.strong.locality P h' hh' Vo
  let dU : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω x y => FU (restrictTo Uo (h' ω)) x y
  let dV : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω x y => FV (restrictTo Vo (h' ω)) x y
  have hdUm : ∀ x y, Measurable[fieldSigmaOn h' W] (fun ω => dU ω x y) := by
    intro x y
    have hcomp : Measurable[fieldSigmaOn h' W] (fun ω => FU (restrictTo Uo (h' ω))) :=
      hFUm.comp (measurable_restrict_sigmaOn hUW)
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hcomp)
  have hdVm : ∀ x y, Measurable[fieldSigmaOn h' W] (fun ω => dV ω x y) := by
    intro x y
    have hcomp : Measurable[fieldSigmaOn h' W] (fun ω => FV (restrictTo Vo (h' ω))) :=
      hFVm.comp (measurable_restrict_sigmaOn hVW)
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hcomp)
  have hdUae : ∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
      dU ω x y = (D (h' ω)).internal U x y := by
    filter_upwards [hUae] with ω hω
    intro x hx y hy
    exact (hω x hx y hy).symm
  have hdVae : ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
      dV ω x y = (D (h' ω)).internal V x y := by
    filter_upwards [hVae] with ω hω
    intro x hx y hy
    exact (hω x hx y hy).symm

  have hradlt : locRad ε < r / 16 := by linarith
  let χ : Rd d → ℝ := fun x => l9bCut (3 * r / 4) ‖x - z‖
  let ψ : Ω → C(Rd d, ℝ) := fun ω => ⟨fun x => χ x * locField κ ε (h' ω) x, by
    exact ((continuous_l9bCut (3 * r / 4)).comp
      (continuous_id.sub continuous_const).norm).mul (continuous_locField hS.seed.kernelSmooth hrad (h' ω))⟩
  have hψeval : ∀ x, Measurable[fieldSigmaOn h' W] (fun ω => ψ ω x) := by
    intro x
    by_cases hχ : χ x = 0
    · have heq : (fun ω => ψ ω x) = fun _ => 0 := by
        funext ω
        simp [ψ, hχ]
      rw [heq]
      exact measurable_const
    · have hcut : l9bCut (3 * r / 4) ‖x - z‖ ≠ 0 := hχ
      obtain ⟨hlo, hhi⟩ := l9bCut_mem_of_ne_zero (by linarith : 0 < 3 * r / 4) hcut
      have hball : closedBall x (locRad ε) ⊆ W := by
        apply closedBall_cut_subset_ann hr hrad.le hradlt z x ?_ ?_
        · nlinarith [hlo]
        · nlinarith [hhi]
      change Measurable[fieldSigmaOn h' W]
        (fun ω => l9bCut (3 * r / 4) ‖x - z‖ * locField κ ε (h' ω) x)
      exact measurable_const.mul
        (l9b_measurable_locField_of_subset hS.seed.kernelSmooth hrad h' hball)
  have hψm : Measurable[fieldSigmaOn h' W] ψ := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    exact ContinuousMap.measurable_iff_eval.mpr hψeval
  have ha := hS.seed.aEps_pos ξ ε hε
  let s : ℝ := (aEps κ ξ ε)⁻¹
  have hs : 0 < s := inv_pos.mpr ha
  have hMeps (ω : Ω) : Meps κ ξ ε (h' ω) =
      (fieldLfppMetric ξ (locFieldC κ ε (h' ω))).smul s hs := by
    simp [Meps, ha, s]
  let M : Ω → ContMetric d := fun ω =>
    (fieldLfppMetric ξ (ψ ω)).smul s hs
  have hfieldMetric : Measurable[fieldSigmaOn h' W]
      (fun ω => fieldLfppMetric ξ (ψ ω)) :=
    (l6c_measurable_fieldLfppMetric ξ).comp hψm
  have hMraw : Measurable[fieldSigmaOn h' W]
      (fun ω => s • (fieldLfppMetric ξ (ψ ω)).1) := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    exact (show Continuous (fun D : ContMetric d => s • D.1) by fun_prop).measurable.comp hfieldMetric
  have hMemb : MeasurableEmbedding ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  have hMm : Measurable[fieldSigmaOn h' W] M := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    apply hMemb.measurable_comp_iff.mp
    convert hMraw using 1
    funext ω
    rfl
  have hMLen : ∀ ω, (M ω).IsLength := fun ω =>
    ContMetric.isLength_smul hs (fieldLfppMetric_isLength ξ (ψ ω))
  have hχU : ∀ x ∈ U, χ x = 1 := by
    intro x hx
    apply l9bCut_eq_one (by positivity : 0 < 3 * r / 4)
    · linarith [hx.1]
    · linarith [hx.2]
  have hχV : ∀ x ∈ V, χ x = 1 := by
    intro x hx
    apply l9bCut_eq_one (by positivity : 0 < 3 * r / 4)
    · linarith [hx.1]
    · linarith [hx.2]
  have hMlocU : ∀ ω, ∀ x ∈ U, ∀ y ∈ U,
      (M ω).internal U x y = (Meps κ ξ ε (h' ω)).internal U x y := by
    intro ω x hx y hy
    change ((fieldLfppMetric ξ (ψ ω)).smul s hs).internal U x y = _
    rw [hMeps ω, ContMetric.internal_smul hs, ContMetric.internal_smul hs]
    apply congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal s * t)
    apply l7a_fieldLfppMetric_internal_congr ξ (ψ ω)
      (locFieldC κ ε (h' ω)) hUopen
    intro v hv
    simp [ψ, χ, hχU v hv, locFieldC, continuous_locField hS.seed.kernelSmooth hrad]
  have hMlocV : ∀ ω, ∀ x ∈ V, ∀ y ∈ V,
      (M ω).internal V x y = (Meps κ ξ ε (h' ω)).internal V x y := by
    intro ω x hx y hy
    change ((fieldLfppMetric ξ (ψ ω)).smul s hs).internal V x y = _
    rw [hMeps ω, ContMetric.internal_smul hs, ContMetric.internal_smul hs]
    apply congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal s * t)
    apply l7a_fieldLfppMetric_internal_congr ξ (ψ ω)
      (locFieldC κ ε (h' ω)) hVopen
    intro v hv
    simp [ψ, χ, hχV v hv, locFieldC, continuous_locField hS.seed.kernelSmooth hrad]

  have hdpos : 0 < d := by have := hS.dim; omega
  letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
  let Si : Set (Rd d) := sphere z (3 * r / 4)
  let So : Set (Rd d) := sphere z r
  obtain ⟨qI, hqI, hqIdense⟩ := exists_denseSeq_rd
    (S := Si) (NormedSpace.sphere_nonempty.2 (by positivity : 0 ≤ 3 * r / 4))
  obtain ⟨qO, hqO, hqOdense⟩ := exists_denseSeq_rd
    (S := So) (NormedSpace.sphere_nonempty.2 hr.le)
  have hSiU : Si ⊆ U := by
    intro x hx
    have hxnorm := mem_sphere_iff_norm.1 hx
    exact ⟨by linarith [hxnorm], by linarith [hxnorm]⟩
  have hSoU : So ⊆ U := by
    intro x hx
    have hxnorm := mem_sphere_iff_norm.1 hx
    exact ⟨by linarith [hxnorm], by linarith [hxnorm]⟩
  have hSiV : Si ⊆ V := by
    intro x hx
    have hxnorm := mem_sphere_iff_norm.1 hx
    exact ⟨by linarith [hxnorm], by linarith [hxnorm]⟩
  have hSoV : So ⊆ V := by
    intro x hx
    have hxnorm := mem_sphere_iff_norm.1 hx
    exact ⟨by linarith [hxnorm], by linarith [hxnorm]⟩
  obtain ⟨IU, hIUm, hIUeq⟩ := measurable_internal hUopen
  obtain ⟨IV, hIVm, hIVeq⟩ := measurable_internal hVopen
  let mU : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω x y => IU (M ω, (x, y))
  let mV : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω x y => IV (M ω, (x, y))
  have hmUm : ∀ x y, Measurable[fieldSigmaOn h' W] (fun ω => mU ω x y) := by
    intro x y
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    have htuple : Measurable[fieldSigmaOn h' W] (fun ω => (M ω, x, y)) := by
      exact hMm.prodMk (measurable_const.prodMk measurable_const)
    exact hIUm.comp htuple
  have hmVm : ∀ x y, Measurable[fieldSigmaOn h' W] (fun ω => mV ω x y) := by
    intro x y
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    have htuple : Measurable[fieldSigmaOn h' W] (fun ω => (M ω, x, y)) := by
      exact hMm.prodMk (measurable_const.prodMk measurable_const)
    exact hIVm.comp htuple
  have hMepsLen : ∀ ω, (Meps κ ξ ε (h' ω)).IsLength := by
    intro ω
    rw [hMeps ω]
    exact ContMetric.isLength_smul hs
      (fieldLfppMetric_isLength ξ (locFieldC κ ε (h' ω)))
  let δD : Ω → ℝ≥0∞ := fun ω => ⨅ p : ℕ × ℕ, dU ω (qI p.1) (qO p.2)
  let δM : Ω → ℝ≥0∞ := fun ω => ⨅ p : ℕ × ℕ, mU ω (qI p.1) (qO p.2)
  have hδDm : Measurable[fieldSigmaOn h' W] δD := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    exact Measurable.iInf fun p => hdUm (qI p.1) (qO p.2)
  have hδMm : Measurable[fieldSigmaOn h' W] δM := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    exact Measurable.iInf fun p => hmUm (qI p.1) (qO p.2)

  let F3 : Set (Rd d × Rd d) := {p | p.1 ∈ annCl z (3 * r / 4) r ∧ p.2 ∈ ball p.1 b}
  have hF3ne : F3.Nonempty := by
    refine ⟨(qI 0, qI 0), ?_⟩
    have hxnorm := mem_sphere_iff_norm.1 (hqI 0)
    exact ⟨⟨by linarith [hxnorm], by linarith [hxnorm]⟩, Metric.mem_ball_self hb⟩
  obtain ⟨q3, hq3, hq3dense⟩ := exists_denseSeq_pair hF3ne
  have hF3U : F3 ⊆ U ×ˢ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hyx : ‖y - x‖ < b := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hxy : ‖x - y‖ < b := by simpa [norm_sub_rev] using hyx
    have htri₁ : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
      calc
        ‖x - z‖ = ‖(x - y) + (y - z)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have htri₂ : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
      calc
        ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    constructor
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact ⟨by linarith [hx.1, hyx], by linarith [hx.2, hyx]⟩
  have hF3Uq : ∀ n, q3 n ∈ U ×ˢ U := fun n => hF3U (hq3 n)
  have hq3shape : ∀ n, (q3 n).1 ∈ annCl z (3 * r / 4) r ∧
      (q3 n).2 ∈ ball (q3 n).1 b := by
    intro n
    simpa only [F3, Set.mem_setOf_eq] using hq3 n

  let Ecross : Set Ω := ⋂ p : ℕ × ℕ, {ω |
    mU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) * c) * dV ω (qI p.1) (qO p.2) ∧
    dU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) / c) * mV ω (qI p.1) (qO p.2)}
  let Ediam : Set Ω := ⋂ p : ℕ × ℕ, {ω |
    dU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δD ω ∧
    mU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δM ω}
  let Econn : Set Ω := ⋂ n : ℕ, {ω |
    mU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η * c) * δD ω ∧
    dU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η / c) * δM ω}
  let E : Set Ω := Ecross ∩ Ediam ∩ Econn
  have hEcross : MeasurableSet[fieldSigmaOn h' W] Ecross := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    apply MeasurableSet.iInter
    intro p
    exact (measurableSet_le (hmUm (qI p.1) (qO p.2))
      (measurable_const.mul (hdVm (qI p.1) (qO p.2)))).inter
      (measurableSet_le (hdUm (qI p.1) (qO p.2))
        (measurable_const.mul (hmVm (qI p.1) (qO p.2))))
  have hEdiam : MeasurableSet[fieldSigmaOn h' W] Ediam := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    apply MeasurableSet.iInter
    intro p
    exact (measurableSet_le (hdUm (qI p.1) (qI p.2))
      (measurable_const.mul hδDm)).inter
      (measurableSet_le (hmUm (qI p.1) (qI p.2))
        (measurable_const.mul hδMm))
  have hEconn : MeasurableSet[fieldSigmaOn h' W] Econn := by
    letI : MeasurableSpace Ω := fieldSigmaOn h' W
    apply MeasurableSet.iInter
    intro n
    exact (measurableSet_le (hmUm (q3 n).1 (q3 n).2)
      (measurable_const.mul hδDm)).inter
      (measurableSet_le (hdUm (q3 n).1 (q3 n).2)
        (measurable_const.mul hδMm))
  have hEm : MeasurableSet[fieldSigmaOn h' W] E := (hEcross.inter hEdiam).inter hEconn

  have hDlen : ∀ᵐ ω ∂P, (D (h' ω)).IsLength := hS.strong.length P h' hh'
  have hδDae : ∀ᵐ ω ∂P, δD ω =
      setDistIn (D (h' ω)) U Si So := by
    filter_upwards [hDlen, hdUae] with ω hlen hloc
    have hformula := setDistIn_eq_iInf_dense (D (h' ω)) hlen hUopen hSiU hSoU
      hqI hqO hqIdense hqOdense
    have hcoords : δD ω = ⨅ p : ℕ × ℕ,
        (D (h' ω)).internal U (qI p.1) (qO p.2) := by
      apply iInf_congr
      intro p
      exact hloc (qI p.1) (hSiU (hqI p.1)) (qO p.2) (hSoU (hqO p.2))
    exact hcoords.trans hformula.symm
  have hδMae : ∀ᵐ ω ∂P, δM ω =
      setDistIn (Meps κ ξ ε (h' ω)) U Si So := by
    filter_upwards [] with ω
    have hlen := hMepsLen ω
    have hformula := setDistIn_eq_iInf_dense (Meps κ ξ ε (h' ω)) hlen hUopen hSiU hSoU
      hqI hqO hqIdense hqOdense
    have hcoords : δM ω = ⨅ p : ℕ × ℕ,
        (Meps κ ξ ε (h' ω)).internal U (qI p.1) (qO p.2) := by
      apply iInf_congr
      intro p
      have hmcoord : mU ω (qI p.1) (qO p.2) =
          (Meps κ ξ ε (h' ω)).internal U (qI p.1) (qO p.2) := by
        change IU (M ω, (qI p.1, qO p.2)) = _
        calc
          IU (M ω, (qI p.1, qO p.2)) = (M ω).internal U (qI p.1) (qO p.2) :=
            (hIUeq (M ω) (hMLen ω) (qI p.1) (qO p.2)).symm
          _ = (Meps κ ξ ε (h' ω)).internal U (qI p.1) (qO p.2) :=
            hMlocU ω (qI p.1) (hSiU (hqI p.1)) (qO p.2) (hSoU (hqO p.2))
      exact hmcoord
    exact hcoords.trans hformula.symm

  have hcntEq (ω : Ω) : ω ∈ E ↔
      (∀ p : ℕ × ℕ,
        mU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) * c) * dV ω (qI p.1) (qO p.2) ∧
        dU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) / c) * mV ω (qI p.1) (qO p.2)) ∧
      (∀ p : ℕ × ℕ,
        dU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δD ω ∧
        mU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δM ω) ∧
      (∀ n : ℕ,
        mU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η * c) * δD ω ∧
        dU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η / c) * δM ω) := by
    constructor
    · intro hE
      rcases hE with ⟨⟨hc, hd⟩, hn⟩
      have hc' : ∀ p : ℕ × ℕ,
          mU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) * c) * dV ω (qI p.1) (qO p.2) ∧
          dU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) / c) * mV ω (qI p.1) (qO p.2) := by
        simpa only [Ecross, Set.mem_iInter, Set.mem_setOf_eq] using hc
      have hd' : ∀ p : ℕ × ℕ,
          dU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δD ω ∧
          mU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δM ω := by
        simpa only [Ediam, Set.mem_iInter, Set.mem_setOf_eq] using hd
      have hn' : ∀ n : ℕ,
          mU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η * c) * δD ω ∧
          dU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η / c) * δM ω := by
        simpa only [Econn, Set.mem_iInter, Set.mem_setOf_eq] using hn
      exact ⟨hc', hd', hn'⟩
    · rintro ⟨hc, hd, hn⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [Ecross, Set.mem_iInter, Set.mem_ofPred_eq] using hc
      · simpa only [Ediam, Set.mem_iInter, Set.mem_ofPred_eq] using hd
      · simpa only [Econn, Set.mem_iInter, Set.mem_ofPred_eq] using hn

  have hcrossDense : Si ×ˢ So ⊆ closure (range (Prod.map qI qO)) := by
    intro p hp
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hqIdense hp.1, hqOdense hp.2⟩
  have hdiamDense : Si ×ˢ Si ⊆ closure (range (Prod.map qI qI)) := by
    intro p hp
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hqIdense hp.1, hqIdense hp.2⟩
  have hcrossSetU : Si ×ˢ So ⊆ U ×ˢ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hSiU hx, hSoU hy⟩
  have hcrossSetV : Si ×ˢ So ⊆ V ×ˢ V := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hSiV hx, hSoV hy⟩
  have hdiamSetU : Si ×ˢ Si ⊆ U ×ˢ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hSiU hx, hSiU hy⟩

  have hGoodFromCount (ω : Ω) (hLenD : (D (h' ω)).IsLength)
      (hLenM : (Meps κ ξ ε (h' ω)).IsLength)
      (hLocDU : ∀ x ∈ U, ∀ y ∈ U, dU ω x y = (D (h' ω)).internal U x y)
      (hLocDV : ∀ x ∈ V, ∀ y ∈ V, dV ω x y = (D (h' ω)).internal V x y)
      (hLocMU : ∀ x ∈ U, ∀ y ∈ U, mU ω x y = (Meps κ ξ ε (h' ω)).internal U x y)
      (hLocMV : ∀ x ∈ V, ∀ y ∈ V, mV ω x y = (Meps κ ξ ε (h' ω)).internal V x y)
      (hDeltaD : δD ω = setDistIn (D (h' ω)) U Si So)
      (hDeltaM : δM ω = setDistIn (Meps κ ξ ε (h' ω)) U Si So)
      (hCross : ∀ p : ℕ × ℕ,
        mU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) * c) * dV ω (qI p.1) (qO p.2) ∧
        dU ω (qI p.1) (qO p.2) ≤ ENNReal.ofReal ((1 + η) / c) * mV ω (qI p.1) (qO p.2))
      (hDiam : ∀ p : ℕ × ℕ,
        dU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δD ω ∧
        mU ω (qI p.1) (qI p.2) ≤ ENNReal.ofReal A * δM ω)
      (hConn : ∀ n : ℕ,
        mU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η * c) * δD ω ∧
        dU ω (q3 n).1 (q3 n).2 ≤ ENNReal.ofReal (η / c) * δM ω) :
      GoodAnnulus (D (h' ω)) (Meps κ ξ ε (h' ω)) A η c b z r := by
    apply goodAnnulus_of_dense_control A η c b z r hUopen hVopen hLenD hLenM
      hqI hqO hq3shape hqIdense hqOdense hq3dense hSiU hSoU hSiV hSoV hF3U
    · intro i o
      have hc := (hCross ⟨i, o⟩).1
      calc
        (Meps κ ξ ε (h' ω)).internal U (qI i) (qO o) = mU ω (qI i) (qO o) :=
          (hLocMU (qI i) (hSiU (hqI i)) (qO o) (hSoU (hqO o))).symm
        _ ≤ ENNReal.ofReal ((1 + η) * c) * dV ω (qI i) (qO o) := hc
        _ = ENNReal.ofReal ((1 + η) * c) * (D (h' ω)).internal V (qI i) (qO o) := by
          rw [hLocDV (qI i) (hSiV (hqI i)) (qO o) (hSoV (hqO o))]
    · intro i o
      have hc := (hCross ⟨i, o⟩).2
      calc
        (D (h' ω)).internal U (qI i) (qO o) = dU ω (qI i) (qO o) :=
          (hLocDU (qI i) (hSiU (hqI i)) (qO o) (hSoU (hqO o))).symm
        _ ≤ ENNReal.ofReal ((1 + η) / c) * mV ω (qI i) (qO o) := hc
        _ = ENNReal.ofReal ((1 + η) / c) * (Meps κ ξ ε (h' ω)).internal V (qI i) (qO o) := by
          rw [hLocMV (qI i) (hSiV (hqI i)) (qO o) (hSoV (hqO o))]
    · intro i j
      have hc := (hDiam ⟨i, j⟩).1
      calc
        (D (h' ω)).internal U (qI i) (qI j) = dU ω (qI i) (qI j) :=
          (hLocDU (qI i) (hSiU (hqI i)) (qI j) (hSiU (hqI j))).symm
        _ ≤ ENNReal.ofReal A * δD ω := hc
        _ = ENNReal.ofReal A * setDistIn (D (h' ω)) U Si So := by rw [hDeltaD]
    · intro i j
      have hc := (hDiam ⟨i, j⟩).2
      calc
        (Meps κ ξ ε (h' ω)).internal U (qI i) (qI j) = mU ω (qI i) (qI j) :=
          (hLocMU (qI i) (hSiU (hqI i)) (qI j) (hSiU (hqI j))).symm
        _ ≤ ENNReal.ofReal A * δM ω := hc
        _ = ENNReal.ofReal A * setDistIn (Meps κ ξ ε (h' ω)) U Si So := by rw [hDeltaM]
    · intro n
      have hc := (hConn n).1
      have hp := hq3 n
      calc
        (Meps κ ξ ε (h' ω)).internal U (q3 n).1 (q3 n).2 = mU ω (q3 n).1 (q3 n).2 :=
          (hLocMU (q3 n).1 (hF3U hp).1 (q3 n).2 (hF3U hp).2).symm
        _ ≤ ENNReal.ofReal (η * c) * δD ω := hc
        _ = ENNReal.ofReal (η * c) * setDistIn (D (h' ω)) U Si So := by rw [hDeltaD]
    · intro n
      have hc := (hConn n).2
      have hp := hq3 n
      calc
        (D (h' ω)).internal U (q3 n).1 (q3 n).2 = dU ω (q3 n).1 (q3 n).2 :=
          (hLocDU (q3 n).1 (hF3U hp).1 (q3 n).2 (hF3U hp).2).symm
        _ ≤ ENNReal.ofReal (η / c) * δM ω := hc
        _ = ENNReal.ofReal (η / c) * setDistIn (Meps κ ξ ε (h' ω)) U Si So := by rw [hDeltaM]

  have hGoodEquiv (ω : Ω)
      (hLenD : (D (h' ω)).IsLength)
      (hLocDU : ∀ x ∈ U, ∀ y ∈ U, dU ω x y = (D (h' ω)).internal U x y)
      (hLocDV : ∀ x ∈ V, ∀ y ∈ V, dV ω x y = (D (h' ω)).internal V x y)
      (hDeltaD : δD ω = setDistIn (D (h' ω)) U Si So)
      (hDeltaM : δM ω = setDistIn (Meps κ ξ ε (h' ω)) U Si So) :
      ω ∈ E ↔ GoodAnnulus (D (h' ω)) (Meps κ ξ ε (h' ω)) A η c b z r := by
    have hLocMU : ∀ x ∈ U, ∀ y ∈ U,
        mU ω x y = (Meps κ ξ ε (h' ω)).internal U x y := by
      intro x hx y hy
      change IU (M ω, (x, y)) = _
      calc
        IU (M ω, (x, y)) = (M ω).internal U x y :=
          (hIUeq (M ω) (hMLen ω) x y).symm
        _ = (Meps κ ξ ε (h' ω)).internal U x y := hMlocU ω x hx y hy
    have hLocMV : ∀ x ∈ V, ∀ y ∈ V,
        mV ω x y = (Meps κ ξ ε (h' ω)).internal V x y := by
      intro x hx y hy
      change IV (M ω, (x, y)) = _
      calc
        IV (M ω, (x, y)) = (M ω).internal V x y :=
          (hIVeq (M ω) (hMLen ω) x y).symm
        _ = (Meps κ ξ ε (h' ω)).internal V x y := hMlocV ω x hx y hy
    have hLenM : (Meps κ ξ ε (h' ω)).IsLength := hMepsLen ω
    have hcount := hcntEq ω
    constructor
    · intro hE
      rcases hcount.mp hE with ⟨hCross, hDiam, hConn⟩
      exact hGoodFromCount ω hLenD hLenM hLocDU hLocDV hLocMU hLocMV hDeltaD hDeltaM
        hCross hDiam hConn
    · intro hGood
      apply (hcntEq ω).mpr
      refine ⟨?_, ?_, ?_⟩
      · intro p
        have hc := hGood.1 (qI p.1) (hqI p.1) (qO p.2) (hqO p.2)
        constructor
        · calc
            mU ω (qI p.1) (qO p.2) =
                (Meps κ ξ ε (h' ω)).internal U (qI p.1) (qO p.2) :=
              hLocMU (qI p.1) (hSiU (hqI p.1)) (qO p.2) (hSoU (hqO p.2))
            _ ≤ ENNReal.ofReal ((1 + η) * c) * (D (h' ω)).internal V (qI p.1) (qO p.2) := hc.1
            _ = ENNReal.ofReal ((1 + η) * c) * dV ω (qI p.1) (qO p.2) := by
              rw [hLocDV (qI p.1) (hSiV (hqI p.1)) (qO p.2) (hSoV (hqO p.2))]
        · calc
            dU ω (qI p.1) (qO p.2) = (D (h' ω)).internal U (qI p.1) (qO p.2) :=
              hLocDU (qI p.1) (hSiU (hqI p.1)) (qO p.2) (hSoU (hqO p.2))
            _ ≤ ENNReal.ofReal ((1 + η) / c) * (Meps κ ξ ε (h' ω)).internal V (qI p.1) (qO p.2) := hc.2
            _ = ENNReal.ofReal ((1 + η) / c) * mV ω (qI p.1) (qO p.2) := by
              rw [hLocMV (qI p.1) (hSiV (hqI p.1)) (qO p.2) (hSoV (hqO p.2))]
      · intro p
        have hc := hGood.2.1 (qI p.1) (hqI p.1) (qI p.2) (hqI p.2)
        constructor
        · calc
            dU ω (qI p.1) (qI p.2) = (D (h' ω)).internal U (qI p.1) (qI p.2) :=
              hLocDU (qI p.1) (hSiU (hqI p.1)) (qI p.2) (hSiU (hqI p.2))
            _ ≤ ENNReal.ofReal A * δD ω := by
              calc
                _ ≤ ENNReal.ofReal A * setDistIn (D (h' ω)) U Si So := hc.1
                _ = ENNReal.ofReal A * δD ω := by rw [← hDeltaD]
        · calc
            mU ω (qI p.1) (qI p.2) = (Meps κ ξ ε (h' ω)).internal U (qI p.1) (qI p.2) :=
              hLocMU (qI p.1) (hSiU (hqI p.1)) (qI p.2) (hSiU (hqI p.2))
            _ ≤ ENNReal.ofReal A * δM ω := by
              calc
                _ ≤ ENNReal.ofReal A * setDistIn (Meps κ ξ ε (h' ω)) U Si So := hc.2
                _ = ENNReal.ofReal A * δM ω := by rw [← hDeltaM]
      · intro n
        have hp := hq3 n
        have hc := hGood.2.2 (q3 n).1 (hq3shape n).1 (q3 n).2 (hq3shape n).2
        constructor
        · calc
            mU ω (q3 n).1 (q3 n).2 =
                (Meps κ ξ ε (h' ω)).internal U (q3 n).1 (q3 n).2 :=
              hLocMU (q3 n).1 (hF3U hp).1 (q3 n).2 (hF3U hp).2
            _ ≤ ENNReal.ofReal (η * c) * δD ω := by
              calc
                _ ≤ ENNReal.ofReal (η * c) * setDistIn (D (h' ω)) U Si So := hc.1
                _ = ENNReal.ofReal (η * c) * δD ω := by rw [← hDeltaD]
        · calc
            dU ω (q3 n).1 (q3 n).2 = (D (h' ω)).internal U (q3 n).1 (q3 n).2 :=
              hLocDU (q3 n).1 (hF3U hp).1 (q3 n).2 (hF3U hp).2
            _ ≤ ENNReal.ofReal (η / c) * δM ω := by
              calc
                _ ≤ ENNReal.ofReal (η / c) * setDistIn (Meps κ ξ ε (h' ω)) U Si So := hc.2
                _ = ENNReal.ofReal (η / c) * δM ω := by rw [← hDeltaM]

  have hEae : ∀ᵐ ω ∂P,
      (ω ∈ E ↔ GoodAnnulus (D (h' ω)) (Meps κ ξ ε (h' ω)) A η c b z r) := by
    filter_upwards [hDlen, hdUae, hdVae, hδDae, hδMae] with ω hlen hlu hlv hδd hδm
    exact hGoodEquiv ω hlen hlu hlv hδd hδm

  have hSphereW : sphere z r ⊆ W := by
    intro x hx
    have hxnorm := mem_sphere_iff_norm.1 hx
    exact ⟨by linarith [hxnorm], by linarith [hxnorm]⟩
  have hd2 : 2 ≤ d := le_trans (by norm_num) hS.dim
  have hErecent : AEEventIn P (fieldSigma0 h W) E :=
    aeEventIn_of_recentred hd2 hS.field.1 hWopen hr hSphereW hEm
  have hDscale : ∀ᵐ ω ∂P,
      D (h' ω) = (D (h ω)).smul (Real.exp (ξ * (-sphereAvg (h ω) r z)))
        (Real.exp_pos _) := by
    filter_upwards [hS.strong.ae_apply_addFun_const hS.field.1.isLGFPlusCont] with ω hweyl
    have hdist : ∀ x y : Rd d,
        (D (h' ω)).1 (x, y) =
          Real.exp (ξ * (-sphereAvg (h ω) r z)) * (D (h ω)).1 (x, y) := by
      intro x y
      simpa only [h', addFun_const] using hweyl (-sphereAvg (h ω) r z) x y
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    rw [ContMetric.smul_apply]
    exact hdist p.1 p.2
  have hMscale (ω : Ω) : Core.Meps κ ξ ε (h' ω) =
      (Core.Meps κ ξ ε (h ω)).smul (Real.exp (ξ * (-sphereAvg (h ω) r z)))
        (Real.exp_pos _) := by
    simpa only [h'] using Meps_addConst hS.seed.kernelSmooth hrad hZ ha (h ω)
      (-sphereAvg (h ω) r z)
  have hHom : ∀ᵐ ω ∂P,
      (GoodAnnulus (D (h' ω)) (Core.Meps κ ξ ε (h' ω)) A η c b z r ↔
        GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η c b z r) := by
    filter_upwards [hDscale] with ω hDω
    rw [hDω, hMscale ω]
    exact goodAnnulus_smul_iff _ _ A η c b (Real.exp (ξ * (-sphereAvg (h ω) r z))) z r
      (Real.exp_pos _)
  have hEeq : E =ᵐ[P] {ω | GoodAnnulus (D (h' ω)) (Core.Meps κ ξ ε (h' ω)) A η c b z r} := by
    filter_upwards [hEae] with ω hω
    exact propext hω
  have hErecentGood : AEEventIn P (fieldSigma0 h W)
      {ω | GoodAnnulus (D (h' ω)) (Core.Meps κ ξ ε (h' ω)) A η c b z r} :=
    l9b_aeEventIn_congr hErecent hEeq
  have hHomSet :
      {ω | GoodAnnulus (D (h' ω)) (Core.Meps κ ξ ε (h' ω)) A η c b z r} =ᵐ[P]
      {ω | GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η c b z r} := by
    filter_upwards [hHom] with ω hω
    exact propext hω
  exact l9b_aeEventIn_congr hErecentGood hHomSet

private theorem eventually_l32meas_small {u q₀ : ℝ}
    (huq : u < q₀) (hq₀ : q₀ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), locRad ε + 8 * ε ^ q₀ < ε ^ u / 16 := by
  let α : ℝ := (1 - u) / 2
  let β : ℝ := q₀ - u
  have hα : 0 < α := by dsimp [α]; linarith [hq₀, huq]
  have hβ : 0 < β := by dsimp [β]; linarith
  have hpow (a : ℝ) (ha : 0 < a) :
      Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
    have ht := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hαsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ α < 1 / 2 :=
    (hpow α hα).eventually (Iio_mem_nhds (by norm_num))
  have hβsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ β < 1 / 256 :=
    (hpow β hβ).eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin,
    l9b_eventually_locRad_small (ζ := 1 - u) (by linarith [hq₀, huq]),
    hαsmall, hβsmall] with ε hε hrad hαε hβε
  have hεpos : 0 < ε := hε
  have hsplitRad : ε ^ (1 - (1 - u) / 2) = ε ^ u * ε ^ α := by
    calc
      ε ^ (1 - (1 - u) / 2) = ε ^ (u + α) := by congr 1 <;> dsimp [α] <;> ring
      _ = ε ^ u * ε ^ α := by rw [Real.rpow_add hεpos]
  have hsplitB : ε ^ q₀ = ε ^ u * ε ^ β := by
    calc
      ε ^ q₀ = ε ^ (u + β) := by congr 1 <;> dsimp [β] <;> ring
      _ = ε ^ u * ε ^ β := by rw [Real.rpow_add hεpos]
  have huPow : 0 < ε ^ u := Real.rpow_pos_of_pos hεpos u
  have hrad24 : 24 * locRad ε ≤ ε ^ u * ε ^ α := by
    rw [← hsplitRad]
    exact hrad
  have hrad48 : locRad ε < ε ^ u / 48 := by
    have hlt : 24 * locRad ε < ε ^ u * (1 / 2) :=
      lt_of_le_of_lt hrad24 (mul_lt_mul_of_pos_left hαε huPow)
    nlinarith
  have hb32 : 8 * ε ^ q₀ < ε ^ u / 32 := by
    calc
      8 * ε ^ q₀ = ε ^ u * (8 * ε ^ β) := by rw [hsplitB]; ring
      _ < ε ^ u * (8 * (1 / 256)) :=
        mul_lt_mul_of_pos_left (by nlinarith) huPow
      _ = ε ^ u / 32 := by ring
  have hsum := add_lt_add hrad48 hb32
  have hcoeff : (1 / 48 : ℝ) + 1 / 32 < 1 / 16 := by norm_num
  nlinarith [huPow]

/-- Lemma 3.2, measurability (3.7) of the good annulus event. -/
theorem lemma32Meas_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.Lemma32Meas κ ξ Q D P h := by
  intro A η u q₀ hA hη hu huq hq₀
  have hev := (eventually_l32meas_small huq hq₀).and hS.seed.locHyp
  obtain ⟨ε₀, hε₀, Hev⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε z r hwindow
  have hεpos : 0 < ε := hε.1
  have hεlt : ε < ε₀ := hε.2
  obtain ⟨hsmallε, hloc⟩ := Hev hε
  obtain ⟨-, -, hrad, -, hmass⟩ := hloc
  have hwinlo : ε ^ u ≤ r := by
    change r ∈ (fun k : ℤ => (256 : ℝ) ^ (-k)) ''
      {k : ℤ | ε ^ u ≤ (256 : ℝ) ^ (-k) ∧ (256 : ℝ) ^ (-k) ≤ ε ^ (u / 2)} at hwindow
    rcases (Set.mem_image _ _ _).1 hwindow with ⟨k, hk, hkr⟩
    rw [← hkr]
    exact hk.1
  have hr : 0 < r := (Real.rpow_pos_of_pos hεpos u).trans_le hwinlo
  have hb : 0 < 8 * ε ^ q₀ := by positivity
  have hZ : locMass κ ε (locRad ε) ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by norm_num) hmass
  have hsmall : locRad ε + 8 * ε ^ q₀ < r / 16 := by
    have hlt := hsmallε
    nlinarith
  exact l32m_aeEventIn_fixed hS A η (cRatio κ ξ Q ε r) (8 * ε ^ q₀) z
    hεpos hr hrad hb hZ hsmall

end HigherDimLFPPAS.Annulus
