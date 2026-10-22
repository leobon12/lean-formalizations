import HigherDimLQGMetric.Sec4.Lemma43
import HigherDimLQGMetric.Sharp.ShellMeas
import HigherDimLQGMetric.ShellDec.Tail

/-!
# Locality of the good shell event (packet L9b; MA6 P3, [1] proof of Lemma 4.4)

`ref1_lemma43_aeEventIn`: for `24 s(ε) ≤ r` (`s(ε) = locRad ε`, the localization radius), the event `E^ε_r(u; C)`
is almost surely equal to an event of `fieldSigma0 h (A_{r/4,4r}(u))`, the σ-algebra of the field modulo
constants on the shell — the input of the shell decoupling (G3's `lemmaA1`).

* Events (1)–(2): W1's `exists_shellVersions` (locality and Weyl scaling of the weak metric).
* Events (3)–(4): with the recentred field `h' = h - h_r(u)`, `ĥ*_ε(h') = ĥ*_ε(h) - h_r(u)` exactly, so the
  events are `{C⁻¹ r 𝔞_{ε/r} ≤ D̂(h')(…)}` and `{diam D̂(h') ≤ C r 𝔞_{ε/r}}`; on `A_{r/3,3r}(u)` the field
  `ĥ*_ε(h')` coincides with a cut-off copy `H = χ ĥ*_ε(h')`, all of whose values are pairings of `h'` with test
  functions supported in `A_{r/4,4r}(u)` (`χ` vanishes off `A_{7r/24, 95r/24}(u)`, and `s ≤ r/24`); the
  functionals are measurable in such a field (DGZ, countable dense pairs); G3's `aeEventIn_of_recentred`
  turns events of the recentred field into `AEEventIn` events of `fieldSigma0 h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

theorem l9b_aeEventIn_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    {V : Set (Rd d)} {E₁ E₂ : Set Ω} (h₁ : AEEventIn P (fieldSigma0 h V) E₁)
    (h₂ : AEEventIn P (fieldSigma0 h V) E₂) : AEEventIn P (fieldSigma0 h V) (E₁ ∩ E₂) := by
  obtain ⟨F₁, hF₁, he₁⟩ := h₁
  obtain ⟨F₂, hF₂, he₂⟩ := h₂
  exact ⟨F₁ ∩ F₂, hF₁.inter hF₂, he₁.inter he₂⟩

theorem l9b_aeEventIn_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    {V : Set (Rd d)} {E₁ E₂ : Set Ω} (h₁ : AEEventIn P (fieldSigma0 h V) E₁)
    (he : E₁ =ᵐ[P] E₂) : AEEventIn P (fieldSigma0 h V) E₂ := by
  obtain ⟨F, hF, hEF⟩ := h₁
  exact ⟨F, hF, he.symm.trans hEF⟩

/-! ## The cutoff -/

/-- the radial cutoff, `1` on `[r/3, 3r]`, `0` off `(7r/24, 95r/24)` -/
def l9bCut (r t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - 7 * r / 24) * (24 / r)) ((95 * r / 24 - t) * (24 / (23 * r)))))

theorem continuous_l9bCut (r : ℝ) : Continuous (l9bCut r) := by
  unfold l9bCut
  fun_prop

theorem l9bCut_eq_one {r t : ℝ} (hr : 0 < r) (h1 : r / 3 ≤ t) (h2 : t ≤ 3 * r) :
    l9bCut r t = 1 := by
  unfold l9bCut
  have e1 : 1 ≤ (t - 7 * r / 24) * (24 / r) := by
    have : (t - 7 * r / 24) * (24 / r) = 24 * (t - 7 * r / 24) / r := by ring
    rw [this, le_div_iff₀ hr]
    linarith
  have e2 : 1 ≤ (95 * r / 24 - t) * (24 / (23 * r)) := by
    have : (95 * r / 24 - t) * (24 / (23 * r)) = 24 * (95 * r / 24 - t) / (23 * r) := by ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

theorem l9bCut_mem_of_ne_zero {r t : ℝ} (hr : 0 < r) (h : l9bCut r t ≠ 0) :
    7 * r / 24 < t ∧ t < 95 * r / 24 := by
  unfold l9bCut at h
  by_contra hcon
  rw [not_and_or, not_lt, not_lt] at hcon
  apply h
  apply max_eq_left
  rcases hcon with ht | ht
  · have : (t - 7 * r / 24) * (24 / r) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    exact (min_le_right _ _).trans ((min_le_left _ _).trans this)
  · have : (95 * r / 24 - t) * (24 / (23 * r)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    exact (min_le_right _ _).trans ((min_le_right _ _).trans this)

/-! ## Measurability of the LFPP shell functionals of the recentred localized field -/

/-- the values of `ĥ*_ε(g)` at points `z` with `B̄_s(z) ⊆ V` are measurable for `fieldSigmaOn g V` -/
theorem l9b_measurable_locField_of_subset {κ : Rd d → ℝ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (convKernel κ)) {ε : ℝ} (hrad : 0 < locRad ε) {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → DistRd d) {V : Set (Rd d)} {z : Rd d} (hz : closedBall z (locRad ε) ⊆ V) :
    Measurable[fieldSigmaOn g V] fun ω => locField κ ε (g ω) z := by
  let ψ : {θ : TestRd d // tsupport (θ : Rd d → ℝ) ⊆ V} :=
    ⟨locTest κ ε (locRad ε) z, (tsupport_locTest_subset hK hrad z).trans hz⟩
  have hsrc : Measurable[fieldSigmaOn g V]
      (fun ω (ψ : {θ : TestRd d // tsupport (θ : Rd d → ℝ) ⊆ V}) => g ω ψ.1) :=
    Measurable.of_comap_le le_rfl
  have hp : Measurable[fieldSigmaOn g V] (fun ω => g ω ψ.1) := (measurable_pi_apply ψ).comp hsrc
  exact measurable_const.mul hp

theorem l9b_closedBall_subset_ann {u z : Rd d} {r s : ℝ} (hs : 24 * s ≤ r) (_hs0 : 0 ≤ s)
    (h1 : 7 * r / 24 < ‖z - u‖) (h2 : ‖z - u‖ < 95 * r / 24) :
    closedBall z s ⊆ ann u (r / 4) (4 * r) := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hle1 : ‖z - u‖ ≤ ‖w - z‖ + ‖w - u‖ := by
    calc ‖z - u‖ = ‖(w - u) - (w - z)‖ := by congr 1; abel
      _ ≤ ‖w - u‖ + ‖w - z‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have hle2 : ‖w - u‖ ≤ ‖w - z‖ + ‖z - u‖ := by
    calc ‖w - u‖ = ‖(w - z) + (z - u)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  constructor <;> linarith

/-- **Locality of the LFPP events (3)–(4)**: for `24 s(ε) ≤ r` and any field process `g`, the events
`{A ≤ D̂(g)(∂B_{r/2}, ∂B_r; A_{r/3,3r})}` and `{diam_{A_{r/2,2r}} D̂(g)(∂B_r) ≤ B}` are measurable for
`fieldSigmaOn g (A_{r/4,4r}(u))`. -/
theorem l9b_measurableSet_lfpp_shell (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (ξ : ℝ) {ε : ℝ}
    (hrad : 0 < locRad ε) {r : ℝ} (hr24 : 24 * locRad ε ≤ r) (u : Rd d) {Ω : Type*}
    [MeasurableSpace Ω] (g : Ω → DistRd d) (a b : ℝ) :
    MeasurableSet[fieldSigmaOn g (ann u (r / 4) (4 * r))] {ω | a ≤ DGZ.lfppSetDist ξ
      (locField κ ε (g ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)} ∧
    MeasurableSet[fieldSigmaOn g (ann u (r / 4) (4 * r))] {ω | DGZ.lfppDiam ξ
      (locField κ ε (g ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤ b} := by
  have hr : 0 < r := by linarith
  set V := ann u (r / 4) (4 * r)
  let m : MeasurableSpace Ω := fieldSigmaOn g V
  let H : Rd d → Ω → ℝ := fun z ω => l9bCut r ‖z - u‖ * locField κ ε (g ω) z
  have hHc : ∀ ω, Continuous fun z => H z ω := fun ω =>
    ((continuous_l9bCut r).comp (continuous_id.sub continuous_const).norm).mul
      (continuous_locField hK hrad _)
  have hHm : ∀ z, Measurable[m] (H z) := by
    intro z
    by_cases hz : l9bCut r ‖z - u‖ = 0
    · have : H z = fun _ => 0 := funext fun ω => by simp only [H, hz, zero_mul]
      rw [this]
      exact measurable_const
    · obtain ⟨h1, h2⟩ := l9bCut_mem_of_ne_zero hr hz
      exact measurable_const.mul (l9b_measurable_locField_of_subset hK hrad g
        (l9b_closedBall_subset_ann hr24 hrad.le h1 h2))
  have hcongr : ∀ ω, ∀ z ∈ ann u (r / 3) (3 * r), locField κ ε (g ω) z = H z ω := by
    intro ω z hz
    simp only [H, l9bCut_eq_one hr hz.1.le hz.2.le, one_mul]
  have hV'o : IsOpen (ann u (r / 3) (3 * r)) := isOpen_ann _ _ _
  have hV'c : IsPreconnected (ann u (r / 3) (3 * r)) :=
    (config_isConnected_ann hd u (by positivity) (by linarith)).2
  have hAo : IsOpen (ann u (r / 2) (2 * r)) := isOpen_ann _ _ _
  have hAc : IsPreconnected (ann u (r / 2) (2 * r)) :=
    (config_isConnected_ann hd u (by positivity) (by linarith)).2
  constructor
  · have hF := @DGZ.measurable_lfppSetDist d Ω m H (ann u (r / 3) (3 * r)) (sphere u (r / 2))
      (sphere u r) hHc hHm hV'o hV'c (l9b_sphere_subset_ann (by linarith) (by linarith))
      (l9b_sphere_subset_ann (by linarith) (by linarith)) ξ
    have he : (fun ω => DGZ.lfppSetDist ξ (locField κ ε (g ω)) (ann u (r / 3) (3 * r))
        (sphere u (r / 2)) (sphere u r)) = fun ω => DGZ.lfppSetDist ξ (fun z => H z ω)
          (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r) :=
      funext fun ω => DGZ.lfppSetDist_congr (hcongr ω)
    change MeasurableSet[m] {ω | a ≤ DGZ.lfppSetDist ξ (locField κ ε (g ω))
      (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)}
    rw [show {ω | a ≤ DGZ.lfppSetDist ξ (locField κ ε (g ω)) (ann u (r / 3) (3 * r))
        (sphere u (r / 2)) (sphere u r)} = (fun ω => DGZ.lfppSetDist ξ (fun z => H z ω)
          (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)) ⁻¹' Ici a by
      ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Ici, ← he]]
    exact hF measurableSet_Ici
  · have hF := @DGZ.measurable_lfppDiam d Ω m H (ann u (r / 2) (2 * r)) (sphere u r)
      hHc hHm hAo hAc (l9b_sphere_subset_ann (by linarith) (by linarith)) ξ
    have hcongr' : ∀ ω, ∀ z ∈ ann u (r / 2) (2 * r), locField κ ε (g ω) z = H z ω :=
      fun ω z hz => hcongr ω z ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have he : (fun ω => DGZ.lfppDiam ξ (locField κ ε (g ω)) (sphere u r)
        (ann u (r / 2) (2 * r))) = fun ω => DGZ.lfppDiam ξ (fun z => H z ω) (sphere u r)
          (ann u (r / 2) (2 * r)) := by
      funext ω
      unfold DGZ.lfppDiam
      congr 1
      exact image_congr fun p _ => HigherDimLFPP.DGZ.lfppDistOn_congr (hcongr' ω) p.1 p.2
    change MeasurableSet[m] {ω | DGZ.lfppDiam ξ (locField κ ε (g ω)) (sphere u r)
      (ann u (r / 2) (2 * r)) ≤ b}
    rw [show {ω | DGZ.lfppDiam ξ (locField κ ε (g ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤ b} =
        (fun ω => DGZ.lfppDiam ξ (fun z => H z ω) (sphere u r) (ann u (r / 2) (2 * r))) ⁻¹' Iic b by
      ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Iic, ← he]]
    exact hF measurableSet_Iic

/-! ## Constant shifts of LFPP functionals -/

theorem l9b_lfppSetDist_add_const (ξ : ℝ) (φ : Rd d → ℝ) (c : ℝ) (V A B : Set (Rd d)) :
    DGZ.lfppSetDist ξ (fun z => φ z + c) V A B = Real.exp (ξ * c) * DGZ.lfppSetDist ξ φ V A B := by
  have h := l9b_lfppSetDist_affine (ξ := ξ) (φ := fun z => φ z + c) (ψ := φ) (c := c) (u := 0)
    one_pos (fun x => by simp) V A B
  simpa [one_smul, zero_add, image_id'] using h

theorem l9b_lfppDiam_add_const (ξ : ℝ) (φ : Rd d → ℝ) (c : ℝ) (U V : Set (Rd d)) :
    DGZ.lfppDiam ξ (fun z => φ z + c) U V = Real.exp (ξ * c) * DGZ.lfppDiam ξ φ U V := by
  have h := l9b_lfppDiam_affine (ξ := ξ) (φ := fun z => φ z + c) (ψ := φ) (c := c) (u := 0)
    one_pos (fun x => by simp) U V
  simpa [one_smul, zero_add, image_id'] using h

theorem l9b_ofReal_mul_le_iff {a k : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (X : ℝ≥0∞) :
    ENNReal.ofReal (a * k) ≤ X ↔ ENNReal.ofReal a ≤ ENNReal.ofReal k⁻¹ * X := by
  have hk' : ENNReal.ofReal k⁻¹ * ENNReal.ofReal k = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hk.le), inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one]
  have hkne : ENNReal.ofReal k⁻¹ ≠ 0 := by simp [hk]
  rw [ENNReal.ofReal_mul ha, ← ENNReal.mul_le_mul_iff_right hkne ENNReal.ofReal_ne_top,
    mul_comm (ENNReal.ofReal a), ← mul_assoc, hk', one_mul, mul_comm]

theorem l9b_le_ofReal_mul_iff {a k : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (X : ℝ≥0∞) :
    X ≤ ENNReal.ofReal (a * k) ↔ ENNReal.ofReal k⁻¹ * X ≤ ENNReal.ofReal a := by
  have hk' : ENNReal.ofReal k⁻¹ * ENNReal.ofReal k = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hk.le), inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one]
  have hkne : ENNReal.ofReal k⁻¹ ≠ 0 := by simp [hk]
  rw [ENNReal.ofReal_mul ha, ← ENNReal.mul_le_mul_iff_right hkne ENNReal.ofReal_ne_top,
    mul_comm (ENNReal.ofReal a), ← mul_assoc, hk', one_mul, mul_comm]

/-- **Locality of the good shell event** (MA6 P3): for `24 s(ε) ≤ r` the event `E^ε_r(u; C)` is almost
surely equal to an event of `fieldSigma0 h (A_{r/4,4r}(u))`. -/
theorem ref1_lemma43_aeEventIn (hd : 3 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hrad : 0 < locRad ε) (hZ : locMass κ ε (locRad ε) ≠ 0)
    {r : ℝ} (hr24 : 24 * locRad ε ≤ r) (u : Rd d) {C : ℝ} (hC : 0 < C) :
    AEEventIn P (fieldSigma0 h (ann u (r / 4) (4 * r))) {ω | shellGood κ ξ D c ε C u r (h ω)} := by
  have hd2 : 2 ≤ d := by omega
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  have hr : 0 < r := by linarith
  set V := ann u (r / 4) (4 * r) with hV
  have hS : sphere u r ⊆ V := l9b_sphere_subset_ann (by linarith) (by linarith)
  obtain ⟨Fdiam, Facross, hFd, hFa, hae⟩ := hD.exists_shellVersions hd2 hh.1 u hr
  have hcr := hD.c_pos r hr
  -- the recentred field
  set h' : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) r u) with hh'
  have hshift : ∀ ω z, locField κ ε (h ω) z = locField κ ε (h' ω) z + sphereAvg (h ω) r u := by
    intro ω z
    have := locField_addConst hK hrad hZ (h' ω) (sphereAvg (h ω) r u) z
    rwa [hh', addConst_addConst, neg_add_cancel, addConst_zero] at this
  have hfun : ∀ ω, locField κ ε (h ω) = fun z => locField κ ε (h' ω) z + sphereAvg (h ω) r u :=
    fun ω => funext (hshift ω)
  obtain ⟨hm3, hm4⟩ := l9b_measurableSet_lfpp_shell hd2 hK ξ hrad hr24 u h'
    (C⁻¹ * (r * aEps κ ξ (ε / r))) (C * (r * aEps κ ξ (ε / r)))
  -- (1)
  have hE1 : AEEventIn P (fieldSigma0 h V) {ω | ENNReal.ofReal (C⁻¹ * c r *
      Real.exp (ξ * sphereAvg (h ω) r u)) ≤ acrossDist (D (h ω)) u (r / 2) r} := by
    refine l9b_aeEventIn_congr (E₁ := {ω | ENNReal.ofReal (C⁻¹ * c r) ≤ Facross ω})
      ⟨_, measurableSet_le measurable_const hFa, EventuallyEq.rfl⟩ ?_
    filter_upwards [hae] with ω hω'
    obtain ⟨-, hω⟩ := hω'
    apply propext
    show ENNReal.ofReal (C⁻¹ * c r) ≤ Facross ω ↔ ENNReal.ofReal (C⁻¹ * c r *
      Real.exp (ξ * sphereAvg (h ω) r u)) ≤ acrossDist (D (h ω)) u (r / 2) r
    rw [hω, l9b_ofReal_mul_le_iff (by positivity) (Real.exp_pos _), ← Real.exp_neg, ← neg_mul]
  -- (2)
  have hE2 : AEEventIn P (fieldSigma0 h V) {ω | sphereDiam (D (h ω)) u r ≤
      ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg (h ω) r u))} := by
    refine l9b_aeEventIn_congr (E₁ := {ω | Fdiam ω ≤ ENNReal.ofReal (C * c r)})
      ⟨_, measurableSet_le hFd measurable_const, EventuallyEq.rfl⟩ ?_
    filter_upwards [hae] with ω hω'
    obtain ⟨hω, -⟩ := hω'
    apply propext
    show Fdiam ω ≤ ENNReal.ofReal (C * c r) ↔ sphereDiam (D (h ω)) u r ≤
      ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg (h ω) r u))
    rw [hω, l9b_le_ofReal_mul_iff (by positivity) (Real.exp_pos _), ← Real.exp_neg, ← neg_mul]
  -- (3)
  have hE3 : AEEventIn P (fieldSigma0 h V) {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) *
      Real.exp (ξ * sphereAvg (h ω) r u) ≤ DGZ.lfppSetDist ξ (locField κ ε (h ω))
        (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)} := by
    have heq : {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) ≤
        DGZ.lfppSetDist ξ (locField κ ε (h ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2))
          (sphere u r)} = {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) ≤ DGZ.lfppSetDist ξ
            (locField κ ε (h' ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [hfun ω, l9b_lfppSetDist_add_const, mul_comm (Real.exp _)]
      exact mul_le_mul_iff_left₀ (Real.exp_pos _)
    rw [heq]
    exact aeEventIn_of_recentred hd2 hh.1 (isOpen_ann _ _ _) hr hS hm3
  -- (4)
  have hE4 : AEEventIn P (fieldSigma0 h V) {ω | DGZ.lfppDiam ξ (locField κ ε (h ω))
      (sphere u r) (ann u (r / 2) (2 * r)) ≤ C * (r * aEps κ ξ (ε / r)) *
        Real.exp (ξ * sphereAvg (h ω) r u)} := by
    have heq : {ω | DGZ.lfppDiam ξ (locField κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤
        C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)} = {ω | DGZ.lfppDiam ξ
          (locField κ ε (h' ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤
            C * (r * aEps κ ξ (ε / r))} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [hfun ω, l9b_lfppDiam_add_const, mul_comm (Real.exp _)]
      exact mul_le_mul_iff_left₀ (Real.exp_pos _)
    rw [heq]
    exact aeEventIn_of_recentred hd2 hh.1 (isOpen_ann _ _ _) hr hS hm4
  have hset : {ω | shellGood κ ξ D c ε C u r (h ω)} =
      {ω | ENNReal.ofReal (C⁻¹ * c r * Real.exp (ξ * sphereAvg (h ω) r u)) ≤
        acrossDist (D (h ω)) u (r / 2) r} ∩
      {ω | sphereDiam (D (h ω)) u r ≤
        ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg (h ω) r u))} ∩
      {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) ≤
        DGZ.lfppSetDist ξ (locField κ ε (h ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2))
          (sphere u r)} ∩
      {ω | DGZ.lfppDiam ξ (locField κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤
        C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)} := by
    ext ω
    simp only [shellGood, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [hset]
  exact l9b_aeEventIn_inter (l9b_aeEventIn_inter (l9b_aeEventIn_inter hE1 hE2) hE3) hE4

end HigherDimLQGMetric
