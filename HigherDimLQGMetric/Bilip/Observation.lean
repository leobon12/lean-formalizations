import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Select.Internal
import HigherDimLQGMetric.Local.CopiesMetric
import LQGMetric.Papers.GM.S2.BilipLocal

/-!
# Borel nesting of internal metric observations

Port of `LQGMetric.LM.LocNest` to `Rd d`. For open `W₁ ⊆ W₂`,
`D.internal W₁` is a Borel function of `D.internal W₂` when `D` is a
continuous length metric. The countable chain construction is essential;
a direct infimum over all paths is not automatically measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal unitInterval
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric.BilipNest

open LQGMetric.MetricGeometry

variable {d : ℕ}

def nestT (W₁ W₂ : Set (Rd d)) : Set (Rd d) :=
  Subtype.val '' Classical.choose (TopologicalSpace.exists_countable_dense (W₂ \ W₁ : Set (Rd d)))

theorem nestT_countable (W₁ W₂ : Set (Rd d)) : (nestT W₁ W₂).Countable :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense (W₂ \ W₁ : Set (Rd d)))).1.image _

theorem nestT_subset (W₁ W₂ : Set (Rd d)) : nestT W₁ W₂ ⊆ W₂ \ W₁ := by
  rintro _ ⟨z, -, rfl⟩; exact z.2

theorem subset_closure_nestT (W₁ W₂ : Set (Rd d)) : W₂ \ W₁ ⊆ closure (nestT W₁ W₂) := by
  intro z hz
  have hd := (Classical.choose_spec (TopologicalSpace.exists_countable_dense
    (W₂ \ W₁ : Set (Rd d)))).2
  have : (⟨z, hz⟩ : (W₂ \ W₁ : Set (Rd d))) ∈ closure (Classical.choose
      (TopologicalSpace.exists_countable_dense (W₂ \ W₁ : Set (Rd d)))) := hd.closure_eq ▸ mem_univ _
  exact closure_mono (subset_refl _) (mem_closure_image continuous_subtype_val.continuousAt this)

variable (W₁ W₂ : Set (Rd d))

/-- `inf_{z ∈ T} ρ(x, z)` -/
def nestBd (ρ : Rd d → Rd d → ℝ≥0∞) (x : Rd d) : ℝ≥0∞ := ⨅ z ∈ nestT W₁ W₂, ρ x z

/-- an admissible step -/
def nestStep (ρ : Rd d → Rd d → ℝ≥0∞) (x y : Rd d) : ℝ≥0∞ :=
  if ρ x y < nestBd W₁ W₂ ρ x then ρ x y else ⊤

/-- the value of the chain `x, l, y` -/
def nestVal (ρ : Rd d → Rd d → ℝ≥0∞) : Rd d → List (Rd d) → Rd d → ℝ≥0∞
  | x, [], y => nestStep W₁ W₂ ρ x y
  | x, q :: l, y => nestStep W₁ W₂ ρ x q + nestVal ρ q l y

/-- `Ψ(ρ)(u, v)` -/
def nestInf (ρ : Rd d → Rd d → ℝ≥0∞) (u v : Rd d) : ℝ≥0∞ :=
  ⨅ l : List (Fin d → ℚ), nestVal W₁ W₂ ρ u (l.map (HigherDimLFPP.ratPt)) v

theorem measurable_nestEval (x y : Rd d) : Measurable fun ρ : Rd d → Rd d → ℝ≥0∞ => ρ x y :=
  (measurable_pi_apply y).comp (measurable_pi_apply x)

theorem measurable_nestStep (x y : Rd d) :
    Measurable fun ρ : Rd d → Rd d → ℝ≥0∞ => nestStep W₁ W₂ ρ x y := by
  have hb : Measurable fun ρ : Rd d → Rd d → ℝ≥0∞ => nestBd W₁ W₂ ρ x :=
    Measurable.biInf _ (nestT_countable W₁ W₂) fun z _ => measurable_nestEval x z
  exact Measurable.ite (measurableSet_lt (measurable_nestEval x y) hb) (measurable_nestEval x y)
    measurable_const

theorem measurable_nestVal (l : List (Rd d)) :
    ∀ x y : Rd d, Measurable fun ρ : Rd d → Rd d → ℝ≥0∞ => nestVal W₁ W₂ ρ x l y := by
  induction l with
  | nil => exact fun x y => measurable_nestStep W₁ W₂ x y
  | cons q l ih => exact fun x y => (measurable_nestStep W₁ W₂ x q).add (ih q y)

theorem measurable_nestInf :
    Measurable fun (ρ : Rd d → Rd d → ℝ≥0∞) (u v : Rd d) => nestInf W₁ W₂ ρ u v :=
  measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    Measurable.iInf fun _ => measurable_nestVal W₁ W₂ _ u v

variable {W₁ W₂}

/-- the distance from the start of a path in `Y` to any of its points is at most its length -/
theorem internalEDist_le_pathLength_apply {X : Type*} [PseudoEMetricSpace X] {Y : Set X}
    {a b : X} (γ : Path a b) (hγ : ∀ t, γ t ∈ Y) (t : I) :
    internalEDist Y a (γ t) ≤ pathLength γ := by
  have h0 : γ.extend 0 = a := Path.extend_zero γ
  have ht : γ.extend (t : ℝ) = γ t := Path.extend_extends' γ t
  have hmaps : MapsTo γ.extend (Icc 0 (t : ℝ)) Y := fun s hs => by
    rw [Path.extend_apply γ ⟨hs.1, hs.2.trans t.2.2⟩]; exact hγ _
  have h1 := internalEDist_le_curveLength t.2.1 γ.continuous_extend.continuousOn hmaps
  rw [h0, ht] at h1
  exact h1.trans (eVariationOn.mono _ (Icc_subset_Icc le_rfl t.2.2))

/-- a step admissible for `D` on `W₁` is admissible for `ρ = D(·,·;W₂)`, with the same value -/
theorem nestStep_le_chainStep (D : ContMetric d) (hD : D.IsLength) (hW : W₁ ⊆ W₂) (x y : Rd d) :
    nestStep W₁ W₂ (D.internal W₂) x y ≤ D.chainStep W₁ x y := by
  unfold ContMetric.chainStep
  split_ifs with h
  · have hball : Metric.eball (D.pt x) (D.bdDist W₁ x) ⊆ D.pt '' W₁ := by
      intro y' hy'
      by_contra hc
      have h1 := Metric.infEDist_le_edist_of_mem (x := D.pt x) (show y' ∈ (D.pt '' W₁)ᶜ from hc)
      rw [Metric.mem_eball, edist_comm] at hy'
      exact absurd (hy'.trans_le h1) (lt_irrefl _)
    have he : D.internal W₂ x y = edist (D.pt x) (D.pt y) :=
      internalEDist_eq_edist_of_ball_subset hD (hball.trans (image_mono hW)) h
    have hbd : D.bdDist W₁ x ≤ nestBd W₁ W₂ (D.internal W₂) x := by
      refine le_iInf₂ fun z hz => ?_
      refine (Metric.infEDist_le_edist_of_mem ?_).trans (edist_le_internalEDist _ _ _)
      exact D.mem_compl_image_pt.2 (nestT_subset W₁ W₂ hz).2
    have hlt' : D.internal W₂ x y < nestBd W₁ W₂ (D.internal W₂) x :=
      he ▸ h.trans_le hbd
    unfold nestStep
    rw [ite_eq_left hlt', he]
  · exact le_top

/-- an admissible `ρ`-step bounds `D(x, y; W₁)` -/
theorem internal_le_nestStep (D : ContMetric d) (hD : D.IsLength) (hW₂ : IsOpen W₂) (x y : Rd d) :
    D.internal W₁ x y ≤ nestStep W₁ W₂ (D.internal W₂) x y := by
  unfold nestStep
  split_ifs with h
  swap; · exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ, hδb⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 h
  have hlt : D.internal W₂ x y < D.internal W₂ x y + (min ε δ : NNReal) :=
    ENNReal.lt_add_right (h.trans_le le_top).ne (by exact_mod_cast (lt_min hε hδ).ne')
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 (show internalEDist (D.pt '' W₂) (D.pt x) (D.pt y) < _ from hlt)
  have hLb : pathLength γ.1 < nestBd W₁ W₂ (D.internal W₂) x := by
    refine hγ.trans_le ((add_le_add le_rfl ?_).trans hδb.le)
    exact_mod_cast min_le_right _ _
  -- the path stays in `W₁`
  have hin : ∀ t, γ.1 t ∈ D.pt '' W₁ := by
    intro t
    by_contra hnot
    set z := γ.1 t
    have hz2 : z ∈ D.pt '' W₂ := γ.2 t
    have hxz : internalEDist (D.pt '' W₂) (D.pt x) z ≤ pathLength γ.1 :=
      internalEDist_le_pathLength_apply γ.1 γ.2 t
    obtain ⟨η, hη, hηb⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hLb
    obtain ⟨s, hs, hsW⟩ := EMetric.isOpen_iff.1 (D.isOpen_image_pt hW₂) z hz2
    have hz' : D.unpt z ∈ W₂ \ W₁ :=
      ⟨D.mem_image_pt.1 (by simpa using hz2), fun h' => hnot (by simpa using D.mem_image_pt.2 h')⟩
    have hO : IsOpen {w : Rd d | edist z (D.pt w) < min s η} :=
      isOpen_lt (continuous_const.edist D.continuous_pt) continuous_const
    obtain ⟨w, hwO, hwT⟩ := mem_closure_iff.1 (subset_closure_nestT W₁ W₂ hz') _ hO
      (by simpa using lt_min hs (show (0 : ℝ≥0∞) < η by exact_mod_cast hη))
    have hwO' : edist z (D.pt w) < min s η := hwO
    have hzw : internalEDist (D.pt '' W₂) z (D.pt w) = edist z (D.pt w) :=
      internalEDist_eq_edist_of_ball_subset hD hsW (hwO'.trans_le (min_le_left _ _))
    have h1 : D.internal W₂ x w < nestBd W₁ W₂ (D.internal W₂) x := by
      refine ((internalEDist_triangle _ _ z _).trans_lt ?_).trans hηb
      rw [hzw]
      exact ENNReal.add_lt_add_of_le_of_lt (hxz.trans_lt (hLb.trans_le le_top)).ne hxz
        (hwO'.trans_le (min_le_right _ _))
    have h2 : nestBd W₁ W₂ (D.internal W₂) x ≤ D.internal W₂ x w := iInf₂_le w hwT
    exact absurd (h2.trans_lt h1) (lt_irrefl _)
  refine (internalEDist_le_pathLength γ.1 hin).trans (hγ.le.trans (add_le_add le_rfl ?_))
  exact_mod_cast min_le_left _ _

theorem nestVal_le_chainVal (D : ContMetric d) (hD : D.IsLength) (hW : W₁ ⊆ W₂) (l : List (Rd d)) :
    ∀ x y : Rd d, nestVal W₁ W₂ (D.internal W₂) x l y ≤ D.chainVal W₁ x l y := by
  induction l with
  | nil => exact fun x y => nestStep_le_chainStep D hD hW x y
  | cons q l ih =>
    intro x y
    exact add_le_add (nestStep_le_chainStep D hD hW x q) (ih q y)

theorem internal_le_nestVal (D : ContMetric d) (hD : D.IsLength) (hW₂ : IsOpen W₂) (l : List (Rd d)) :
    ∀ x y : Rd d, D.internal W₁ x y ≤ nestVal W₁ W₂ (D.internal W₂) x l y := by
  induction l with
  | nil => exact fun x y => internal_le_nestStep D hD hW₂ x y
  | cons q l ih =>
    intro x y
    exact (internalEDist_triangle _ _ (D.pt q) _).trans
      (add_le_add (internal_le_nestStep D hD hW₂ x q) (ih q y))

/-- **`D(·,·;W₁) = Ψ(D(·,·;W₂))`** for a continuous length metric and open `W₁ ⊆ W₂` -/
theorem internal_eq_nestInf (D : ContMetric d) (hD : D.IsLength) (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (hW : W₁ ⊆ W₂) (u v : Rd d) :
    D.internal W₁ u v = nestInf W₁ W₂ (D.internal W₂) u v := by
  refine le_antisymm (le_iInf fun l => internal_le_nestVal D hD hW₂ _ u v) ?_
  rw [D.internal_eq_chainInf hD hW₁]
  exact iInf_mono fun l => nestVal_le_chainVal D hD hW _ u v

/-- An internal metric on a smaller open set is measurable from the internal
metric on a larger open set, modulo the event where the metric is a length
metric. This is the `Rd d` version of `LQGMetric.LM.locInternalNest`. -/
theorem famSigma_le_aeClosure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → ContMetric d}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) {W₁ W₂ : Set (Rd d)}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) (hW : W₁ ⊆ W₂) :
    famSigmaRd (internalFamRd D) W₁ ≤
      LQGMetric.GM.Bilip.aeClosure P (famSigmaRd (internalFamRd D) W₂) := by
  intro E hE
  obtain ⟨B, hB, rfl⟩ := hE
  let F : (Rd d → Rd d → ℝ≥0∞) → (Rd d → Rd d → ℝ≥0∞) := nestInf W₁ W₂
  have hFm : Measurable F := measurable_nestInf W₁ W₂
  refine ⟨(fun ω => F ((D ω).internal W₂)) ⁻¹' B, ?_, ?_⟩
  · exact ⟨F ⁻¹' B, hFm hB, rfl⟩
  · filter_upwards [hlen] with ω hω
    change ((D ω).internal W₁ ∈ B) = (F ((D ω).internal W₂) ∈ B)
    congr 1
    funext u v
    exact internal_eq_nestInf (D ω) hω hW₁ hW₂ hW u v

/-- Scaling both internal observations by positive finite factors does not
change the nesting argument, provided the factors are measurable in a common
conditioning σ-algebra. This is the form used for recentered shell metrics. -/
theorem scaledFamSigma_le_aeClosure {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → ContMetric d} (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    {H : MeasurableSpace Ω} {c₁ c₂ : Ω → ℝ≥0∞}
    (hc₁ : Measurable[H] c₁) (hc₂ : Measurable[H] c₂)
    (hc₂0 : ∀ ω, c₂ ω ≠ 0) (hc₂top : ∀ ω, c₂ ω ≠ ∞)
    {W₁ W₂ : Set (Rd d)} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hW : W₁ ⊆ W₂) :
    MeasurableSpace.comap
      (fun ω u v => c₁ ω * (D ω).internal W₁ u v) inferInstance ≤
      LQGMetric.GM.Bilip.aeClosure P
        (H ⊔ MeasurableSpace.comap
          (fun ω u v => c₂ ω * (D ω).internal W₂ u v) inferInstance) := by
  let T : MeasurableSpace Ω := MeasurableSpace.comap
    (fun ω u v => c₂ ω * (D ω).internal W₂ u v) inferInstance
  let J : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω u v => c₂ ω * (D ω).internal W₂ u v
  let R : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω u v => (c₂ ω)⁻¹ * J ω u v
  let F : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω u v => c₁ ω * nestInf W₁ W₂ (R ω) u v
  have hc₁m : Measurable[H ⊔ T] c₁ := hc₁.mono le_sup_left le_rfl
  have hc₂m : Measurable[H ⊔ T] c₂ := hc₂.mono le_sup_left le_rfl
  have hJ : Measurable[H ⊔ T] J := (comap_measurable J).mono le_sup_right le_rfl
  have hR : Measurable[H ⊔ T] R := by
    refine (@measurable_pi_iff _ _ _ (H ⊔ T) _ _).2 fun u => ?_
    refine (@measurable_pi_iff _ _ _ (H ⊔ T) _ _).2 fun v => ?_
    exact hc₂m.inv.mul ((measurable_pi_apply v).comp
      ((measurable_pi_apply u).comp hJ))
  have hF : Measurable[H ⊔ T] F := by
    have hN := (measurable_nestInf W₁ W₂).comp hR
    refine (@measurable_pi_iff _ _ _ (H ⊔ T) _ _).2 fun u => ?_
    refine (@measurable_pi_iff _ _ _ (H ⊔ T) _ _).2 fun v => ?_
    exact hc₁m.mul ((measurable_pi_apply v).comp
      ((measurable_pi_apply u).comp hN))
  intro E hE
  obtain ⟨B, hB, rfl⟩ := hE
  refine ⟨F ⁻¹' B, hF hB, ?_⟩
  filter_upwards [hlen] with ω hω
  change ((fun u v => c₁ ω * (D ω).internal W₁ u v) ∈ B) = (F ω ∈ B)
  congr 1
  funext u v
  have hcancel : R ω = (D ω).internal W₂ := by
    funext x y
    dsimp [R, J]
    exact ENNReal.inv_mul_cancel_left (hc₂0 ω) (hc₂top ω)
  change c₁ ω * (D ω).internal W₁ u v = c₁ ω * nestInf W₁ W₂ (R ω) u v
  rw [hcancel, internal_eq_nestInf (D ω) hω hW₁ hW₂ hW u v]

/-- The internal metric at one normalization on a smaller domain is observable
from the full field and the metric at another normalization on a larger domain. -/
theorem rescFamSigma_le_full_join {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (ξ : ℝ) (z : Rd d)
    (r₁ r₂ : ℝ) {W₁ W₂ : Set (Rd d)}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) (hW : W₁ ⊆ W₂) :
    famSigmaRd (rescFam ξ h D z r₁) W₁ ≤
      LQGMetric.GM.Bilip.aeClosure P
        (fullSigmaRd h ⊔ famSigmaRd (rescFam ξ h D z r₂) W₂) := by
  have hscale₁ : Measurable[fullSigmaRd h] (l7b_scale ξ h r₁ z) :=
    l7b_measurable_scale ξ (comap_measurable h) r₁ z
  have hscale₂ : Measurable[fullSigmaRd h] (l7b_scale ξ h r₂ z) :=
    l7b_measurable_scale ξ (comap_measurable h) r₂ z
  have hne₀ (ω : Ω) : l7b_scale ξ h r₂ z ω ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hneTop (ω : Ω) : l7b_scale ξ h r₂ z ω ≠ ∞ := ENNReal.ofReal_ne_top
  exact scaledFamSigma_le_aeClosure hlen hscale₁ hscale₂ hne₀ hneTop
    hW₁ hW₂ hW


end HigherDimLQGMetric.BilipNest
