import HigherDimLQGContinuity.Forcing.Components

/-! # Gate arc shortcut and block estimates -/

set_option autoImplicit false

noncomputable section

open Set Topology Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem q6_internal_le_diamIn (D : ContMetric d) {A W : Set (Rd d)}
    {x y : Rd d} (hx : x ∈ W) (hy : y ∈ W) :
    D.internal A x y ≤ diamIn D A W := by
  unfold diamIn
  exact le_iSup_of_le x <| le_iSup_of_le hx <|
    le_iSup_of_le y <| le_iSup_of_le hy le_rfl

/-- The secondary Weyl metric has a chamber shortcut between the two enlarged gates. -/
theorem q6_gate_arc_cost {D E E' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ η M θ h δsep ε₀ εnet εatt aout H b v d₀ Ω : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hWE : IsWeylInternal η (-f) E E') (hη : 0 ≤ η)
    (hmis : |η - ξ| * M ≤ Ω) (hd₀ : 0 < d₀) (hv : 0 < v)
    (hΩ : 0 ≤ Ω)
    (e : cert.Ch) {x y : Rd d}
    (hx : x ∈ cthickening h (cert.N (cert.gate0 e)))
    (hy : y ∈ cthickening h (cert.N (cert.gate1 e))) :
    ∃ u w : Rd d, d₀ ≤ D.1 (u, w) ∧
      D.1 (u, x) ≤ v * d₀ / 1000 ∧ D.1 (y, w) ≤ v * d₀ / 1000 ∧
      E'.internal (siteB d) x y ≤
        ENNReal.ofReal (θ * Real.exp Ω * (1 + 5 * v) * D.1 (u, w)) := by
  obtain ⟨u, w, G₀, G₁, Cham, hG₀, hG₁, hCham, hG₀U, hG₁U, hChamU,
    huN, hwN, huG, hwG, hduw, hdiam₀, hdiam₁,
    hconn₀, hconn₁, hsmall₀, hsmall₁, hcham⟩ := cert.arc e
  have hθ : 0 < θ := by rw [cert.θ_eq]; exact Real.exp_pos _
  have he : 1 ≤ Real.exp Ω := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hΩ
  let β : ℝ := v * d₀ / 1000
  let α : ℝ := v * θ * d₀ / 1000
  let κ : ℝ := θ * Real.exp Ω
  let γ : ℝ := (1 + 4 * v) * D.1 (u, w)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hγ : 0 ≤ γ := by
    dsimp [γ]
    exact mul_nonneg (by linarith only [hv]) (hduw.trans' hd₀.le)
  have hplateau : ENNReal.ofReal (Real.exp (-(η * M))) ≤ ENNReal.ofReal κ :=
    ENNReal.ofReal_le_ofReal (q6_secondary_plateau_bounds cert hmis).2
  have hUoB : cert.Uo ⊆ siteB d := by
    intro z hz
    apply q6_siteC_subset_B d
    exact interior_subset (cert.hV (self_subset_cthickening cert.U (cert.hUoU hz)))
  have hB : IsOpen (siteB d) := isOpen_ball
  have huThick : u ∈ cthickening h (cert.N (cert.gate0 e)) :=
    self_subset_cthickening (cert.N _) huN
  have hwThick : w ∈ cthickening h (cert.N (cert.gate1 e)) :=
    self_subset_cthickening (cert.N _) hwN
  have hdux : D.1 (u, x) ≤ β := by
    apply (ENNReal.ofReal_le_ofReal_iff hβ).mp
    calc
      ENNReal.ofReal (D.1 (u, x)) ≤ D.internal (siteA d) u x :=
        D.ofReal_le_internal _ _ _
      _ ≤ diamIn D (siteA d) (cthickening h (cert.N (cert.gate0 e))) :=
        q6_internal_le_diamIn D huThick hx
      _ ≤ ENNReal.ofReal β := hdiam₀
  have hdyw : D.1 (y, w) ≤ β := by
    apply (ENNReal.ofReal_le_ofReal_iff hβ).mp
    calc
      ENNReal.ofReal (D.1 (y, w)) ≤ D.internal (siteA d) y w :=
        D.ofReal_le_internal _ _ _
      _ ≤ diamIn D (siteA d) (cthickening h (cert.N (cert.gate1 e))) :=
        q6_internal_le_diamIn D hy hwThick
      _ ≤ ENNReal.ofReal β := hdiam₁
  obtain ⟨z₀, hz₀, hxz₀⟩ := hconn₀ x hx
  obtain ⟨z₁, hz₁, hyz₁⟩ := hconn₁ y hy
  have hconnCost₀ : E'.internal (siteB d) x z₀ ≤ ENNReal.ofReal α :=
    (q6_weyl_internal_bounds hWE hη cert.f_bd hB x z₀).2.trans hxz₀
  have hconnCost₁ : E'.internal (siteB d) z₁ y ≤ ENNReal.ofReal α :=
    (q6_weyl_internal_bounds hWE hη cert.f_bd hB z₁ y).2.trans
      (by simpa only [E.internal_comm] using hyz₁)
  have hG₀cost : E'.internal (siteB d) z₀ u ≤ ENNReal.ofReal (κ * β) := by
    calc
      E'.internal (siteB d) z₀ u ≤ E'.internal G₀ z₀ u :=
        E'.internal_anti (hG₀U.trans hUoB) _ _
      _ = ENNReal.ofReal (Real.exp (-(η * M))) * E.internal G₀ z₀ u :=
        q6_weyl_internal_const hWE hG₀
          (fun z hz => cert.f_eq z (cert.hUoU (hG₀U hz))) _ _
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal β :=
        mul_le_mul' hplateau (hsmall₀ z₀ hz₀)
      _ = ENNReal.ofReal (κ * β) := (ENNReal.ofReal_mul hκ).symm
  have hG₁cost : E'.internal (siteB d) w z₁ ≤ ENNReal.ofReal (κ * β) := by
    calc
      E'.internal (siteB d) w z₁ ≤ E'.internal G₁ w z₁ :=
        E'.internal_anti (hG₁U.trans hUoB) _ _
      _ = ENNReal.ofReal (Real.exp (-(η * M))) * E.internal G₁ w z₁ :=
        q6_weyl_internal_const hWE hG₁
          (fun z hz => cert.f_eq z (cert.hUoU (hG₁U hz))) _ _
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal β := by
        apply mul_le_mul' hplateau
        simpa only [E.internal_comm] using hsmall₁ z₁ hz₁
      _ = ENNReal.ofReal (κ * β) := (ENNReal.ofReal_mul hκ).symm
  have hChamCost : E'.internal (siteB d) u w ≤ ENNReal.ofReal (κ * γ) := by
    calc
      E'.internal (siteB d) u w ≤ E'.internal Cham u w :=
        E'.internal_anti (hChamU.trans hUoB) _ _
      _ = ENNReal.ofReal (Real.exp (-(η * M))) * E.internal Cham u w :=
        q6_weyl_internal_const hWE hCham
          (fun z hz => cert.f_eq z (cert.hUoU (hChamU hz))) _ _
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal γ :=
        mul_le_mul' hplateau hcham
      _ = ENNReal.ofReal (κ * γ) := (ENNReal.ofReal_mul hκ).symm
  have hpath : E'.internal (siteB d) x y ≤
      E'.internal (siteB d) x z₀ + E'.internal (siteB d) z₀ u +
      E'.internal (siteB d) u w + E'.internal (siteB d) w z₁ +
      E'.internal (siteB d) z₁ y := by
    calc
      E'.internal (siteB d) x y ≤
          E'.internal (siteB d) x z₀ + E'.internal (siteB d) z₀ y :=
        E'.internal_triangle _ _ _ _
      _ ≤ E'.internal (siteB d) x z₀ +
          (E'.internal (siteB d) z₀ u + E'.internal (siteB d) u y) :=
        add_le_add_right (E'.internal_triangle (siteB d) z₀ u y) _
      _ ≤ E'.internal (siteB d) x z₀ +
          (E'.internal (siteB d) z₀ u +
            (E'.internal (siteB d) u w + E'.internal (siteB d) w y)) := by
        gcongr
        exact E'.internal_triangle _ _ _ _
      _ ≤ E'.internal (siteB d) x z₀ +
          (E'.internal (siteB d) z₀ u +
            (E'.internal (siteB d) u w +
              (E'.internal (siteB d) w z₁ + E'.internal (siteB d) z₁ y))) := by
        gcongr
        exact E'.internal_triangle _ _ _ _
      _ = _ := by simp only [add_assoc]
  have htotal : E'.internal (siteB d) x y ≤
      ENNReal.ofReal α + ENNReal.ofReal (κ * β) + ENNReal.ofReal (κ * γ) +
      ENNReal.ofReal (κ * β) + ENNReal.ofReal α :=
    hpath.trans (by
      exact add_le_add (add_le_add (add_le_add (add_le_add
        hconnCost₀ hG₀cost) hChamCost) hG₁cost) hconnCost₁)
  have hακβ : α ≤ κ * β := by
    have hβθ : 0 ≤ θ * β := mul_nonneg hθ.le hβ
    have := mul_le_mul_of_nonneg_left he hβθ
    dsimp [α, β, κ] at *
    nlinarith only [this]
  have h4β : 4 * β ≤ v * D.1 (u, w) := by
    have := mul_le_mul_of_nonneg_left hduw hv.le
    dsimp [β]
    nlinarith only [this, hv, hd₀]
  have hfour : κ * (4 * β) ≤ κ * (v * D.1 (u, w)) :=
    mul_le_mul_of_nonneg_left h4β hκ
  have hreal : 2 * α + κ * (2 * β + γ) ≤
      θ * Real.exp Ω * (1 + 5 * v) * D.1 (u, w) := by
    dsimp [κ, γ] at *
    nlinarith only [hακβ, hfour]
  have htotal' : E'.internal (siteB d) x y ≤
      ENNReal.ofReal (2 * α + κ * (2 * β + γ)) := by
    calc
      E'.internal (siteB d) x y ≤
          ENNReal.ofReal α + ENNReal.ofReal (κ * β) + ENNReal.ofReal (κ * γ) +
          ENNReal.ofReal (κ * β) + ENNReal.ofReal α := htotal
      _ = ENNReal.ofReal (2 * α + κ * (2 * β + γ)) := by
        rw [← ENNReal.ofReal_add hα (mul_nonneg hκ hβ),
          ← ENNReal.ofReal_add (add_nonneg hα (mul_nonneg hκ hβ))
            (mul_nonneg hκ hγ),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ α + κ * β + κ * γ)
            (mul_nonneg hκ hβ),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ α + κ * β + κ * γ + κ * β) hα]
        congr 1
        ring
  exact ⟨u, w, hduw, hdux, hdyw, htotal'.trans (ENNReal.ofReal_le_ofReal hreal)⟩

/-- Numerical conversion of a gate arc into the required geodesic block bounds. -/
theorem q6_gate_block_estimates {D E D' E' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ Ω : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hWD : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hd₀ : 0 < d₀) (hv : 0 < v) (hvmax : v ≤ 1 / 100) (hΩ : 0 ≤ Ω)
    {P : ℝ → Rd d} {s t : ℝ} (hst : s ≤ t)
    (hP : ContinuousOn P (Icc s t))
    {u w : Rd d} (hduw : d₀ ≤ D.1 (u, w))
    (hleft : D.1 (u, P s) ≤ v * d₀ / 1000)
    (hright : D.1 (P t, w) ≤ v * d₀ / 1000)
    (hcost : E'.internal (siteB d) (P s) (P t) ≤
      ENNReal.ofReal (θ * Real.exp Ω * (1 + 5 * v) * D.1 (u, w))) :
    ENNReal.ofReal (θ * d₀ / 2) ≤ D'.len P s t ∧
      E'.internal (siteB d) (P s) (P t) ≤
        ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * Ω)) * D'.len P s t := by
  have hθ : 0 < θ := by rw [cert.θ_eq]; exact Real.exp_pos _
  have hduwpos : 0 < D.1 (u, w) := hd₀.trans_le hduw
  have htri : D.1 (u, w) ≤ D.1 (u, P s) + D.1 (P s, P t) + D.1 (P t, w) := by
    calc
      D.1 (u, w) ≤ D.1 (u, P t) + D.1 (P t, w) := D.apply_triangle _ _ _
      _ ≤ (D.1 (u, P s) + D.1 (P s, P t)) + D.1 (P t, w) := by
        gcongr
        exact D.apply_triangle _ _ _
  have hdist : D.1 (u, w) ≤ D.1 (P s, P t) + 2 * (v * d₀ / 1000) := by
    linarith only [htri, hleft, hright]
  have hmult : v * d₀ ≤ v * D.1 (u, w) :=
    mul_le_mul_of_nonneg_left hduw hv.le
  have hfactor : 1 / 2 ≤ 1 - v / 100 := by linarith only [hvmax]
  have hrealbase : (1 - v / 100) * D.1 (u, w) ≤ D.1 (P s, P t) := by
    nlinarith only [hdist, hmult, mul_nonneg hv.le hduwpos.le]
  have hbased0 : d₀ / 2 ≤ (1 - v / 100) * D.1 (u, w) := by
    have hhalf : d₀ / 2 ≤ D.1 (u, w) / 2 := by linarith only [hduw]
    have hfact : D.1 (u, w) / 2 ≤ (1 - v / 100) * D.1 (u, w) := by
      nlinarith only [mul_le_mul_of_nonneg_right hfactor hduwpos.le]
    exact hhalf.trans hfact
  have hprimary := (q6_weyl_len_bounds hWD hξ cert.f_bd hst hP).1
  rw [← cert.θ_eq] at hprimary
  have hbaselower : ENNReal.ofReal (θ * ((1 - v / 100) * D.1 (u, w))) ≤
      D'.len P s t := by
    calc
      ENNReal.ofReal (θ * ((1 - v / 100) * D.1 (u, w))) ≤
          ENNReal.ofReal (θ * D.1 (P s, P t)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hrealbase hθ.le
      _ = ENNReal.ofReal θ * ENNReal.ofReal (D.1 (P s, P t)) :=
        ENNReal.ofReal_mul hθ.le
      _ ≤ ENNReal.ofReal θ * D.len P s t :=
        mul_le_mul' le_rfl (D.ofReal_le_len P hst)
      _ ≤ D'.len P s t := hprimary
  have hlow : ENNReal.ofReal (θ * d₀ / 2) ≤ D'.len P s t := by
    calc
      ENNReal.ofReal (θ * d₀ / 2) ≤
          ENNReal.ofReal (θ * ((1 - v / 100) * D.1 (u, w))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith only [hbased0, hθ]
      _ ≤ D'.len P s t := hbaselower
  have hfac : 1 + 5 * v ≤ (1 + 6 * v) * (1 - v / 100) := by
    nlinarith only [hv, hvmax, sq_nonneg v]
  have hexp : Real.exp Ω ≤ Real.exp (2 * Ω) :=
    Real.exp_le_exp.mpr (by linarith only [hΩ])
  have hnum : θ * Real.exp Ω * (1 + 5 * v) * D.1 (u, w) ≤
      ((1 + 6 * v) * Real.exp (2 * Ω)) *
        (θ * ((1 - v / 100) * D.1 (u, w))) := by
    have hstep₁ : θ * Real.exp Ω * (1 + 5 * v) * D.1 (u, w) ≤
        θ * Real.exp Ω * ((1 + 6 * v) * (1 - v / 100)) * D.1 (u, w) := by
      gcongr
    have hstep₂ : θ * Real.exp Ω * ((1 + 6 * v) * (1 - v / 100)) * D.1 (u, w) ≤
        θ * Real.exp (2 * Ω) * ((1 + 6 * v) * (1 - v / 100)) * D.1 (u, w) := by
      gcongr
    exact hstep₁.trans <| hstep₂.trans_eq (by ring)
  have hC : 0 ≤ (1 + 6 * v) * Real.exp (2 * Ω) := by positivity
  have hupper : E'.internal (siteB d) (P s) (P t) ≤
      ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * Ω)) * D'.len P s t := by
    calc
      E'.internal (siteB d) (P s) (P t) ≤
          ENNReal.ofReal (θ * Real.exp Ω * (1 + 5 * v) * D.1 (u, w)) := hcost
      _ ≤ ENNReal.ofReal (((1 + 6 * v) * Real.exp (2 * Ω)) *
          (θ * ((1 - v / 100) * D.1 (u, w)))) :=
        ENNReal.ofReal_le_ofReal hnum
      _ = ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * Ω)) *
          ENNReal.ofReal (θ * ((1 - v / 100) * D.1 (u, w))) :=
        ENNReal.ofReal_mul hC
      _ ≤ ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * Ω)) * D'.len P s t :=
        mul_le_mul' le_rfl hbaselower
  exact ⟨hlow, hupper⟩

end HigherDimLQGContinuity
