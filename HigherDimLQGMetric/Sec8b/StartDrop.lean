import HigherDimLQGMetric.Sec8b.CollectorWindow
import HigherDimLQGMetric.Sec6.Transfer

/-! Annulus crossing costs and discounted connections for the start-drop estimate (26). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric Topology unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A path's component through an interior ball visit has boundary points on
the sphere. This is used with `θ = r/2` to locate the two radius-`2r` points. -/
theorem s7b_component_sphere (η : C(unitInterval, Rd d)) (z : Rd d)
    (θ : ℝ) (τ : unitInterval)
    (h0 : η 0 ∉ ball z (4 * θ)) (h1 : η 1 ∉ ball z (4 * θ))
    (hτ : η τ ∈ ball z (4 * θ)) :
    let α := sec8Alpha η z θ τ
    let β := sec8Beta η z θ τ
    α < τ ∧ τ < β ∧ η α ∈ sphere z (4 * θ) ∧
      η β ∈ sphere z (4 * θ) ∧
      ∀ t ∈ Ioo α β, η t ∈ ball z (4 * θ) := by
  dsimp only
  let α := sec8Alpha η z θ τ
  let β := sec8Beta η z θ τ
  have houtα : η α ∉ ball z (4 * θ) := sec8_alpha_boundary η z θ h0 τ
  have houtβ : η β ∉ ball z (4 * θ) := sec8_beta_boundary η z θ h1 τ
  have hαle : α ≤ τ := by
    have hm := sec8LastHit_mem η (ball z (4 * θ))ᶜ isOpen_ball.isClosed_compl τ
    rcases hm with hzero | ⟨hτle, _⟩
    · rw [show α = 0 from hzero]
      exact bot_le
    · exact hτle
  have hβge : τ ≤ β := by
    have hm := sec8FirstHit_mem η (ball z (4 * θ))ᶜ isOpen_ball.isClosed_compl τ
    rcases hm with hone | ⟨hτle, _⟩
    · rw [show β = 1 from hone]
      exact le_top
    · exact hτle
  have hατ : α < τ := lt_of_le_of_ne hαle (fun heq => houtα (heq ▸ hτ))
  have hτβ : τ < β := lt_of_le_of_ne hβge (fun heq => houtβ (heq ▸ hτ))
  have hαcl : α ∈ closure (Ioo α τ) := by
    rw [closure_Ioo hατ.ne]
    exact ⟨le_rfl, hατ.le⟩
  have hβcl : β ∈ closure (Ioo τ β) := by
    rw [closure_Ioo hτβ.ne]
    exact ⟨hτβ.le, le_rfl⟩
  have hαclosed : η α ∈ closedBall z (4 * θ) := by
    have himage : η '' Ioo α τ ⊆ ball z (4 * θ) := by
      rintro u ⟨t, ht, rfl⟩
      exact sec8_in_ball_after_alpha η z θ τ t ht
    exact closure_ball_subset_closedBall
      (closure_mono himage (mem_closure_image η.continuous.continuousAt hαcl))
  have hβclosed : η β ∈ closedBall z (4 * θ) := by
    have himage : η '' Ioo τ β ⊆ ball z (4 * θ) := by
      rintro u ⟨t, ht, rfl⟩
      exact sec8_in_ball_before_beta η z θ τ t ht
    exact closure_ball_subset_closedBall
      (closure_mono himage (mem_closure_image η.continuous.continuousAt hβcl))
  have hαsphere : η α ∈ sphere z (4 * θ) := by
    rw [mem_sphere]
    exact le_antisymm (mem_closedBall.mp hαclosed) (le_of_not_gt houtα)
  have hβsphere : η β ∈ sphere z (4 * θ) := by
    rw [mem_sphere]
    exact le_antisymm (mem_closedBall.mp hβclosed) (le_of_not_gt houtβ)
  have hinside : ∀ t ∈ Ioo α β, η t ∈ ball z (4 * θ) := by
    intro t ht
    rcases lt_trichotomy t τ with hlt | heq | hgt
    · exact sec8_in_ball_after_alpha η z θ τ t ⟨ht.1, hlt⟩
    · simpa only [heq] using hτ
    · exact sec8_in_ball_before_beta η z θ τ t ⟨hgt, ht.2⟩
  exact ⟨hατ, hτβ, hαsphere, hβsphere, hinside⟩

/-- The radius-two sphere is inside the trap collector after scaling. -/
theorem s7b_sphere2_mem_collector {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    {r : ℝ} (hr : 0 < r) (z u : Rd d)
    (hu : u ∈ sphere z (2 * r)) :
    u ∈ sec8Collector T.V r z := by
  let v : Rd d := r⁻¹ • (u - z)
  have huNorm : ‖u - z‖ = 2 * r := by
    simpa only [mem_sphere, dist_eq_norm] using hu
  have hvNorm : ‖v‖ = 2 := by
    dsimp [v]
    rw [S6a.norm_pull hr, huNorm]
    field_simp
  have hv : v ∈ sphere (0 : Rd d) 2 := by
    simpa only [mem_sphere, dist_zero_right] using hvNorm
  exact ⟨v, T.sphereV hv, S6a.affine_pull hr.ne' z u⟩

/-- The (T1) crossing estimate on any real subinterval, by affine
reparametrization to `[0,1]`. -/
theorem s7b_T1_segment {ξ : ℝ} {V : Set (Rd d)}
    {f : ℕ → C(Rd d, ℝ)} {J : ℕ}
    {a b c g H c' s r : ℝ} {z : Rd d} {j : ℕ}
    {D Dt : ContMetric d}
    (htrap : TrapProps ξ V f J a b c g H c' D Dt s r z j)
    (P : ℝ → Rd d) {α β : ℝ} (hαβ : α ≤ β)
    (hP : ContinuousOn P (Icc α β))
    (hα : P α ∈ closure (sec8Collector V r z))
    (hβ : P β ∈ sphere z r ∪ sphere z (3 * r)) :
    ENNReal.ofReal (a * s) ≤ D.len P α β := by
  let φ : ℝ → ℝ := fun t => α + t * (β - α)
  let Q : ℝ → Rd d := P ∘ φ
  have hφc : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hφm : MapsTo φ (Icc (0 : ℝ) 1) (Icc α β) := by
    intro t ht
    have hd : 0 ≤ β - α := sub_nonneg.mpr hαβ
    dsimp [φ]
    constructor
    · nlinarith [mul_nonneg ht.1 hd]
    · have hm := mul_le_of_le_one_left hd ht.2
      linarith only [hm]
  have hQc : ContinuousOn Q (Icc (0 : ℝ) 1) :=
    hP.comp hφc.continuousOn hφm
  have hQ0 : Q 0 = P α := by simp [Q, φ]
  have hQ1 : Q 1 = P β := by simp [Q, φ]
  have ht1 := htrap.1 Q hQc (by simpa only [sec8Collector, hQ0] using hα)
    (by simpa only [hQ1] using hβ)
  have hlen := S6a.len_affine_reparam D P hαβ zero_le_one
  dsimp [Q, φ] at ht1
  change ENNReal.ofReal (a * s) ≤
    D.len (fun t => P (α + t * (β - α))) 0 1 at ht1
  rw [hlen] at ht1
  simpa only [zero_mul, add_zero, one_mul, show α + (β - α) = β by ring] using ht1

/-- The reversed crossing has the same (T1) cost. -/
theorem s7b_T1_segment_rev {ξ : ℝ} {V : Set (Rd d)}
    {f : ℕ → C(Rd d, ℝ)} {J : ℕ}
    {a b c g H c' s r : ℝ} {z : Rd d} {j : ℕ}
    {D Dt : ContMetric d}
    (htrap : TrapProps ξ V f J a b c g H c' D Dt s r z j)
    (P : ℝ → Rd d) {α β : ℝ} (hαβ : α ≤ β)
    (hP : ContinuousOn P (Icc α β))
    (hα : P α ∈ sphere z r ∪ sphere z (3 * r))
    (hβ : P β ∈ closure (sec8Collector V r z)) :
    ENNReal.ofReal (a * s) ≤ D.len P α β := by
  let Q : ℝ → Rd d := fun t => P (α + β - t)
  have hQc : ContinuousOn Q (Icc α β) := by
    have hφc : Continuous fun t : ℝ => α + β - t := by fun_prop
    have hφm : MapsTo (fun t : ℝ => α + β - t) (Icc α β) (Icc α β) := by
      intro t ht
      constructor <;> dsimp <;> linarith [ht.1, ht.2]
    exact hP.comp hφc.continuousOn hφm
  have hQα : Q α = P β := by simp [Q]
  have hQβ : Q β = P α := by simp [Q]
  have hrev := s7b_T1_segment htrap Q hαβ hQc
    (by simpa only [hQα] using hβ) (by simpa only [hQβ] using hα)
  have hlen : D.len Q α β = D.len P α β := by
    unfold ContMetric.len
    have h := LQGMetric.MetricGeometry.curveLength_reverse (D.pt ∘ P) hαβ
    simpa only [Q, Function.comp_def] using h
  rwa [hlen] at hrev

/-- The (T2) connection survives the other discounted bumps because their
supports miss this site's annulus. -/
theorem s7b_T2_connection {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {s r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D Dt E : ContMetric d) (hDlen : D.IsLength)
    (htrap : TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
      D Dt s r site.1 site.2)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (u v : Rd d)
    (hu : u ∈ closure (sec8Collector T.V r site.1))
    (hv : v ∈ closure (sec8Collector T.V r site.1)) :
    E.internal (ann site.1 r (3 * r)) u v ≤
      ENNReal.ofReal ((2 * T.a - T.g) * s) := by
  let Eone := weylMetric ξ (-bumpAt (T.f site.2) r site.1) D hDlen
  have hEone : IsWeylOf ξ (-bumpAt (T.f site.2) r site.1) D Eone :=
    weylMetric_spec hDlen
  have hconn := htrap.2.1 Eone hEone u
    (by simpa only [sec8Collector] using hu) v
    (by simpa only [sec8Collector] using hv)
  have hsupp : ∀ j < T.J, tsupport (T.f j) ⊆ ann (0 : Rd d) 1 3 :=
    fun j hj => (T.bumps j hj).2.2.1
  have heq : E.internal (ann site.1 r (3 * r)) u v =
      Eone.internal (ann site.1 r (3 * r)) u v := by
    rw [← weylScaleOn_eq_internal E hE (isOpen_ann site.1 r (3 * r)),
      weylMetric_internal hDlen (isOpen_ann site.1 r (3 * r))]
    apply weylScaleOn_congr
    intro w hw
    simp only [ContinuousMap.neg_apply]
    rw [F_Z_eq_bumpAt hsupp hr hsite hJ hdisj
      (S6a.ann_subset_ball hr site.1 hw)]
  rwa [heq]

/-- One-window metric surgery: a shortcut of cost `c` replacing a segment of
original length at least `l` lowers the endpoint distance by at least `l-c`.
This version is stated without subtraction, so it works directly in `ℝ≥0∞`. -/
theorem s7b_one_window_drop (D E : ContMetric d)
    (x y : Rd d) (P : ℝ → Rd d) (hP : IsGeod D P)
    (hP0 : P 0 = x) (hP1 : P 1 = y)
    {α β l c : ℝ} (h0 : 0 ≤ α) (hαβ : α ≤ β) (h1 : β ≤ 1)
    (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hleft : E.len P 0 α ≤ D.len P 0 α)
    (hright : E.len P β 1 ≤ D.len P β 1)
    (hlocal : ENNReal.ofReal l ≤ D.len P α β)
    (U : Set (Rd d))
    (hshort : E.internal U (P α) (P β) ≤ ENNReal.ofReal c) :
    E.1 (x, y) + l ≤ D.1 (x, y) + c := by
  have htri : E.1 (x, y) ≤
      E.1 (x, P α) + E.1 (P α, P β) + E.1 (P β, y) := by
    have h1' := E.apply_triangle x (P β) y
    have h2' := E.apply_triangle x (P α) (P β)
    linarith only [h1', h2']
  have hE : ENNReal.ofReal (E.1 (x, y)) ≤
      E.len P 0 α + E.internal U (P α) (P β) + E.len P β 1 := by
    have hle := ENNReal.ofReal_le_ofReal htri
    rw [ENNReal.ofReal_add (add_nonneg (E.nonneg x (P α))
      (E.nonneg (P α) (P β))) (E.nonneg (P β) y),
      ENNReal.ofReal_add (E.nonneg x (P α))
        (E.nonneg (P α) (P β))] at hle
    exact hle.trans (add_le_add
      (add_le_add (by simpa only [hP0] using E.ofReal_le_len P h0)
        (E.ofReal_le_internal U (P α) (P β)))
      (by simpa only [hP1] using E.ofReal_le_len P h1))
  have hsplit : D.len P 0 1 =
      D.len P 0 α + D.len P α β + D.len P β 1 := by
    calc
      D.len P 0 1 = D.len P 0 β + D.len P β 1 :=
        (D.len_add P (h0.trans hαβ) h1).symm
      _ = D.len P 0 α + D.len P α β + D.len P β 1 := by
        rw [D.len_add P h0 hαβ]
  have hreal : ENNReal.ofReal (E.1 (x, y) + l) ≤
      ENNReal.ofReal (D.1 (x, y) + c) := by
    rw [ENNReal.ofReal_add (E.nonneg x y) hl,
      ENNReal.ofReal_add (D.nonneg x y) hc]
    calc
      ENNReal.ofReal (E.1 (x, y)) + ENNReal.ofReal l ≤
          (E.len P 0 α + E.internal U (P α) (P β) + E.len P β 1) +
            ENNReal.ofReal l := add_le_add hE le_rfl
      _ ≤ (D.len P 0 α + ENNReal.ofReal c + D.len P β 1) +
            D.len P α β := by
          apply add_le_add
          · exact add_le_add (add_le_add hleft hshort) hright
          · exact hlocal
      _ = D.len P 0 1 + ENNReal.ofReal c := by
          rw [hsplit]
          ac_rfl
      _ = ENNReal.ofReal (D.1 (x, y)) + ENNReal.ofReal c := by
          rw [hP.2, hP0, hP1]
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (D.nonneg x y) hc)).mp hreal

/-- Both annular crossings surrounding a radius-`r` visit cost at least
`2 a s`. The two radius-`2r` endpoints belong to the collector. -/
theorem s7b_two_crossings {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) {z : Rd d} {j : ℕ}
    {D Dt : ContMetric d}
    (htrap : TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
      D Dt s r z j)
    (P : ℝ → Rd d) {α τ β : ℝ}
    (hατ : α ≤ τ) (hτβ : τ ≤ β)
    (hP : ContinuousOn P (Icc α β))
    (hα : P α ∈ sphere z (2 * r))
    (hβ : P β ∈ sphere z (2 * r))
    (hτ : P τ ∈ ball z r) :
    ENNReal.ofReal (2 * T.a * s) ≤ D.len P α β := by
  let f : ℝ → ℝ := fun t => ‖P t - z‖
  have hf : ContinuousOn f (Icc α β) := by
    exact continuous_norm.comp_continuousOn (hP.sub continuousOn_const)
  have hαf : f α = 2 * r := by simpa only [f, mem_sphere, dist_eq_norm] using hα
  have hβf : f β = 2 * r := by simpa only [f, mem_sphere, dist_eq_norm] using hβ
  have hτf : f τ < r := by simpa only [f, mem_ball, dist_eq_norm] using hτ
  have hατf : ContinuousOn f (Icc α τ) :=
    hf.mono (Icc_subset_Icc le_rfl hτβ)
  have hτβf : ContinuousOn f (Icc τ β) :=
    hf.mono (Icc_subset_Icc hατ le_rfl)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' hατ hατf
    (show f τ ≤ r ∧ r ≤ f α by constructor <;> rw [hαf] at * <;> linarith)
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hτβ hτβf
    (show f τ ≤ r ∧ r ≤ f β by constructor <;> rw [hβf] at * <;> linarith)
  have huSphere : P u ∈ sphere z r := by
    simpa only [mem_sphere, dist_eq_norm, f] using hfu
  have hvSphere : P v ∈ sphere z r := by
    simpa only [mem_sphere, dist_eq_norm, f] using hfv
  have hαV := s7b_sphere2_mem_collector T hr z (P α) hα
  have hβV := s7b_sphere2_mem_collector T hr z (P β) hβ
  have hleft := s7b_T1_segment htrap P hu.1
    (hP.mono (Icc_subset_Icc le_rfl (hu.2.trans hτβ)))
    (subset_closure hαV) (Or.inl huSphere)
  have hright := s7b_T1_segment_rev htrap P hv.2
    (hP.mono (Icc_subset_Icc (hατ.trans hv.1) le_rfl))
    (Or.inl hvSphere) (subset_closure hβV)
  have hsum : ENNReal.ofReal (T.a * s) + ENNReal.ofReal (T.a * s) ≤
      D.len P α u + D.len P v β := add_le_add hleft hright
  have hlen : D.len P α β =
      D.len P α u + D.len P u v + D.len P v β := by
    calc
      D.len P α β = D.len P α u + D.len P u β :=
        (D.len_add P hu.1 ((hu.2.trans hv.1).trans hv.2)).symm
      _ = D.len P α u + D.len P u v + D.len P v β := by
        rw [← D.len_add P (hu.2.trans hv.1) hv.2]
        ac_rfl
  have htwo : 2 * T.a * s = T.a * s + T.a * s := by ring
  have hpos : 0 ≤ T.a * s := mul_nonneg T.constants.1.le hs
  have hreal : ENNReal.ofReal (2 * T.a * s) =
      ENNReal.ofReal (T.a * s) + ENNReal.ofReal (T.a * s) := by
    rw [htwo, ENNReal.ofReal_add hpos hpos]
  rw [hreal]
  exact hsum.trans (by
    rw [hlen]
    calc
      D.len P α u + D.len P v β ≤
          D.len P α u + (D.len P u v + D.len P v β) :=
            add_le_add le_rfl (le_add_of_nonneg_left bot_le)
      _ = D.len P α u + D.len P u v + D.len P v β := by ac_rfl)

/-- One trap visited by the original selected geodesic lowers the fully
discounted endpoint distance by at least `g s`. -/
theorem s7b_one_site_drop {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun) (hξ : 0 < ξ)
    {s r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D Dt E : ContMetric d) (hDlen : D.IsLength)
    (htrap : TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
      D Dt s r site.1 site.2)
    (hs : 0 < s) (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (x y : Rd d) (η : C(unitInterval, Rd d))
    (hη : IsConstSpeedGeod D x y η)
    (hx : x ∉ closedBall site.1 (4 * r))
    (hy : y ∉ closedBall site.1 (4 * r))
    (hvisit : ∃ τ : unitInterval, η τ ∈ ball site.1 r) :
    E.1 (x, y) + T.g * s ≤ D.1 (x, y) := by
  obtain ⟨τ, hτ⟩ := hvisit
  have hη0 : η 0 = x := hη.1
  have hη1 : η 1 = y := hη.2.1
  have hx2 : η 0 ∉ ball site.1 (2 * r) := by
    rw [hη0]
    intro h
    exact hx (mem_closedBall.mpr (by
      have hd := mem_ball.mp h
      have hrr : 2 * r ≤ 4 * r := by linarith
      exact hd.le.trans hrr))
  have hy2 : η 1 ∉ ball site.1 (2 * r) := by
    rw [hη1]
    intro h
    exact hy (mem_closedBall.mpr (by
      have hd := mem_ball.mp h
      have hrr : 2 * r ≤ 4 * r := by linarith
      exact hd.le.trans hrr))
  have hcomponent := s7b_component_sphere η site.1 (r / 2) τ
    (by simpa only [show 4 * (r / 2) = 2 * r by ring] using hx2)
    (by simpa only [show 4 * (r / 2) = 2 * r by ring] using hy2)
    (by simpa only [show 4 * (r / 2) = 2 * r by ring] using
      (Metric.ball_subset_ball (show r ≤ 2 * r by linarith) hτ))
  let α := sec8Alpha η site.1 (r / 2) τ
  let β := sec8Beta η site.1 (r / 2) τ
  have hατ : α < τ := hcomponent.1
  have hτβ : τ < β := hcomponent.2.1
  have hα : η α ∈ sphere site.1 (2 * r) := by
    simpa only [show 4 * (r / 2) = 2 * r by ring] using hcomponent.2.2.1
  have hβ : η β ∈ sphere site.1 (2 * r) := by
    simpa only [show 4 * (r / 2) = 2 * r by ring] using hcomponent.2.2.2.1
  let P := s7b_realPath η
  have hPgeod : IsGeod D P := s7b_constSpeed_isGeod D x y η hη
  have hPcont : Continuous P := η.continuous.comp continuous_projIcc
  have hP0 : P 0 = x := by simpa only [P, s7b_realPath_zero] using hη0
  have hP1 : P 1 = y := by simpa only [P, s7b_realPath_one] using hη1
  have hcross : ENNReal.ofReal (2 * T.a * s) ≤ D.len P α β :=
    s7b_two_crossings T hs.le hr htrap P hατ.le hτβ.le hPcont.continuousOn
      (by simpa only [P, s7b_realPath_coe] using hα)
      (by simpa only [P, s7b_realPath_coe] using hβ)
      (by simpa only [P, s7b_realPath_coe] using hτ)
  have hshort : E.internal (ann site.1 r (3 * r)) (P α) (P β) ≤
      ENNReal.ofReal ((2 * T.a - T.g) * s) :=
    s7b_T2_connection T hr hJ hdisj hsite D Dt E hDlen htrap hE (P α) (P β)
      (subset_closure (s7b_sphere2_mem_collector T hr site.1 (P α)
        (by simpa only [P, s7b_realPath_coe] using hα)))
      (subset_closure (s7b_sphere2_mem_collector T hr site.1 (P β)
        (by simpa only [P, s7b_realPath_coe] using hβ)))
  have hα0 : 0 ≤ (α : ℝ) := α.property.1
  have hβ1 : (β : ℝ) ≤ 1 := β.property.2
  have hl : 0 ≤ 2 * T.a * s :=
    mul_nonneg (mul_nonneg (by norm_num) T.constants.1.le) hs.le
  have hc : 0 ≤ (2 * T.a - T.g) * s := by
    have hg := T.constants.2.2.2.1
    rw [hg]
    nlinarith [T.constants.1, hs]
  have hsave := s7b_one_window_drop D E x y P hPgeod hP0 hP1
    hα0 (hατ.le.trans hτβ.le) hβ1 hl hc
    (s7b_discount_len_le T hξ hJ D E hE P hPcont.continuousOn)
    (s7b_discount_len_le T hξ hJ D E hE P hPcont.continuousOn)
    hcross (ann site.1 r (3 * r)) hshort
  nlinarith only [hsave]

/-- Finitely many nonoverlapping path windows may all be replaced by local
shortcuts. The estimate is kept in `ℝ≥0∞` until the final finite geodesic
length is used. -/
theorem s7b_many_window_drop {ι : Type*} [DecidableEq ι] (D E : ContMetric d) (P : ℝ → Rd d)
    (intervals : Finset ι) (win : ι → ℝ × ℝ) (l c : ι → ℝ)
    (hdisj : (intervals : Set ι).PairwiseDisjoint (fun p => Ioo (win p).1 (win p).2))
    (hvalid : ∀ p ∈ intervals, (win p).1 < (win p).2)
    (hlocal : ∀ p ∈ intervals, ENNReal.ofReal (l p) ≤ D.len P (win p).1 (win p).2)
    (hshort : ∀ p ∈ intervals,
      ENNReal.ofReal (E.1 (P (win p).1, P (win p).2)) ≤ ENNReal.ofReal (c p))
    (hlen : ∀ a b : ℝ, a ≤ b → E.len P a b ≤ D.len P a b) :
    ∀ a b : ℝ, (∀ p ∈ intervals, a ≤ (win p).1 ∧ (win p).2 ≤ b) → a ≤ b →
      ENNReal.ofReal (E.1 (P a, P b)) + ∑ p ∈ intervals, ENNReal.ofReal (l p) ≤
        D.len P a b + ∑ p ∈ intervals, ENNReal.ofReal (c p) := by
  classical
  refine Finset.induction_on_max_value (fun p : ι => (win p).1)
    (motive := fun intervals =>
      (intervals : Set ι).PairwiseDisjoint (fun p => Ioo (win p).1 (win p).2) →
      (∀ p ∈ intervals, (win p).1 < (win p).2) →
      (∀ p ∈ intervals, ENNReal.ofReal (l p) ≤ D.len P (win p).1 (win p).2) →
      (∀ p ∈ intervals, ENNReal.ofReal (E.1 (P (win p).1, P (win p).2)) ≤ ENNReal.ofReal (c p)) →
      ∀ a b : ℝ, (∀ p ∈ intervals, a ≤ (win p).1 ∧ (win p).2 ≤ b) → a ≤ b →
        ENNReal.ofReal (E.1 (P a, P b)) + ∑ p ∈ intervals, ENNReal.ofReal (l p) ≤
          D.len P a b + ∑ p ∈ intervals, ENNReal.ofReal (c p)) intervals ?_ ?_
      hdisj hvalid hlocal hshort
  · intro _ _ _ _ a b _ hab
    simp only [Finset.sum_empty, add_zero]
    exact (E.ofReal_le_len P hab).trans (hlen a b hab)
  · intro w intervals hwI hmax ih hdisj' hvalid' hlocal' hshort' a b hbound hab
    have hwi : a ≤ (win w).1 ∧ (win w).2 ≤ b := hbound w (Finset.mem_insert_self w intervals)
    have hwl : (win w).1 < (win w).2 := hvalid' w (Finset.mem_insert_self w intervals)
    have hIleft : ∀ p ∈ intervals, a ≤ (win p).1 ∧ (win p).2 ≤ (win w).1 := by
      intro p hp
      have hp' := hbound p (Finset.mem_insert_of_mem hp)
      have hpa : (win p).1 ≤ (win w).1 := hmax p hp
      have hpLt : (win p).1 < (win p).2 := hvalid' p (Finset.mem_insert_of_mem hp)
      refine ⟨hp'.1, ?_⟩
      by_contra hbad
      have hwp : w ≠ p := fun heq => hwI (heq ▸ hp)
      have hsep := hdisj' (Finset.mem_coe.2 (Finset.mem_insert_self w intervals))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hp)) hwp
      have hmid : (win w).1 < ((win w).1 + min (win w).2 (win p).2) / 2 ∧
          ((win w).1 + min (win w).2 (win p).2) / 2 < min (win w).2 (win p).2 := by
        have hm : (win w).1 < min (win w).2 (win p).2 := lt_min hwl (lt_of_not_ge hbad)
        constructor <;> linarith
      exact Set.disjoint_left.1 hsep
        ⟨hmid.1, lt_of_lt_of_le hmid.2 (min_le_left _ _)⟩
        ⟨lt_of_le_of_lt hpa hmid.1, lt_of_lt_of_le hmid.2 (min_le_right _ _)⟩
    have hdisjI : (intervals : Set ι).PairwiseDisjoint (fun p => Ioo (win p).1 (win p).2) :=
      hdisj'.subset (by rw [Finset.coe_insert]; exact subset_insert _ _)
    have hvalidI : ∀ p ∈ intervals, (win p).1 < (win p).2 :=
      fun p hp => hvalid' p (Finset.mem_insert_of_mem hp)
    have hlocalI : ∀ p ∈ intervals, ENNReal.ofReal (l p) ≤ D.len P (win p).1 (win p).2 :=
      fun p hp => hlocal' p (Finset.mem_insert_of_mem hp)
    have hshortI : ∀ p ∈ intervals,
        ENNReal.ofReal (E.1 (P (win p).1, P (win p).2)) ≤ ENNReal.ofReal (c p) :=
      fun p hp => hshort' p (Finset.mem_insert_of_mem hp)
    have hpre := ih hdisjI hvalidI hlocalI hshortI a (win w).1 hIleft hwi.1
    have hloc := hlocal' w (Finset.mem_insert_self w intervals)
    have hsho := hshort' w (Finset.mem_insert_self w intervals)
    have hpost := (E.ofReal_le_len P hwi.2).trans (hlen (win w).2 b hwi.2)
    have htri : ENNReal.ofReal (E.1 (P a, P b)) ≤
        ENNReal.ofReal (E.1 (P a, P (win w).1)) +
        ENNReal.ofReal (E.1 (P (win w).1, P (win w).2)) +
        ENNReal.ofReal (E.1 (P (win w).2, P b)) := by
      have ht1 := E.apply_triangle (P a) (P (win w).2) (P b)
      have ht2 := E.apply_triangle (P a) (P (win w).1) (P (win w).2)
      have ht : E.1 (P a, P b) ≤
          E.1 (P a, P (win w).1) + E.1 (P (win w).1, P (win w).2) + E.1 (P (win w).2, P b) := by
        linarith only [ht1, ht2]
      have h1 := E.nonneg (P a) (P (win w).1)
      have h2 := E.nonneg (P (win w).1) (P (win w).2)
      have h3 := E.nonneg (P (win w).2) (P b)
      simpa only [ENNReal.ofReal_add (add_nonneg h1 h2) h3,
        ENNReal.ofReal_add h1 h2] using ENNReal.ofReal_le_ofReal ht
    have hsplit : D.len P a b =
        D.len P a (win w).1 + D.len P (win w).1 (win w).2 + D.len P (win w).2 b := by
      calc
        D.len P a b = D.len P a (win w).2 + D.len P (win w).2 b :=
          (D.len_add P (hwi.1.trans hwl.le) hwi.2).symm
        _ = D.len P a (win w).1 + D.len P (win w).1 (win w).2 + D.len P (win w).2 b := by
          rw [← D.len_add P hwi.1 hwl.le]
    simp only [Finset.sum_insert hwI] at *
    calc
      ENNReal.ofReal (E.1 (P a, P b)) +
          (ENNReal.ofReal (l w) + ∑ p ∈ intervals, ENNReal.ofReal (l p)) ≤
          (ENNReal.ofReal (E.1 (P a, P (win w).1)) +
            ENNReal.ofReal (E.1 (P (win w).1, P (win w).2)) +
            ENNReal.ofReal (E.1 (P (win w).2, P b))) +
            (ENNReal.ofReal (l w) + ∑ p ∈ intervals, ENNReal.ofReal (l p)) :=
              add_le_add htri le_rfl
      _ ≤ (D.len P a (win w).1 + ∑ p ∈ intervals, ENNReal.ofReal (c p)) +
            ENNReal.ofReal (c w) + D.len P (win w).2 b + D.len P (win w).1 (win w).2 := by
          have hsum := add_le_add (add_le_add (add_le_add hpre hsho) hpost) hloc
          convert hsum using 1 <;> ac_rfl
      _ = D.len P a b +
            (ENNReal.ofReal (c w) + ∑ p ∈ intervals, ENNReal.ofReal (c p)) := by
          rw [hsplit]
          ac_rfl

end HigherDimLQGMetric
