import MyProject.Common.AreaFormula

/-!
# The Sobolev trace estimate (Evans §5.5)

The **trace theorem** gives a bounded linear operator `T : W^{1,p}(Ω) → L^p(∂Ω)` extending
restriction `u ↦ u|_{∂Ω}` for `C¹` functions.  Its analytic heart is the boundary estimate
`∫_{∂Ω} |u|^p dμ_H ≤ C ‖u‖_{W^{1,p}(Ω)}^p`.

This file builds that estimate off the Chapter-6 general divergence theorem
(`divergence_theorem` in `Common/AreaFormula.lean`).  We treat the `p = 2` (H¹) case first —
`u²` is manifestly `C¹`, so the estimate avoids the `|u|^p` regularity subtlety and reduces to:
apply Gauss–Green to `u² · F`, where `F` is a `C¹` vector field transverse to `∂Ω`
(`⟪F, ν⟫ ≥ 1`), obtained by smoothing the continuous unit outward normal `ν`.

* `exists_transverse_field` — the transverse `C¹` field (this file's geometric core).
-/

open MeasureTheory MeasureTheory.Measure Filter Topology Metric Set AreaFormula
open scoped ENNReal NNReal RealInnerProductSpace Manifold

namespace Sobolev

local notation "ℝ^" m => EuclideanSpace ℝ (Fin m)

variable {m : ℕ}

/-- **Transverse `C¹` field.** On a bounded `C¹` domain `Ω` with continuous outward unit normal `ν`,
there is a globally `C¹` vector field `F` with `⟪F, ν⟫ ≥ 1` everywhere on `∂Ω`.  It is built by
uniformly smoothing the (continuous, unit) normal: cut `ν` down to a compactly supported field equal
to `ν` near `∂Ω`, approximate it within `½` by a `C^∞` field `g`
(`UniformContinuous.exists_contDiff_dist_le`), and take `F = 2 g`.  This is the field fed to the
divergence theorem in the trace estimate. -/
theorem exists_transverse_field {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν) :
    ∃ F : (ℝ^(m + 2)) → (ℝ^(m + 2)), ContDiff ℝ 1 F ∧
      ∀ x ∈ frontier Ω, (1 : ℝ) ≤ ⟪F x, ν x⟫ := by
  have hfrcompact : IsCompact (frontier Ω) := hΩ.isCompact_frontier
  have hfrclosed : IsClosed (frontier Ω) := isClosed_frontier
  -- `ν` is a unit vector on `∂Ω` (chart normal is unit; `e`, `flatten` are isometries)
  have hνunit : ∀ x ∈ frontier Ω, ‖ν x‖ = 1 := by
    intro x hx
    obtain ⟨r, hr, e, γ, hγ, hchart⟩ := hΩ.locallyGraph x hx
    have hxb : x ∈ frontier Ω ∩ Metric.ball x r := ⟨hx, Metric.mem_ball_self hr⟩
    rw [hν.eq_chart x r e γ hγ hchart x hxb, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map]
    exact AreaFormula.norm_graphNormal γ _
  -- enclose `∂Ω` in an open ball, hence in the interior of a compact closed ball
  obtain ⟨R, hR⟩ := hfrcompact.isBounded.subset_closedBall (0 : ℝ^(m + 2))
  have hRpos : (0 : ℝ) < |R| + 1 := by positivity
  have hball : frontier Ω ⊆ Metric.ball 0 (|R| + 1) :=
    hR.trans (Metric.closedBall_subset_ball (by have := le_abs_self R; linarith))
  have hint : frontier Ω ⊆ interior (Metric.closedBall (0 : ℝ^(m + 2)) (|R| + 1)) := by
    rw [interior_closedBall _ hRpos.ne']; exact hball
  -- smooth cutoff `χ`: `= 1` near `∂Ω`, supported in the compact closed ball
  obtain ⟨χ, hχ1, hχ0, hχ01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, ℝ^(m + 2))) (n := ⊤)
      hfrclosed hint
  have hχcd : ContDiff ℝ 1 (⇑χ) := by
    have h := χ.contMDiff; rw [contMDiff_iff_contDiff] at h; exact h.of_le (mod_cast le_top)
  have hχcont : Continuous (⇑χ) := hχcd.continuous
  have hχcs : HasCompactSupport (⇑χ) :=
    HasCompactSupport.intro (isCompact_closedBall 0 (|R| + 1)) (fun x hx => hχ0 x hx)
  -- the cut-down normal field `f₀ = χ • ν`
  set f₀ : (ℝ^(m + 2)) → (ℝ^(m + 2)) := fun x => χ x • ν x with hf₀def
  have hf₀cont : Continuous f₀ := hχcont.smul hν.continuous
  have hf₀cs : HasCompactSupport f₀ :=
    HasCompactSupport.intro (isCompact_closedBall 0 (|R| + 1)) (fun x hx => by
      simp only [hf₀def, hχ0 x hx, zero_smul])
  have hf₀uc : UniformContinuous f₀ := hf₀cs.uniformContinuous_of_continuous hf₀cont
  have hf₀eq : ∀ x ∈ frontier Ω, f₀ x = ν x := by
    intro x hx
    simp only [hf₀def, hχ1.self_of_nhdsSet x hx, one_smul]
  -- uniform `C^∞` approximation of `f₀` within `½`
  obtain ⟨g, hgcd, hgle⟩ := hf₀uc.exists_contDiff_dist_le (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨fun x => (2 : ℝ) • g x, ?_, ?_⟩
  · exact (hgcd.of_le (mod_cast le_top)).const_smul (2 : ℝ)
  · intro x hx
    rw [real_inner_smul_left]
    have hgν : ‖g x - ν x‖ ≤ 1 / 2 := by
      have := (hgle x).le
      rwa [dist_eq_norm, hf₀eq x hx] at this
    have hself : ⟪ν x, ν x⟫ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hνunit x hx]; norm_num
    have hsplit : ⟪g x, ν x⟫ = ⟪g x - ν x, ν x⟫ + ⟪ν x, ν x⟫ := by
      rw [← inner_add_left]; congr 1; abel
    have hcs : |⟪g x - ν x, ν x⟫| ≤ ‖g x - ν x‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
    have hlow : -(1 / 2) ≤ ⟪g x - ν x, ν x⟫ := by
      have h2 : ‖g x - ν x‖ * ‖ν x‖ ≤ 1 / 2 := by rw [hνunit x hx, mul_one]; exact hgν
      have := (abs_le.mp (hcs.trans h2)).1
      linarith
    have hhalf : (1 : ℝ) / 2 ≤ ⟪g x, ν x⟫ := by rw [hsplit, hself]; linarith
    linarith

/-- **Divergence Leibniz rule** for a scalar field `g` times a vector field `F`:
`div (g • F) = g · div F + Dg(F)`.  (`Dg(F)` is the directional derivative of `g` in the
direction `F`, i.e. `⟪∇g, F⟫`.)  This is the product rule that turns the divergence of `u² • F`
into the interior integrand of the trace estimate. -/
theorem divergenceE_smul_scalar {n : ℕ} {g : (ℝ^n) → ℝ} {F : (ℝ^n) → (ℝ^n)} {x : ℝ^n}
    (hg : DifferentiableAt ℝ g x) (hF : DifferentiableAt ℝ F x) :
    divergenceE (fun y => g y • F y) x = g x * divergenceE F x + fderiv ℝ g x (F x) := by
  have hfd : fderiv ℝ (fun y => g y • F y) x
      = g x • fderiv ℝ F x + (fderiv ℝ g x).smulRight (F x) :=
    (hg.hasFDerivAt.smul hF.hasFDerivAt).fderiv
  rw [divergenceE, hfd]
  have hcross : ∀ i : Fin n,
      ((g x • fderiv ℝ F x + (fderiv ℝ g x).smulRight (F x)) (EuclideanSpace.single i 1)) i
        = g x * ((fderiv ℝ F x (EuclideanSpace.single i 1)) i)
          + (fderiv ℝ g x (EuclideanSpace.single i 1)) * (F x i) := by
    intro i
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.smulRight_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hcross i), Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  have hFxexp : (∑ i, (F x i) • EuclideanSpace.single i (1 : ℝ)) = F x := by
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (F x)]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply])
  calc ∑ i, (fderiv ℝ g x (EuclideanSpace.single i 1)) * (F x i)
      = ∑ i, fderiv ℝ g x ((F x i) • EuclideanSpace.single i (1 : ℝ)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, smul_eq_mul, mul_comm]
    _ = fderiv ℝ g x (∑ i, (F x i) • EuclideanSpace.single i (1 : ℝ)) := (map_sum _ _ _).symm
    _ = fderiv ℝ g x (F x) := by rw [hFxexp]

/-- **Young's inequality in the trace form.** For `p ≥ 2`, `s, D ∈ ℝ` with `D ≥ 0`,
`p |s| (s²)^{p/2-1} D ≤ (p-1)(s²)^{p/2} + D^p` (all powers `rpow`).  This packages the
`ab ≤ aᵖ/p + bᵍ/q` bound (conjugate exponents `p/(p-1)`, `p`) that turns the cross term
`p·u·(u²)^{p/2-1}·Du(F)` of `div(|u|^p F)` into `(u²)^{p/2}` plus `‖Du‖^p`. -/
theorem trace_young {p : ℝ} (hp : 2 ≤ p) (s D : ℝ) (hD : 0 ≤ D) :
    p * |s| * (s ^ 2) ^ (p / 2 - 1) * D ≤ (p - 1) * (s ^ 2) ^ (p / 2) + D ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : p ≠ 0 := by linarith
  have hpm1 : p - 1 ≠ 0 := by linarith
  rcases eq_or_ne s 0 with hs | hs
  · subst hs; simp only [abs_zero, mul_zero, zero_mul]
    exact add_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg hD _)
  · have hs2 : (0 : ℝ) < s ^ 2 := by positivity
    have habs : |s| = (s ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_sq_eq_abs, Real.sqrt_eq_rpow]
    have hcomb : |s| * (s ^ 2) ^ (p / 2 - 1) = (s ^ 2) ^ ((p - 1) / 2) := by
      rw [habs, ← Real.rpow_add hs2]; congr 1; ring
    have hconj : (p / (p - 1)).HolderConjugate p := by
      rw [Real.holderConjugate_iff]
      refine ⟨?_, ?_⟩
      · rw [lt_div_iff₀ (by linarith)]; linarith
      · field_simp; ring
    have hY := Real.young_inequality_of_nonneg (Real.rpow_nonneg hs2.le ((p - 1) / 2)) hD hconj
    have hpow : ((s ^ 2) ^ ((p - 1) / 2)) ^ (p / (p - 1)) = (s ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_mul hs2.le]; congr 1; field_simp
    rw [hpow] at hY
    calc p * |s| * (s ^ 2) ^ (p / 2 - 1) * D
        = p * ((s ^ 2) ^ ((p - 1) / 2) * D) := by rw [← hcomb]; ring
      _ ≤ p * ((s ^ 2) ^ (p / 2) / (p / (p - 1)) + D ^ p / p) :=
          mul_le_mul_of_nonneg_left hY hp0.le
      _ = (p - 1) * (s ^ 2) ^ (p / 2) + D ^ p := by field_simp

/-- **Positive-base Young inequality** for the smoothed trace estimate.  For `p ≥ 1`, a strictly
positive base `b > 0` with `s² ≤ b`, and `D ≥ 0`,
`p |s| b^{p/2-1} D ≤ (p-1) b^{p/2} + D^p`.  The base `b = ε² + s² > 0` avoids the `s = 0` regularity
issue, so this covers the whole range `p ≥ 1` (unlike `trace_young`, which needs `p ≥ 2`). -/
theorem trace_young_pos {p : ℝ} (hp : 1 ≤ p) (b s D : ℝ) (hb : 0 < b) (hsb : s ^ 2 ≤ b)
    (hD : 0 ≤ D) : p * |s| * b ^ (p / 2 - 1) * D ≤ (p - 1) * b ^ (p / 2) + D ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  -- |s| ≤ √b = b^{1/2}
  have hsle : |s| ≤ b ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (sq_nonneg _) hsb (by norm_num)
  -- |s| b^{p/2-1} ≤ b^{(p-1)/2}
  have hcomb : |s| * b ^ (p / 2 - 1) ≤ b ^ ((p - 1) / 2) := by
    calc |s| * b ^ (p / 2 - 1) ≤ b ^ ((1 : ℝ) / 2) * b ^ (p / 2 - 1) :=
          mul_le_mul_of_nonneg_right hsle (Real.rpow_nonneg hb.le _)
      _ = b ^ ((p - 1) / 2) := by rw [← Real.rpow_add hb]; congr 1; ring
  have hbpm : (0 : ℝ) ≤ b ^ ((p - 1) / 2) := Real.rpow_nonneg hb.le _
  -- the core `p · b^{(p-1)/2} · D ≤ (p-1) b^{p/2} + D^p`
  have hcore : p * b ^ ((p - 1) / 2) * D ≤ (p - 1) * b ^ (p / 2) + D ^ p := by
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · subst hp1
      rw [show (((1 : ℝ) - 1) / 2) = 0 by norm_num, Real.rpow_zero, Real.rpow_one]
      simp
    · have hpm1 : p - 1 ≠ 0 := by linarith
      have hconj : (p / (p - 1)).HolderConjugate p := by
        rw [Real.holderConjugate_iff]
        exact ⟨by rw [lt_div_iff₀ (by linarith)]; linarith, by field_simp; ring⟩
      have hY := Real.young_inequality_of_nonneg hbpm hD hconj
      have hpow : (b ^ ((p - 1) / 2)) ^ (p / (p - 1)) = b ^ (p / 2) := by
        rw [← Real.rpow_mul hb.le]; congr 1; field_simp
      rw [hpow] at hY
      calc p * b ^ ((p - 1) / 2) * D = p * (b ^ ((p - 1) / 2) * D) := by ring
        _ ≤ p * (b ^ (p / 2) / (p / (p - 1)) + D ^ p / p) :=
            mul_le_mul_of_nonneg_left hY hp0.le
        _ = (p - 1) * b ^ (p / 2) + D ^ p := by field_simp
  calc p * |s| * b ^ (p / 2 - 1) * D = p * (|s| * b ^ (p / 2 - 1)) * D := by ring
    _ ≤ p * b ^ ((p - 1) / 2) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomb hp0.le) hD
    _ ≤ (p - 1) * b ^ (p / 2) + D ^ p := hcore

/-- **The `L²` (H¹) trace estimate** (Evans §5.5, `p = 2`): for a `C¹` function `u` on a bounded
`C¹` domain `Ω`, the boundary `L²` mass is controlled by the `H¹(Ω)` energy,
`∫_{∂Ω} u² dμ_H ≤ C (∫_Ω u² + ∫_Ω ‖Du‖²)`.  This is the analytic heart of the trace theorem.
Proof: apply the divergence theorem to the field `u² • F` (`F` the transverse field
`exists_transverse_field`).  On `∂Ω`, `⟪u² • F, ν⟫ ≥ u²`; in `Ω`, the divergence Leibniz rule plus
Cauchy–Schwarz and Young give `div(u² • F) ≤ C(u² + ‖Du‖²)` with `C` from sup bounds of `div F`
and `‖F‖` over the compact closure. -/
theorem trace_estimate_sq {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν)
    {u : (ℝ^(m + 2)) → ℝ} (hu : ContDiff ℝ 1 u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫ x in frontier Ω, (u x) ^ 2 ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
        ≤ C * ((∫ x in Ω, (u x) ^ 2) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2) := by
  obtain ⟨F, hFcd, hFν⟩ := exists_transverse_field hΩ hν
  have hGcd : ContDiff ℝ 1 (fun y => (u y) ^ 2 • F y) := (hu.pow 2).smul hFcd
  -- finiteness + measurability plumbing
  have hvolfin : volume Ω ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hΩ.isCompact_closure.measure_lt_top).ne
  have hμfin : (μHE[m + 1] : Measure (ℝ^(m + 2))) (frontier Ω) ≠ ∞ :=
    (surfaceMeasure_frontier_lt_top hΩ).ne
  have hfrmeas : MeasurableSet (frontier Ω) := isClosed_frontier.measurableSet
  -- integrability helpers: a continuous function is integrable on `Ω` (volume) and on `∂Ω` (μ_H)
  have intΩ : ∀ {φ : (ℝ^(m + 2)) → ℝ}, Continuous φ → IntegrableOn φ Ω volume := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded hvolfin hφ.aestronglyMeasurable
      ((ae_restrict_iff' hΩ.measurableSet).mpr (ae_of_all _ (fun x hx => hB x (subset_closure hx))))
  have intFr : ∀ {φ : (ℝ^(m + 2)) → ℝ}, Continuous φ →
      IntegrableOn φ (frontier Ω) (μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hΩ.isCompact_frontier.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded hμfin hφ.aestronglyMeasurable
      ((ae_restrict_iff' hfrmeas).mpr (ae_of_all _ (fun x hx => hB x hx)))
  -- sup bounds of `div F` and `‖F‖` over the compact closure
  obtain ⟨M₁, hM₁⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn
    (continuous_divergenceE hFcd).continuousOn
  obtain ⟨M₂, hM₂⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hFcd.continuous.continuousOn
  set M₁' : ℝ := max M₁ 0 with hM₁'def
  set M₂' : ℝ := max M₂ 0 with hM₂'def
  refine ⟨M₁' + M₂', add_nonneg (le_max_right _ _) (le_max_right _ _), ?_⟩
  -- pointwise interior bound
  have hptwise : ∀ x ∈ Ω, divergenceE (fun y => (u y) ^ 2 • F y) x
      ≤ (M₁' + M₂') * ((u x) ^ 2 + ‖fderiv ℝ u x‖ ^ 2) := by
    intro x hx
    have hxcl : x ∈ closure Ω := subset_closure hx
    have hud : HasFDerivAt u (fderiv ℝ u x) x :=
      (hu.differentiable one_ne_zero).differentiableAt.hasFDerivAt
    have hLeib : divergenceE (fun y => (u y) ^ 2 • F y) x
        = (u x) ^ 2 * divergenceE F x + fderiv ℝ (fun y => (u y) ^ 2) x (F x) :=
      divergenceE_smul_scalar ((hu.differentiable one_ne_zero).differentiableAt.pow 2)
        (hFcd.differentiable one_ne_zero).differentiableAt
    have hsqfd : fderiv ℝ (fun y => (u y) ^ 2) x (F x) = 2 * u x * fderiv ℝ u x (F x) := by
      rw [(hud.pow 2).fderiv]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [hLeib, hsqfd]
    have hD : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ := norm_nonneg _
    have hM₂'nn : (0 : ℝ) ≤ M₂' := le_max_right _ _
    -- term 1: u² · div F ≤ M₁' · u²
    have hdivle : divergenceE F x ≤ M₁' :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM₁ x hxcl).trans (le_max_left _ _))
    have p1 : (u x) ^ 2 * divergenceE F x ≤ (u x) ^ 2 * M₁' := by
      have := sq_nonneg (u x); nlinarith [hdivle]
    -- term 2: 2 u v ≤ M₂' (u² + ‖Du‖²)
    have hvle : |fderiv ℝ u x (F x)| ≤ ‖fderiv ℝ u x‖ * ‖F x‖ := by
      have := (fderiv ℝ u x).le_opNorm (F x); rwa [Real.norm_eq_abs] at this
    have hnF2 : ‖F x‖ ≤ M₂' := (hM₂ x hxcl).trans (le_max_left _ _)
    have p2 : 2 * u x * fderiv ℝ u x (F x) ≤ M₂' * ((u x) ^ 2 + ‖fderiv ℝ u x‖ ^ 2) := by
      have step1 : 2 * u x * fderiv ℝ u x (F x) ≤ 2 * |u x| * |fderiv ℝ u x (F x)| := by
        nlinarith [le_abs_self (u x * fderiv ℝ u x (F x)), abs_mul (u x) (fderiv ℝ u x (F x))]
      have hvM : |fderiv ℝ u x (F x)| ≤ ‖fderiv ℝ u x‖ * M₂' :=
        hvle.trans (by nlinarith [hD, hnF2])
      have step2 : 2 * |u x| * |fderiv ℝ u x (F x)| ≤ 2 * |u x| * (‖fderiv ℝ u x‖ * M₂') := by
        nlinarith [abs_nonneg (u x), hvM]
      have hAM : 2 * |u x| * ‖fderiv ℝ u x‖ ≤ (u x) ^ 2 + ‖fderiv ℝ u x‖ ^ 2 := by
        nlinarith [sq_nonneg (|u x| - ‖fderiv ℝ u x‖), sq_abs (u x)]
      have step3 : 2 * |u x| * (‖fderiv ℝ u x‖ * M₂') ≤ M₂' * ((u x) ^ 2 + ‖fderiv ℝ u x‖ ^ 2) := by
        nlinarith [hM₂'nn, hAM]
      linarith [step1.trans (step2.trans step3)]
    nlinarith [p1, p2, sq_nonneg (‖fderiv ℝ u x‖), le_max_right M₁ 0]
  -- assemble via the divergence theorem
  calc ∫ x in frontier Ω, (u x) ^ 2 ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      ≤ ∫ x in frontier Ω, ⟪(u x) ^ 2 • F x, ν x⟫ ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
        refine setIntegral_mono_on (intFr (hu.continuous.pow 2))
          (intFr (Continuous.inner ((hu.continuous.pow 2).smul hFcd.continuous) hν.continuous))
          hfrmeas (fun x hx => ?_)
        rw [real_inner_smul_left]
        nlinarith [sq_nonneg (u x), hFν x hx]
    _ = ∫ x in Ω, divergenceE (fun y => (u y) ^ 2 • F y) x := (divergence_theorem hΩ hν hGcd).symm
    _ ≤ ∫ x in Ω, (M₁' + M₂') * ((u x) ^ 2 + ‖fderiv ℝ u x‖ ^ 2) :=
        setIntegral_mono_on (intΩ (continuous_divergenceE hGcd))
          (intΩ (continuous_const.mul ((hu.continuous.pow 2).add
            ((hu.continuous_fderiv one_ne_zero).norm.pow 2)))) hΩ.measurableSet hptwise
    _ = (M₁' + M₂') * ((∫ x in Ω, (u x) ^ 2) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2) := by
        rw [integral_const_mul, integral_add (intΩ (hu.continuous.pow 2))
          (intΩ ((hu.continuous_fderiv one_ne_zero).norm.pow 2))]

/-- **The general `Lᵖ` trace estimate** (Evans §5.5, `p ≥ 2`): for a `C¹` function `u` on a bounded
`C¹` domain `Ω`, `∫_{∂Ω} |u|^p dμ_H ≤ C (∫_Ω |u|^p + ∫_Ω ‖Du‖^p)`, where `|u|^p = (u²)^{p/2}`.
The restriction `p ≥ 2` makes `(u²)^{p/2}` genuinely `C¹` (`rpow_const_of_le`), so the boundary
integrand needs no `ε`-smoothing.  Same Gauss–Green argument as the `p=2` case, with the interior
Young bound `p |u| (u²)^{p/2-1} ‖Du‖ ≤ (p-1)(u²)^{p/2} + ‖Du‖^p` supplied by `trace_young`. -/
theorem trace_estimate_pow {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν)
    {u : (ℝ^(m + 2)) → ℝ} (hu : ContDiff ℝ 1 u) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
        ≤ C * ((∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) := by
  obtain ⟨F, hFcd, hFν⟩ := exists_transverse_field hΩ hν
  have hle : ((1 : ℕ) : ℝ) ≤ p / 2 := by push_cast; linarith
  have hUcd : ContDiff ℝ 1 (fun x => ((u x) ^ 2) ^ (p / 2)) := (hu.pow 2).rpow_const_of_le hle
  have hGcd : ContDiff ℝ 1 (fun y => ((u y) ^ 2) ^ (p / 2) • F y) := hUcd.smul hFcd
  have hcontUP : Continuous (fun x => ((u x) ^ 2) ^ (p / 2)) := hUcd.continuous
  have hcontDuP : Continuous (fun x => ‖fderiv ℝ u x‖ ^ p) :=
    (hu.continuous_fderiv one_ne_zero).norm.rpow_const (fun _ => Or.inr (by linarith))
  -- plumbing (same as the p=2 case)
  have hvolfin : volume Ω ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hΩ.isCompact_closure.measure_lt_top).ne
  have hμfin : (μHE[m + 1] : Measure (ℝ^(m + 2))) (frontier Ω) ≠ ∞ :=
    (surfaceMeasure_frontier_lt_top hΩ).ne
  have hfrmeas : MeasurableSet (frontier Ω) := isClosed_frontier.measurableSet
  have intΩ : ∀ {φ : (ℝ^(m + 2)) → ℝ}, Continuous φ → IntegrableOn φ Ω volume := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded hvolfin hφ.aestronglyMeasurable
      ((ae_restrict_iff' hΩ.measurableSet).mpr (ae_of_all _ (fun x hx => hB x (subset_closure hx))))
  have intFr : ∀ {φ : (ℝ^(m + 2)) → ℝ}, Continuous φ →
      IntegrableOn φ (frontier Ω) (μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hΩ.isCompact_frontier.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded hμfin hφ.aestronglyMeasurable
      ((ae_restrict_iff' hfrmeas).mpr (ae_of_all _ (fun x hx => hB x hx)))
  obtain ⟨M₁, hM₁⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn
    (continuous_divergenceE hFcd).continuousOn
  obtain ⟨M₂, hM₂⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hFcd.continuous.continuousOn
  set M₁' : ℝ := max M₁ 0 with hM₁'def
  set M₂' : ℝ := max M₂ 0 with hM₂'def
  have hM₁'nn : (0 : ℝ) ≤ M₁' := le_max_right _ _
  have hM₂'nn : (0 : ℝ) ≤ M₂' := le_max_right _ _
  refine ⟨M₁' + p * M₂', by positivity, ?_⟩
  -- pointwise interior bound via the divergence Leibniz rule + trace_young
  have hptwise : ∀ x ∈ Ω, divergenceE (fun y => ((u y) ^ 2) ^ (p / 2) • F y) x
      ≤ (M₁' + p * M₂') * (((u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) := by
    intro x hx
    have hxcl : x ∈ closure Ω := subset_closure hx
    have hud : HasFDerivAt u (fderiv ℝ u x) x :=
      (hu.differentiable one_ne_zero).differentiableAt.hasFDerivAt
    have hfd : HasFDerivAt (fun y => ((u y) ^ 2) ^ (p / 2))
        ((p / 2 * ((u x) ^ 2) ^ (p / 2 - 1)) • ((2 • u x ^ 1) • fderiv ℝ u x)) x :=
      (hud.pow 2).rpow_const (Or.inr (by linarith : (1 : ℝ) ≤ p / 2))
    have hLeib : divergenceE (fun y => ((u y) ^ 2) ^ (p / 2) • F y) x
        = ((u x) ^ 2) ^ (p / 2) * divergenceE F x
          + fderiv ℝ (fun y => ((u y) ^ 2) ^ (p / 2)) x (F x) :=
      divergenceE_smul_scalar hfd.differentiableAt
        (hFcd.differentiable one_ne_zero).differentiableAt
    have hcross : fderiv ℝ (fun y => ((u y) ^ 2) ^ (p / 2)) x (F x)
        = p * u x * ((u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x) := by
      rw [hfd.fderiv]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, pow_one]
      push_cast; ring
    rw [hLeib, hcross]
    have hB : (0 : ℝ) ≤ ((u x) ^ 2) ^ (p / 2) := Real.rpow_nonneg (by positivity) _
    have hA : (0 : ℝ) ≤ ((u x) ^ 2) ^ (p / 2 - 1) := Real.rpow_nonneg (by positivity) _
    have hDu : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ := norm_nonneg _
    have hDup : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ ^ p := Real.rpow_nonneg hDu _
    have hdivle : divergenceE F x ≤ M₁' :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM₁ x hxcl).trans (le_max_left _ _))
    have t1 : ((u x) ^ 2) ^ (p / 2) * divergenceE F x ≤ M₁' * ((u x) ^ 2) ^ (p / 2) := by
      nlinarith [hB, hdivle]
    have hvle : |fderiv ℝ u x (F x)| ≤ ‖fderiv ℝ u x‖ * ‖F x‖ := by
      have := (fderiv ℝ u x).le_opNorm (F x); rwa [Real.norm_eq_abs] at this
    have hnF2 : ‖F x‖ ≤ M₂' := (hM₂ x hxcl).trans (le_max_left _ _)
    have huv : u x * fderiv ℝ u x (F x) ≤ M₂' * (|u x| * ‖fderiv ℝ u x‖) :=
      calc u x * fderiv ℝ u x (F x) ≤ |u x| * |fderiv ℝ u x (F x)| :=
            (le_abs_self _).trans_eq (abs_mul _ _)
        _ ≤ |u x| * (‖fderiv ℝ u x‖ * M₂') :=
            mul_le_mul_of_nonneg_left
              (hvle.trans (mul_le_mul_of_nonneg_left hnF2 hDu)) (abs_nonneg _)
        _ = M₂' * (|u x| * ‖fderiv ℝ u x‖) := by ring
    have hyoung := trace_young hp (u x) (‖fderiv ℝ u x‖) hDu
    have hcrossbound : p * u x * ((u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x)
        ≤ M₂' * ((p - 1) * ((u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) :=
      calc p * u x * ((u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x)
          ≤ p * ((u x) ^ 2) ^ (p / 2 - 1) * (M₂' * (|u x| * ‖fderiv ℝ u x‖)) := by
            nlinarith [mul_le_mul_of_nonneg_left huv (mul_nonneg (by linarith : (0:ℝ) ≤ p) hA)]
        _ ≤ M₂' * ((p - 1) * ((u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) := by
            nlinarith [mul_le_mul_of_nonneg_left hyoung hM₂'nn]
    calc ((u x) ^ 2) ^ (p / 2) * divergenceE F x
            + p * u x * ((u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x)
        ≤ M₁' * ((u x) ^ 2) ^ (p / 2)
            + M₂' * ((p - 1) * ((u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) :=
          add_le_add t1 hcrossbound
      _ ≤ (M₁' + p * M₂') * (((u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) := by
          nlinarith [mul_nonneg hM₁'nn hDup, mul_nonneg hM₂'nn hB,
            mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ p - 1) hM₂'nn) hDup]
  calc ∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      ≤ ∫ x in frontier Ω, ⟪((u x) ^ 2) ^ (p / 2) • F x, ν x⟫
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
        refine setIntegral_mono_on (intFr hcontUP)
          (intFr (Continuous.inner (hcontUP.smul hFcd.continuous) hν.continuous))
          hfrmeas (fun x hx => ?_)
        rw [real_inner_smul_left]
        nlinarith [Real.rpow_nonneg (sq_nonneg (u x)) (p / 2), hFν x hx]
    _ = ∫ x in Ω, divergenceE (fun y => ((u y) ^ 2) ^ (p / 2) • F y) x :=
        (divergence_theorem hΩ hν hGcd).symm
    _ ≤ ∫ x in Ω, (M₁' + p * M₂') * (((u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) :=
        setIntegral_mono_on (intΩ (continuous_divergenceE hGcd))
          (intΩ (continuous_const.mul (hcontUP.add hcontDuP))) hΩ.measurableSet hptwise
    _ = (M₁' + p * M₂') * ((∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) := by
        rw [integral_const_mul, integral_add (intΩ hcontUP) (intΩ hcontDuP)]

/-- **The `Lᵖ` Sobolev trace estimate for all `p ≥ 1`** (Evans §5.5): for a `C¹` function `u` on a
bounded `C¹` domain `Ω`, `∫_{∂Ω} |u|^p dμ_H ≤ C(∫_Ω |u|^p + ∫_Ω ‖Du‖^p)` with `|u|^p = (u²)^{p/2}`.
For `1 ≤ p < 2` the integrand `(u²)^{p/2}` is no longer `C¹` at `u = 0`, so we run the argument on
the strictly-positive smoothing `(ε²+u²)^{p/2}` (`C¹` since the base never vanishes), obtaining
the estimate with a constant `C` independent of `ε`, then send `ε → 0` by dominated convergence.
This finishes the boundary estimate — the analytic heart of the trace theorem — across the entire
Sobolev range. -/
theorem trace_estimate_lp {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ℝ^(m + 2)) → ℝ, ContDiff ℝ 1 u →
      ∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
        ≤ C * ((∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) := by
  obtain ⟨F, hFcd, hFν⟩ := exists_transverse_field hΩ hν
  -- plumbing (independent of `u`)
  have hvolfin : volume Ω ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hΩ.isCompact_closure.measure_lt_top).ne
  have hμfin : (μHE[m + 1] : Measure (ℝ^(m + 2))) (frontier Ω) ≠ ∞ :=
    (surfaceMeasure_frontier_lt_top hΩ).ne
  have hfrmeas : MeasurableSet (frontier Ω) := isClosed_frontier.measurableSet
  have intΩ : ∀ {φ : (ℝ^(m + 2)) → ℝ}, Continuous φ → IntegrableOn φ Ω volume := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded hvolfin hφ.aestronglyMeasurable
      ((ae_restrict_iff' hΩ.measurableSet).mpr (ae_of_all _ (fun x hx => hB x (subset_closure hx))))
  have intFr : ∀ {φ : (ℝ^(m + 2)) → ℝ}, Continuous φ →
      IntegrableOn φ (frontier Ω) (μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hΩ.isCompact_frontier.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded hμfin hφ.aestronglyMeasurable
      ((ae_restrict_iff' hfrmeas).mpr (ae_of_all _ (fun x hx => hB x hx)))
  obtain ⟨M₁, hM₁⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn
    (continuous_divergenceE hFcd).continuousOn
  obtain ⟨M₂, hM₂⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hFcd.continuous.continuousOn
  set M₁' : ℝ := max M₁ 0 with hM₁'def
  set M₂' : ℝ := max M₂ 0 with hM₂'def
  have hM₁'nn : (0 : ℝ) ≤ M₁' := le_max_right _ _
  have hM₂'nn : (0 : ℝ) ≤ M₂' := le_max_right _ _
  set C : ℝ := M₁' + p * M₂' with hCdef
  have hCnn : (0 : ℝ) ≤ C := by positivity
  refine ⟨C, hCnn, fun u hu => ?_⟩
  have hcontDuP : Continuous (fun x => ‖fderiv ℝ u x‖ ^ p) :=
    (hu.continuous_fderiv one_ne_zero).norm.rpow_const (fun _ => Or.inr (by linarith))
  -- continuity of `(c + u²)^{p/2}` for any `c` (base `≥ 0`, exponent `≥ 0`)
  have hcontc : ∀ c : ℝ, Continuous (fun x => (c + (u x) ^ 2) ^ (p / 2)) := fun c =>
    (continuous_const.add (hu.continuous.pow 2)).rpow_const (fun _ => Or.inr (by linarith))
  have hcontU0 : Continuous (fun x => ((u x) ^ 2) ^ (p / 2)) :=
    (hu.continuous.pow 2).rpow_const (fun _ => Or.inr (by linarith))
  -- the smoothed estimate, with `C` independent of `ε`
  have hsmooth : ∀ e : ℝ, 0 < e →
      ∫ x in frontier Ω, (e ^ 2 + (u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
        ≤ C * ((∫ x in Ω, (e ^ 2 + (u x) ^ 2) ^ (p / 2)) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) := by
    intro e he
    have hbne : ∀ x, (e ^ 2 + (u x) ^ 2) ≠ 0 := fun x =>
      (add_pos_of_pos_of_nonneg (pow_pos he 2) (sq_nonneg (u x))).ne'
    have hUcd : ContDiff ℝ 1 (fun x => (e ^ 2 + (u x) ^ 2) ^ (p / 2)) :=
      (contDiff_const.add (hu.pow 2)).rpow_const_of_ne hbne
    have hGcd : ContDiff ℝ 1 (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2) • F y) := hUcd.smul hFcd
    have hptwise : ∀ x ∈ Ω, divergenceE (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2) • F y) x
        ≤ C * ((e ^ 2 + (u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) := by
      intro x hx
      have hxcl : x ∈ closure Ω := subset_closure hx
      have hbpos : (0 : ℝ) < e ^ 2 + (u x) ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos he 2) (sq_nonneg _)
      have hud : HasFDerivAt u (fderiv ℝ u x) x :=
        (hu.differentiable one_ne_zero).differentiableAt.hasFDerivAt
      have hbfd : HasFDerivAt (fun y => e ^ 2 + (u y) ^ 2) (0 + (2 • u x ^ 1) • fderiv ℝ u x) x :=
        (hasFDerivAt_const (e ^ 2) x).add (hud.pow 2)
      have hfd : HasFDerivAt (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2))
          ((p / 2 * (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1)) • (0 + (2 • u x ^ 1) • fderiv ℝ u x)) x :=
        hbfd.rpow_const (Or.inl (hbne x))
      have hLeib : divergenceE (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2) • F y) x
          = (e ^ 2 + (u x) ^ 2) ^ (p / 2) * divergenceE F x
            + fderiv ℝ (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2)) x (F x) :=
        divergenceE_smul_scalar hfd.differentiableAt
          (hFcd.differentiable one_ne_zero).differentiableAt
      have hcross : fderiv ℝ (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2)) x (F x)
          = p * u x * (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x) := by
        rw [hfd.fderiv]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, pow_one, zero_add]
        push_cast; ring
      rw [hLeib, hcross]
      have hB : (0 : ℝ) ≤ (e ^ 2 + (u x) ^ 2) ^ (p / 2) := Real.rpow_nonneg hbpos.le _
      have hA : (0 : ℝ) ≤ (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1) := Real.rpow_nonneg hbpos.le _
      have hDu : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ := norm_nonneg _
      have hDup : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ ^ p := Real.rpow_nonneg hDu _
      have hdivle : divergenceE F x ≤ M₁' :=
        (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM₁ x hxcl).trans (le_max_left _ _))
      have t1 : (e ^ 2 + (u x) ^ 2) ^ (p / 2) * divergenceE F x
          ≤ M₁' * (e ^ 2 + (u x) ^ 2) ^ (p / 2) := by nlinarith [hB, hdivle]
      have hvle : |fderiv ℝ u x (F x)| ≤ ‖fderiv ℝ u x‖ * ‖F x‖ := by
        have := (fderiv ℝ u x).le_opNorm (F x); rwa [Real.norm_eq_abs] at this
      have hnF2 : ‖F x‖ ≤ M₂' := (hM₂ x hxcl).trans (le_max_left _ _)
      have huv : u x * fderiv ℝ u x (F x) ≤ M₂' * (|u x| * ‖fderiv ℝ u x‖) :=
        calc u x * fderiv ℝ u x (F x) ≤ |u x| * |fderiv ℝ u x (F x)| :=
              (le_abs_self _).trans_eq (abs_mul _ _)
          _ ≤ |u x| * (‖fderiv ℝ u x‖ * M₂') :=
              mul_le_mul_of_nonneg_left
                (hvle.trans (mul_le_mul_of_nonneg_left hnF2 hDu)) (abs_nonneg _)
          _ = M₂' * (|u x| * ‖fderiv ℝ u x‖) := by ring
      have hyoung := trace_young_pos hp (e ^ 2 + (u x) ^ 2) (u x) (‖fderiv ℝ u x‖) hbpos
        (by nlinarith [sq_nonneg e]) hDu
      have hcrossbound : p * u x * (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x)
          ≤ M₂' * ((p - 1) * (e ^ 2 + (u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) :=
        calc p * u x * (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x)
            ≤ p * (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1) * (M₂' * (|u x| * ‖fderiv ℝ u x‖)) := by
              nlinarith [mul_le_mul_of_nonneg_left huv (mul_nonneg (by linarith : (0:ℝ) ≤ p) hA)]
          _ ≤ M₂' * ((p - 1) * (e ^ 2 + (u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) := by
              nlinarith [mul_le_mul_of_nonneg_left hyoung hM₂'nn]
      calc (e ^ 2 + (u x) ^ 2) ^ (p / 2) * divergenceE F x
              + p * u x * (e ^ 2 + (u x) ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (F x)
          ≤ M₁' * (e ^ 2 + (u x) ^ 2) ^ (p / 2)
              + M₂' * ((p - 1) * (e ^ 2 + (u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) :=
            add_le_add t1 hcrossbound
        _ ≤ C * ((e ^ 2 + (u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) := by
            rw [hCdef]
            nlinarith [mul_nonneg hM₁'nn hDup, mul_nonneg hM₂'nn hB,
              mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ p - 1) hM₂'nn) hDup]
    calc ∫ x in frontier Ω, (e ^ 2 + (u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
        ≤ ∫ x in frontier Ω, ⟪(e ^ 2 + (u x) ^ 2) ^ (p / 2) • F x, ν x⟫
            ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
          refine setIntegral_mono_on (intFr (hcontc _))
            (intFr (Continuous.inner ((hcontc _).smul hFcd.continuous) hν.continuous))
            hfrmeas (fun x hx => ?_)
          rw [real_inner_smul_left]
          nlinarith [Real.rpow_nonneg (add_pos_of_pos_of_nonneg (pow_pos he 2)
            (sq_nonneg (u x))).le (p / 2), hFν x hx]
      _ = ∫ x in Ω, divergenceE (fun y => (e ^ 2 + (u y) ^ 2) ^ (p / 2) • F y) x :=
          (divergence_theorem hΩ hν hGcd).symm
      _ ≤ ∫ x in Ω, C * ((e ^ 2 + (u x) ^ 2) ^ (p / 2) + ‖fderiv ℝ u x‖ ^ p) :=
          setIntegral_mono_on (intΩ (continuous_divergenceE hGcd))
            (intΩ (continuous_const.mul ((hcontc _).add hcontDuP))) hΩ.measurableSet hptwise
      _ = C * ((∫ x in Ω, (e ^ 2 + (u x) ^ 2) ^ (p / 2)) + ∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) := by
          rw [integral_const_mul, integral_add (intΩ (hcontc _)) (intΩ hcontDuP)]
  -- send `ε → 0` by dominated convergence along `aₖ = 1/(k+1)`
  set a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with ha_def
  have ha_pos : ∀ k, 0 < a k := fun k => by positivity
  have ha_le_one : ∀ k, a k ≤ 1 := fun k => by
    rw [ha_def, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
  have ha0 : Filter.Tendsto a Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have dctTendsto : ∀ (μ : Measure (ℝ^(m + 2))),
      Integrable (fun x => (1 + (u x) ^ 2) ^ (p / 2)) μ →
      Filter.Tendsto (fun k : ℕ => ∫ x, ((a k) ^ 2 + (u x) ^ 2) ^ (p / 2) ∂μ) Filter.atTop
        (𝓝 (∫ x, ((u x) ^ 2) ^ (p / 2) ∂μ)) := by
    intro μ hbint
    refine tendsto_integral_of_dominated_convergence (fun x => (1 + (u x) ^ 2) ^ (p / 2))
      (fun k => (hcontc _).aestronglyMeasurable) hbint (fun k => ?_) ?_
    · refine ae_of_all _ (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [ha_le_one k, (ha_pos k).le])
        (by linarith)
    · refine ae_of_all _ (fun x => ?_)
      have hbt : Filter.Tendsto (fun k : ℕ => (a k) ^ 2 + (u x) ^ 2) Filter.atTop
          (𝓝 ((u x) ^ 2)) := by simpa using (ha0.pow 2).add_const ((u x) ^ 2)
      exact (Real.continuousAt_rpow_const _ (p / 2) (Or.inr (by linarith))).tendsto.comp hbt
  have hAtendsto := dctTendsto (μHE[m + 1].restrict (frontier Ω)) (intFr (hcontc 1))
  have hBtendsto := dctTendsto (volume.restrict Ω) (intΩ (hcontc 1))
  exact le_of_tendsto_of_tendsto' hAtendsto
    ((hBtendsto.add_const _).const_mul C) (fun k => hsmooth (a k) (ha_pos k))

/-- **The trace estimate in `Lᵖ`-operator form.** There is a constant `K ≥ 0` such that for every
`C¹` function `u` the `Lᵖ(∂Ω)` norm of its boundary trace is bounded by `K` times the `W^{1,p}`
graph norm `max(‖u‖_{Lᵖ(Ω)}, ‖Du‖_{Lᵖ(Ω)})` (with `Du` the derivative in `Lᵖ(Ω; (ℝⁿ→L ℝ))`).
This is `trace_estimate_lp` rewritten through `‖·.toLp·‖ = (∫ ‖·‖^p)^{1/p}`; it is the boundedness
that makes the trace a continuous linear operator. -/
theorem trace_lp_bound {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν) {p : ℝ} (hp : 1 ≤ p)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqne : q ≠ ⊤) (hqp : q.toReal = p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : (ℝ^(m + 2)) → ℝ), ContDiff ℝ 1 u →
      ∀ (hbd : MemLp u q (μHE[m + 1].restrict (frontier Ω)))
        (hΩu : MemLp u q (volume.restrict Ω))
        (hΩd : MemLp (fun x => fderiv ℝ u x) q (volume.restrict Ω)),
        ‖hbd.toLp u‖ ≤ K * max ‖hΩu.toLp u‖ ‖hΩd.toLp (fun x => fderiv ℝ u x)‖ := by
  obtain ⟨C, hCnn, hEst⟩ := trace_estimate_lp hΩ hν hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hP0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hPt : q ≠ ⊤ := hqne
  have hPtoReal : q.toReal = p := hqp
  have hbridge : ∀ t : ℝ, ((t ^ 2) ^ (p / 2) : ℝ) = |t| ^ p := fun t => by
    rw [← sq_abs t, ← Real.rpow_natCast |t| 2, ← Real.rpow_mul (abs_nonneg t)]
    congr 1; push_cast; ring
  -- `‖toLp f‖ = (∫ ‖f‖^p)^{1/p}`, valid for scalar and vector-valued `f`
  have hnormform : ∀ {E : Type} [NormedAddCommGroup E] {μ : Measure (ℝ^(m + 2))}
      (f : (ℝ^(m + 2)) → E) (hf : MemLp f q μ),
      ‖hf.toLp f‖ = (∫ x, ‖f x‖ ^ p ∂μ) ^ p⁻¹ := by
    intro E _ μ f hf
    rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp, hf.eLpNorm_eq_integral_rpow_norm hP0 hPt,
      hPtoReal, ENNReal.toReal_ofReal (Real.rpow_nonneg
        (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)]
  refine ⟨(2 * C) ^ p⁻¹, by positivity, fun u hu hbd hΩu hΩd => ?_⟩
  have hB_nn : 0 ≤ ∫ x in Ω, ((u x) ^ 2) ^ (p / 2) :=
    integral_nonneg fun x => Real.rpow_nonneg (sq_nonneg _) _
  have hD_nn : 0 ≤ ∫ x in Ω, ‖fderiv ℝ u x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hA_nn : 0 ≤ ∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2)
      ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := integral_nonneg fun x => Real.rpow_nonneg (sq_nonneg _) _
  have hMnn : 0 ≤ max ‖hΩu.toLp u‖ ‖hΩd.toLp (fun x => fderiv ℝ u x)‖ :=
    le_max_of_le_left (norm_nonneg (hΩu.toLp u))
  -- the three `Lᵖ` norms as `(∫ ·)^{1/p}`, matching `trace_estimate_lp`
  have hnB : ‖hΩu.toLp u‖ = (∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) ^ p⁻¹ := by
    rw [hnormform u hΩu]; congr 1
    exact integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [Real.norm_eq_abs, ← hbridge])
  have hnD : ‖hΩd.toLp (fun x => fderiv ℝ u x)‖ = (∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) ^ p⁻¹ := by
    rw [hnormform _ hΩd]
  have hnbd : ‖hbd.toLp u‖
      = (∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) ^ p⁻¹ := by
    rw [hnormform u hbd]; congr 1
    exact integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [Real.norm_eq_abs, ← hbridge])
  have hpow_id : ∀ x : ℝ, 0 ≤ x → (x ^ p⁻¹) ^ p = x := fun x hx => by
    rw [← Real.rpow_mul hx, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  rw [hnbd]
  set M : ℝ := max ‖hΩu.toLp u‖ ‖hΩd.toLp (fun x => fderiv ℝ u x)‖ with hM
  have hBle : (∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) ≤ M ^ p := by
    have h1 : (∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) ^ p⁻¹ ≤ M := hnB ▸ le_max_left _ _
    calc (∫ x in Ω, ((u x) ^ 2) ^ (p / 2))
        = ((∫ x in Ω, ((u x) ^ 2) ^ (p / 2)) ^ p⁻¹) ^ p := (hpow_id _ hB_nn).symm
      _ ≤ M ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hB_nn _) h1 hp0.le
  have hDle : (∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) ≤ M ^ p := by
    have h1 : (∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) ^ p⁻¹ ≤ M := hnD ▸ le_max_right _ _
    calc (∫ x in Ω, ‖fderiv ℝ u x‖ ^ p)
        = ((∫ x in Ω, ‖fderiv ℝ u x‖ ^ p) ^ p⁻¹) ^ p := (hpow_id _ hD_nn).symm
      _ ≤ M ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hD_nn _) h1 hp0.le
  have hAle : (∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      ≤ 2 * C * M ^ p :=
    (hEst u hu).trans (by nlinarith [hBle, hDle, hCnn])
  calc (∫ x in frontier Ω, ((u x) ^ 2) ^ (p / 2) ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) ^ p⁻¹
      ≤ (2 * C * M ^ p) ^ p⁻¹ := Real.rpow_le_rpow hA_nn hAle (by positivity)
    _ = (2 * C) ^ p⁻¹ * M := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hMnn _), ← Real.rpow_mul hMnn,
          mul_inv_cancel₀ hp0.ne', Real.rpow_one]

/-! ### The trace operator

We package the boundary trace as a genuine bounded linear operator.  A `C¹` function on the bounded
`C¹` domain is `Lᵖ` on `Ω` (bounded on the compact `closure Ω`), its derivative is `Lᵖ(Ω)`, and its
boundary restriction is `Lᵖ(∂Ω)`.  Sending `u ↦ (u, Du)` embeds the `C¹` functions into the graph
space `H = Lᵖ(Ω) × Lᵖ(Ω; ℝⁿ →L ℝ)` (a `W^{1,p}`-type space), and `trace_lp_bound` makes the trace
`u ↦ u|_{∂Ω}` bounded relative to that embedding.  It therefore factors through the range of the
embedding as a `ContinuousLinearMap` into `Lᵖ(∂Ω)`. -/

/-- A continuous function is `Lᵖ` on the bounded `C¹` domain `Ω` (bounded on the compact closure).
Stated for an opaque exponent `q` so the `Lp q` machinery below never tries to reduce it. -/
theorem memLp_of_continuous_restrict_Ω {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {q : ℝ≥0∞} {E : Type} [NormedAddCommGroup E] {φ : (ℝ^(m + 2)) → E} (hφ : Continuous φ) :
    MemLp φ q (volume.restrict Ω) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (measure_mono subset_closure).trans_lt hΩ.isCompact_closure.measure_lt_top⟩
  obtain ⟨B, hB⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hφ.continuousOn
  exact MemLp.of_bound hφ.aestronglyMeasurable B
    ((ae_restrict_iff' hΩ.measurableSet).mpr (ae_of_all _ fun x hx => hB x (subset_closure hx)))

/-- A continuous function is `Lᵖ` on the boundary `∂Ω` (bounded on the compact `∂Ω`, finite `μ_H`). -/
theorem memLp_of_continuous_restrict_frontier {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {q : ℝ≥0∞} {E : Type} [NormedAddCommGroup E] {φ : (ℝ^(m + 2)) → E}
    (hφ : Continuous φ) : MemLp φ q (μHE[m + 1].restrict (frontier Ω)) := by
  haveI : IsFiniteMeasure ((μHE[m + 1] : Measure (ℝ^(m + 2))).restrict (frontier Ω)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact surfaceMeasure_frontier_lt_top hΩ⟩
  obtain ⟨B, hB⟩ := hΩ.isCompact_frontier.exists_bound_of_continuousOn hφ.continuousOn
  exact MemLp.of_bound hφ.aestronglyMeasurable B
    ((ae_restrict_iff' isClosed_frontier.measurableSet).mpr (ae_of_all _ fun x hx => hB x hx))

/-- The submodule of `C¹` functions inside the ambient function space. -/
def contDiffSubmodule : Submodule ℝ ((ℝ^(m + 2)) → ℝ) where
  carrier := {u | ContDiff ℝ 1 u}
  add_mem' {a b} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) := ha.add hb
  zero_mem' := (contDiff_const : ContDiff ℝ 1 (0 : (ℝ^(m + 2)) → ℝ))
  smul_mem' c a (ha : ContDiff ℝ 1 a) := ha.const_smul c

/-- `C¹`-ness extracted from membership in `contDiffSubmodule`. -/
theorem contDiff_of_mem_contDiffSubmodule (u : contDiffSubmodule (m := m)) :
    ContDiff ℝ 1 (u : (ℝ^(m + 2)) → ℝ) := u.2

/-- The graph space `H = Lᵖ(Ω) × Lᵖ(Ω; ℝⁿ →L ℝ)` housing `(u, Du)`.  The exponent `q : ℝ≥0∞` is kept
opaque (never `ENNReal.ofReal p`) so the `Lp q` defeq machinery does not blow up downstream. -/
abbrev traceGraphSpace (Ω : Set (ℝ^(m + 2))) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Type _ :=
  Lp ℝ q (volume.restrict Ω) × Lp ((ℝ^(m + 2)) →L[ℝ] ℝ) q (volume.restrict Ω)

variable {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
  {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The Sobolev embedding `u ↦ (u, Du)` of the `C¹` functions into the graph space. -/
noncomputable def traceEmbed :
    contDiffSubmodule (m := m) →ₗ[ℝ] traceGraphSpace Ω q where
  toFun u := ((memLp_of_continuous_restrict_Ω hΩ (contDiff_of_mem_contDiffSubmodule u).continuous).toLp u,
    (memLp_of_continuous_restrict_Ω hΩ
      ((contDiff_of_mem_contDiffSubmodule u).continuous_fderiv one_ne_zero)).toLp
      (fun x => fderiv ℝ (u : (ℝ^(m + 2)) → ℝ) x))
  map_add' u v := by
    have hu := contDiff_of_mem_contDiffSubmodule u
    have hv := contDiff_of_mem_contDiffSubmodule v
    have huv := contDiff_of_mem_contDiffSubmodule (u + v)
    refine Prod.ext ?_ ?_
    · exact (MemLp.toLp_congr (memLp_of_continuous_restrict_Ω hΩ huv.continuous)
        ((memLp_of_continuous_restrict_Ω hΩ hu.continuous).add
          (memLp_of_continuous_restrict_Ω hΩ hv.continuous))
        Filter.EventuallyEq.rfl).trans
        (MemLp.toLp_add (memLp_of_continuous_restrict_Ω hΩ hu.continuous)
          (memLp_of_continuous_restrict_Ω hΩ hv.continuous))
    · exact (MemLp.toLp_congr
        (memLp_of_continuous_restrict_Ω hΩ (huv.continuous_fderiv one_ne_zero))
        ((memLp_of_continuous_restrict_Ω hΩ (hu.continuous_fderiv one_ne_zero)).add
          (memLp_of_continuous_restrict_Ω hΩ (hv.continuous_fderiv one_ne_zero)))
        (ae_of_all _ fun x => ((hu.differentiable one_ne_zero x).hasFDerivAt.add
          (hv.differentiable one_ne_zero x).hasFDerivAt).fderiv)).trans
        (MemLp.toLp_add (memLp_of_continuous_restrict_Ω hΩ (hu.continuous_fderiv one_ne_zero))
          (memLp_of_continuous_restrict_Ω hΩ (hv.continuous_fderiv one_ne_zero)))
  map_smul' c u := by
    have hu := contDiff_of_mem_contDiffSubmodule u
    have hcu := contDiff_of_mem_contDiffSubmodule (c • u)
    refine Prod.ext ?_ ?_
    · exact (MemLp.toLp_congr (memLp_of_continuous_restrict_Ω hΩ hcu.continuous)
        ((memLp_of_continuous_restrict_Ω hΩ hu.continuous).const_smul c)
        Filter.EventuallyEq.rfl).trans
        (MemLp.toLp_const_smul c (memLp_of_continuous_restrict_Ω hΩ hu.continuous))
    · exact (MemLp.toLp_congr
        (memLp_of_continuous_restrict_Ω hΩ (hcu.continuous_fderiv one_ne_zero))
        ((memLp_of_continuous_restrict_Ω hΩ (hu.continuous_fderiv one_ne_zero)).const_smul c)
        (ae_of_all _ fun x =>
          ((hu.differentiable one_ne_zero x).hasFDerivAt.const_smul c).fderiv)).trans
        (MemLp.toLp_const_smul c
          (memLp_of_continuous_restrict_Ω hΩ (hu.continuous_fderiv one_ne_zero)))

/-- The boundary-trace linear map `u ↦ u|_{∂Ω}` on the `C¹` functions. -/
noncomputable def traceRestrict :
    contDiffSubmodule (m := m) →ₗ[ℝ] Lp ℝ q (μHE[m + 1].restrict (frontier Ω)) where
  toFun u := (memLp_of_continuous_restrict_frontier hΩ
    (contDiff_of_mem_contDiffSubmodule u).continuous).toLp u
  map_add' u v :=
    (MemLp.toLp_congr (memLp_of_continuous_restrict_frontier hΩ
        (contDiff_of_mem_contDiffSubmodule (u + v)).continuous)
      ((memLp_of_continuous_restrict_frontier hΩ
          (contDiff_of_mem_contDiffSubmodule u).continuous).add
        (memLp_of_continuous_restrict_frontier hΩ
          (contDiff_of_mem_contDiffSubmodule v).continuous))
      Filter.EventuallyEq.rfl).trans
      (MemLp.toLp_add (memLp_of_continuous_restrict_frontier hΩ
          (contDiff_of_mem_contDiffSubmodule u).continuous)
        (memLp_of_continuous_restrict_frontier hΩ
          (contDiff_of_mem_contDiffSubmodule v).continuous))
  map_smul' c u :=
    (MemLp.toLp_congr (memLp_of_continuous_restrict_frontier hΩ
        (contDiff_of_mem_contDiffSubmodule (c • u)).continuous)
      ((memLp_of_continuous_restrict_frontier hΩ
          (contDiff_of_mem_contDiffSubmodule u).continuous).const_smul c)
      Filter.EventuallyEq.rfl).trans (MemLp.toLp_const_smul c
        (memLp_of_continuous_restrict_frontier hΩ
          (contDiff_of_mem_contDiffSubmodule u).continuous))

/-- Componentwise value of `traceEmbed` (`rfl`; used so downstream reasoning never unfolds the map). -/
@[simp] theorem traceEmbed_apply (u : contDiffSubmodule (m := m)) :
    traceEmbed hΩ (q := q) u = ((memLp_of_continuous_restrict_Ω hΩ
        (contDiff_of_mem_contDiffSubmodule u).continuous).toLp u,
      (memLp_of_continuous_restrict_Ω hΩ
        ((contDiff_of_mem_contDiffSubmodule u).continuous_fderiv one_ne_zero)).toLp
        (fun x => fderiv ℝ (u : (ℝ^(m + 2)) → ℝ) x)) := rfl

/-- Value of `traceRestrict` (`rfl`). -/
@[simp] theorem traceRestrict_apply (u : contDiffSubmodule (m := m)) :
    traceRestrict hΩ (q := q) u = (memLp_of_continuous_restrict_frontier hΩ
      (contDiff_of_mem_contDiffSubmodule u).continuous).toLp u := rfl

set_option maxHeartbeats 1000000 in
/-- `ker traceEmbed ≤ ker traceRestrict`: a `C¹` function that vanishes in `Lᵖ(Ω)` is `0` on `Ω`
(continuity + `Ω` open), hence `0` on `closure Ω ⊇ ∂Ω`, so its trace is `0`. -/
theorem traceEmbed_ker_le :
    LinearMap.ker (traceEmbed hΩ (q := q)) ≤ LinearMap.ker (traceRestrict hΩ (q := q)) := by
  intro w hw
  rw [LinearMap.mem_ker] at hw ⊢
  have hwc : ContDiff ℝ 1 (w : (ℝ^(m + 2)) → ℝ) := contDiff_of_mem_contDiffSubmodule w
  have h1 : (memLp_of_continuous_restrict_Ω hΩ (q := q) hwc.continuous).toLp
      (w : (ℝ^(m + 2)) → ℝ) = 0 := by
    have h := congrArg Prod.fst hw; rw [traceEmbed_apply] at h; exact h
  have hae : (w : (ℝ^(m + 2)) → ℝ) =ᵐ[volume.restrict Ω] 0 := by
    have hcoe := (memLp_of_continuous_restrict_Ω hΩ (q := q) hwc.continuous).coeFn_toLp
    rw [h1] at hcoe; exact hcoe.symm.trans (Lp.coeFn_zero ..)
  have heqCl : Set.EqOn (w : (ℝ^(m + 2)) → ℝ) 0 (closure Ω) :=
    (Measure.eqOn_of_ae_eq hae hwc.continuous.continuousOn continuous_const.continuousOn
      (by rw [hΩ.isOpen.interior_eq]; exact subset_closure)).closure hwc.continuous continuous_const
  have haebd : (w : (ℝ^(m + 2)) → ℝ) =ᵐ[μHE[m + 1].restrict (frontier Ω)] 0 :=
    (ae_restrict_iff' isClosed_frontier.measurableSet).mpr
      (ae_of_all _ fun x hx => heqCl (frontier_subset_closure hx))
  rw [traceRestrict_apply]
  exact (MemLp.toLp_congr (memLp_of_continuous_restrict_frontier hΩ hwc.continuous)
    MemLp.zero haebd).trans (MemLp.toLp_zero MemLp.zero)

set_option maxHeartbeats 4000000 in
/-- **The Sobolev trace operator** `T : W^{1,p}_{C¹}(Ω) → Lᵖ(∂Ω)` — the bounded linear operator
sending a `C¹` function (embedded in the graph space `Lᵖ(Ω) × Lᵖ(Ω; ℝⁿ →L ℝ)` via `u ↦ (u, Du)`)
to its boundary trace `u|_{∂Ω}`.  Boundedness is `trace_lp_bound`; the trace factors through the
range of the embedding by `traceEmbed_ker_le`.  Defined on the range of the embedding — the closure
of which is where the trace extends to all of `W^{1,p}(Ω)` once `C¹`-density up to the boundary
(a Sobolev extension operator) is available.  Made tractable by keeping the exponent `q` opaque. -/
noncomputable def traceCLM (hν : IsOutwardNormal Ω ν) (hqne : q ≠ ⊤) :
    ↥(LinearMap.range (traceEmbed hΩ (q := q))) →L[ℝ]
      Lp ℝ q (μHE[m + 1].restrict (frontier Ω)) :=
  let hp : (1 : ℝ) ≤ q.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hqne Fact.out
  LinearMap.mkContinuous
    ((Submodule.liftQ _ (traceRestrict hΩ (q := q)) (traceEmbed_ker_le hΩ)).comp
      (traceEmbed hΩ (q := q)).quotKerEquivRange.symm.toLinearMap)
    (trace_lp_bound hΩ hν hp hqne rfl).choose
    (by
      obtain ⟨hKnn, hK⟩ := (trace_lp_bound hΩ hν hp hqne rfl).choose_spec
      have hKbound : ∀ w : contDiffSubmodule (m := m), ‖traceRestrict hΩ (q := q) w‖
          ≤ (trace_lp_bound hΩ hν hp hqne rfl).choose * ‖traceEmbed hΩ (q := q) w‖ := by
        intro w
        rw [traceRestrict_apply, traceEmbed_apply, Prod.norm_def]
        exact hK (w : (ℝ^(m + 2)) → ℝ) (contDiff_of_mem_contDiffSubmodule w)
          (memLp_of_continuous_restrict_frontier hΩ (contDiff_of_mem_contDiffSubmodule w).continuous)
          (memLp_of_continuous_restrict_Ω hΩ (contDiff_of_mem_contDiffSubmodule w).continuous)
          (memLp_of_continuous_restrict_Ω hΩ
            ((contDiff_of_mem_contDiffSubmodule w).continuous_fderiv one_ne_zero))
      intro z
      obtain ⟨w, hw⟩ := z.2
      have hsymm : (traceEmbed hΩ (q := q)).quotKerEquivRange.symm z = Submodule.Quotient.mk w :=
        (LinearEquiv.symm_apply_eq _).mpr
          (Subtype.ext (((traceEmbed hΩ (q := q)).quotKerEquivRange_apply_mk w).trans hw)).symm
      calc ‖((Submodule.liftQ _ (traceRestrict hΩ (q := q)) (traceEmbed_ker_le hΩ)).comp
              (traceEmbed hΩ (q := q)).quotKerEquivRange.symm.toLinearMap) z‖
          = ‖traceRestrict hΩ (q := q) w‖ := by
            simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, Submodule.liftQ_apply]
        _ ≤ (trace_lp_bound hΩ hν hp hqne rfl).choose * ‖traceEmbed hΩ (q := q) w‖ := hKbound w
        _ = (trace_lp_bound hΩ hν hp hqne rfl).choose * ‖z‖ := by
            rw [Submodule.coe_norm, hw])

end Sobolev
