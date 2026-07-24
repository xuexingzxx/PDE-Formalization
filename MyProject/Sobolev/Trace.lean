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
end Sobolev
