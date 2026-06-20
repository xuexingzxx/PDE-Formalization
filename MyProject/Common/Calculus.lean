import Mathlib

open MeasureTheory InnerProductSpace

/-!
# Calculus Utilities for Spacetime Functions (Evans PDE)

Definitions and lemmas for partial derivatives of functions on spacetime `ℝⁿ × ℝ`,
matching Evans' notation throughout the PDE formalization.

## Notation
* `Du`  — spatial gradient (Evans' notation), a vector in `ℝⁿ`
* `u_t` — time derivative, a scalar
* `Δu`  — Laplacian, used in Poisson/heat/wave equations
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Spatial Gradient -/

/-- The spatial gradient `Du(x, t)`: the gradient of `x' ↦ u(x', t)` at `x`.
    This is Evans' `Du`, a vector in `ℝⁿ`. -/
noncomputable def spatialGradient (u : ℝⁿ × ℝ → ℝ) (p : ℝⁿ × ℝ) : ℝⁿ :=
  gradient (fun x => u (x, p.2)) p.1



/-! ### Time Derivative -/

/-- The time derivative `u_t(x, t)`: the derivative of `t' ↦ u(x, t')` at `t`.
    This is Evans' `u_t`, a scalar. -/
noncomputable def timeDerivative (u : ℝⁿ × ℝ → ℝ) (p : ℝⁿ × ℝ) : ℝ :=
  deriv (fun t => u (p.1, t)) p.2

/-- Spatial Laplacian of a spacetime function: `Δ_x u(x, t)`. -/
noncomputable def spatialLaplacian (u : ℝⁿ × ℝ → ℝ) (p : ℝⁿ × ℝ) : ℝ :=
  Laplacian.laplacian (fun x => u (x, p.2)) p.1

/-- **Cross-term vanishes**: if `H(·, s)` satisfies the local Lipschitz bound
    `|H t' s − H t₀ s| ≤ M|t'−t₀|` (for `t'` near `t₀` and `s` in the integration range), then
    `C(t') = ∫_{t₀}^{t'} (H t' s − H t₀ s) ds` has derivative `0` at `t₀`: the integrand is
    `O(|t'−t₀|)` over an interval of length `|t'−t₀|`, so `C(t') = O((t'−t₀)²) = o(t'−t₀)`.
    This is the piece that the FTC + parametric-integral lemmas do not provide. -/
lemma hasDerivAt_crossTerm {H : ℝ → ℝ → ℝ} {t₀ M : ℝ} (hM : 0 ≤ M)
    (hLip : ∀ᶠ t' in nhds t₀, ∀ s ∈ Set.uIoc t₀ t', |H t' s - H t₀ s| ≤ M * |t' - t₀|) :
    HasDerivAt (fun t' => ∫ s in t₀..t', (H t' s - H t₀ s)) 0 t₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds t₀ (by positivity : (0:ℝ) < c / (M + 1)), hLip]
    with t' ht' ht'lip
  have ht'dist : |t' - t₀| < c / (M + 1) := by
    rw [Metric.mem_ball, Real.dist_eq] at ht'; exact ht'
  -- |C(t')| ≤ M · |t' − t₀|².
  have hbound : |∫ s in t₀..t', (H t' s - H t₀ s)| ≤ M * |t' - t₀| ^ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s => H t' s - H t₀ s) (a := t₀) (b := t') (C := M * |t' - t₀|)
      (fun s hs => by simpa [Real.norm_eq_abs] using ht'lip s hs)
    simpa [Real.norm_eq_abs, pow_two, mul_assoc] using h
  have hsimp : (fun t' => ∫ s in t₀..t', (H t' s - H t₀ s)) t' -
      (fun t' => ∫ s in t₀..t', (H t' s - H t₀ s)) t₀ - (t' - t₀) • (0 : ℝ)
      = ∫ s in t₀..t', (H t' s - H t₀ s) := by
    simp [intervalIntegral.integral_same]
  rw [hsimp]
  calc ‖∫ s in t₀..t', (H t' s - H t₀ s)‖
      = |∫ s in t₀..t', (H t' s - H t₀ s)| := Real.norm_eq_abs _
    _ ≤ M * |t' - t₀| ^ 2 := hbound
    _ = (M * |t' - t₀|) * |t' - t₀| := by ring
    _ ≤ c * ‖t' - t₀‖ := by
        rw [Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc M * |t' - t₀| ≤ (M + 1) * (c / (M + 1)) := by
              apply mul_le_mul _ ht'dist.le (abs_nonneg _) (by linarith)
              linarith
          _ = c := by field_simp

/-- **Leibniz rule** for an integral with parameter-dependent integrand and variable upper
    limit: if `H` and its first partial `Ht` (with `∂₁H = Ht` everywhere) are jointly
    continuous, then `d/dt' ∫₀^{t'} H t' s ds |_{t'=t} = H t t + ∫₀ᵗ Ht t s ds`.

    **Proof**: decompose `F = P + B + C` with `P(t') = ∫₀^{t'} H t s` (FTC, gives `H t t`),
    `B(t') = ∫₀ᵗ H t' s − ∫₀ᵗ H t s` (differentiation under the integral over the fixed
    interval `[0,t]`, gives `∫₀ᵗ Ht t s`), and the cross-term `C(t') = ∫ₜ^{t'}(H t' s − H t s)`
    (`hasDerivAt_crossTerm`, gives `0`). The uniform bound on `Ht` over a compact box (used both
    for the dominated-convergence step and for the cross-term's local Lipschitz estimate) comes
    from continuity. -/
lemma leibniz_integral {H Ht : ℝ → ℝ → ℝ} {t : ℝ}
    (hH : Continuous (fun p : ℝ × ℝ => H p.1 p.2))
    (hHt : Continuous (fun p : ℝ × ℝ => Ht p.1 p.2))
    (hderiv : ∀ a s : ℝ, HasDerivAt (fun a' => H a' s) (Ht a s) a) :
    HasDerivAt (fun t' => ∫ s in (0:ℝ)..t', H t' s) (H t t + ∫ s in (0:ℝ)..t, Ht t s) t := by
  -- Slice continuity.
  have hHc : ∀ a, Continuous (fun s => H a s) := fun a =>
    hH.comp (continuous_const.prodMk continuous_id)
  have hHtc : ∀ a, Continuous (fun s => Ht a s) := fun a =>
    hHt.comp (continuous_const.prodMk continuous_id)
  -- A compact box and a uniform bound `M` on `|Ht|` over it.
  set R : ℝ := |t| + 2 with hR
  have hbox : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hMbound⟩ := hbox.exists_bound_of_continuousOn hHt.continuousOn
  have hRpos : 0 < R := by rw [hR]; positivity
  have h0R : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith, le_of_lt hRpos⟩
  -- Membership facts for the box.
  have hsub : Set.Icc (t - 1) (t + 1) ⊆ Set.Icc (-R) R := by
    apply Set.Icc_subset_Icc <;> rw [hR] <;>
      [nlinarith [neg_abs_le t]; nlinarith [le_abs_self t]]
  have htbox : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have htR : t ∈ Set.Icc (-R) R := hsub htbox
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMbound (t, 0) ⟨htbox, h0R⟩)
  -- `Ht`-bound on the box, as inequalities of reals.
  have hbnd : ∀ x ∈ Set.Icc (t - 1) (t + 1), ∀ s ∈ Set.Icc (-R) R, |Ht x s| ≤ M := by
    intro x hx s hs
    simpa [Real.norm_eq_abs] using hMbound (x, s) ⟨hx, hs⟩
  -- Cross-term: local Lipschitz bound via the mean value inequality.
  have hLip : ∀ᶠ t' in nhds t, ∀ s ∈ Set.uIoc t t', |H t' s - H t s| ≤ M * |t' - t| := by
    filter_upwards [Metric.ball_mem_nhds t one_pos] with t' ht' s hs
    rw [Metric.mem_ball, Real.dist_eq] at ht'
    have habs := abs_le.mp ht'.le
    have hconv : Set.uIcc t t' ⊆ Set.Icc (t - 1) (t + 1) := by
      apply Set.uIcc_subset_Icc <;> exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have hsbox : s ∈ Set.Icc (-R) R := hsub (hconv (Set.uIoc_subset_uIcc hs))
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => H x s) (f' := fun x => Ht x s) (s := Set.uIcc t t') (C := M)
      (fun x _ => (hderiv x s).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hbnd x (hconv hx) s hsbox)
      (convex_uIcc t t') Set.right_mem_uIcc Set.left_mem_uIcc
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    rw [abs_sub_comm (H t' s) (H t s), abs_sub_comm t' t]
    exact hmvt
  -- Piece P: FTC for the fixed integrand `H t`.
  have hP : HasDerivAt (fun t' => ∫ s in (0:ℝ)..t', H t s) (H t t) t :=
    intervalIntegral.integral_hasDerivAt_right ((hHc t).intervalIntegrable 0 t)
      ((hHc t).stronglyMeasurableAtFilter MeasureTheory.volume (nhds t)) (hHc t).continuousAt
  -- Piece B: differentiation under the integral over `[0,t]`.
  have hB := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := 0) (b := t) (μ := MeasureTheory.volume) (F := H) (F' := Ht) (x₀ := t)
    (bound := fun _ => M) (s := Set.Icc (t - 1) (t + 1))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun x => (hHc x).aestronglyMeasurable.restrict)
    ((hHc t).intervalIntegrable 0 t)
    (hHtc t).aestronglyMeasurable.restrict
    (MeasureTheory.ae_of_all _ fun s hs x hx => by
      rw [Real.norm_eq_abs]
      exact hbnd x hx s ((Set.uIcc_subset_Icc h0R htR) (Set.uIoc_subset_uIcc hs)))
    (intervalIntegrable_const)
    (MeasureTheory.ae_of_all _ fun s _ x _ => hderiv x s)
  have hBconst : HasDerivAt
      (fun t' => (∫ s in (0:ℝ)..t, H t' s) - ∫ s in (0:ℝ)..t, H t s)
      (∫ s in (0:ℝ)..t, Ht t s) t := by
    simpa using hB.2.sub_const (∫ s in (0:ℝ)..t, H t s)
  -- Piece C: the cross-term.
  have hC := hasDerivAt_crossTerm hM0 hLip
  -- Assemble: `F = P + B + C`.
  have hFeq : (fun t' => ∫ s in (0:ℝ)..t', H t' s)
      = fun t' => (∫ s in (0:ℝ)..t', H t s)
          + ((∫ s in (0:ℝ)..t, H t' s) - ∫ s in (0:ℝ)..t, H t s)
          + ∫ s in t..t', (H t' s - H t s) := by
    funext t'
    have e1 : (∫ s in (0:ℝ)..t', H t' s)
        = (∫ s in (0:ℝ)..t, H t' s) + ∫ s in t..t', H t' s :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((hHc t').intervalIntegrable 0 t) ((hHc t').intervalIntegrable t t')).symm
    have e2 : (∫ s in (0:ℝ)..t', H t s)
        = (∫ s in (0:ℝ)..t, H t s) + ∫ s in t..t', H t s :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((hHc t).intervalIntegrable 0 t) ((hHc t).intervalIntegrable t t')).symm
    have e3 : (∫ s in t..t', (H t' s - H t s))
        = (∫ s in t..t', H t' s) - ∫ s in t..t', H t s :=
      intervalIntegral.integral_sub ((hHc t').intervalIntegrable t t')
        ((hHc t).intervalIntegrable t t')
    rw [e1, e2, e3]; ring
  rw [hFeq]
  simpa using (hP.add hBconst).add hC

/-! ### Gaussian moment integrability

Integrability over `ℝⁿ` of `‖z‖^k · exp(−c‖z‖²)` for `k = 0, 1, 2` (`c > 0`). Mathlib
provides the base `n`-dimensional Gaussian (`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`)
and the `1`-D moments, but not these `n`-dimensional polynomial moments. They are the standard
dominating functions for differentiating Gaussian/heat-kernel convolutions under the integral
sign, and are stated generally (any `c > 0`, any dimension `n`) for reuse. -/

/-- Elementary bound `v·e^{−v} ≤ e^{−1}` for all real `v` (the maximum of `v·e^{−v}`,
    attained at `v = 1`), via `x + 1 ≤ eˣ`. -/
private lemma mul_exp_neg_le (v : ℝ) : v * Real.exp (-v) ≤ Real.exp (-1) := by
  have h1 : v ≤ Real.exp (v - 1) := by have := Real.add_one_le_exp (v - 1); linarith
  calc v * Real.exp (-v)
      ≤ Real.exp (v - 1) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- Scalar domination `r·e^{−cr} ≤ (2/(c·e))·e^{−(c/2)r}` for `c > 0`:
    split `e^{−cr} = e^{−(c/2)r}·e^{−(c/2)r}` and bound `r·e^{−(c/2)r}` by `mul_exp_neg_le`. -/
private lemma sq_mul_exp_le {c : ℝ} (hc : 0 < c) (r : ℝ) :
    r * Real.exp (-c * r) ≤ 2 / (c * Real.exp 1) * Real.exp (-(c / 2) * r) := by
  have hcne : c ≠ 0 := hc.ne'
  have hene : Real.exp 1 ≠ 0 := (Real.exp_pos _).ne'
  have hv := mul_exp_neg_le (c / 2 * r)
  rw [show -(c / 2 * r) = -(c / 2) * r from by ring] at hv
  have hsplit : Real.exp (-c * r) = Real.exp (-(c / 2) * r) * Real.exp (-(c / 2) * r) := by
    rw [← Real.exp_add]; congr 1; ring
  have lhs_eq : r * Real.exp (-c * r)
      = 2 / c * (c / 2 * r * Real.exp (-(c / 2) * r)) * Real.exp (-(c / 2) * r) := by
    rw [hsplit]; field_simp
  have rhs_eq : 2 / c * Real.exp (-1) * Real.exp (-(c / 2) * r)
      = 2 / (c * Real.exp 1) * Real.exp (-(c / 2) * r) := by
    rw [Real.exp_neg]; field_simp
  calc r * Real.exp (-c * r)
      = 2 / c * (c / 2 * r * Real.exp (-(c / 2) * r)) * Real.exp (-(c / 2) * r) := lhs_eq
    _ ≤ 2 / c * Real.exp (-1) * Real.exp (-(c / 2) * r) := by gcongr
    _ = 2 / (c * Real.exp 1) * Real.exp (-(c / 2) * r) := rhs_eq

/-- **0th Gaussian moment**: the `n`-dim Gaussian `exp(−c‖z‖²)` is integrable for `c > 0`. -/
lemma integrable_exp_neg_mul_norm_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : ℝⁿ => Real.exp (-c * ‖z‖ ^ 2)) := by
  have hb : (0 : ℝ) < (Complex.ofReal c).re := by simpa using hc
  have hI := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℝⁿ) (b := (c : ℂ)) hb 0 0).norm
  refine hI.congr ?_
  filter_upwards with z
  have harg : (-(c : ℂ) * (↑‖z‖) ^ 2 + 0 * ↑(⟪(0 : ℝⁿ), z⟫_ℝ))
      = ((-c * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_zero_left]; push_cast; ring
  rw [harg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- **2nd Gaussian moment**: `‖z‖²·exp(−c‖z‖²)` is integrable over `ℝⁿ` for `c > 0`.
    Dominated by `(2/(c·e))·exp(−(c/2)‖z‖²)` via `sq_mul_exp_le`. -/
lemma integrable_norm_sq_mul_exp_neg_mul_norm_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : ℝⁿ => ‖z‖ ^ 2 * Real.exp (-c * ‖z‖ ^ 2)) := by
  have hc2 : (0 : ℝ) < c / 2 := by positivity
  have hbase := (integrable_exp_neg_mul_norm_sq (n := n) hc2).const_mul (2 / (c * Real.exp 1))
  refine Integrable.mono' hbase ?_ ?_
  · exact ((continuous_norm.pow 2).mul
      ((continuous_const.mul (continuous_norm.pow 2)).rexp)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sq_mul_exp_le hc (‖z‖ ^ 2)

/-- **1st Gaussian moment**: `‖z‖·exp(−c‖z‖²)` is integrable over `ℝⁿ` for `c > 0`.
    Dominated by `(1 + ‖z‖²)·exp(−c‖z‖²)` (since `‖z‖ ≤ 1 + ‖z‖²`), i.e. the 0th + 2nd moments. -/
lemma integrable_norm_mul_exp_neg_mul_norm_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : ℝⁿ => ‖z‖ * Real.exp (-c * ‖z‖ ^ 2)) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_norm_sq (n := n) hc).add
    (integrable_norm_sq_mul_exp_neg_mul_norm_sq (n := n) hc)) ?_ ?_
  · exact (continuous_norm.mul
      ((continuous_const.mul (continuous_norm.pow 2)).rexp)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hr : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    calc ‖z‖ * Real.exp (-c * ‖z‖ ^ 2)
        ≤ (1 + ‖z‖ ^ 2) * Real.exp (-c * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)
      _ = Real.exp (-c * ‖z‖ ^ 2) + ‖z‖ ^ 2 * Real.exp (-c * ‖z‖ ^ 2) := by ring

/-! ### General normed-space and second-derivative utilities

A handful of dimension- and field-agnostic helpers that arose while differentiating
convolutions under the integral sign, stated in full generality for reuse across chapters. -/

/-- **Quadratic triangle bound**: `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` in any real inner product space
    (from the parallelogram law `‖a+b‖² + ‖a−b‖² = 2‖a‖² + 2‖b‖²`). -/
lemma norm_add_sq_le_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_sq_real a b
  have h2 := norm_sub_sq_real a b
  nlinarith [h1, h2, sq_nonneg ‖a - b‖]

/-- **Scalar-multiplication operator-norm bound for continuous linear maps**:
    `‖c • L‖ ≤ ‖c‖·‖L‖`. Stated and proved directly via `opNorm_le_bound`, so it applies even
    to iterated CLM spaces `E →L[𝕜] (F →L[𝕜] G)` where Mathlib's `NormSMulClass` instance on the
    outer space is missing (a topology diamond); only the inner codomain `M` needs the instance. -/
lemma norm_smul_clm_le {𝕜 E M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    (c : 𝕜) (L : E →L[𝕜] M) : ‖c • L‖ ≤ ‖c‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_assoc]
  gcongr
  exact L.le_opNorm v

/-- **Operator-norm bound for post-composition with evaluation**: for a CLM-valued CLM
    `S : E →L[𝕜] (F →L[𝕜] G)` and `v : F`, evaluating the inner map at `v` has
    `‖(apply 𝕜 G v) ∘L S‖ ≤ ‖S‖·‖v‖`. Lands an iterated-CLM bound in single-CLM form. -/
lemma norm_comp_apply_le {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (v : F) (S : E →L[𝕜] F →L[𝕜] G) :
    ‖(ContinuousLinearMap.apply 𝕜 G v).comp S‖ ≤ ‖S‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  calc ‖(S w) v‖ ≤ ‖S w‖ * ‖v‖ := (S w).le_opNorm v
    _ ≤ ‖S‖ * ‖w‖ * ‖v‖ := by gcongr; exact S.le_opNorm w
    _ = ‖S‖ * ‖v‖ * ‖w‖ := by ring

/-- **Evaluation commutes with the second derivative**: if `z ↦ Dh z` is differentiable at `x`,
    then differentiating the directional map `z ↦ Dh z v` and the full second derivative agree,
    `D(z ↦ Dh z v) x w = D(Dh) x w v`. The "eval bridge" turning a second Fréchet derivative
    into nested scalar directional derivatives. -/
lemma fderiv_fderiv_apply {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : E → F) (x v w : E) (hd : DifferentiableAt 𝕜 (fderiv 𝕜 h) x) :
    fderiv 𝕜 (fun z => fderiv 𝕜 h z v) x w = fderiv 𝕜 (fderiv 𝕜 h) x w v := by
  have hcomp : HasFDerivAt (fun z => fderiv 𝕜 h z v)
      ((ContinuousLinearMap.apply 𝕜 F v).comp (fderiv 𝕜 (fderiv 𝕜 h) x)) x :=
    (ContinuousLinearMap.apply 𝕜 F v).hasFDerivAt.comp x hd.hasFDerivAt
  rw [hcomp.fderiv]; rfl

/-- **Laplacian under the integral sign**: for an integrand `K z y` whose convolution-type
    integral defines `F z = ∫ K z y dy`, if each diagonal second directional derivative already
    passes under the integral (`hper`) and the resulting integrands are integrable (`hint`), then
    so does the full Laplacian: `Δ(∫ K · y) x = ∫ (Δ K(·, y)) x`.

    This packages the dimension-dependent plumbing — write `Δ` as the trace `∑ᵢ (D²·)(eᵢ, eᵢ)`
    over the standard orthonormal basis, then swap the finite sum with the integral — leaving only
    the genuine differentiation-under-the-integral facts (`hper`, `hint`) to the caller. Reusable
    for any potential of convolution type (heat kernel, Newtonian potential, …). -/
lemma laplacian_integral_eq (K : ℝⁿ → ℝⁿ → ℝ) (x : ℝⁿ)
    (hper : ∀ i, iteratedFDeriv ℝ 2 (fun z => ∫ y, K z y) x
          ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i]
        = ∫ y, iteratedFDeriv ℝ 2 (fun z => K z y) x
          ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i])
    (hint : ∀ i, Integrable (fun y => iteratedFDeriv ℝ 2 (fun z => K z y) x
          ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i])) :
    Laplacian.laplacian (fun z => ∫ y, K z y) x
      = ∫ y, Laplacian.laplacian (fun z => K z y) x := by
  rw [congr_fun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun z => ∫ y, K z y)) x,
    Finset.sum_congr rfl (fun i _ => hper i), ← integral_finset_sum _ (fun i _ => hint i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact (congr_fun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun z => K z y)) x).symm

/-! ### Real inner product as a bilinear CLM

Mathlib's `innerSL ℝ` is a *conjugate*-linear bundled map (`ℝⁿ →L⋆[ℝ] ℝⁿ →L[ℝ] ℝ`); over `ℝ`
conjugation is trivial, but the conjugate-linear type gets in the way of `fderiv`/`HasFDerivAt`,
which want a genuine `ℝ`-linear map. `realInnerBiL` is the same underlying function retyped as an
honest bilinear `ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ`, so it can be differentiated directly. -/

/-- The real inner product as a bilinear CLM (avoids conjugate-linear ambiguity). -/
noncomputable def realInnerBiL : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ :=
  (innerSL ℝ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ)

/-- The real inner product with fixed left argument, as a CLM. -/
noncomputable def realInnerL (x : ℝⁿ) : ℝⁿ →L[ℝ] ℝ := realInnerBiL x

lemma realInnerL_apply (x y : ℝⁿ) : realInnerL x y = ⟪x, y⟫_ℝ :=
  congr_fun (coe_innerSL_apply ℝ x) y

/-- `innerSL ℝ w` and the genuinely `ℝ`-linear `realInnerBiL w` agree (both are `⟪w, ·⟫`). -/
lemma innerSL_eq_realInnerBiL (w : ℝⁿ) : innerSL ℝ w = realInnerBiL w := by
  ext v; rw [innerSL_apply_apply, ← realInnerL_apply]; rfl

/-- Operator norm of `realInnerBiL w` equals `‖w‖` (it is the functional `⟪w, ·⟫`). -/
lemma norm_realInnerBiL_apply (w : ℝⁿ) : ‖realInnerBiL w‖ = ‖w‖ := by
  rw [← innerSL_eq_realInnerBiL, innerSL_apply_norm]

/-! ### Radial power calculus

Fréchet derivative and Laplacian of `x ↦ ‖x‖ᵖ` away from the origin, for any real exponent `p`.
The Laplacian formula `Δ‖·‖ᵖ = p(n + p − 2)‖x‖ᵖ⁻² ` underlies the fundamental solutions of
Laplace's equation (`p = 2 − n`) and is reusable for any radial-potential computation. -/

/-- First Fréchet derivative of `‖·‖ᵖ` at `x ≠ 0` for any real exponent `p`. -/
lemma hasFDerivAt_norm_rpow_of_ne (x : ℝⁿ) (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun x : ℝⁿ => ‖x‖ ^ p)
      ((p * ‖x‖ ^ (p - 2)) • realInnerL x) x := by
  have heq : (p * ‖x‖ ^ (p - 2)) • realInnerL x =
      (p * ‖x‖ ^ (p - 2)) • (innerSL ℝ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ) x := rfl
  rw [heq]
  apply HasStrictFDerivAt.hasFDerivAt
  convert (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- **Laplacian of a radial power**: `Δ(‖·‖ᵖ)(x) = p · (n + p − 2) · ‖x‖ᵖ⁻²` for `x ≠ 0`. -/
lemma laplacian_norm_rpow_eq (p : ℝ) (x : ℝⁿ) (hx : x ≠ 0) :
    Laplacian.laplacian (fun x : ℝⁿ => ‖x‖ ^ p) x
      = p * ((n : ℝ) + p - 2) * ‖x‖ ^ (p - 2) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Laplacian.laplacian (fun y : ℝⁿ => ‖y‖ ^ p) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun y : ℝⁿ => ‖y‖ ^ p) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : ℝⁿ => ‖y‖ ^ p) e) x]
  simp_rw [iteratedFDeriv_two_apply]
  have hfderiv : ∀ᶠ y in nhds x,
      fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ p) y =
      (p * ‖y‖ ^ (p - 2)) • realInnerL y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hx)]
    intro y hy
    exact (hasFDerivAt_norm_rpow_of_ne y (Set.mem_compl_singleton_iff.mp hy) p).fderiv
  have hc := (hasFDerivAt_norm_rpow_of_ne x hx (p - 2)).const_mul p
  have hg : HasFDerivAt (fun y : ℝⁿ => realInnerL y) realInnerBiL x :=
    realInnerBiL.hasFDerivAt
  have hderiv2 : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ p)) x (e i) (e i) =
      p * (p - 2) * ‖x‖ ^ (p - 4) * ⟪x, e i⟫_ℝ ^ 2 +
      p * ‖x‖ ^ (p - 2) := by
    intro i
    have hfe : fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ p)) x =
        fderiv ℝ (fun y => (p * ‖y‖ ^ (p - 2)) • realInnerL y) x :=
      Filter.EventuallyEq.fderiv_eq hfderiv
    rw [hfe]
    have hcd : DifferentiableAt ℝ (fun y : ℝⁿ => p * ‖y‖ ^ (p - 2)) x :=
      hc.differentiableAt
    have hgd : DifferentiableAt ℝ (fun y : ℝⁿ => realInnerL y) x :=
      hg.differentiableAt
    have hconv : (fun y : ℝⁿ => (p * ‖y‖ ^ (p - 2)) • realInnerL y) =
        (fun y : ℝⁿ => p * ‖y‖ ^ (p - 2)) • (fun y : ℝⁿ => realInnerL y) := by
      funext y; rfl
    rw [show fderiv ℝ (fun y : ℝⁿ => (p * ‖y‖ ^ (p - 2)) • realInnerL y) x =
        fderiv ℝ ((fun y : ℝⁿ => p * ‖y‖ ^ (p - 2)) •
          fun y : ℝⁿ => realInnerL y) x from
      congr_arg (fderiv ℝ · x) hconv]
    rw [fderiv_smul hcd hgd]
    have hgfderiv : fderiv ℝ (fun y : ℝⁿ => realInnerL y) x = realInnerBiL :=
      hg.fderiv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.smulRight_apply, hc.fderiv, hgfderiv]
    have hei : realInnerBiL (e i) (e i) = 1 := by
      have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i i
      simp at h
      have heq : realInnerBiL (e i) (e i) = ⟪e i, e i⟫_ℝ :=
        realInnerL_apply (e i) (e i)
      rw [heq]
      simp only [e, EuclideanSpace.basisFun_apply]
      exact h
    have hxi : realInnerL x (e i) = ⟪x, e i⟫_ℝ :=
      realInnerL_apply x (e i)
    rw [hei, hxi]
    simp only [smul_eq_mul, mul_one]
    ring
  simp_rw [show ∀ i : Fin n, ![e i, e i] 0 = e i from fun i => rfl,
           show ∀ i : Fin n, ![e i, e i] 1 = e i from fun i => rfl]
  simp_rw [hderiv2]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hparseval := e.sum_sq_inner_left x
  have hcombine : ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 2) := by
    rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_add hxpos]; congr 1; ring
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  conv_lhs =>
    rw [show ∑ i : Fin n, ⟪x, e i⟫_ℝ ^ 2 = ‖x‖ ^ 2 from hparseval]
  conv_lhs =>
    rw [show p * (p - 2) * ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 =
        p * (p - 2) * ‖x‖ ^ (p - 2) from by
      rw [show p * (p - 2) * ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 =
          p * (p - 2) * (‖x‖ ^ (p - 4) * ‖x‖ ^ 2) from by ring]
      rw [hcombine]]
  ring

/-- **Laplacian of `‖·‖²`**: `Δ(‖·‖²) = 2n` everywhere on `ℝⁿ`. This is the canonical strictly
    subharmonic function (`Δ > 0` for `n ≥ 1`), the perturbation used to prove the maximum
    principle. Unlike `laplacian_norm_rpow_eq`, it holds at the origin too, since `‖·‖²` is
    smooth there (constant Hessian `2·Id`). -/
lemma laplacian_norm_sq (x : ℝⁿ) :
    Laplacian.laplacian (fun y : ℝⁿ => ‖y‖ ^ 2) x = 2 * (n : ℝ) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Laplacian.laplacian (fun y : ℝⁿ => ‖y‖ ^ 2) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun y : ℝⁿ => ‖y‖ ^ 2) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : ℝⁿ => ‖y‖ ^ 2) e) x]
  simp_rw [iteratedFDeriv_two_apply]
  have hfderiv : fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ 2) = fun y => (2 : ℕ) • realInnerL y := by
    funext y
    rw [(hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv, innerSL_eq_realInnerBiL]
    rfl
  have hsecond : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ 2)) x (e i) (e i) = 2 := by
    intro i
    rw [hfderiv]
    have hg : HasFDerivAt (fun y : ℝⁿ => (2 : ℕ) • realInnerL y) ((2 : ℕ) • realInnerBiL) x :=
      realInnerBiL.hasFDerivAt.const_smul (2 : ℕ)
    rw [hg.fderiv]
    have hei : realInnerBiL (e i) (e i) = 1 := by
      have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i i
      simp at h
      have heq : realInnerBiL (e i) (e i) = ⟪e i, e i⟫_ℝ := realInnerL_apply (e i) (e i)
      rw [heq]; simp only [e, EuclideanSpace.basisFun_apply]; exact h
    simp only [ContinuousLinearMap.smul_apply, hei, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  simp_rw [show ∀ i : Fin n, ![e i, e i] 0 = e i from fun i => rfl,
           show ∀ i : Fin n, ![e i, e i] 1 = e i from fun i => rfl]
  simp_rw [hsecond]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### Radial integrability on the unit ball

`n`-dimensional polar coordinates (`MeasureTheory.integrable_fun_norm_addHaar`) reduce the
integrability of a *radial* function `y ↦ f ‖y‖` over the unit ball to a one-dimensional
integral of `r ↦ r^{n-1} f r`. The power case `f r = r^p` is the workhorse of potential theory:
`‖·‖^p` is integrable near the origin in `ℝⁿ` exactly when `p > -n`. -/

/-- **Radial reduction for integrability on the unit ball** (`n ≥ 1`): a radial integrand
    `y ↦ f ‖y‖` is integrable on `B(0,1) ⊆ ℝⁿ` iff its one-dimensional radial profile
    `r ↦ r^{n-1} · f r` is integrable on `(0,1)`. -/
lemma integrableOn_unitBall_radial (hn : 1 ≤ n) (f : ℝ → ℝ) :
    IntegrableOn (fun y : ℝⁿ => f ‖y‖) (Metric.ball 0 1) ↔
      IntegrableOn (fun r => r ^ (n - 1) * f r) (Set.Ioo 0 1) := by
  haveI : Nontrivial ℝⁿ :=
    ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, by
      intro h
      have h0 : (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) : Fin n → ℝ) ⟨0, hn⟩ = 0 := by
        rw [← h]; simp
      simp at h0⟩
  rw [← integrable_indicator_iff measurableSet_ball]
  have hGball : (Metric.ball (0 : ℝⁿ) 1).indicator (fun y => f ‖y‖)
      = fun y => (Set.Iio (1 : ℝ)).indicator f ‖y‖ := by
    funext y
    by_cases hy : ‖y‖ < 1 <;>
      simp [Metric.mem_ball, dist_zero_right, Set.mem_Iio, hy]
  rw [hGball, integrable_fun_norm_addHaar (volume : Measure ℝⁿ), finrank_euclideanSpace_fin]
  have hk : (fun r : ℝ => r ^ (n - 1) • (Set.Iio (1 : ℝ)).indicator f r)
      = (Set.Iio (1 : ℝ)).indicator (fun r => r ^ (n - 1) * f r) := by
    funext r; simp only [smul_eq_mul, Set.indicator_apply]; split_ifs <;> ring
  rw [hk, integrableOn_indicator_iff measurableSet_Iio,
    show Set.Iio (1 : ℝ) ∩ Set.Ioi 0 = Set.Ioo 0 1 from by
      rw [Set.inter_comm]; exact Set.Ioi_inter_Iio]

/-- **`‖·‖^p` is integrable near the origin iff `p > -n`** (the easy, integrable direction):
    on `ℝⁿ` with `n ≥ 1`, `y ↦ ‖y‖^p` is integrable on `B(0,1)` whenever `p > -n`. This is the
    standard local-integrability fact for Riesz/Newtonian-type kernels (e.g. `p = 2 - n`). -/
lemma integrableOn_norm_rpow_unitBall (hn : 1 ≤ n) {p : ℝ} (hp : -(n : ℝ) < p) :
    IntegrableOn (fun y : ℝⁿ => ‖y‖ ^ p) (Metric.ball 0 1) := by
  refine (integrableOn_unitBall_radial hn (f := fun t => t ^ p)).mpr ?_
  have hs : (-1 : ℝ) < (n : ℝ) - 1 + p := by linarith
  refine MeasureTheory.IntegrableOn.congr_fun
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := (n : ℝ) - 1 + p) one_pos).mpr hs)
    ?_ measurableSet_Ioo
  intro r hr
  have hr0 : (0 : ℝ) < r := hr.1
  change r ^ ((n : ℝ) - 1 + p) = r ^ (n - 1) * r ^ p
  rw [← Real.rpow_natCast r (n - 1), ← Real.rpow_add hr0, Nat.cast_sub hn, Nat.cast_one]

/-! ### Second-derivative sign at a local maximum (maximum-principle foundations)

The analytic heart of the maximum principle for harmonic (more generally, subharmonic)
functions: at an interior local maximum of a `C²` function the second derivative is `≤ 0` in
every direction, so the Laplacian (its trace over an orthonormal basis) is `≤ 0`. -/

/-- **1-D second-derivative test at a local maximum**: if `g : ℝ → ℝ` has a local maximum at `t`
    and is continuous there, then `g''(t) ≤ 0`. (Mathlib has the converse `isLocalMax_of_…`; this
    is the forward sign, proved by contradiction with the minimum second-derivative test.) -/
lemma deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {t : ℝ}
    (hmax : IsLocalMax g t) (hc : ContinuousAt g t) : deriv (deriv g) t ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have hmin : IsLocalMin g t := isLocalMin_of_deriv_deriv_pos hlt hmax.deriv_eq_zero hc
  have hconst : g =ᶠ[nhds t] fun _ => g t := by
    filter_upwards [hmax, hmin] with x hx1 hx2 using le_antisymm hx1 hx2
  have hd1 : deriv g =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.deriv] with x hx; rw [hx]; simp
  have hzero : deriv (deriv g) t = 0 := by rw [hd1.deriv_eq]; simp
  linarith

/-- **The Laplacian is `≤ 0` at an interior local maximum** of a `C²` function (the analytic
    core of the maximum principle for harmonic/subharmonic functions). For each basis vector
    `eᵢ` the slice `s ↦ f(x + s·eᵢ)` has a local maximum at `0`, so its second derivative
    `D²f(x)(eᵢ, eᵢ) ≤ 0`; summing over the standard orthonormal basis gives `Δf x ≤ 0`. -/
lemma laplacian_nonpos_of_isLocalMax {f : ℝⁿ → ℝ} {x : ℝⁿ}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) :
    Laplacian.laplacian f x ≤ 0 := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  rw [congr_fun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) x]
  refine Finset.sum_nonpos fun i _ => ?_
  set v : ℝⁿ := stdOrthonormalBasis ℝ ℝⁿ i with hv_def
  set L : ℝ → ℝⁿ := fun s => x + s • v with hL_def
  set g : ℝ → ℝ := fun s => f (L s) with hg_def
  have hL0 : L 0 = x := by simp [hL_def]
  have hLcont : Continuous L := by fun_prop
  have hLtend : Filter.Tendsto L (nhds 0) (nhds x) := hL0 ▸ hLcont.tendsto 0
  have hLderiv : ∀ s, HasDerivAt L v s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s • v) v s := by
      simpa using (hasDerivAt_id s).smul_const v
    exact h1.const_add x
  -- `deriv g` near `0` is `s ↦ Df(L s) v` (chain rule on the differentiable patch of `f`).
  have hgderiv : ∀ᶠ s in nhds (0 : ℝ), HasDerivAt g (fderiv ℝ f (L s) v) s := by
    filter_upwards [hLtend.eventually hfev] with s hs
    exact hs.hasFDerivAt.comp_hasDerivAt s (hLderiv s)
  have hderivg : deriv g =ᶠ[nhds 0] fun s => fderiv ℝ f (L s) v := by
    filter_upwards [hgderiv] with s hs using hs.deriv
  -- the second derivative of the slice is `D²f(x)(v, v)`.
  have hM : HasDerivAt (fun s => fderiv ℝ f (L s) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hl : HasFDerivAt (fun z => fderiv ℝ f z v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x)) (L 0) := by
      rw [hL0]; exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hdf.hasFDerivAt
    have hcomp := (hl.comp 0 (hLderiv 0).hasFDerivAt).hasDerivAt
    simpa [Function.comp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.smulRight_apply] using hcomp
  have hddg : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [hderivg.deriv_eq]; exact hM.deriv
  have hiter : iteratedFDeriv ℝ 2 f x ![v, v] = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [iteratedFDeriv_two_apply]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hiter, ← hddg]
  refine deriv_deriv_nonpos_of_isLocalMax ?_ ?_
  · filter_upwards [hLtend.eventually hmax] with s hs
    show g s ≤ g 0
    rw [show g 0 = f x by simp [hg_def, hL0]]; exact hs
  · exact hf.continuousAt.comp_of_eq hLcont.continuousAt hL0
