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
