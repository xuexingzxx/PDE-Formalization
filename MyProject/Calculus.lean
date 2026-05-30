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

/-- The Fréchet derivative of `u` at `(x,t)` in the characteristic direction `(b,1)`
    equals the sum of the spatial inner product and the time derivative. -/
lemma fderiv_transport_dir (u : ℝⁿ × ℝ → ℝ) (x : ℝⁿ) (t : ℝ) (b : ℝⁿ)
    (hu : DifferentiableAt ℝ u (x, t)) :
    fderiv ℝ u (x, t) (b, (1 : ℝ)) =
    ⟪spatialGradient u (x, t), b⟫_ℝ + timeDerivative u (x, t) := by
  simp only [spatialGradient, timeDerivative]
  have hx : HasFDerivAt (fun x => u (x, t))
      (fderiv ℝ u (x, t) ∘L ContinuousLinearMap.inl ℝ ℝⁿ ℝ) x :=
    hu.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)
  have ht : HasDerivAt (fun t => u (x, t))
      (fderiv ℝ u (x, t) (0, 1)) t :=
    hu.hasFDerivAt.comp_hasDerivAt t (hasFDerivAt_prodMk_right x t).hasDerivAt
  have hsplit : fderiv ℝ u (x, t) (b, (1:ℝ)) =
      fderiv ℝ u (x, t) (b, 0) + fderiv ℝ u (x, t) (0, 1) := by
    rw [← map_add]; congr 1; simp
  have hspace : fderiv ℝ u (x, t) (b, 0) = ⟪gradient (fun x => u (x, t)) x, b⟫_ℝ := by
    rw [inner_gradient_left hx.differentiableAt, hx.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have htime : fderiv ℝ u (x, t) (0, 1) = deriv (fun t => u (x, t)) t :=
    ht.deriv.symm
  rw [hsplit, hspace, htime]


/-- Leibniz rule for integrals with parameter-dependent integrand and upper limit.
    d/dt ∫₀ᵗ H(t,s) ds = H(t,t) + ∫₀ᵗ ∂_t H(t,s) ds
    Proof: combine FTC (integral_hasDerivAt_right) with differentiation under
    integral sign (hasDerivAt_integral_of_dominated_loc_of_lip).
    Blocked: Mathlib has these separately but no combined version. -/
lemma leibniz_integral {H : ℝ → ℝ → ℝ} {H' : ℝ → ℝ} {t : ℝ}
    (hH_cont : Continuous (fun p : ℝ × ℝ => H p.1 p.2))
    (hH'_cont : Continuous (fun p : ℝ × ℝ => H' p.2))
    (hH_diff : ∀ s : ℝ, HasDerivAt (fun t => H t s) (H' s) t)
    (hH_int : ∀ t₀ : ℝ, IntervalIntegrable (fun s => H t₀ s) MeasureTheory.volume 0 t₀) :
    HasDerivAt (fun t => ∫ s in (0:ℝ)..t, H t s)
      (H t t + ∫ s in (0:ℝ)..t, H' s) t := by
  sorry
