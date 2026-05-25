import MyProject.Calculus

open MeasureTheory InnerProductSpace

/-!
# Transport Equation (Evans PDE, §2.1)

Formalizing the initial value problem for the homogeneous transport equation:

  (IVP)  u_t + b · Du = 0   in ℝⁿ × (0, ∞)
         u = g               on ℝⁿ × {t = 0}

The key insight: along any characteristic line `z(s) = (x + sb, t + s)`,
  d/ds [u(z(s))] = b · Du + u_t = 0
so `u` is constant on characteristics. Tracing back to `t = 0` gives u(x, t) = g(x − tb).

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §2.1.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### The PDE -/

/-- `u` satisfies the homogeneous transport equation `u_t + b · Du = 0` at every
    spacetime point, where `u_t` is `timeDerivative` and `b · Du = ⟪Du, b⟫` uses
    `spatialGradient`. -/
def IsTransportSolution (b : ℝⁿ) (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, timeDerivative u p + ⟪spatialGradient u p, b⟫_ℝ = 0

/-! ### Characteristics -/

/-- The characteristic flow: the linear map `(x, t) ↦ x − t · b`.
    Characteristics of the equation are lines parallel to `(b, 1)` in `ℝⁿ⁺¹`. -/
noncomputable def charFlow (b : ℝⁿ) : ℝⁿ × ℝ →L[ℝ] ℝⁿ :=
  ContinuousLinearMap.fst ℝ ℝⁿ ℝ -
  (ContinuousLinearMap.snd ℝ ℝⁿ ℝ).smulRight b

@[simp]
lemma charFlow_apply (b x : ℝⁿ) (t : ℝ) : charFlow b (x, t) = x - t • b := by
  simp [charFlow]

/-- The characteristic direction `(b, 1)` is in the kernel of `charFlow b`. -/
lemma charFlow_direction_zero (b : ℝⁿ) : charFlow b (b, (1 : ℝ)) = 0 := by simp

/-! ### Solution Formula -/

/-- Evans' solution: `u(x, t) = g(x − tb)`, i.e., `g` at the foot of the characteristic. -/
noncomputable def evansFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) : ℝⁿ × ℝ → ℝ :=
  g ∘ charFlow b

@[simp]
lemma evansFormula_apply (b : ℝⁿ) (g : ℝⁿ → ℝ) (x : ℝⁿ) (t : ℝ) :
    evansFormula b g (x, t) = g (x - t • b) := by simp [evansFormula]

/-! ### Main Theorems -/

/-- **Initial condition**: `u(x, 0) = g(x)`. -/
theorem evansFormula_initial (b : ℝⁿ) (g : ℝⁿ → ℝ) (x : ℝⁿ) :
    evansFormula b g (x, 0) = g x := by simp

/-- Regularity: `evansFormula b g` is differentiable whenever `g` is. -/
theorem evansFormula_differentiable (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g) :
    Differentiable ℝ (evansFormula b g) :=
  hg.comp (charFlow b).differentiable

/-- The spatial gradient of `evansFormula b g` at `p` equals the gradient of `g`
    pulled back to the foot of the characteristic.
    Proof: `x ↦ x − t·b` is a translation with derivative `id`, so by the chain rule
    for gradients, `∇_x[g(x−tb)] = ∇g(x−tb)`. -/
lemma spatialGradient_evansFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g)
    (p : ℝⁿ × ℝ) :
    spatialGradient (evansFormula b g) p = gradient g (charFlow b p) := by
  simp only [spatialGradient, evansFormula, Function.comp, charFlow_apply]
  sorry

/-- The time derivative of `evansFormula b g` at `p` equals `−⟪∇g(x−tb), b⟫`.
    Proof: by the chain rule, `∂_t[g(x−tb)] = ∇g(x−tb) · (−b) = −⟪∇g(x−tb), b⟫`. -/
lemma timeDerivative_evansFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g)
    (p : ℝⁿ × ℝ) :
    timeDerivative (evansFormula b g) p = -⟪gradient g (charFlow b p), b⟫_ℝ := by
  simp only [timeDerivative, evansFormula, Function.comp, charFlow_apply]
  sorry

/-- **Evans §2.1.1, Theorem 1**: `u(x, t) = g(x − tb)` solves the transport equation.

    **Proof**: The spatial gradient pulls back to `∇g(x−tb)` and the time derivative
    equals `−⟪∇g(x−tb), b⟫`, so their sum vanishes. -/
theorem evansFormula_solves_transport (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g) :
    IsTransportSolution b (evansFormula b g) := by
  intro p
  rw [timeDerivative_evansFormula b g hg p, spatialGradient_evansFormula b g hg p]
  simp [real_inner_comm]

/-! ## §2.1.2 Inhomogeneous Transport Equation -/

/-- `u` satisfies the inhomogeneous transport equation `u_t + b · Du = f`. -/
def IsInhomTransportSolution (b : ℝⁿ) (f : ℝⁿ × ℝ → ℝ) (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, timeDerivative u p + ⟪spatialGradient u p, b⟫_ℝ = f p

/-- Duhamel's formula: `u(x,t) = g(x−tb) + ∫₀ᵗ f(x−(t−s)b, s) ds`.
    The first term solves the homogeneous equation; the integral corrects for the source `f`. -/
noncomputable def duhamelFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) (f : ℝⁿ × ℝ → ℝ) :
    ℝⁿ × ℝ → ℝ :=
  fun p => g (p.1 - p.2 • b) + ∫ s in (0 : ℝ)..p.2, f (p.1 - (p.2 - s) • b, s)

/-- **Initial condition**: `u(x, 0) = g(x)`. The Duhamel integral vanishes at `t = 0`. -/
theorem duhamelFormula_initial (b : ℝⁿ) (g : ℝⁿ → ℝ) (f : ℝⁿ × ℝ → ℝ) (x : ℝⁿ) :
    duhamelFormula b g f (x, 0) = g x := by
  simp [duhamelFormula, intervalIntegral.integral_same]

/-- **Evans §2.1.2, Theorem 2**: Duhamel's formula solves the inhomogeneous transport equation.

    **Proof sketch**: Split `u = v + w` where `v(x,t) = g(x−tb)` and
    `w(x,t) = ∫₀ᵗ f(x−(t−s)b, s) ds`. We know `v_t + b·Dv = 0`. For `w`, the
    Leibniz rule gives `w_t = f(x,t) + ∫₀ᵗ ∂_t[f(x−(t−s)b,s)] ds` (FTC boundary term)
    and `b·Dw = ∫₀ᵗ b·∇f(x−(t−s)b,s) ds`. Since `∂_t[f(x−(t−s)b,s)] = −b·∇f(x−(t−s)b,s)`,
    the two integrals cancel and `w_t + b·Dw = f(x,t)`. -/
theorem duhamelFormula_solves (b : ℝⁿ) (g : ℝⁿ → ℝ) (f : ℝⁿ × ℝ → ℝ)
    (hg : Differentiable ℝ g) (hf : ContDiff ℝ 1 f) :
    IsInhomTransportSolution b f (duhamelFormula b g f) := by
  sorry

/-! ### Uniqueness via Characteristics (TODO)

The idea: if `u` is C¹, solves the IVP, and `v = evansFormula b g`, then
  `w := u − v` solves the transport equation with zero initial data.
  For any fixed `(x, t)`, define `z(s) = w(x + sb, t + s)`.
  Then `z'(s) = timeDerivative w (x+sb, t+s) + ⟪spatialGradient w (x+sb, t+s), b⟫ = 0`,
  so `z` is constant. `z(0) = w(x, t)` and `z(−t) = w(x − tb, 0) = 0`, giving `w ≡ 0`. -/

theorem evansFormula_unique (b : ℝⁿ) (g : ℝⁿ → ℝ)
    (u : ℝⁿ × ℝ → ℝ)
    (hu_pde : IsTransportSolution b u)
    (hu_init : ∀ x : ℝⁿ, u (x, 0) = g x)
    (hu_diff : Differentiable ℝ u) :
    u = evansFormula b g := by
  sorry
