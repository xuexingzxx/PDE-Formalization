import Mathlib

open MeasureTheory

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

/-- `u` satisfies the homogeneous transport equation `u_t + b · Du = 0` if the
    Fréchet derivative at every spacetime point vanishes in the characteristic direction.
    By linearity: `fderiv ℝ u p (b, 1) = (b · Du)(p) + u_t(p)`. -/
def IsTransportSolution (b : ℝⁿ) (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, fderiv ℝ u p (b, 1) = 0

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

/-- **Evans §2.1.1, Theorem 1**: `u(x, t) = g(x − tb)` solves the transport equation.

    **Proof**: By the chain rule,
      `fderiv(u) p = fderiv(g)(charFlow b p) ∘L charFlow b`
    Applied to the characteristic direction `(b, 1)`:
      `charFlow b (b, 1) = b − 1·b = 0`
    so the composition sends `(b, 1)` to `fderiv(g)(·)(0) = 0`. -/
theorem evansFormula_solves_transport (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g) :
    IsTransportSolution b (evansFormula b g) := by
  intro p
  have hchain : HasFDerivAt (evansFormula b g)
      (fderiv ℝ g (charFlow b p) ∘L charFlow b) p :=
    (hg (charFlow b p)).hasFDerivAt.comp p (charFlow b).hasFDerivAt
  rw [hchain.fderiv, ContinuousLinearMap.comp_apply, charFlow_direction_zero, map_zero]

/-! ### Uniqueness via Characteristics (TODO)

The idea: if `u` is C¹, solves the IVP, and `v = evansFormula b g`, then
  `w := u − v` solves the transport equation with zero initial data.
  For any fixed `(x, t)`, define `z(s) = w(x + sb, t + s)`.
  Then `z'(s) = fderiv ℝ w (x + sb, t + s) (b, 1) = 0`, so `z` is constant.
  `z(0) = w(x, t)` and `z(−t) = w(x − tb, 0) = 0`, giving `w ≡ 0`. -/

theorem evansFormula_unique (b : ℝⁿ) (g : ℝⁿ → ℝ)
    (u : ℝⁿ × ℝ → ℝ)
    (hu_pde : IsTransportSolution b u)
    (hu_init : ∀ x : ℝⁿ, u (x, 0) = g x)
    (hu_diff : Differentiable ℝ u) :
    u = evansFormula b g := by
  sorry
