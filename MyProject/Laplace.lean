import MyProject.Calculus

open MeasureTheory InnerProductSpace Set

/-!
# Laplace and Poisson Equations (Evans PDE, §2.2)

Formalizing classical solutions to:

  (Laplace)  −Δu = 0   in U ⊆ ℝⁿ
  (Poisson)  −Δu = f   in U ⊆ ℝⁿ

Key results:
* Fundamental solution `Φ(x)` — the "building block" for solving Poisson's equation
* Representation formula: `u(x) = ∫ Φ(x−y) f(y) dy` (Newtonian potential)
* Mean value property: harmonic ↔ `u(x) = avgᵣ u` on spheres/balls
* Maximum principle: harmonic functions attain max/min on the boundary

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §2.2.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### The PDEs -/

/-- `u` is harmonic on the open set `U`: `Δu = 0` in `U` pointwise. -/
def IsHarmonic (U : Set ℝⁿ) (u : ℝⁿ → ℝ) : Prop :=
  ∀ x ∈ U, laplacian u x = 0

/-- `u` solves Poisson's equation `−Δu = f` on `U`. -/
def IsPoissonSolution (U : Set ℝⁿ) (f : ℝⁿ → ℝ) (u : ℝⁿ → ℝ) : Prop :=
  ∀ x ∈ U, -laplacian u x = f x

/-- Laplace's equation is Poisson's equation with `f = 0`. -/
lemma isHarmonic_iff_isPoissonSolution_zero (U : Set ℝⁿ) (u : ℝⁿ → ℝ) :
    IsHarmonic U u ↔ IsPoissonSolution U 0 u := by
  simp [IsHarmonic, IsPoissonSolution, neg_eq_zero]

/-! ### Fundamental Solution -/

/-- Volume of the unit ball in `ℝⁿ`, used in the normalization of `fundamentalSolution`. -/
noncomputable def unitBallVol (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- The fundamental solution of the Laplacian (Evans §2.2.1).

    For `n ≥ 3`: `Φ(x) = 1 / (n(n−2)ωₙ) · |x|^(2−n)`
    For `n = 2`: `Φ(x) = −1/(2π) · log |x|`
    where `ωₙ = unitBallVol` is the volume of the unit ball in `ℝⁿ`.

    `Φ` is defined for `x ≠ 0` and satisfies `−ΔΦ = δ₀` in the distributional sense. -/
noncomputable def fundamentalSolution : ℝⁿ → ℝ :=
  fun x =>
    if n = 0 then 0
    else if n = 1 then (1 / 2 : ℝ) * ‖x‖
    else if n = 2 then -(1 / (2 * Real.pi)) * Real.log ‖x‖
    else
      let d : ℝ := (n : ℝ)
      let ω : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
      (1 / (d * (d - 2) * ω)) * ‖x‖ ^ (2 - d)

/-! ### Newtonian Potential -/

/-- The Newtonian potential: `u(x) = ∫ Φ(x − y) f(y) dy`.
    This is the convolution of the fundamental solution with the source `f`. -/
noncomputable def newtonianPotential (f : ℝⁿ → ℝ) : ℝⁿ → ℝ :=
  fun x => ∫ y, fundamentalSolution (x - y) * f y

/-! ### Mean Value Property -/

/-- The mean value on the sphere `∂B(x, r)` using the `(n−1)`-dimensional Hausdorff measure,
    i.e., the surface area measure on `∂B(x, r)`. -/
noncomputable def sphereMean (u : ℝⁿ → ℝ) (x : ℝⁿ) (r : ℝ) : ℝ :=
  ⨍ y in Metric.sphere x r, u y ∂(Measure.hausdorffMeasure ((n : ℝ) - 1))

/-- The mean value on the ball `B(x, r)` using the Lebesgue measure. -/
noncomputable def ballMean (u : ℝⁿ → ℝ) (x : ℝⁿ) (r : ℝ) : ℝ :=
  ⨍ y in Metric.ball x r, u y

/-- **Mean Value Property (sphere version)** (Evans §2.2.2, Theorem 2):
    If `u` is harmonic in `U`, then for every ball `B(x,r) ⊂⊂ U`,
    `u(x) = 1/(nωₙ rⁿ⁻¹) ∫_{∂B(x,r)} u dS = sphereMean u x r`.

    **Proof sketch**: Apply Green's identity to `u` and `Φ(· − x)` on the region
    `B(x,r) \ B(x,ε)`, then let `ε → 0`. The boundary term on `∂B(x,ε)` converges
    to `u(x)` by continuity. -/
theorem harmonic_sphereMeanValue (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = sphereMean u x r := by
  sorry

/-- **Mean Value Property (ball version)** (Evans §2.2.2, Theorem 2):
    `u(x) = 1/(ωₙ rⁿ) ∫_{B(x,r)} u dy = ballMean u x r`. -/
theorem harmonic_ballMeanValue (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = ballMean u x r := by
  sorry

/-- **Converse**: If `u ∈ C²(U)` satisfies the mean value property on balls, it is harmonic.
    (Evans §2.2.2, Theorem 2, converse direction.) -/
theorem meanValue_implies_harmonic (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu_c2 : ContDiff ℝ 2 u)
    (hmv : ∀ x ∈ U, ∀ r > 0, Metric.closedBall x r ⊆ U → u x = ballMean u x r) :
    IsHarmonic U u := by
  sorry

/-! ### Maximum Principle -/

/-- **Strong Maximum Principle** (Evans §2.2.3, Theorem 4):
    A harmonic function on a connected open set `U` that attains its maximum
    in the interior is constant.

    **Proof**: If `u(x₀) = max`, then `u = u(x₀)` on `B(x₀, r)` by the mean value
    property; the set where `u` achieves its max is open and closed in `U`. -/
theorem harmonic_strongMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hconn : IsConnected U)
    (hu : IsHarmonic U u) (hu_c : Continuous u)
    (x₀ : ℝⁿ) (hx₀ : x₀ ∈ U)
    (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  sorry

/-- **Weak Maximum Principle** (Evans §2.2.3, Theorem 3):
    On a bounded open set `U`, a harmonic function achieves its maximum on `∂U`.
    Equivalently, `max_{Ū} u = max_{∂U} u`. -/
theorem harmonic_weakMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hbdd : Bornology.IsBounded U)
    (hu : IsHarmonic U u) (hu_c : ContinuousOn u (closure U)) :
    ∀ x ∈ U, u x ≤ sSup (u '' frontier U) := by
  sorry

/-! ### Smoothness of Harmonic Functions -/

/-- **Regularity** (Evans §2.2.3, Theorem 6):
    Harmonic functions are `C∞` on `U`: if `u ∈ C²(U)` is harmonic, then `u ∈ C∞(U)`.

    **Proof**: Convolve with a radial mollifier; harmonic + mean value property
    gives `u * η_ε = u` on `U`, so `u` inherits the smoothness of `η_ε`. -/
theorem harmonic_smooth (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ ⊤ u U := by
  sorry

/-! ### Representation Formula for Poisson's Equation -/

/-- **Representation Formula** (Evans §2.2.4, Theorem 9):
    If `f ∈ Cc²(ℝⁿ)` (compactly supported `C²`), then
    `u(x) = ∫ Φ(x−y) f(y) dy` solves `−Δu = f` in `ℝⁿ`.

    **Proof sketch**:
    1. Differentiate under the integral: `−Δu(x) = ∫ (−Δ_x Φ)(x−y) f(y) dy`
       (handled by separating off the singularity on `B(x,ε)`).
    2. Green's identity on `B(x,ε)ᶜ`: bulk term vanishes since `−ΔΦ = 0` off `0`.
    3. Boundary term on `∂B(x,ε)`: as `ε → 0`, converges to `f(x)`. -/
theorem newtonianPotential_solves_poisson (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) :
    IsPoissonSolution Set.univ f (newtonianPotential f) := by
  sorry
