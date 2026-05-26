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

/-! #### Intermediate Lemmas (Evans §2.2.4 proof steps) -/

/-- `fundamentalSolution` is smooth on `ℝⁿ \ {0}`.
    For `n ≥ 3`, `Φ(x) = c · ‖x‖^(2−n)` is a composition of smooth functions away from 0.
    For `n = 2`, `Φ(x) = c · log ‖x‖` is smooth away from 0. -/
lemma fundamentalSolution_contDiff_off_zero :
    ContDiffOn ℝ ⊤ (fundamentalSolution (n := n)) ({0} : Set ℝⁿ)ᶜ := by
  -- ‖·‖ is C∞ on {0}ᶜ: it's smooth at every nonzero point
  have hn_smooth : ContDiffOn ℝ ⊤ (fun x : ℝⁿ => ‖x‖) ({0} : Set ℝⁿ)ᶜ :=
    fun x hx => (contDiffAt_norm ℝ (Set.mem_compl_singleton_iff.mp hx)).contDiffWithinAt
  -- ‖x‖ ≠ 0 for x ≠ 0
  have hn_ne : ∀ x ∈ ({0} : Set ℝⁿ)ᶜ, ‖x‖ ≠ 0 :=
    fun x hx => (norm_pos_iff.mpr (Set.mem_compl_singleton_iff.mp hx)).ne'
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · -- n = 0: fundamentalSolution is the constant 0
      have heq : fundamentalSolution (n := 0) =
          fun (_ : EuclideanSpace ℝ (Fin 0)) => (0 : ℝ) := by
        funext; simp [fundamentalSolution]
      rw [heq]; exact contDiffOn_const
    · -- n = 1: fundamentalSolution x = (1/2) * ‖x‖, smooth on {0}ᶜ
      have heq : fundamentalSolution (n := 1) =
          fun x : EuclideanSpace ℝ (Fin 1) => (1 / 2 : ℝ) * ‖x‖ := by
        funext; simp [fundamentalSolution]
      rw [heq]; exact contDiffOn_const.mul hn_smooth
    · -- n = 2: fundamentalSolution x = -(1/(2π)) * log ‖x‖
      have heq : fundamentalSolution (n := 2) =
          fun x : EuclideanSpace ℝ (Fin 2) =>
            -(1 / (2 * Real.pi)) * Real.log ‖x‖ := by
        funext; simp [fundamentalSolution]
      rw [heq]
      -- log ‖·‖ is C∞ on {0}ᶜ since ‖x‖ > 0 and log is C∞ on (0,∞)
      exact contDiffOn_const.mul (hn_smooth.log hn_ne)
  · -- n ≥ 3: fundamentalSolution x = c * ‖x‖^(2-n)
    -- where c = 1 / (n(n-2) * vol(B¹ₙ))
    have heq : fundamentalSolution (n := n) = fun x : ℝⁿ =>
        (1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)) *
        ‖x‖ ^ (2 - (n : ℝ)) := by
      funext x
      simp only [fundamentalSolution, if_neg (show n ≠ 0 from by omega),
        if_neg (show n ≠ 1 from by omega), if_neg (show n ≠ 2 from by omega)]
    rw [heq]
    -- ‖x‖^(2-n) is C∞ on {0}ᶜ since ‖x‖ ≠ 0 there
    exact contDiffOn_const.mul (hn_smooth.rpow_const_of_ne hn_ne)

/-- **Key Lemma**: `fundamentalSolution` is harmonic on `ℝⁿ \ {0}`:
    `Δ(Φ)(x) = 0` for all `x ≠ 0`.

    **Proof**: Direct computation using `Φ(x) = c · ‖x‖^(2−n)` for `n ≥ 3`.
    In polar coordinates `r = ‖x‖`, the Laplacian is
    `Δ = ∂²/∂r² + (n−1)/r · ∂/∂r`, and one checks
    `Δ(r^(2−n)) = (2−n)(1−n)r^(−n) + (n−1)(2−n)r^(−n) = 0`. -/
lemma fundamentalSolution_harmonic_off_zero (x : ℝⁿ) (hx : x ≠ 0) :
    laplacian fundamentalSolution x = 0 := by
  sorry

/-- The near-singularity integral is small:
    `∫_{B(x,ε)} |Φ(x−y)| dy → 0` as `ε → 0`.
    Since `Φ(z) ~ ‖z‖^(2−n)` and the integrand is in L¹ near 0 for `n ≥ 3`,
    the integral over the shrinking ball vanishes. -/
lemma fundamentalSolution_near_integral_tendsto_zero (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  sorry

/-- **Green's second identity** on an annular domain `B(x,r) \ B(x,ε)`:
    For smooth `u`, `v` on `ℝⁿ`:
    `∫_{B(x,r)\B(x,ε)} (v·Δu − u·Δv) dy`
    `= ∫_{∂B(x,r)} (v·∂_ν u − u·∂_ν v) dS − ∫_{∂B(x,ε)} (v·∂_ν u − u·∂_ν v) dS`.

    **Proof**: Stokes' theorem applied to the 1-form `v·∇u − u·∇v`.
    Mathlib's divergence theorem covers rectangular boxes; the spherical case
    requires an approximation argument or a Stokes theorem for smooth manifolds. -/
lemma green_identity_annulus (u v : ℝⁿ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : ℝⁿ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ∫ y in Metric.ball x r \ Metric.ball x ε, (v y * laplacian u y - u y * laplacian v y)
    = (∫ y in Metric.sphere x r,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)))
    - (∫ y in Metric.sphere x ε,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1))) := by
  sorry

/-- The total outward normal flux of `∇Φ` through any sphere `∂B(x, ε)` equals `−1`.
    More precisely: `∫_{∂B(0,ε)} (∂/∂r) Φ(y) dS = −1`.

    **Proof**: For `n ≥ 3`, `Φ(x) = c ‖x‖^(2−n)` gives
    `∂_ν Φ = (2−n) c ‖x‖^(1−n)` on `∂B(0,ε)`.
    Surface area of `∂B(0,ε)` is `n · ωₙ · εⁿ⁻¹`.
    Total flux = `(2−n) c (n ωₙ) ε^(1−n) · ε^(n-1) = (2−n) · c · n · ωₙ = −1`
    by the choice `c = 1/(n(n−2)ωₙ)`. -/
lemma fundamentalSolution_totalFlux (ε : ℝ) (hε : 0 < ε) :
    ∫ y in Metric.sphere (0 : ℝⁿ) ε,
      ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ
      ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)) = -1 := by
  sorry

/-- The boundary integral on `∂B(x,ε)` from Green's identity converges to `f(x)`:
    `∫_{∂B(x,ε)} [Φ(y−x) ∂_ν f(y) − f(y) ∂_ν Φ(y−x)] dS → f(x)` as `ε → 0`.

    **Proof**:
    * `Φ` term: `|Φ(y−x)| ~ ε^(2−n)` and surface area `~ ε^(n−1)`, so this → 0.
    * `∂_ν Φ` term: `∂_ν Φ(y−x) = −1/(n ωₙ εⁿ⁻¹)` on `∂B(x,ε)`, so
      `∫_{∂B(x,ε)} f(y) ∂_ν Φ(y−x) dS = −f(x) + o(1)` by continuity of `f`. -/
lemma green_boundary_tendsto_f (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f x)) := by
  sorry

/-- **Representation Formula** (Evans §2.2.4, Theorem 9):
    If `f ∈ Cc²(ℝⁿ)`, then `u(x) = ∫ Φ(x−y) f(y) dy` solves `−Δu = f` in `ℝⁿ`.

    **Proof** (Evans §2.2.4):
    Fix `x ∈ ℝⁿ` and `ε > 0`. Write `u = u₁ + u₂` where:
    * `u₁(x) = ∫_{B(x,ε)} Φ(x−y) f(y) dy` — near-singularity part, → 0 as ε → 0.
    * `u₂(x) = ∫_{B(x,ε)ᶜ} Φ(x−y) f(y) dy` — regular part.

    For `u₂`, differentiate twice under the integral (Φ is smooth on `B(x,ε)ᶜ`):
    `−Δ_x u₂ = ∫_{B(x,ε)ᶜ} (−Δ_x Φ)(x−y) f(y) dy = 0`
    since `−ΔΦ = 0` off 0 (`fundamentalSolution_harmonic_off_zero`).

    Apply Green's second identity (`green_identity_annulus`) to `u₂` and `v = Φ(·−x)` on
    the annulus `B(x,R) \ B(x,ε)` where `R > supp(f)`:
    the outer boundary term vanishes (f has compact support), leaving
    `0 = ∫_{B(x,R)\B(x,ε)} Φ(x−y)(−Δf)(y) dy + boundary integral on ∂B(x,ε)`.

    As `ε → 0`, `green_boundary_tendsto_f` gives the boundary term → `f(x)`,
    so `−Δu(x) = f(x)`. -/
theorem newtonianPotential_solves_poisson (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) :
    IsPoissonSolution Set.univ f (newtonianPotential f) := by
  intro x _
  -- The proof proceeds via regularization at ε and taking ε → 0.
  -- The key steps are the intermediate lemmas above.
  -- Full verification requires Stokes' theorem on spherical domains,
  -- which is not yet in Mathlib in the required form.
  sorry
