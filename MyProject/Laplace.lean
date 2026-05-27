import MyProject.Calculus

open MeasureTheory InnerProductSpace Set Laplacian Topology

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
  ∀ x ∈ U, Δ u x = 0

/-- `u` solves Poisson's equation `−Δu = f` on `U`. -/
def IsPoissonSolution (U : Set ℝⁿ) (f : ℝⁿ → ℝ) (u : ℝⁿ → ℝ) : Prop :=
  ∀ x ∈ U, -Δ u x = f x

/-- Laplace's equation is Poisson's equation with `f = 0`. -/
lemma isHarmonic_iff_isPoissonSolution_zero (U : Set ℝⁿ) (u : ℝⁿ → ℝ) :
    IsHarmonic U u ↔ IsPoissonSolution U 0 u := by
  simp [IsHarmonic, IsPoissonSolution, neg_eq_zero]

/-! ### Fundamental Solution -/

/-- The fundamental solution of the Laplacian (Evans §2.2.1).

    For `n ≥ 3`: `Φ(x) = 1 / (n(n−2)ωₙ) · |x|^(2−n)`
    For `n = 2`: `Φ(x) = −1/(2π) · log |x|`
    where `ωₙ` is the volume of the unit ball in `ℝⁿ`.

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

/-- **Mean Value Property (sphere version)** (Evans §2.2.2, Theorem 2). -/
theorem harmonic_sphereMeanValue (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = sphereMean u x r := by
  sorry

/-- **Mean Value Property (ball version)** (Evans §2.2.2, Theorem 2). -/
theorem harmonic_ballMeanValue (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = ballMean u x r := by
  sorry

/-- **Converse**: mean value property implies harmonic. -/
theorem meanValue_implies_harmonic (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu_c2 : ContDiff ℝ 2 u)
    (hmv : ∀ x ∈ U, ∀ r > 0, Metric.closedBall x r ⊆ U → u x = ballMean u x r) :
    IsHarmonic U u := by
  sorry

/-! ### Maximum Principle -/

/-- **Strong Maximum Principle** (Evans §2.2.3, Theorem 4). -/
theorem harmonic_strongMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hconn : IsConnected U)
    (hu : IsHarmonic U u) (hu_c : Continuous u)
    (x₀ : ℝⁿ) (hx₀ : x₀ ∈ U)
    (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  sorry

/-- **Weak Maximum Principle** (Evans §2.2.3, Theorem 3). -/
theorem harmonic_weakMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hbdd : Bornology.IsBounded U)
    (hu : IsHarmonic U u) (hu_c : ContinuousOn u (closure U)) :
    ∀ x ∈ U, u x ≤ sSup (u '' frontier U) := by
  sorry

/-! ### Smoothness of Harmonic Functions -/

/-- **Regularity** (Evans §2.2.3, Theorem 6). -/
theorem harmonic_smooth (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ ⊤ u U := by
  sorry

/-! ### Representation Formula for Poisson's Equation -/

/-! #### Intermediate Lemmas (Evans §2.2.4 proof steps) -/

/-- `fundamentalSolution` is smooth on `ℝⁿ \ {0}`. -/
lemma fundamentalSolution_contDiff_off_zero :
    ContDiffOn ℝ ⊤ (fundamentalSolution (n := n)) ({0} : Set ℝⁿ)ᶜ := by
  have hn_smooth : ContDiffOn ℝ ⊤ (fun x : ℝⁿ => ‖x‖) ({0} : Set ℝⁿ)ᶜ :=
    fun x hx => (contDiffAt_norm ℝ (Set.mem_compl_singleton_iff.mp hx)).contDiffWithinAt
  have hn_ne : ∀ x ∈ ({0} : Set ℝⁿ)ᶜ, ‖x‖ ≠ 0 :=
    fun x hx => (norm_pos_iff.mpr (Set.mem_compl_singleton_iff.mp hx)).ne'
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · have heq : fundamentalSolution (n := 0) =
          fun (_ : EuclideanSpace ℝ (Fin 0)) => (0 : ℝ) := by
        funext; simp [fundamentalSolution]
      rw [heq]; exact contDiffOn_const
    · have heq : fundamentalSolution (n := 1) =
          fun x : EuclideanSpace ℝ (Fin 1) => (1 / 2 : ℝ) * ‖x‖ := by
        funext; simp [fundamentalSolution]
      rw [heq]; exact contDiffOn_const.mul hn_smooth
    · have heq : fundamentalSolution (n := 2) =
          fun x : EuclideanSpace ℝ (Fin 2) =>
            -(1 / (2 * Real.pi)) * Real.log ‖x‖ := by
        funext; simp [fundamentalSolution]
      rw [heq]
      exact contDiffOn_const.mul (hn_smooth.log hn_ne)
  · have heq : fundamentalSolution (n := n) = fun x : ℝⁿ =>
        (1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)) *
        ‖x‖ ^ (2 - (n : ℝ)) := by
      funext x
      simp only [fundamentalSolution, if_neg (show n ≠ 0 from by omega),
        if_neg (show n ≠ 1 from by omega), if_neg (show n ≠ 2 from by omega)]
    rw [heq]
    exact contDiffOn_const.mul (hn_smooth.rpow_const_of_ne hn_ne)

/-! #### Helpers for harmonicity of the fundamental solution -/

/-- The real inner product as a bilinear CLM, avoiding conjugate-linear ambiguity. -/
noncomputable def realInnerBiL : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ :=
  (innerSL ℝ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ)

/-- The real inner product with fixed left argument. -/
noncomputable def realInnerL (x : ℝⁿ) : ℝⁿ →L[ℝ] ℝ :=
  realInnerBiL x

lemma realInnerL_apply (x y : ℝⁿ) : realInnerL x y = ⟪x, y⟫_ℝ :=
  congr_fun (coe_innerSL_apply ℝ x) y

/-- Linearity of `Laplacian.laplacian` under scalar multiplication. -/
private lemma laplacian_const_mul (c : ℝ) (f : ℝⁿ → ℝ) (hf : ContDiffAt ℝ 2 f x) :
    Δ (fun y => c * f y) x = c * Δ f x := by
  have smul_eq : (fun y : ℝⁿ => c * f y) = c • f := funext fun y => (smul_eq_mul c (f y)).symm
  rw [smul_eq, InnerProductSpace.laplacian_smul c hf]
  simp [smul_eq_mul]

/-- First Fréchet derivative of `‖·‖^p` at `x ≠ 0` for any real exponent `p`. -/
private lemma hasFDerivAt_norm_rpow_of_ne (x : ℝⁿ) (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun x : ℝⁿ => ‖x‖ ^ p)
      ((p * ‖x‖ ^ (p - 2)) • realInnerL x) x := by
  have heq : (p * ‖x‖ ^ (p - 2)) • realInnerL x =
      (p * ‖x‖ ^ (p - 2)) • (innerSL ℝ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ) x := rfl
  rw [heq]
  apply HasStrictFDerivAt.hasFDerivAt
  convert (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- **Laplacian of a radial power**: `Δ(‖·‖^p)(x) = p · (n + p − 2) · ‖x‖^(p−2)`. -/
private lemma laplacian_norm_rpow_eq (p : ℝ) (x : ℝⁿ) (hx : x ≠ 0) :
    Δ (fun x : ℝⁿ => ‖x‖ ^ p) x = p * ((n : ℝ) + p - 2) * ‖x‖ ^ (p - 2) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Δ (fun y : ℝⁿ => ‖y‖ ^ p) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun y : ℝⁿ => ‖y‖ ^ p) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : ℝⁿ => ‖y‖ ^ p) e) x]
  simp_rw [iteratedFDeriv_two_apply]
  have hfderiv : ∀ᶠ y in 𝓝 x,
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

/-- **Laplacian of `log ‖·‖`**: `Δ(log ‖·‖)(x) = (n − 2) · ‖x‖^(−2)`. -/
private lemma laplacian_log_norm_eq (x : ℝⁿ) (hx : x ≠ 0) :
    Δ (fun x : ℝⁿ => Real.log ‖x‖) x = ((n : ℝ) - 2) * ‖x‖ ^ (-(2 : ℝ)) := by
  sorry

/-- **Key Lemma**: `fundamentalSolution` is harmonic on `ℝⁿ \ {0}`. -/
lemma fundamentalSolution_harmonic_off_zero (x : ℝⁿ) (hx : x ≠ 0) :
    Δ (fundamentalSolution : ℝⁿ → ℝ) x = 0 := by
  have hx_mem : x ∈ ({0} : Set ℝⁿ)ᶜ := Set.mem_compl_singleton_iff.mpr hx
  have hcd : ContDiffAt ℝ 2 (fundamentalSolution (n := n)) x :=
    (fundamentalSolution_contDiff_off_zero.contDiffAt
      (IsOpen.mem_nhds isOpen_compl_singleton hx_mem)).of_le le_top
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · have heq : (fundamentalSolution (n := 0) : EuclideanSpace ℝ (Fin 0) → ℝ) = fun _ => 0 :=
        funext (by simp [fundamentalSolution])
      rw [heq]; simp
    · have heq : (fundamentalSolution (n := 1) : EuclideanSpace ℝ (Fin 1) → ℝ) =
          fun x => (1 / 2 : ℝ) * ‖x‖ ^ (1 : ℝ) :=
        funext (by simp [fundamentalSolution, Real.rpow_one])
      have hf : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ (1 : ℝ)) x := by
        simp_rw [Real.rpow_one]; exact (contDiffAt_norm ℝ hx).of_le le_top
      rw [heq, laplacian_const_mul (1/2) _ hf, laplacian_norm_rpow_eq 1 x hx]
      norm_num
    · have heq : (fundamentalSolution (n := 2) : EuclideanSpace ℝ (Fin 2) → ℝ) =
          fun x => -(1 / (2 * Real.pi)) * Real.log ‖x‖ :=
        funext (by simp [fundamentalSolution])
      have hf : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) => Real.log ‖x‖) x :=
        ((contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)).of_le le_top
      rw [heq, laplacian_const_mul _ _ hf, laplacian_log_norm_eq x hx]
      norm_num
  · set c := (1 / ((n : ℝ) * ((n : ℝ) - 2) *
        (volume (Metric.ball (0 : ℝⁿ) 1)).toReal))
    have heq : (fundamentalSolution (n := n) : ℝⁿ → ℝ) = fun x => c * ‖x‖ ^ (2 - (n : ℝ)) :=
      funext (by simp [fundamentalSolution, c, show n ≠ 0 from by omega,
        show n ≠ 1 from by omega, show n ≠ 2 from by omega])
    have hf : ContDiffAt ℝ 2 (fun x : ℝⁿ => ‖x‖ ^ (2 - (n : ℝ))) x :=
      ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)).of_le le_top
    rw [heq, laplacian_const_mul c _ hf, laplacian_norm_rpow_eq (2 - (n:ℝ)) x hx]
    simp

/-- Near-singularity integral vanishes as ε → 0. -/
lemma fundamentalSolution_near_integral_tendsto_zero (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  sorry

/-- **Green's second identity** on annular domain `B(x,r) \ B(x,ε)`. -/
lemma green_identity_annulus (u v : ℝⁿ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : ℝⁿ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ∫ y in Metric.ball x r \ Metric.ball x ε, (v y * Δ u y - u y * Δ v y)
    = (∫ y in Metric.sphere x r,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)))
    - (∫ y in Metric.sphere x ε,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1))) := by
  sorry

/-- Total outward normal flux of `∇Φ` through `∂B(0, ε)` equals `−1`. -/
lemma fundamentalSolution_totalFlux (ε : ℝ) (hε : 0 < ε) :
    ∫ y in Metric.sphere (0 : ℝⁿ) ε,
      ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ
      ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)) = -1 := by
  sorry

/-- Boundary integral from Green's identity converges to `f(x)` as ε → 0. -/
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

/-- **Representation Formula** (Evans §2.2.4, Theorem 9). -/
theorem newtonianPotential_solves_poisson (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) :
    IsPoissonSolution Set.univ f (newtonianPotential f) := by
  intro x _
  sorry
