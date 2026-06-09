import MyProject.Calculus

open MeasureTheory InnerProductSpace Set Topology

/-!
# Heat Equation (Evans PDE, §2.3)

Formalizing the initial value problem for the heat (diffusion) equation:

  (IVP)  u_t − Δu = 0   in ℝⁿ × (0, ∞)
         u = g           on ℝⁿ × {t = 0}

and its inhomogeneous version `u_t − Δu = f`.

The central object is the **fundamental solution** (heat kernel)

  Φ(x, t) = (4πt)^(−n/2) · exp(−|x|² / 4t)   for t > 0,   Φ(x, t) = 0 for t ≤ 0.

It is a smooth, strictly positive solution of the heat equation for `t > 0`, integrates
to `1` over `ℝⁿ` at each time, and concentrates at the origin as `t ↓ 0`. Convolving the
initial data against `Φ` solves the IVP:  `u(x, t) = ∫ Φ(x − y, t) g(y) dy`.

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §2.3.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### The PDE -/

/-- `u` satisfies the homogeneous heat equation `u_t − Δu = 0` at every spacetime point,
    where `u_t` is `timeDerivative` and `Δu` is the spatial Laplacian `spatialLaplacian`. -/
def IsHeatSolution (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, timeDerivative u p - spatialLaplacian u p = 0

/-- `u` satisfies the inhomogeneous heat equation `u_t − Δu = f`. -/
def IsInhomHeatSolution (f : ℝⁿ × ℝ → ℝ) (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, timeDerivative u p - spatialLaplacian u p = f p

/-- The homogeneous heat equation is the inhomogeneous one with source `f = 0`. -/
lemma isHeatSolution_iff_isInhomHeatSolution_zero (u : ℝⁿ × ℝ → ℝ) :
    IsHeatSolution u ↔ IsInhomHeatSolution 0 u := by
  rfl

/-! ### The Heat Kernel (Fundamental Solution) -/

/-- The fundamental solution of the heat operator (Evans §2.3.1):

      `Φ(x, t) = (4πt)^(−n/2) · exp(−|x|²/4t)`   for `t > 0`,

    and `Φ(x, t) = 0` for `t ≤ 0`. It satisfies `Φ_t − ΔΦ = 0` for `t > 0` and
    `∫_{ℝⁿ} Φ(·, t) = 1` for each `t > 0`. -/
noncomputable def heatKernel (p : ℝⁿ × ℝ) : ℝ :=
  if 0 < p.2 then
    (4 * Real.pi * p.2) ^ (-(n : ℝ) / 2) * Real.exp (-‖p.1‖ ^ 2 / (4 * p.2))
  else 0

@[simp]
lemma heatKernel_apply (x : ℝⁿ) (t : ℝ) :
    heatKernel (x, t) =
      if 0 < t then (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))
      else 0 := rfl

/-- For `t ≤ 0` the heat kernel is zero (it is supported on positive times). -/
@[simp]
lemma heatKernel_of_nonpos (x : ℝⁿ) {t : ℝ} (ht : t ≤ 0) : heatKernel (x, t) = 0 := by
  simp [heatKernel, not_lt.mpr ht]

/-- The heat kernel is strictly positive for positive times. -/
lemma heatKernel_pos (x : ℝⁿ) {t : ℝ} (ht : 0 < t) : 0 < heatKernel (x, t) := by
  simp only [heatKernel_apply, if_pos ht]
  apply mul_pos
  · apply Real.rpow_pos_of_pos
    positivity
  · exact Real.exp_pos _

/-- The heat kernel is nonnegative everywhere. -/
lemma heatKernel_nonneg (x : ℝⁿ) (t : ℝ) : 0 ≤ heatKernel (x, t) := by
  by_cases ht : 0 < t
  · exact (heatKernel_pos x ht).le
  · simp [heatKernel_of_nonpos x (not_lt.mp ht)]

/-- The heat kernel is radial, hence even in space: `Φ(−x, t) = Φ(x, t)`. -/
lemma heatKernel_even (x : ℝⁿ) (t : ℝ) : heatKernel (-x, t) = heatKernel (x, t) := by
  simp only [heatKernel_apply, norm_neg]

/-! ### Solution of the Initial Value Problem -/

/-- The solution of the heat IVP with initial data `g`, given by convolution of `g`
    against the heat kernel:  `u(x, t) = ∫_{ℝⁿ} Φ(x − y, t) g(y) dy`. -/
noncomputable def heatSolution (g : ℝⁿ → ℝ) : ℝⁿ × ℝ → ℝ :=
  fun p => ∫ y, heatKernel (p.1 - y, p.2) * g y

/-! ### Main Theorems -/

/-- **Normalization (Evans §2.3.1, Lemma)**: the heat kernel integrates to `1` over
    `ℝⁿ` for every positive time.

    **Proof**: the kernel is `(4πt)^{−n/2}` times the Gaussian `exp(−|x|²/4t)`, whose
    integral over `ℝⁿ` is `(π/(1/4t))^{n/2} = (4πt)^{n/2}` by Mathlib's multivariate
    Gaussian integral `integral_rexp_neg_mul_sq_norm`. The two powers cancel. -/
theorem heatKernel_integral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝⁿ, heatKernel (x, t) = 1 := by
  have h4t : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  -- The multivariate Gaussian integral.
  have hgauss : ∫ x : ℝⁿ, Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2)
      = (4 * Real.pi * t) ^ ((n : ℝ) / 2) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝⁿ) hb
    rw [finrank_euclideanSpace_fin] at h
    rw [h]
    have h4t' : (4 : ℝ) * t ≠ 0 := by positivity
    congr 1
    field_simp
  calc ∫ x : ℝⁿ, heatKernel (x, t)
      = ∫ x : ℝⁿ, (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
        congr 1
        funext x
        simp only [heatKernel_apply, if_pos ht]
        rw [show -‖x‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖x‖ ^ 2 from by ring]
    _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * ∫ x : ℝⁿ, Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
        rw [integral_const_mul]
    _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (4 * Real.pi * t) ^ ((n : ℝ) / 2) := by
        rw [hgauss]
    _ = 1 := by
        rw [← Real.rpow_add h4t]
        rw [show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 from by ring, Real.rpow_zero]

/-- The kernel still integrates to `1` after the convolution shift `y ↦ x − y`
    (the reflection-translation `y ↦ x − y` preserves Lebesgue measure). -/
lemma heatKernel_integral_translate_eq_one (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    ∫ y : ℝⁿ, heatKernel (x - y, t) = 1 := by
  calc ∫ y : ℝⁿ, heatKernel (x - y, t)
      = ∫ y : ℝⁿ, heatKernel (y, t) :=
        MeasureTheory.integral_sub_left_eq_self
          (fun z : ℝⁿ => heatKernel (z, t)) MeasureTheory.volume x
    _ = 1 := heatKernel_integral_eq_one ht

/-- **Constant initial data is preserved**: the solution with `g ≡ c` is the constant `c`.
    A consistency check on the solution formula — constants solve the heat equation — and a
    direct corollary of the kernel's unit mass. -/
theorem heatSolution_const (c : ℝ) (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    heatSolution (fun _ => c) (x, t) = c := by
  simp only [heatSolution]
  rw [integral_mul_const, heatKernel_integral_translate_eq_one x ht, one_mul]

/-- **Time derivative of the heat kernel**: `Φ_t = Φ · (|x|²/(4t²) − n/(2t))`.

    **Proof**: on `t > 0` the kernel agrees with the smooth branch
    `F(s) = (4πs)^{−n/2}·exp(−|x|²/4s)`. Writing `Φ = u·v` with `u(s) = (4πs)^{−n/2}` and
    `v(s) = exp(−|x|²/4s)`, the product and chain rules give
    `u'(t) = u(t)·(−n/(2t))` and `v'(t) = v(t)·(|x|²/(4t²))`, whose sum is the claim. -/
lemma heatKernel_hasDerivAt_time (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatKernel (x, s))
      (heatKernel (x, t) * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))) t := by
  set c : ℝ := ‖x‖ ^ 2 with hc
  set a : ℝ := -(n : ℝ) / 2 with ha
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  -- The smooth branch of the kernel near `t`.
  set F : ℝ → ℝ := fun s => (4 * Real.pi * s) ^ a * Real.exp (-c / (4 * s)) with hF
  -- `u(s) = (4πs)^a` and its derivative.
  have hbase : HasDerivAt (fun s => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  have hu : HasDerivAt (fun s => (4 * Real.pi * s) ^ a)
      (a * (4 * Real.pi * t) ^ (a - 1) * (4 * Real.pi)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl hpos.ne')).comp t hbase
  -- `g(s) = −c/(4s)` and its derivative `c/(4t²)`.
  have hg : HasDerivAt (fun s => -c / (4 * s)) (c / (4 * t ^ 2)) t := by
    have hd : HasDerivAt (fun s => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul 4
    have h := (hasDerivAt_const t (-c)).div hd (by positivity : (0:ℝ) < 4 * t).ne'
    convert h using 1
    field_simp
    ring
  -- `v(s) = exp(g s)` and its derivative.
  have hv : HasDerivAt (fun s => Real.exp (-c / (4 * s)))
      (Real.exp (-c / (4 * t)) * (c / (4 * t ^ 2))) t := hg.exp
  -- The product `F = u·v` has the claimed derivative.
  have hFderiv : HasDerivAt F
      (F t * (c / (4 * t ^ 2) - (n : ℝ) / (2 * t))) t := by
    have hmul := hu.mul hv
    convert hmul using 1
    simp only [hF]
    -- `(4πt)^(a-1) = (4πt)^a · (4πt)⁻¹`, then elementary algebra in the atom `(4πt)^a`.
    rw [Real.rpow_sub hpos, Real.rpow_one, ha]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  -- Transfer the derivative back to the kernel.
  have hev : (fun s => heatKernel (x, s)) =ᶠ[nhds t] F := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [heatKernel_apply, if_pos (Set.mem_Ioi.mp hs), hF, hc, ha]
  have hkF : heatKernel (x, t) = F t := by
    simp only [heatKernel_apply, if_pos ht, hF, hc, ha]
  rw [hkF]
  exact hFderiv.congr_of_eventuallyEq hev

/-- **Time derivative of the heat kernel**: `Φ_t = Φ · (|x|²/(4t²) − n/(2t))`
    (the `deriv` form of `heatKernel_hasDerivAt_time`). -/
lemma heatKernel_timeDerivative (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    timeDerivative heatKernel (x, t)
      = heatKernel (x, t) * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) :=
  (heatKernel_hasDerivAt_time x ht).deriv

/-- The real inner product as a bilinear CLM (avoids conjugate-linear ambiguity). -/
noncomputable def heatInnerBiL : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ :=
  (innerSL ℝ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ)

/-- The real inner product with fixed left argument, as a CLM. -/
noncomputable def heatInnerL (x : ℝⁿ) : ℝⁿ →L[ℝ] ℝ := heatInnerBiL x

lemma heatInnerL_apply (x y : ℝⁿ) : heatInnerL x y = ⟪x, y⟫_ℝ :=
  congr_fun (coe_innerSL_apply ℝ x) y

/-- **Laplacian of the spatial Gaussian**:
    `Δ_y exp(−|y|²/4t) = exp(−|x|²/4t)·(|x|²/(4t²) − n/(2t))`.

    **Proof**: the first derivative is `∇(e^φ) = m·⟪·,−⟫` with `φ(y) = −|y|²/4t`,
    `m(y) = e^φ·(−1/2t)`; since `m = (−1/2t)·e^φ` is itself a multiple of the function, the
    second derivative along `eᵢ` is `m(x) + (−1/2t)·m(x)·⟪x,eᵢ⟫²`. Summing over the standard
    basis (Parseval: `∑ ⟪x,eᵢ⟫² = |x|²`) gives `n·m(x) − m(x)·|x|²/(2t)`, which equals the
    claim after substituting `m(x) = e^φ·(−1/2t)`. -/
lemma gaussian_laplacian (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    Laplacian.laplacian (fun y : ℝⁿ => Real.exp (-‖y‖ ^ 2 / (4 * t))) x
      = Real.exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
  have htne : t ≠ 0 := ht.ne'
  -- Coefficient in the first derivative: `∇G y = m y • heatInnerL y`.
  set m : ℝⁿ → ℝ := fun y => Real.exp (-‖y‖ ^ 2 / (4 * t)) * (-(1 / (2 * t))) with hm
  -- Step 1: the first Fréchet derivative of the Gaussian, everywhere.
  have hGfd : ∀ y : ℝⁿ, HasFDerivAt (fun z : ℝⁿ => Real.exp (-‖z‖ ^ 2 / (4 * t)))
      (m y • heatInnerL y) y := by
    intro y
    have hsq := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
    have hφ : HasFDerivAt (fun z : ℝⁿ => -‖z‖ ^ 2 / (4 * t))
        ((-(1 / (2 * t))) • heatInnerL y) y := by
      have h := hsq.const_mul (-(1 / (4 * t)))
      have hfun : (fun z : ℝⁿ => -‖z‖ ^ 2 / (4 * t))
          = fun z => (-(1 / (4 * t))) * ‖z‖ ^ 2 := by funext z; ring
      rw [hfun]
      convert h using 1
      ext v
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, heatInnerL_apply,
        innerSL_apply_apply, nsmul_eq_mul]
      ring
    have hexp := hφ.exp
    have heq : m y • heatInnerL y
        = Real.exp (-‖y‖ ^ 2 / (4 * t)) • ((-(1 / (2 * t))) • heatInnerL y) := by
      simp only [hm, smul_smul]
    rw [heq]
    exact hexp
  -- fderiv G as a function.
  have hfderivG : fderiv ℝ (fun y : ℝⁿ => Real.exp (-‖y‖ ^ 2 / (4 * t)))
      = fun y => m y • heatInnerL y := by
    funext y; exact (hGfd y).fderiv
  -- The coefficient `m` is differentiable, with derivative `(−1/2t · m x) • heatInnerL x`.
  have hmfd : HasFDerivAt m ((-(1 / (2 * t)) * m x) • heatInnerL x) x := by
    have h := (hGfd x).mul_const (-(1 / (2 * t)))
    rw [hm]
    convert h using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, heatInnerL_apply]
    ring
  -- Step 2: expand the Laplacian over the standard orthonormal basis.
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Laplacian.laplacian (fun y : ℝⁿ => Real.exp (-‖y‖ ^ 2 / (4 * t))) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun y : ℝⁿ => Real.exp (-‖y‖ ^ 2 / (4 * t))) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ e) x]
  simp_rw [iteratedFDeriv_two_apply]
  -- Step 3: the second directional derivative along `eᵢ`.
  have hderiv2 : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => Real.exp (-‖y‖ ^ 2 / (4 * t)))) x (e i) (e i) =
      m x + (-(1 / (2 * t)) * m x) * ⟪x, e i⟫_ℝ ^ 2 := by
    intro i
    rw [show fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => Real.exp (-‖y‖ ^ 2 / (4 * t)))) x =
        fderiv ℝ (fun y : ℝⁿ => m y • heatInnerL y) x from by rw [hfderivG]]
    have hmd : DifferentiableAt ℝ m x := hmfd.differentiableAt
    have hrd : DifferentiableAt ℝ (fun y : ℝⁿ => heatInnerL y) x := heatInnerBiL.differentiableAt
    have hconv : (fun y : ℝⁿ => m y • heatInnerL y)
        = (fun y : ℝⁿ => m y) • (fun y : ℝⁿ => heatInnerL y) := by funext y; rfl
    rw [show fderiv ℝ (fun y : ℝⁿ => m y • heatInnerL y) x =
        fderiv ℝ ((fun y : ℝⁿ => m y) • fun y : ℝⁿ => heatInnerL y) x from
      congr_arg (fderiv ℝ · x) hconv]
    rw [fderiv_smul hmd hrd]
    have hgfderiv : fderiv ℝ (fun y : ℝⁿ => heatInnerL y) x = heatInnerBiL :=
      heatInnerBiL.hasFDerivAt.fderiv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hgfderiv, hmfd.fderiv]
    have hei : heatInnerBiL (e i) (e i) = 1 := by
      have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i i
      simp only [if_true] at h
      have heq : heatInnerBiL (e i) (e i) = ⟪e i, e i⟫_ℝ := heatInnerL_apply (e i) (e i)
      rw [heq]; simpa only [e, EuclideanSpace.basisFun_apply] using h
    have hxi : heatInnerL x (e i) = ⟪x, e i⟫_ℝ := heatInnerL_apply x (e i)
    rw [hei, hxi]
    simp only [smul_eq_mul, mul_one]
    ring
  simp_rw [show ∀ i : Fin n, ![e i, e i] 0 = e i from fun _ => rfl,
           show ∀ i : Fin n, ![e i, e i] 1 = e i from fun _ => rfl]
  simp_rw [hderiv2]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  rw [show ∑ i : Fin n, ⟪x, e i⟫_ℝ ^ 2 = ‖x‖ ^ 2 from e.sum_sq_inner_left x, hm]
  field_simp
  ring

/-- **Spatial Laplacian of the heat kernel**: `ΔΦ = Φ · (|x|²/(4t²) − n/(2t))`.

    **Proof**: for `t > 0` the kernel is the constant `(4πt)^{−n/2}` times the spatial
    Gaussian `exp(−|y|²/4t)`. The constant pulls out of the Laplacian (`laplacian_smul`,
    using that the Gaussian is `C²`), reducing to `gaussian_laplacian`. -/
lemma heatKernel_spatialLaplacian (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    spatialLaplacian heatKernel (x, t)
      = heatKernel (x, t) * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
  set C : ℝ := (4 * Real.pi * t) ^ (-(n : ℝ) / 2) with hC
  set g : ℝⁿ → ℝ := fun y => Real.exp (-‖y‖ ^ 2 / (4 * t)) with hg
  -- For `t > 0`, the kernel in the space variable is `C • g`.
  have hfun : (fun y : ℝⁿ => heatKernel (y, t)) = C • g := by
    funext y
    simp only [heatKernel_apply, if_pos ht, hg, hC, Pi.smul_apply, smul_eq_mul]
  -- The spatial Gaussian is smooth, hence `C²`.
  have hgcd : ContDiff ℝ 2 g := by
    have h1 : ContDiff ℝ 2 (fun y : ℝⁿ => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
    exact (h1.neg.div_const (4 * t)).exp
  -- Pull the constant out of the Laplacian and apply `gaussian_laplacian`.
  simp only [spatialLaplacian, hfun, laplacian_smul C hgcd.contDiffAt, smul_eq_mul]
  rw [hg, gaussian_laplacian x ht]
  have hk : heatKernel (x, t) = C * Real.exp (-‖x‖ ^ 2 / (4 * t)) := by
    simp only [heatKernel_apply, if_pos ht, hC]
  rw [hk]; ring

/-- **Evans §2.3.1, Theorem 1 (part)**: the heat kernel solves the heat equation away
    from the initial time. Immediate from `heatKernel_timeDerivative` and
    `heatKernel_spatialLaplacian`, which both equal `Φ · (|x|²/(4t²) − n/(2t))`. -/
theorem heatKernel_solves_heat (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    timeDerivative heatKernel (x, t) - spatialLaplacian heatKernel (x, t) = 0 := by
  rw [heatKernel_timeDerivative x ht, heatKernel_spatialLaplacian x ht]
  ring

/-- **Translation invariance of the Laplacian**: `Δ(f(· − y))(x) = (Δf)(x − y)`.
    The Laplacian is a sum of second derivatives, which commute with the constant shift
    `· − y` (`iteratedFDeriv_comp_sub`). -/
lemma laplacian_comp_sub (f : ℝⁿ → ℝ) (y x : ℝⁿ) :
    Laplacian.laplacian (fun z => f (z - y)) x = Laplacian.laplacian f (x - y) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Laplacian.laplacian (fun z => f (z - y)) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun z => f (z - y)) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ e) x,
      show Laplacian.laplacian f (x - y) =
        ∑ i, iteratedFDeriv ℝ 2 f (x - y) ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ e) (x - y)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) 2 y x]

/-- **Integrand cancellation**: for each fixed `y`, the translated kernel `(x,t) ↦ Φ(x−y,t)`
    solves the heat equation — its time derivative equals its spatial Laplacian. This is the
    pointwise heart of why the convolution `∫ Φ(x−y,t) g(y) dy` solves the heat equation:
    under the integral the `t`- and `x`-derivatives both land on `Φ` and cancel.

    Proved completely from `heatKernel_timeDerivative`, `heatKernel_spatialLaplacian`
    (both equal `Φ(x−y,t)·(|x−y|²/(4t²) − n/(2t))`) and `laplacian_comp_sub`. -/
lemma heatKernel_translate_solves_heat (x y : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => heatKernel (x - y, s)) t
      = Laplacian.laplacian (fun z : ℝⁿ => heatKernel (z - y, t)) x := by
  have hL : deriv (fun s => heatKernel (x - y, s)) t
      = timeDerivative heatKernel (x - y, t) := rfl
  have hR : Laplacian.laplacian (fun z : ℝⁿ => heatKernel (z - y, t)) x
      = spatialLaplacian heatKernel (x - y, t) := by
    rw [spatialLaplacian]
    exact laplacian_comp_sub (fun w : ℝⁿ => heatKernel (w, t)) y x
  rw [hL, hR, heatKernel_timeDerivative (x - y) ht, heatKernel_spatialLaplacian (x - y) ht]

/-! ### Gaussian moment integrability (auxiliary)

The dominated-convergence bounds for differentiating the convolution under the integral
need integrability over `ℝⁿ` of `exp(−c‖z‖²)` and `‖z‖²·exp(−c‖z‖²)`. Mathlib has the base
`n`-dimensional Gaussian (`integrable_cexp_neg_mul_sq_norm_add`) and the 1-D moments, but not
the `n`-dim moments; we supply the two we need. -/

/-- Elementary bound `v·e^{−v} ≤ e^{−1}` for all real `v` (the maximum of `v·e^{−v}`,
    attained at `v = 1`), via `x + 1 ≤ eˣ`. -/
private lemma mul_exp_neg_le (v : ℝ) : v * Real.exp (-v) ≤ Real.exp (-1) := by
  have h1 : v ≤ Real.exp (v - 1) := by have := Real.add_one_le_exp (v - 1); linarith
  calc v * Real.exp (-v)
      ≤ Real.exp (v - 1) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- Scalar domination `r·e^{−cr} ≤ (2/(c·e))·e^{−(c/2)r}` for `c > 0`, `r ≥ 0`:
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

/-- The pure `n`-dimensional Gaussian `exp(−c‖z‖²)` is integrable for `c > 0`. -/
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

/-- The second Gaussian moment `‖z‖²·exp(−c‖z‖²)` is integrable over `ℝⁿ` for `c > 0`.
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

/-- The first Gaussian moment `‖z‖·exp(−c‖z‖²)` is integrable over `ℝⁿ` for `c > 0`.
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

/-- Uniform domination of the kernel's time-derivative magnitude over `s ∈ [a,b]`
    (with `0 < a ≤ s ≤ b`) by a fixed Gaussian moment. The three `s`-dependent factors
    `(4πs)^{−n/2}`, `exp(−‖z‖²/4s)` and `|‖z‖²/(4s²) − n/(2s)|` are each bounded by their
    values/extremes at the endpoints, giving a single integrable dominator independent of `s`. -/
private lemma heatKernel_time_deriv_bound (z : ℝⁿ) {a b s : ℝ}
    (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) :
    heatKernel (z, s) * |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)|
      ≤ (4 * Real.pi * a) ^ (-(n : ℝ) / 2)
        * Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2)
        * (‖z‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) := by
  have hs : 0 < s := lt_of_lt_of_le ha has
  have hb : 0 < b := lt_of_lt_of_le hs hsb
  have hπ := Real.pi_pos
  rw [heatKernel_apply, if_pos hs]
  -- factor 1: the power, antitone in the base via inverses
  have hrpow : (4 * Real.pi * s) ^ (-(n : ℝ) / 2) ≤ (4 * Real.pi * a) ^ (-(n : ℝ) / 2) := by
    have hbase_le : (4 * Real.pi * a) ^ ((n : ℝ) / 2) ≤ (4 * Real.pi * s) ^ ((n : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
    rw [show (-(n : ℝ) / 2) = -((n : ℝ) / 2) from by ring,
      Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    exact inv_anti₀ (by positivity) hbase_le
  -- factor 2: the Gaussian, monotone since `1/(4s) ≥ 1/(4b)`
  have hexp : Real.exp (-‖z‖ ^ 2 / (4 * s)) ≤ Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [show -‖z‖ ^ 2 / (4 * s) = -(1 / (4 * s)) * ‖z‖ ^ 2 from by ring]
    have h1 : (1 : ℝ) / (4 * b) ≤ 1 / (4 * s) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖z‖)]
  -- factor 3: the polynomial, bounded by its extremes
  have hpoly : |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)|
      ≤ ‖z‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a) := by
    have hs2a : ‖z‖ ^ 2 / (4 * s ^ 2) ≤ ‖z‖ ^ 2 / (4 * a ^ 2) := by gcongr
    have hna : (n : ℝ) / (2 * s) ≤ (n : ℝ) / (2 * a) := by gcongr
    have hz0 : (0 : ℝ) ≤ ‖z‖ ^ 2 / (4 * s ^ 2) := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) / (2 * s) := by positivity
    have hza : (0 : ℝ) ≤ ‖z‖ ^ 2 / (4 * a ^ 2) := by positivity
    have hnaa : (0 : ℝ) ≤ (n : ℝ) / (2 * a) := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  calc (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * s))
        * |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)|
      ≤ (4 * Real.pi * a) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2)
        * (‖z‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) := by
        apply mul_le_mul _ hpoly (abs_nonneg _) (by positivity)
        exact mul_le_mul hrpow hexp (Real.exp_nonneg _) (by positivity)

/-- **Spatial gradient of the heat kernel** (as a Fréchet derivative): for `t > 0`,
    `D_z Φ(z−y,t) = −(1/2t)·Φ(z−y,t)·⟪z−y, ·⟫`. -/
lemma heatKernel_hasFDerivAt_space (y z' : ℝⁿ) (ht : 0 < t) :
    HasFDerivAt (fun z => heatKernel (z - y, t))
      ((-(1 / (2 * t)) * heatKernel (z' - y, t)) • innerSL ℝ (z' - y)) z' := by
  have hfun : (fun z : ℝⁿ => heatKernel (z - y, t))
      = fun z => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-(1 / (4 * t)) * ‖z - y‖ ^ 2) := by
    funext z; simp only [heatKernel_apply, if_pos ht]
    rw [show -‖z - y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖z - y‖ ^ 2 from by ring]
  have hk : heatKernel (z' - y, t)
      = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖z' - y‖ ^ 2) := by
    simp only [heatKernel_apply, if_pos ht]
    rw [show -‖z' - y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖z' - y‖ ^ 2 from by ring]
  rw [hfun]
  refine ((((((hasFDerivAt_sub_const y).norm_sq).const_mul (-(1 / (4 * t)))).exp).const_mul
    ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))) : HasFDerivAt _ _ z').congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply, smul_eq_mul, hk]
  ring

/-- The norm of the kernel's spatial gradient: `‖D_z Φ(z−y,t)‖ = (1/2t)·Φ(z−y,t)·‖z−y‖`. -/
lemma heatKernel_fderiv_space_norm (y z' : ℝⁿ) (ht : 0 < t) :
    ‖fderiv ℝ (fun z => heatKernel (z - y, t)) z'‖
      = 1 / (2 * t) * heatKernel (z' - y, t) * ‖z' - y‖ := by
  rw [(heatKernel_hasFDerivAt_space y z' ht).fderiv, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * t)),
    abs_of_nonneg (heatKernel_nonneg _ _)]

/-- `innerSL ℝ w` and the genuinely `ℝ`-linear `heatInnerBiL w` agree (both are `⟪w, ·⟫`).
    Lets us differentiate `z ↦ ⟪z−y, ·⟫` as a `→L[ℝ]`-valued map. -/
private lemma innerSL_eq_heatInnerBiL (w : ℝⁿ) : innerSL ℝ w = heatInnerBiL w := by
  ext v; rw [innerSL_apply_apply, ← heatInnerL_apply]; rfl

/-- Operator norm of `heatInnerBiL w` equals `‖w‖` (it is `⟪w, ·⟫`). -/
private lemma norm_heatInnerBiL_apply (w : ℝⁿ) : ‖heatInnerBiL w‖ = ‖w‖ := by
  rw [← innerSL_eq_heatInnerBiL, innerSL_apply_norm]

/-- **Second spatial derivative of the heat kernel** (existence + bound): the kernel's
    spatial gradient `z ↦ D_zΦ(z−y,t)` is itself differentiable, with second derivative
    bounded by `(1/2t)·Φ(z−y,t)·(1 + (1/2t)‖z−y‖²)` — a Gaussian times a quadratic. -/
lemma heatKernel_hasFDerivAt_space2 (y z' : ℝⁿ) (ht : 0 < t) :
    HasFDerivAt (fun z => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z)
      ((-(1 / (2 * t)) * heatKernel (z' - y, t)) • heatInnerBiL
        + ((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z' - y, t)) • innerSL ℝ (z' - y))
            : ℝⁿ →L[ℝ] ℝ).smulRight (heatInnerBiL (z' - y))) z' := by
  have hDfun : (fun z => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z)
      = fun z => (-(1 / (2 * t)) * heatKernel (z - y, t)) • heatInnerBiL (z - y) := by
    funext z
    rw [(heatKernel_hasFDerivAt_space y z ht).fderiv, innerSL_eq_heatInnerBiL]
  rw [hDfun]
  have ha : HasFDerivAt (fun z : ℝⁿ => -(1 / (2 * t)) * heatKernel (z - y, t))
      ((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z' - y, t)) • innerSL ℝ (z' - y))) z' :=
    (heatKernel_hasFDerivAt_space y z' ht).const_mul (-(1 / (2 * t)))
  have hB : HasFDerivAt (fun z : ℝⁿ => heatInnerBiL (z - y)) heatInnerBiL z' := by
    have h := heatInnerBiL.hasFDerivAt.comp z' (hasFDerivAt_sub_const y)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  exact ha.smul hB

/-- Norm bound on the kernel's second spatial derivative: a Gaussian times a quadratic,
    `‖D²Φ(z−y,t)‖ ≤ (1/2t)·Φ(z−y,t)·(1 + (1/2t)‖z−y‖²)`. -/
lemma heatKernel_fderiv2_norm_le (y z' : ℝⁿ) (ht : 0 < t) :
    ‖fderiv ℝ (fun z => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z) z'‖
      ≤ 1 / (2 * t) * heatKernel (z' - y, t) * (1 + 1 / (2 * t) * ‖z' - y‖ ^ 2) := by
  rw [(heatKernel_hasFDerivAt_space2 y z' ht).fderiv]
  have ht2 : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
  have hk : (0 : ℝ) ≤ heatKernel (z' - y, t) := heatKernel_nonneg _ _
  have hnB : ‖(heatInnerBiL : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (fun w => by simp [norm_heatInnerBiL_apply])
  have hM : ‖(-(1 / (2 * t)) * heatKernel (z' - y, t)) • innerSL ℝ (z' - y)‖
      = 1 / (2 * t) * heatKernel (z' - y, t) * ‖z' - y‖ := by
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg ht2, abs_of_nonneg hk]
  refine le_trans (norm_add_le ((-(1 / (2 * t)) * heatKernel (z' - y, t)) • heatInnerBiL)
    (((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z' - y, t)) • innerSL ℝ (z' - y))
        : ℝⁿ →L[ℝ] ℝ).smulRight (heatInnerBiL (z' - y)))) ?_
  have hterm1 : ‖(-(1 / (2 * t)) * heatKernel (z' - y, t)) • (heatInnerBiL : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ)‖
      ≤ 1 / (2 * t) * heatKernel (z' - y, t) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ht2 hk) (fun v => le_of_eq ?_)
    rw [ContinuousLinearMap.smul_apply, norm_smul, norm_heatInnerBiL_apply,
      Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ht2, abs_of_nonneg hk]
  have hterm2 : ‖((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z' - y, t))
        • innerSL ℝ (z' - y)) : ℝⁿ →L[ℝ] ℝ).smulRight (heatInnerBiL (z' - y))‖
      ≤ 1 / (2 * t) * heatKernel (z' - y, t) * (1 / (2 * t) * ‖z' - y‖ ^ 2) := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_heatInnerBiL_apply, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg ht2, hM]
    have : 1 / (2 * t) * (1 / (2 * t) * heatKernel (z' - y, t) * ‖z' - y‖) * ‖z' - y‖
        = 1 / (2 * t) * heatKernel (z' - y, t) * (1 / (2 * t) * ‖z' - y‖ ^ 2) := by ring
    rw [this]
  calc ‖(-(1 / (2 * t)) * heatKernel (z' - y, t)) • (heatInnerBiL : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ)‖
        + ‖((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z' - y, t))
            • innerSL ℝ (z' - y)) : ℝⁿ →L[ℝ] ℝ).smulRight (heatInnerBiL (z' - y))‖
      ≤ 1 / (2 * t) * heatKernel (z' - y, t)
          + 1 / (2 * t) * heatKernel (z' - y, t) * (1 / (2 * t) * ‖z' - y‖ ^ 2) :=
        add_le_add hterm1 hterm2
    _ = 1 / (2 * t) * heatKernel (z' - y, t) * (1 + 1 / (2 * t) * ‖z' - y‖ ^ 2) := by ring

/-- A quadratic comparison used to dominate the spatially-differentiated kernel over a ball:
    `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` (from `0 ≤ ‖a − b‖²`). -/
private lemma norm_add_sq_le_two (a b : ℝⁿ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_sq_real a b
  have h2 := norm_sub_sq_real a b
  have h3 : (0 : ℝ) ≤ ‖a - b‖ ^ 2 := sq_nonneg _
  nlinarith [h1, h2, h3]

/-- **First spatial derivative under the integral**: at every point `x`, the heat-solution
    convolution `z ↦ ∫ Φ(z−y,t) g(y) dy` is Fréchet-differentiable, with derivative the
    integral of the kernel's spatial derivative. The dominating bound uses the kernel norm
    `heatKernel_fderiv_space_norm` together with `‖z−y‖² ≥ ½‖x−y‖² − 1` on the unit ball,
    reducing integrability to the 0th and 1st Gaussian moments. -/
lemma heatSolution_hasFDerivAt_space (g : ℝⁿ → ℝ) (hg : Continuous g)
    {Cg : ℝ} (hgb : ∀ y, |g y| ≤ Cg) (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    HasFDerivAt (fun z => ∫ y, heatKernel (z - y, t) * g y)
      (∫ y, g y • fderiv ℝ (fun z => heatKernel (z - y, t)) x) x := by
  have hCt : (0 : ℝ) < 1 / (8 * t) := by positivity
  -- continuity & integrability of the kernel in `y` for each fixed `z`
  have hker_cont : ∀ z : ℝⁿ, Continuous (fun y : ℝⁿ => heatKernel (z - y, t)) := by
    intro z
    by_cases hz : 0 < t
    · simp only [heatKernel_apply, if_pos hz]; fun_prop
    · simp only [heatKernel_apply, if_neg hz]; exact continuous_const
  have hker_int : ∀ z : ℝⁿ, Integrable (fun y : ℝⁿ => heatKernel (z - y, t)) := by
    intro z
    have hform : (fun y : ℝⁿ => heatKernel (z - y, t))
        = fun y => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-(1 / (4 * t)) * ‖z - y‖ ^ 2) := by
      funext y; simp only [heatKernel_apply, if_pos ht]
      rw [show -‖z - y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖z - y‖ ^ 2 from by ring]
    rw [hform]
    refine Integrable.const_mul ?_ _
    have hc : (0 : ℝ) < 1 / (4 * t) := by positivity
    simpa [sub_eq_add_neg] using
      ((integrable_exp_neg_mul_norm_sq (n := n) hc).comp_add_left z).comp_neg
  -- the dominating function and its integrability (0th + 1st Gaussian moments)
  set C : ℝ := (4 * Real.pi * t) ^ (-(n : ℝ) / 2) with hCdef
  have hbound_int : Integrable (fun y : ℝⁿ =>
      Cg * (1 / (2 * t)) * (C * Real.exp (1 / (4 * t))) *
        ((1 + ‖x - y‖) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2))) := by
    have h0 := integrable_exp_neg_mul_norm_sq (n := n) hCt
    have h1 := integrable_norm_mul_exp_neg_mul_norm_sq (n := n) hCt
    have hh : Integrable (fun z : ℝⁿ =>
        (1 + ‖z‖) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by
      have hrw : (fun z : ℝⁿ => (1 + ‖z‖) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2))
          = fun z => Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)
            + ‖z‖ * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by funext z; ring
      rw [hrw]; exact h0.add h1
    have hht : Integrable (fun y : ℝⁿ =>
        (1 + ‖x - y‖) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)) := by
      simpa [sub_eq_add_neg] using (hh.comp_add_left x).comp_neg
    exact hht.const_mul _
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun z y => heatKernel (z - y, t) * g y)
    (F' := fun z y => g y • fderiv ℝ (fun z' => heatKernel (z' - y, t)) z)
    (bound := fun y => Cg * (1 / (2 * t)) * (C * Real.exp (1 / (4 * t))) *
      ((1 + ‖x - y‖) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)))
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun z => ((hker_cont z).mul hg).aestronglyMeasurable)
    ?_ ?_ ?_ hbound_int ?_)
  · -- F x integrable
    apply Integrable.mono' ((hker_int x).const_mul Cg)
      ((hker_cont x).mul hg).aestronglyMeasurable
    filter_upwards with y
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs (heatKernel _), abs_of_nonneg (heatKernel_nonneg _ _),
      Real.norm_eq_abs (g y)]
    calc heatKernel (x - y, t) * |g y|
        ≤ heatKernel (x - y, t) * Cg :=
          mul_le_mul_of_nonneg_left (hgb y) (heatKernel_nonneg _ _)
      _ = Cg * heatKernel (x - y, t) := mul_comm _ _
  · -- F' x measurable
    dsimp only
    have heq : (fun y : ℝⁿ => g y • fderiv ℝ (fun z' => heatKernel (z' - y, t)) x)
        = fun y => g y • ((-(1 / (2 * t)) * heatKernel (x - y, t)) • innerSL ℝ (x - y)) := by
      funext y; rw [(heatKernel_hasFDerivAt_space y x ht).fderiv]
    rw [heq]
    exact (hg.smul ((continuous_const.mul (hker_cont x)).smul
      ((innerSL ℝ).continuous.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · -- bound
    refine Filter.Eventually.of_forall fun y z hz => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [norm_smul, Real.norm_eq_abs, heatKernel_fderiv_space_norm y z ht]
    have hCpos : 0 < C := by rw [hCdef]; positivity
    have hzy : ‖z - y‖ ≤ 1 + ‖x - y‖ := by
      calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
        _ ≤ 1 + ‖x - y‖ := by linarith [hz.le]
    have hgeo : (1 / 2) * ‖x - y‖ ^ 2 - 1 ≤ ‖z - y‖ ^ 2 := by
      have h := norm_add_sq_le_two (x - z) (z - y)
      rw [sub_add_sub_cancel] at h
      have hxz : ‖x - z‖ ^ 2 ≤ 1 := by
        rw [← norm_neg (x - z), neg_sub]; nlinarith [hz, norm_nonneg (z - x)]
      nlinarith [h, hxz]
    have htne : t ≠ 0 := ht.ne'
    have hexp_ineq : -(1 / (4 * t)) * ‖z - y‖ ^ 2
        ≤ 1 / (4 * t) + -(1 / (8 * t)) * ‖x - y‖ ^ 2 := by
      have key := mul_le_mul_of_nonneg_left hgeo (show (0 : ℝ) ≤ 1 / (4 * t) by positivity)
      have h84 : (1 : ℝ) / (8 * t) = 1 / (4 * t) * (1 / 2) := by field_simp; ring
      rw [h84]; nlinarith [key]
    have hker_le : heatKernel (z - y, t)
        ≤ C * Real.exp (1 / (4 * t)) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2) := by
      rw [heatKernel_apply, if_pos ht, ← hCdef, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hCpos.le
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      rw [show -‖z - y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖z - y‖ ^ 2 from by ring]
      linarith [hexp_ineq]
    have hkpos : 0 ≤ heatKernel (z - y, t) := heatKernel_nonneg _ _
    have ht2 : 0 ≤ 1 / (2 * t) := by positivity
    have hCgnn : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb y)
    have hexpnn : 0 ≤ C * Real.exp (1 / (4 * t)) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2) := by
      positivity
    calc |g y| * (1 / (2 * t) * heatKernel (z - y, t) * ‖z - y‖)
        ≤ Cg * (1 / (2 * t) * (C * Real.exp (1 / (4 * t))
            * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)) * (1 + ‖x - y‖)) :=
          mul_le_mul (hgb y)
            (mul_le_mul (mul_le_mul_of_nonneg_left hker_le ht2) hzy (norm_nonneg _)
              (mul_nonneg ht2 hexpnn))
            (mul_nonneg (mul_nonneg ht2 hkpos) (norm_nonneg _)) hCgnn
      _ = Cg * (1 / (2 * t)) * (C * Real.exp (1 / (4 * t)))
            * ((1 + ‖x - y‖) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)) := by ring
  · -- h_diff
    refine Filter.Eventually.of_forall fun y z _ => ?_
    dsimp only
    rw [(heatKernel_hasFDerivAt_space y z ht).fderiv]
    exact (heatKernel_hasFDerivAt_space y z ht).mul_const (g y)

/-- `‖c • L‖ ≤ |c|·‖L‖` for an iterated CLM `L`, routed through `opNorm_le_bound` to dodge
    the missing `IsBoundedSMul` instance on `ℝⁿ →L (ℝⁿ→Lℝ)`. -/
private lemma norm_smul_iterated_le (c : ℝ) (L : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝ) : ‖c • L‖ ≤ |c| * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
  gcongr
  exact L.le_opNorm v

/-- Spatial continuity of the kernel in the convolution variable. -/
private lemma heatKernel_cont_y (z : ℝⁿ) (t : ℝ) :
    Continuous (fun y : ℝⁿ => heatKernel (z - y, t)) := by
  by_cases hz : 0 < t
  · simp only [heatKernel_apply, if_pos hz]; fun_prop
  · simp only [heatKernel_apply, if_neg hz]; exact continuous_const

/-- The kernel's spatial gradient is continuous in the convolution variable `y`. -/
private lemma heatKernel_fderiv_cont_y (z : ℝⁿ) (ht : 0 < t) :
    Continuous (fun y : ℝⁿ => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z) := by
  have heq : (fun y : ℝⁿ => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z)
      = fun y => (-(1 / (2 * t)) * heatKernel (z - y, t)) • innerSL ℝ (z - y) := by
    funext y; exact (heatKernel_hasFDerivAt_space y z ht).fderiv
  rw [heq]
  exact (continuous_const.mul (heatKernel_cont_y z t)).smul
    ((innerSL ℝ).continuous.comp (continuous_const.sub continuous_id))

/-- The kernel's second spatial derivative is continuous in the convolution variable `y`. -/
private lemma heatKernel_fderiv2_cont_y (z : ℝⁿ) (ht : 0 < t) :
    Continuous (fun y : ℝⁿ =>
      fderiv ℝ (fun z' => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z') z) := by
  have heq : (fun y : ℝⁿ =>
        fderiv ℝ (fun z' => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z') z)
      = fun y => (-(1 / (2 * t)) * heatKernel (z - y, t)) • heatInnerBiL
          + ((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z - y, t)) • innerSL ℝ (z - y))
              : ℝⁿ →L[ℝ] ℝ).smulRight (heatInnerBiL (z - y)) := by
    funext y; exact (heatKernel_hasFDerivAt_space2 y z ht).fderiv
  rw [heq]
  refine Continuous.add ((continuous_const.mul (heatKernel_cont_y z t)).smul continuous_const) ?_
  have hL : Continuous (fun y : ℝⁿ =>
      ((-(1 / (2 * t))) • ((-(1 / (2 * t)) * heatKernel (z - y, t)) • innerSL ℝ (z - y))
        : ℝⁿ →L[ℝ] ℝ)) :=
    ((continuous_const.mul (heatKernel_cont_y z t)).smul
      ((innerSL ℝ).continuous.comp (continuous_const.sub continuous_id))).const_smul _
  have hw : Continuous (fun y : ℝⁿ => heatInnerBiL (z - y)) :=
    heatInnerBiL.continuous.comp (continuous_const.sub continuous_id)
  exact ((ContinuousLinearMap.smulRightL ℝ ℝⁿ (ℝⁿ →L[ℝ] ℝ)).continuous.comp hL).clm_apply hw

/-- On the unit ball `‖z'−x‖<1`: `‖z'−y‖ ≤ 1 + ‖x−y‖`. -/
private lemma norm_sub_ball_le (x z' y : ℝⁿ) (hz : ‖z' - x‖ < 1) : ‖z' - y‖ ≤ 1 + ‖x - y‖ := by
  calc ‖z' - y‖ = ‖(z' - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖z' - x‖ + ‖x - y‖ := norm_add_le _ _
    _ ≤ 1 + ‖x - y‖ := by linarith [hz.le]

/-- On the unit ball, the kernel is dominated by a fixed Gaussian in `‖x−y‖`:
    `Φ(z'−y,t) ≤ (4πt)^{−n/2}·e^{1/4t}·e^{−‖x−y‖²/8t}`. -/
private lemma heatKernel_ball_le (x z' y : ℝⁿ) {t : ℝ} (ht : 0 < t) (hz : ‖z' - x‖ < 1) :
    heatKernel (z' - y, t) ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
      * Real.exp (1 / (4 * t)) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2) := by
  have hgeo : (1 / 2) * ‖x - y‖ ^ 2 - 1 ≤ ‖z' - y‖ ^ 2 := by
    have h := norm_add_sq_le_two (x - z') (z' - y)
    rw [sub_add_sub_cancel] at h
    have hxz : ‖x - z'‖ ^ 2 ≤ 1 := by
      rw [← norm_neg (x - z'), neg_sub]; nlinarith [hz, norm_nonneg (z' - x)]
    nlinarith [h, hxz]
  rw [heatKernel_apply, if_pos ht, mul_assoc ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  rw [show -‖z' - y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖z' - y‖ ^ 2 from by ring]
  have key := mul_le_mul_of_nonneg_left hgeo (show (0 : ℝ) ≤ 1 / (4 * t) by positivity)
  have h84 : (1 : ℝ) / (8 * t) = 1 / (4 * t) * (1 / 2) := by field_simp; ring
  rw [h84]; nlinarith [key]

/-- **Second spatial derivative under the integral** (`HasFDerivAt` form): the
    convolution's gradient `z ↦ ∫ g(y)·DΦ(z−y,t)` is Fréchet-differentiable at `x`, with
    derivative `∫ g(y)·D²Φ(x−y,t)`. -/
lemma heatSolution_hasFDerivAt_grad (g : ℝⁿ → ℝ) (hg : Continuous g)
    {Cg : ℝ} (hgb : ∀ y, |g y| ≤ Cg) (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    HasFDerivAt (fun z => ∫ y, g y • fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z)
      (∫ y, g y • fderiv ℝ (fun z' => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z') x) x := by
  set C : ℝ := (4 * Real.pi * t) ^ (-(n : ℝ) / 2) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hc8 : (0 : ℝ) < 1 / (8 * t) := by positivity
  have hc4 : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hm0 := integrable_exp_neg_mul_norm_sq (n := n) hc8
  have hm1 := integrable_norm_mul_exp_neg_mul_norm_sq (n := n) hc8
  have hm2 := integrable_norm_sq_mul_exp_neg_mul_norm_sq (n := n) hc8
  have hht : Integrable (fun y : ℝⁿ => Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)
      * (1 + 1 / (2 * t) * (1 + ‖x - y‖) ^ 2)) := by
    have hh : Integrable (fun z : ℝⁿ => Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)
        * (1 + 1 / (2 * t) * (1 + ‖z‖) ^ 2)) := by
      have hrw : (fun z : ℝⁿ => Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)
          * (1 + 1 / (2 * t) * (1 + ‖z‖) ^ 2))
          = fun z => (1 + 1 / (2 * t)) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)
            + 1 / t * (‖z‖ * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2))
            + 1 / (2 * t) * (‖z‖ ^ 2 * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by
        funext z; ring
      rw [hrw]; exact ((hm0.const_mul _).add (hm1.const_mul _)).add (hm2.const_mul _)
    simpa [sub_eq_add_neg] using (hh.comp_add_left x).comp_neg
  have hki : Integrable (fun y : ℝⁿ => heatKernel (x - y, t) * ‖x - y‖) := by
    have hform : (fun y : ℝⁿ => heatKernel (x - y, t) * ‖x - y‖)
        = fun y => C * (‖x - y‖ * Real.exp (-(1 / (4 * t)) * ‖x - y‖ ^ 2)) := by
      funext y
      rw [heatKernel_apply, if_pos ht, ← hCdef,
        show -‖x - y‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖x - y‖ ^ 2 from by ring]
      ring
    rw [hform]
    refine Integrable.const_mul ?_ _
    simpa [sub_eq_add_neg] using
      ((integrable_norm_mul_exp_neg_mul_norm_sq (n := n) hc4).comp_add_left x).comp_neg
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun z y => g y • fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z)
    (F' := fun z y => g y • fderiv ℝ (fun z' => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z') z)
    (bound := fun y => Cg * (1 / (2 * t) * (C * Real.exp (1 / (4 * t))
      * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)) * (1 + 1 / (2 * t) * (1 + ‖x - y‖) ^ 2)))
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun z =>
      (hg.smul (heatKernel_fderiv_cont_y z ht)).aestronglyMeasurable)
    ?hF_int (hg.smul (heatKernel_fderiv2_cont_y x ht)).aestronglyMeasurable
    ?h_bound ?bound_int ?h_diff)
  case hF_int =>
    apply Integrable.mono' (hki.const_mul (Cg * (1 / (2 * t))))
      (hg.smul (heatKernel_fderiv_cont_y x ht)).aestronglyMeasurable
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs, heatKernel_fderiv_space_norm y x ht,
      show Cg * (1 / (2 * t)) * (heatKernel (x - y, t) * ‖x - y‖)
        = Cg * (1 / (2 * t) * heatKernel (x - y, t) * ‖x - y‖) from by ring]
    exact mul_le_mul_of_nonneg_right (hgb y)
      (mul_nonneg (mul_nonneg (by positivity) (heatKernel_nonneg _ _)) (norm_nonneg _))
  case h_bound =>
    refine Filter.Eventually.of_forall fun y z hz => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    dsimp only
    have hCgnn : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb y)
    refine le_trans (norm_smul_iterated_le (g y)
      (fderiv ℝ (fun z' => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z') z)) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (hgb y)
      (norm_nonneg (fderiv ℝ (fun z' => fderiv ℝ (fun z'' => heatKernel (z'' - y, t)) z') z))) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (heatKernel_fderiv2_norm_le y z ht) hCgnn) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCgnn
    have hkb := heatKernel_ball_le x z y ht hz
    have hsq : ‖z - y‖ ^ 2 ≤ (1 + ‖x - y‖) ^ 2 := by
      nlinarith [norm_sub_ball_le x z y hz, norm_nonneg (z - y), norm_nonneg (x - y)]
    have hkn : 0 ≤ heatKernel (z - y, t) := heatKernel_nonneg _ _
    gcongr
  case bound_int =>
    have hrw : (fun y : ℝⁿ => Cg * (1 / (2 * t) * (C * Real.exp (1 / (4 * t))
          * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)) * (1 + 1 / (2 * t) * (1 + ‖x - y‖) ^ 2)))
        = fun y => Cg * (1 / (2 * t)) * (C * Real.exp (1 / (4 * t)))
            * (Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2)
              * (1 + 1 / (2 * t) * (1 + ‖x - y‖) ^ 2)) := by
      funext y; ring
    rw [hrw]; exact hht.const_mul _
  case h_diff =>
    refine Filter.Eventually.of_forall fun z y _ => ?_
    dsimp only
    rw [(heatKernel_hasFDerivAt_space2 z y ht).fderiv]
    exact (heatKernel_hasFDerivAt_space2 z y ht).const_smul (g z)

/-- **Evans §2.3.1, Theorem 1**: for bounded continuous initial data `g`, the convolution
    `u(x,t) = ∫ Φ(x−y,t) g(y) dy` solves the homogeneous heat equation in `ℝⁿ × (0, ∞)`.

    **Proof structure**: differentiating under the integral sign moves the `t`-derivative
    (`htime`, proved via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the Gaussian
    moment bound `heatKernel_time_deriv_bound`) and the spatial Laplacian (`hspace` — still a
    `sorry`) onto the kernel. The two resulting integrands cancel *pointwise* by
    `heatKernel_translate_solves_heat`, so the difference of the integrals is zero. -/
theorem heatSolution_solves_heat (g : ℝⁿ → ℝ) (hg : Continuous g)
    {Cg : ℝ} (hgb : ∀ y, |g y| ≤ Cg)
    (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    timeDerivative (heatSolution g) (x, t) -
      spatialLaplacian (heatSolution g) (x, t) = 0 := by
  -- A compact time-window `(a, b) ∋ t` inside `(0, ∞)`.
  set a : ℝ := t / 2 with ha_def
  set b : ℝ := 2 * t with hb_def
  have hapos : 0 < a := by rw [ha_def]; linarith
  have hta : a < t := by rw [ha_def]; linarith
  have htb : t < b := by rw [hb_def]; linarith
  have hcb : (0 : ℝ) < 1 / (4 * b) := by rw [hb_def]; positivity
  -- Spatial continuity of the kernel at each fixed time.
  have hker_cont : ∀ s : ℝ, Continuous (fun y : ℝⁿ => heatKernel (x - y, s)) := by
    intro s
    by_cases hs0 : 0 < s
    · simp only [heatKernel_apply, if_pos hs0]; fun_prop
    · simp only [heatKernel_apply, if_neg hs0]; exact continuous_const
  -- The kernel is integrable in the convolution variable (Gaussian, after translation).
  have hker_int : ∀ s : ℝ, 0 < s → Integrable (fun y : ℝⁿ => heatKernel (x - y, s)) := by
    intro s hs
    have hform : (fun y : ℝⁿ => heatKernel (x - y, s))
        = fun y => (4 * Real.pi * s) ^ (-(n : ℝ) / 2)
            * Real.exp (-(1 / (4 * s)) * ‖x - y‖ ^ 2) := by
      funext y; simp only [heatKernel_apply, if_pos hs]
      rw [show -‖x - y‖ ^ 2 / (4 * s) = -(1 / (4 * s)) * ‖x - y‖ ^ 2 from by ring]
    rw [hform]
    apply Integrable.const_mul
    have hc : (0 : ℝ) < 1 / (4 * s) := by positivity
    have hbase := integrable_exp_neg_mul_norm_sq (n := n) hc
    simpa [sub_eq_add_neg] using (hbase.comp_add_left x).comp_neg
  -- The Gaussian-moment dominator is integrable.
  have hbound_int : Integrable (fun y : ℝⁿ =>
      (4 * Real.pi * a) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * b)) * ‖x - y‖ ^ 2)
        * (‖x - y‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) * Cg) := by
    have hmom2 := integrable_norm_sq_mul_exp_neg_mul_norm_sq (n := n) hcb
    have hmom0 := integrable_exp_neg_mul_norm_sq (n := n) hcb
    have hh : Integrable (fun z : ℝⁿ =>
        (4 * Real.pi * a) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2)
          * (‖z‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) * Cg) := by
      have hrw : (fun z : ℝⁿ =>
          (4 * Real.pi * a) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2)
            * (‖z‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) * Cg)
          = fun z => ((4 * Real.pi * a) ^ (-(n : ℝ) / 2) * Cg / (4 * a ^ 2))
              * (‖z‖ ^ 2 * Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2))
            + ((4 * Real.pi * a) ^ (-(n : ℝ) / 2) * Cg * ((n : ℝ) / (2 * a)))
              * Real.exp (-(1 / (4 * b)) * ‖z‖ ^ 2) := by
        funext z; ring
      rw [hrw]
      exact (hmom2.const_mul _).add (hmom0.const_mul _)
    simpa [sub_eq_add_neg] using (hh.comp_add_left x).comp_neg
  -- **htime**: the time derivative passes under the integral.
  have htime : timeDerivative (heatSolution g) (x, t)
      = ∫ y : ℝⁿ, deriv (fun s => heatKernel (x - y, s)) t * g y := by
    have hF_meas : ∀ᶠ s in nhds t,
        AEStronglyMeasurable (fun y : ℝⁿ => heatKernel (x - y, s) * g y) volume :=
      Filter.Eventually.of_forall fun s => ((hker_cont s).mul hg).aestronglyMeasurable
    have hF_int : Integrable (fun y : ℝⁿ => heatKernel (x - y, t) * g y) := by
      apply Integrable.mono' ((hker_int t ht).const_mul Cg)
        ((hker_cont t).mul hg).aestronglyMeasurable
      filter_upwards with y
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs (heatKernel _), abs_of_nonneg (heatKernel_nonneg _ _),
        Real.norm_eq_abs (g y)]
      calc heatKernel (x - y, t) * |g y|
          ≤ heatKernel (x - y, t) * Cg :=
            mul_le_mul_of_nonneg_left (hgb y) (heatKernel_nonneg _ _)
        _ = Cg * heatKernel (x - y, t) := mul_comm _ _
    have hF'_meas : AEStronglyMeasurable (fun y : ℝⁿ => heatKernel (x - y, t)
        * (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * g y) volume :=
      (((hker_cont t).mul (by fun_prop)).mul hg).aestronglyMeasurable
    have h_bound : ∀ᵐ y : ℝⁿ ∂volume, ∀ s ∈ Set.Ioo a b,
        ‖heatKernel (x - y, s) * (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * g y‖
          ≤ (4 * Real.pi * a) ^ (-(n : ℝ) / 2)
              * Real.exp (-(1 / (4 * b)) * ‖x - y‖ ^ 2)
              * (‖x - y‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) * Cg := by
      refine Filter.Eventually.of_forall fun y s hs => ?_
      rw [Set.mem_Ioo] at hs
      rw [norm_mul, norm_mul, Real.norm_eq_abs (heatKernel _),
        abs_of_nonneg (heatKernel_nonneg _ _), Real.norm_eq_abs _, Real.norm_eq_abs (g y)]
      exact mul_le_mul (heatKernel_time_deriv_bound (x - y) hapos hs.1.le hs.2.le)
        (hgb y) (abs_nonneg _) (by positivity)
    have h_diff : ∀ᵐ y : ℝⁿ ∂volume, ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s' => heatKernel (x - y, s') * g y)
          (heatKernel (x - y, s) * (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * g y) s := by
      refine Filter.Eventually.of_forall fun y s hs => ?_
      rw [Set.mem_Ioo] at hs
      exact (heatKernel_hasDerivAt_time (x - y) (lt_trans hapos hs.1)).mul_const (g y)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := fun s y => heatKernel (x - y, s) * g y)
      (F' := fun s y => heatKernel (x - y, s)
        * (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * g y)
      (x₀ := t) (bound := fun y => (4 * Real.pi * a) ^ (-(n : ℝ) / 2)
        * Real.exp (-(1 / (4 * b)) * ‖x - y‖ ^ 2)
        * (‖x - y‖ ^ 2 / (4 * a ^ 2) + (n : ℝ) / (2 * a)) * Cg)
      (Ioo_mem_nhds hta htb) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
    have hval : timeDerivative (heatSolution g) (x, t)
        = ∫ y, heatKernel (x - y, t)
            * (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * g y := key.2.deriv
    rw [hval]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [(heatKernel_hasDerivAt_time (x - y) ht).deriv]
  -- Differentiation under the integral: the spatial Laplacian lands on the kernel.
  have hspace : spatialLaplacian (heatSolution g) (x, t)
      = ∫ y : ℝⁿ, Laplacian.laplacian (fun z : ℝⁿ => heatKernel (z - y, t)) x * g y := by
    -- The basis-trace assembly is blocked: `ContinuousENorm` (hence `Integrable` and
    -- `ContinuousLinearMap.integral_apply`) is missing for the iterated CLM space
    -- `ℝⁿ →L (ℝⁿ →L ℝ)`, so scalars cannot be extracted from `∫ y, g y • D²Φ(x−y,t)`.
    sorry
  -- The two integrands coincide pointwise, since the kernel solves the heat equation.
  have hcancel : (fun y : ℝⁿ => deriv (fun s => heatKernel (x - y, s)) t * g y)
      = fun y : ℝⁿ => Laplacian.laplacian (fun z : ℝⁿ => heatKernel (z - y, t)) x * g y := by
    funext y
    rw [heatKernel_translate_solves_heat x y ht]
  rw [htime, hspace, hcancel, sub_self]
