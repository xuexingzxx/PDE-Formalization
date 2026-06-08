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
lemma heatKernel_timeDerivative (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    timeDerivative heatKernel (x, t)
      = heatKernel (x, t) * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
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
  rw [timeDerivative, hev.deriv_eq, hFderiv.deriv, hkF]

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

/-- **Evans §2.3.1, Theorem 1**: the convolution `u(x,t) = ∫ Φ(x−y,t) g(y) dy` solves
    the homogeneous heat equation in `ℝⁿ × (0, ∞)`.

    **Proof structure**: differentiating under the integral sign moves the `t`-derivative
    and the spatial Laplacian onto the kernel (`htime`, `hspace` — the analytic gap, needing
    dominated-convergence bounds for the Gaussian and its derivatives, plus a growth bound on
    `g`). The two resulting integrands then cancel *pointwise* by
    `heatKernel_translate_solves_heat`, so the integrals are equal and their difference is
    zero. The cancellation step is fully proved here; only the two
    differentiation-under-the-integral identities remain as `sorry`. -/
theorem heatSolution_solves_heat (g : ℝⁿ → ℝ) (hg : Continuous g)
    (x : ℝⁿ) {t : ℝ} (ht : 0 < t) :
    timeDerivative (heatSolution g) (x, t) -
      spatialLaplacian (heatSolution g) (x, t) = 0 := by
  -- Differentiation under the integral: the `t`-derivative lands on the kernel.
  have htime : timeDerivative (heatSolution g) (x, t)
      = ∫ y : ℝⁿ, deriv (fun s => heatKernel (x - y, s)) t * g y := by
    sorry
  -- Differentiation under the integral: the spatial Laplacian lands on the kernel.
  have hspace : spatialLaplacian (heatSolution g) (x, t)
      = ∫ y : ℝⁿ, Laplacian.laplacian (fun z : ℝⁿ => heatKernel (z - y, t)) x * g y := by
    sorry
  -- The two integrands coincide pointwise, since the kernel solves the heat equation.
  have hcancel : (fun y : ℝⁿ => deriv (fun s => heatKernel (x - y, s)) t * g y)
      = fun y : ℝⁿ => Laplacian.laplacian (fun z : ℝⁿ => heatKernel (z - y, t)) x * g y := by
    funext y
    rw [heatKernel_translate_solves_heat x y ht]
  rw [htime, hspace, hcancel, sub_self]
