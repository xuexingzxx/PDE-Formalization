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

/-- **Weak Maximum Principle** (Evans §2.2.3, Theorem 3). A `C²` harmonic function on a
    bounded open set attains its supremum on the boundary. Proved by the standard subharmonic
    perturbation `v_ε = u + ε‖·‖²` (`Δv_ε = 2nε > 0`, so by `laplacian_nonpos_of_isLocalMax` it
    has no interior maximum), then letting `ε → 0`. -/
theorem harmonic_weakMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hn : 1 ≤ n) (hU : IsOpen U) (hbdd : Bornology.IsBounded U)
    (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u) :
    ∀ x ∈ U, u x ≤ sSup (u '' frontier U) := by
  have hK : IsCompact (closure U) := hbdd.isCompact_closure
  have hcont : Continuous u := hu_c2.continuous
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨R, hR⟩ := (hbdd.closure).subset_closedBall (0 : ℝⁿ)
  have hRnorm : ∀ y ∈ closure U, ‖y‖ ≤ R := fun y hy => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hy
  have hfrontK : IsCompact (frontier U) :=
    hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hBdd : BddAbove (u '' frontier U) := (hfrontK.image hcont).bddAbove
  set M := sSup (u '' frontier U) with hM
  intro x hx
  have key : ∀ ε : ℝ, 0 < ε → u x ≤ M + ε * R ^ 2 := by
    intro ε hε
    set v : ℝⁿ → ℝ := fun y => u y + ε * ‖y‖ ^ 2 with hv
    have hvcont : Continuous v := by fun_prop
    obtain ⟨xs, hxs_mem, hxs_max⟩ :=
      hK.exists_isMaxOn ⟨x, subset_closure hx⟩ hvcont.continuousOn
    have hxs_notU : xs ∉ U := by
      intro hxsU
      have hlm : IsLocalMax v xs :=
        hxs_max.isLocalMax (Filter.mem_of_superset (hU.mem_nhds hxsU) subset_closure)
      have hvadd : v = u + fun y : ℝⁿ => ε * ‖y‖ ^ 2 := by
        funext y; simp only [hv, Pi.add_apply]
      have hsq2 : ContDiffAt ℝ 2 (fun y : ℝⁿ => ‖y‖ ^ 2) xs :=
        (contDiff_norm_sq ℝ : ContDiff ℝ 2 fun y : ℝⁿ => ‖y‖ ^ 2).contDiffAt
      have h2 : ContDiffAt ℝ 2 (fun y : ℝⁿ => ε * ‖y‖ ^ 2) xs := hsq2.const_smul ε
      have hvc2 : ContDiffAt ℝ 2 v xs := by rw [hvadd]; exact hu_c2.contDiffAt.add h2
      have hle : Laplacian.laplacian v xs ≤ 0 := laplacian_nonpos_of_isLocalMax hvc2 hlm
      have hΔ : Laplacian.laplacian v xs = Laplacian.laplacian u xs + ε * (2 * (n : ℝ)) := by
        rw [hvadd, ContDiffAt.laplacian_add hu_c2.contDiffAt h2]
        congr 1
        have hsmul : (fun y : ℝⁿ => ε * ‖y‖ ^ 2) = ε • fun y : ℝⁿ => ‖y‖ ^ 2 := by
          funext y; simp [Pi.smul_apply, smul_eq_mul]
        rw [hsmul, laplacian_smul ε hsq2, laplacian_norm_sq, smul_eq_mul]
      rw [hΔ, hu xs hxsU, zero_add] at hle
      exact absurd hle (not_le.mpr (mul_pos hε (mul_pos two_pos hnpos)))
    have hxs_front : xs ∈ frontier U :=
      ⟨hxs_mem, by rw [hU.interior_eq]; exact hxs_notU⟩
    have h1 : u x ≤ v x := by rw [hv]; nlinarith [sq_nonneg ‖x‖, hε]
    have h2 : v x ≤ v xs := hxs_max (subset_closure hx)
    have h4 : u xs ≤ M := le_csSup hBdd ⟨xs, hxs_front, rfl⟩
    have h5 : ‖xs‖ ^ 2 ≤ R ^ 2 := by nlinarith [hRnorm xs hxs_mem, norm_nonneg xs]
    calc u x ≤ v x := h1
      _ ≤ v xs := h2
      _ = u xs + ε * ‖xs‖ ^ 2 := rfl
      _ ≤ M + ε * R ^ 2 := by nlinarith [h4, h5, hε.le]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hR1 : (0 : ℝ) < R ^ 2 + 1 := by positivity
  have hk := key (δ / (R ^ 2 + 1)) (by positivity)
  have hbound : δ / (R ^ 2 + 1) * R ^ 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR1]; nlinarith [hδ.le]
  linarith [hk, hbound]

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

/-! #### Helpers for harmonicity of the fundamental solution

The real inner product as a bilinear CLM (`realInnerBiL`/`realInnerL`) and the radial-power
derivative/Laplacian formulas (`hasFDerivAt_norm_rpow_of_ne`, `laplacian_norm_rpow_eq`) live in
`Calculus.lean`, shared with the Heat chapter. -/

/-- Linearity of `Laplacian.laplacian` under scalar multiplication. -/
private lemma laplacian_const_mul (c : ℝ) (f : ℝⁿ → ℝ) (hf : ContDiffAt ℝ 2 f x) :
    Δ (fun y => c * f y) x = c * Δ f x := by
  have smul_eq : (fun y : ℝⁿ => c * f y) = c • f := funext fun y => (smul_eq_mul c (f y)).symm
  rw [smul_eq, InnerProductSpace.laplacian_smul c hf]
  simp [smul_eq_mul]

/-- **Laplacian of `log ‖·‖`**: `Δ(log ‖·‖)(x) = (n − 2) · ‖x‖^(−2)`. -/
private lemma laplacian_log_norm_eq (x : ℝⁿ) (hx : x ≠ 0) :
    Δ (fun x : ℝⁿ => Real.log ‖x‖) x = ((n : ℝ) - 2) * ‖x‖ ^ (-(2 : ℝ)) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Δ (fun y : ℝⁿ => Real.log ‖y‖) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun y : ℝⁿ => Real.log ‖y‖) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : ℝⁿ => Real.log ‖y‖) e) x]
  simp_rw [iteratedFDeriv_two_apply]
  -- fderiv of log ‖·‖ near x is ‖y‖^(-2) • realInnerL y
  have hfderiv : ∀ᶠ y in 𝓝 x,
      fderiv ℝ (fun y : ℝⁿ => Real.log ‖y‖) y = ‖y‖ ^ (-(2 : ℝ)) • realInnerL y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hx)]
    intro y hy
    have hyne : y ≠ 0 := Set.mem_compl_singleton_iff.mp hy
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    have hfn : HasFDerivAt (fun z : ℝⁿ => ‖z‖) (‖y‖ ^ (-(1 : ℝ)) • realInnerL y) y := by
      have := hasFDerivAt_norm_rpow_of_ne y hyne 1
      simp only [one_mul, show (1 : ℝ) - 2 = -(1 : ℝ) by norm_num, Real.rpow_one] at this
      exact this
    have hlog := hfn.log hynorm.ne'
    convert hlog.fderiv using 1
    rw [smul_smul]
    congr 1
    rw [show ‖y‖⁻¹ = ‖y‖ ^ (-(1 : ℝ)) by
          rw [Real.rpow_neg (norm_nonneg y), Real.rpow_one],
        ← Real.rpow_add hynorm]
    norm_num
  -- per-basis second derivative
  have hderiv2 : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => Real.log ‖y‖)) x (e i) (e i) =
      -(2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) * ⟪x, e i⟫_ℝ ^ 2 + ‖x‖ ^ (-(2 : ℝ)) := by
    intro i
    have hfe : fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => Real.log ‖y‖)) x =
        fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ)) • realInnerL y) x :=
      Filter.EventuallyEq.fderiv_eq hfderiv
    rw [hfe]
    have hc := hasFDerivAt_norm_rpow_of_ne x hx (-(2 : ℝ))
    have hcd : DifferentiableAt ℝ (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ))) x := hc.differentiableAt
    have hgd : DifferentiableAt ℝ (fun y : ℝⁿ => realInnerL y) x :=
      realInnerBiL.hasFDerivAt.differentiableAt
    have hconv : (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ)) • realInnerL y) =
        (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ))) • (fun y : ℝⁿ => realInnerL y) :=
      funext fun y => rfl
    rw [show fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ)) • realInnerL y) x =
        fderiv ℝ ((fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ))) • fun y : ℝⁿ => realInnerL y) x from
      congr_arg (fderiv ℝ · x) hconv]
    rw [fderiv_smul hcd hgd]
    have hgfderiv : fderiv ℝ (fun y : ℝⁿ => realInnerL y) x = realInnerBiL :=
      realInnerBiL.hasFDerivAt.fderiv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.smulRight_apply, hc.fderiv, hgfderiv]
    have hei : realInnerBiL (e i) (e i) = 1 := by
      have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i i
      simp at h
      have heq : realInnerBiL (e i) (e i) = ⟪e i, e i⟫_ℝ := realInnerL_apply (e i) (e i)
      rw [heq]; simp only [e, EuclideanSpace.basisFun_apply]; exact h
    have hxi : realInnerL x (e i) = ⟪x, e i⟫_ℝ := realInnerL_apply x (e i)
    rw [hei, hxi]
    simp only [smul_eq_mul, mul_one]
    ring
  simp_rw [show ∀ i : Fin n, ![e i, e i] 0 = e i from fun i => rfl,
           show ∀ i : Fin n, ![e i, e i] 1 = e i from fun i => rfl]
  simp_rw [hderiv2]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hparseval := e.sum_sq_inner_left x
  have hcombine : ‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2 = ‖x‖ ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_add hxpos]; congr 1; ring
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  conv_lhs =>
    rw [show ∑ i : Fin n, ⟪x, e i⟫_ℝ ^ 2 = ‖x‖ ^ 2 from hparseval]
  conv_lhs =>
    rw [show -(2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2 = -(2 : ℝ) * ‖x‖ ^ (-(2 : ℝ)) from by
      rw [show -(2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2 =
          -(2 : ℝ) * (‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2) from by ring]
      rw [hcombine]]
  ring

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

/-! #### Helper lemmas for near-singularity integral -/

/-- Translation invariance of ball integrals:
    ∫_{B(x,ε)} f(x - y) dy = ∫_{B(0,ε)} f(z) dz.
    Proved via Set.indicator + integral_sub_left_eq_self. -/
private lemma integral_ball_translate (f : ℝⁿ → ℝ) (x : ℝⁿ) (ε : ℝ) :
    ∫ y in Metric.ball x ε, f (x - y) =
    ∫ z in Metric.ball (0 : ℝⁿ) ε, f z := by
  rw [← MeasureTheory.integral_indicator measurableSet_ball,
      ← MeasureTheory.integral_indicator measurableSet_ball]
  have h : (fun y : ℝⁿ => (Metric.ball x ε).indicator (fun y => f (x - y)) y) =
      (fun y : ℝⁿ => (Metric.ball (0 : ℝⁿ) ε).indicator f (x - y)) := by
    ext y
    unfold Set.indicator
    simp only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, sub_zero]
  rw [h]
  exact MeasureTheory.integral_sub_left_eq_self
    ((Metric.ball (0 : ℝⁿ) ε).indicator f) MeasureTheory.volume x

/-- `‖Φ‖` is integrable on the unit ball `B(0,1)`. The radial profile of `‖Φ‖` is
    `r^(2−n)` (for `n ≥ 3`), `|log r|` (for `n = 2`), or linear/zero (small `n`); in every case
    the polar-coordinate integrand `r^(n−1)·‖Φ‖(r)` is bounded on `(0,1)`. We reduce to that
    one-dimensional integral with Mathlib's `n`-dim polar integration
    `integrable_fun_norm_addHaar` (filling the gap that earlier blocked this step). -/
lemma fundamentalSolution_norm_integrableOn_unitBall :
    MeasureTheory.IntegrableOn (fun y : ℝⁿ => ‖fundamentalSolution y‖) (Metric.ball 0 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: `Φ ≡ 0`.
    have hz : (fun y : ℝⁿ => ‖fundamentalSolution y‖) = fun _ => (0 : ℝ) := by
      funext y; simp [fundamentalSolution, hn0]
    rw [hz]; exact MeasureTheory.integrableOn_zero
  -- The radial profile `F` of `‖Φ‖`.
  set F : ℝ → ℝ := fun r =>
    if n = 1 then (1 / 2 : ℝ) * r
    else if n = 2 then |(-(1 / (2 * Real.pi)) * Real.log r)|
    else |(1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : ℝⁿ) 1)).toReal))| * r ^ (2 - (n : ℝ))
    with hFdef
  have hrad : (fun y : ℝⁿ => ‖fundamentalSolution y‖) = fun y => F ‖y‖ := by
    funext y
    simp only [fundamentalSolution, hFdef, if_neg (show n ≠ 0 by omega)]
    split_ifs with h1 h2
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · rw [Real.norm_eq_abs]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  -- Reduce the n-dim ball integral to the 1-D radial integral (shared `Calculus` lemma).
  rw [hrad]
  refine (integrableOn_unitBall_radial hnpos (f := F)).mpr ?_
  -- Now: `IntegrableOn (fun r => r^(n-1) * F r) (Ioo 0 1)`; split on `n`.
  rcases lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · -- `n = 1`: the integrand is `(1/2)·r`, continuous.
      have hF1 : F = fun r : ℝ => (1 / 2 : ℝ) * r := by
        funext r; simp only [hFdef, if_true]
      simp only [hF1]
      exact ((by fun_prop : Continuous (fun r : ℝ => r ^ (1 - 1) * ((1 / 2 : ℝ) * r)))
        |>.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · -- `n = 2`: the integrand is `(1/2π)·r·|log r| ≤ 1/2π`, bounded on a finite-measure set.
      have hF2 : F = fun r : ℝ => |(-(1 / (2 * Real.pi)) * Real.log r)| := by
        funext r; simp only [hFdef, if_true]; rw [if_neg (by decide : ¬(2 : ℕ) = 1)]
      simp only [hF2]
      have hgInt : MeasureTheory.IntegrableOn (fun _ : ℝ => 1 / (2 * Real.pi)) (Set.Ioo 0 1) :=
        MeasureTheory.integrableOn_const
          (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      refine MeasureTheory.Integrable.mono' (g := fun _ => 1 / (2 * Real.pi)) hgInt ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ContinuousOn.mul (by fun_prop) ?_
        refine continuous_abs.comp_continuousOn (continuousOn_const.mul ?_)
        exact Real.continuousOn_log.mono fun r hr => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hr.1
      · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun r hr => ?_
        obtain ⟨hr0, hr1⟩ := hr
        simp only [Real.norm_eq_abs]
        have hlognn : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1.le
        have hlogle : r * -Real.log r ≤ 1 := by
          rw [← Real.log_inv]
          have hinv : Real.log r⁻¹ ≤ r⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
          have hrr : r * (r⁻¹ - 1) = 1 - r := by
            rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hr0), mul_one]
          calc r * Real.log r⁻¹ ≤ r * (r⁻¹ - 1) := mul_le_mul_of_nonneg_left hinv hr0.le
            _ = 1 - r := hrr
            _ ≤ 1 := by linarith
        have he : abs (r ^ (2 - 1) * abs (-(1 / (2 * Real.pi)) * Real.log r))
            = 1 / (2 * Real.pi) * (r * -Real.log r) := by
          rw [show r ^ (2 - 1) = r from by norm_num, abs_mul, abs_abs, abs_of_pos hr0,
            abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 1 / (2 * Real.pi) by positivity),
            abs_of_nonpos hlognn]
          ring
        rw [he]
        calc 1 / (2 * Real.pi) * (r * -Real.log r)
            ≤ 1 / (2 * Real.pi) * 1 := mul_le_mul_of_nonneg_left hlogle (by positivity)
          _ = 1 / (2 * Real.pi) := by ring
  · -- `n ≥ 3`: the integrand simplifies to `|c|·r` (since `r^(n-1)·r^(2-n) = r`), continuous.
    have hpow : ∀ r : ℝ, 0 < r → r ^ (n - 1) * r ^ (2 - (n : ℝ)) = r := by
      intro r hr0
      rw [← Real.rpow_natCast r (n - 1), ← Real.rpow_add hr0,
        Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one,
        show ((n : ℝ) - 1) + (2 - (n : ℝ)) = 1 by ring, Real.rpow_one]
    have hF3 : ∀ r : ℝ, 0 < r → r ^ (n - 1) * F r
        = |1 / ((n : ℝ) * ((n : ℝ) - 2) *
            (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * r := by
      intro r hr0
      simp only [hFdef, if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega)]
      rw [show r ^ (n - 1) * (|1 / ((n : ℝ) * ((n : ℝ) - 2) *
              (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * r ^ (2 - (n : ℝ)))
            = |1 / ((n : ℝ) * ((n : ℝ) - 2) *
              (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * (r ^ (n - 1) * r ^ (2 - (n : ℝ)))
          from by ring, hpow r hr0]
    refine MeasureTheory.IntegrableOn.congr_fun
      (show MeasureTheory.IntegrableOn (fun r : ℝ => |1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * r) (Set.Ioo 0 1) from
        ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set
          Set.Ioo_subset_Icc_self)
      ?_ measurableSet_Ioo
    intro r hr
    exact (hF3 r hr.1).symm

/-- Near-singularity integral vanishes as ε → 0 (Evans §2.2.4, p.23).
    ∫_{B(x,ε)} ‖Φ(x-y)‖ dy → 0 as ε → 0⁺.

    Proof strategy:
    1. Translate: ∫_{B(x,ε)} ‖Φ(x-y)‖ = ∫_{B(0,ε)} ‖Φ‖ via integral_ball_translate.
    2. ‖Φ‖ integrable on B(0,1): `fundamentalSolution_norm_integrableOn_unitBall`, proved via
       Mathlib's n-dim polar integration (∫_{B(0,1)} ‖y‖^(2-n) = nωₙ ∫₀¹ r dr < ∞).
    3. Sequential convergence: B(0,1/(k+1)) ↘ {0}, use tendsto_setIntegral_of_antitone.
    4. Transfer: sequential → nhdsWithin via Metric.tendsto_nhdsWithin_nhds. -/
lemma fundamentalSolution_near_integral_tendsto_zero (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hshift : ∀ ε : ℝ, ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖ =
      ∫ z in Metric.ball (0 : ℝⁿ) ε, ‖fundamentalSolution z‖ :=
    fun ε => integral_ball_translate (fun z => ‖fundamentalSolution z‖) x ε
  simp_rw [hshift]
  -- Step 2: ‖Φ‖ is locally integrable on B(0, 1), via n-dim polar integration
  -- (Mathlib's `integrable_fun_norm_addHaar`).
  have hint : MeasureTheory.IntegrableOn (fun y : ℝⁿ => ‖fundamentalSolution y‖)
      (Metric.ball 0 1) := fundamentalSolution_norm_integrableOn_unitBall
  -- Step 3: sequential convergence via antitone balls B(0, 1/(k+1)) → {0}
  have hinter : ⋂ k : ℕ, Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)) = {0} := by
    ext y; simp only [Set.mem_iInter, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← norm_eq_zero]; apply le_antisymm _ (norm_nonneg _)
      apply le_of_forall_pos_le_add; intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
      have hle : ‖y‖ ≤ 1 / ((k : ℝ) + 1) := le_of_lt (h k)
      have hlt : 1 / ((k : ℝ) + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
        have := (div_lt_iff₀ hε).mp hk
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      linarith
    · rintro rfl k
      simp only [norm_zero]
      positivity
  have hseq : Filter.Tendsto
      (fun k : ℕ => ∫ z in Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)), ‖fundamentalSolution z‖)
      Filter.atTop (nhds 0) := by
    -- ∫_{B(0,1/(k+1))} ‖Φ‖ → ∫_{{0}} ‖Φ‖ = 0
    -- {0} integral vanishes: n=0 by fundamentalSolution=0; n≥1 by volume {0} = 0 (NoAtoms).
    have hfin : ∫ z in ({0} : Set ℝⁿ), ‖fundamentalSolution z‖ = 0 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [fundamentalSolution]
      · rw [MeasureTheory.integral_singleton]
        have h0 : (MeasureTheory.volume : MeasureTheory.Measure ℝⁿ) {0} = 0 := by
          haveI : Nontrivial ℝⁿ :=
            ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, by
              intro h
              have : (EuclideanSpace.single ⟨0, hn⟩ (1:ℝ) : Fin n → ℝ) ⟨0, hn⟩ = 0 := by
                rw [← h]; simp
              simp at this⟩
          haveI : (𝓝[≠] (0 : ℝⁿ)).NeBot := Real.punctured_nhds_module_neBot 0
          haveI : MeasureTheory.NoAtoms (MeasureTheory.volume : MeasureTheory.Measure ℝⁿ) :=
            MeasureTheory.Measure.IsAddHaarMeasure.noAtoms _
          exact MeasureTheory.NoAtoms.measure_singleton 0
        simp [MeasureTheory.Measure.real, h0]
    rw [← hfin, ← hinter]
    apply MeasureTheory.tendsto_setIntegral_of_antitone
    · intro k; exact measurableSet_ball
    · intro a b hab
      exact Metric.ball_subset_ball (by
        apply div_le_div_of_nonneg_left one_pos.le (by positivity) (by
          exact_mod_cast Nat.add_le_add_right hab 1))
    · exact ⟨0, hint.mono (Metric.ball_subset_ball (by norm_cast; norm_num)) le_rfl⟩
  -- Step 4: transfer sequential → nhdsWithin 0 (Ioi 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hseq δ hδ
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun ε hεpos hεδ => ?_⟩
  have hεpos' : 0 < ε := Set.mem_Ioi.mp hεpos
  have hεlt : ε < 1 / ((k : ℝ) + 1) := by
    simp only [Real.dist_eq, sub_zero, abs_of_pos hεpos'] at hεδ; exact hεδ
  have hint_k : MeasureTheory.IntegrableOn (fun y : ℝⁿ => ‖fundamentalSolution y‖)
      (Metric.ball 0 (1 / ((k : ℝ) + 1))) :=
    hint.mono (Metric.ball_subset_ball (by
      rw [div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) k])) le_rfl
  have hball_sub : Metric.ball (0 : ℝⁿ) ε ⊆ Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)) :=
    Metric.ball_subset_ball hεlt.le
  have hmono : ∫ z in Metric.ball (0 : ℝⁿ) ε, ‖fundamentalSolution z‖ ≤
      ∫ z in Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)), ‖fundamentalSolution z‖ := by
    apply MeasureTheory.setIntegral_mono_set hint_k
    · exact Filter.Eventually.of_forall (fun z =>
        show (0 : ℝ) ≤ ‖fundamentalSolution z‖ from norm_nonneg _)
    · exact MeasureTheory.ae_of_all _ (fun z hz => hball_sub hz)
  have hkle := hk k le_rfl
  have hk_nn : 0 ≤ ∫ z in Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)),
      ‖fundamentalSolution z‖ :=
    MeasureTheory.integral_nonneg (fun z => norm_nonneg (fundamentalSolution z))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hk_nn] at hkle
  have hint_nn : 0 ≤ ∫ z in Metric.ball (0 : ℝⁿ) ε, ‖fundamentalSolution z‖ :=
    MeasureTheory.integral_nonneg (fun z => norm_nonneg _)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg hint_nn]
  linarith

/-- **Green's second identity** on annular domain `B(x,r) \ B(x,ε)`.
    Evans §2.2.4 strategy:
    (1) Algebra:  v Δu − u Δv = div(v ∇u − u ∇v)      [product rule, cross terms cancel]
    (2) Gauss–Green on annulus: ∫_Ω div F = ∫_{S_r} F·ν dσ − ∫_{S_ε} F·ν dσ
        Sign: annulus outward normal on inner sphere is −ν (inward to B(x,ε)).
    Blocked: step (2) needs Stokes on smooth domains, not yet in Mathlib.
    (Mathlib's divergence theorem covers rectangular boxes only.) -/
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
  -- Standard ONB for ℝⁿ
  set e := EuclideanSpace.basisFun (Fin n) ℝ with he_def
  -- Step 1 (Evans §2.2, algebra): v Δu − u Δv = ∑ᵢ ∂_{eᵢ}(v·∂_{eᵢ}u − u·∂_{eᵢ}v)
  -- Proof: product rule gives ∂_{eᵢ}(v·∂_{eᵢ}u) = (∂_{eᵢ}v)(∂_{eᵢ}u) + v·∂²_{eᵢeᵢ}u,
  -- and the cross terms (∂_{eᵢ}v)(∂_{eᵢ}u) cancel when we subtract the same with u↔v.
  have hdivid : ∀ y : ℝⁿ,
      v y * Δ u y - u y * Δ v y =
      ∑ i : Fin n, fderiv ℝ (fun z =>
          v z * fderiv ℝ u z (e i) - u z * fderiv ℝ v z (e i)) y (e i) := by
    intro y
    -- Expand Δu, Δv using the ONB: Δf y = ∑ᵢ iteratedFDeriv 2 f y ![eᵢ, eᵢ]
    have hΔu : Δ u y = ∑ i : Fin n, iteratedFDeriv ℝ 2 u y ![e i, e i] :=
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis u e) y
    have hΔv : Δ v y = ∑ i : Fin n, iteratedFDeriv ℝ 2 v y ![e i, e i] :=
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis v e) y
    rw [hΔu, hΔv]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext i; symm
    -- For each i: compute fderiv via product rule and chain rule
    -- HasFDerivAt for fun z => fderiv u z (eᵢ):
    --   fderiv u is C¹ (from hu : ContDiff 2 u), evaluate the CLM at eᵢ for chain rule.
    have hfdu_i : HasFDerivAt (fun z : ℝⁿ => fderiv ℝ u z (e i))
        ((fderiv ℝ (fderiv ℝ u) y).flip (e i)) y := by
      have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
      have h2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) y) y :=
        (h1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h3 := h2.clm_apply (hasFDerivAt_const (e i) y)
      simp only [ContinuousLinearMap.comp_zero, zero_add] at h3
      exact h3
    have hfdv_i : HasFDerivAt (fun z : ℝⁿ => fderiv ℝ v z (e i))
        ((fderiv ℝ (fderiv ℝ v) y).flip (e i)) y := by
      have h1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
      have h2 : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) y) y :=
        (h1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h3 := h2.clm_apply (hasFDerivAt_const (e i) y)
      simp only [ContinuousLinearMap.comp_zero, zero_add] at h3
      exact h3
    -- HasFDerivAt for v and u themselves
    have hv_hfd : HasFDerivAt v (fderiv ℝ v y) y :=
      (hv.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hu_hfd : HasFDerivAt u (fderiv ℝ u y) y :=
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    -- Product rule + subtraction: first term v*(fderiv u · eᵢ), second u*(fderiv v · eᵢ)
    have hterm : HasFDerivAt (fun z : ℝⁿ => v z * fderiv ℝ u z (e i) - u z * fderiv ℝ v z (e i))
        (v y • (fderiv ℝ (fderiv ℝ u) y).flip (e i) + fderiv ℝ u y (e i) • fderiv ℝ v y -
         (u y • (fderiv ℝ (fderiv ℝ v) y).flip (e i) + fderiv ℝ v y (e i) • fderiv ℝ u y)) y :=
      (hv_hfd.mul hfdu_i).sub (hu_hfd.mul hfdv_i)
    -- Evaluate at eᵢ and use iteratedFDeriv_two_apply to identify ∂²u
    rw [hterm.fderiv]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    -- iteratedFDeriv_two_apply: fderiv(fderiv u) y (eᵢ) (eᵢ) = iteratedFDeriv 2 u y ![eᵢ,eᵢ]
    have hd2u : fderiv ℝ (fderiv ℝ u) y (e i) (e i) = iteratedFDeriv ℝ 2 u y ![e i, e i] := by
      have h := iteratedFDeriv_two_apply (𝕜 := ℝ) u y ![e i, e i]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      exact h.symm
    have hd2v : fderiv ℝ (fderiv ℝ v) y (e i) (e i) = iteratedFDeriv ℝ 2 v y ![e i, e i] := by
      have h := iteratedFDeriv_two_apply (𝕜 := ℝ) v y ![e i, e i]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      exact h.symm
    rw [hd2u, hd2v]; ring
  -- Step 2 (Evans §2.2): Gauss–Green theorem on the annulus Ω = B(x,r) \ B̄(x,ε).
  --   ∫_Ω ∑ᵢ ∂_{eᵢ} Fᵢ = ∫_{S(x,r)} ∑ᵢ Fᵢ ⟨eᵢ, ν⟩ dσ − ∫_{S(x,ε)} ∑ᵢ Fᵢ ⟨eᵢ, ν⟩ dσ
  -- where Fᵢ(y) = v(y)·∂_{eᵢ}u(y) − u(y)·∂_{eᵢ}v(y) and ν = ‖y−x‖⁻¹(y−x).
  -- Inner product expansion: ∑ᵢ Fᵢ ⟨eᵢ, ν⟩ = ∑ᵢ(v·∂_{eᵢ}u − u·∂_{eᵢ}v)⟨eᵢ,ν⟩
  --   = v·⟨∇u, ν⟩ − u·⟨∇v, ν⟩  (linearity + ⟨∇f, w⟩ = fderiv f · w = ∑ᵢ ∂_{eᵢ}f · ⟨eᵢ,w⟩).
  -- BLOCKED: Stokes/Gauss-Green on smooth domains is not in Mathlib.
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

/-- **Representation Formula** (Evans §2.2.4, Theorem 9).
    u(x) = ∫ Φ(x-y) f(y) dy solves −Δu = f.
    Proof requires: green_identity_annulus + fundamentalSolution_totalFlux
    + fundamentalSolution_near_integral_tendsto_zero + green_boundary_tendsto_f. -/
theorem newtonianPotential_solves_poisson (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) :
    IsPoissonSolution Set.univ f (newtonianPotential f) := by
  intro x _
  sorry
