import MyProject.Sobolev.RellichKondrachov

/-!
# Morrey's inequality (Evans §5.6.2)

The `p > n` Sobolev embedding `W^{1,p} ↪ C^{0,1−n/p}`, complementing the already-proved
Gagliardo–Nirenberg–Sobolev (`p < n`) embedding in `Mollification.lean`.

**Status: step 2 (the potential estimate) is complete and sorry-free** —
`potential_estimate` (`n ≥ 2`):
`∫_{B(0,r)} |u(x+z)−u(x)| dz ≤ (rⁿ/n) ∫_{B(0,r)} ‖Du(x+w)‖/‖w‖^{n−1} dw`.

Build plan:
  1. ray bound        |u(x+h) − u(x)| ≤ ‖h‖ · ∫₀¹ ‖Du(x+t·h)‖ dt         [DONE]
  2. potential est.   ∫_{B(0,r)} |u(x+z)−u(x)| dz ≤ (rⁿ/n) ∫_{B(0,r)} ‖Du(x+z)‖/‖z‖^{n−1} dz  [DONE]
  3. Hölder step      ∫_{B} ‖Du(x+·)‖/‖·‖^{n−1} ≤ C r^{1−n/p} ‖Du‖_p   (needs (n−1)p' < n ⟺ p > n)
  4. Morrey          |u(x)−u(y)| ≤ C ‖x−y‖^{1−n/p} ‖Du‖_p   +  the C^{0,1−n/p} statement

KEY ROUTE for (2) — Cartesian dilation, NOT spheres (so no Laplace/AreaFormula import):
  ∫_{B(0,r)}|u(x+z)−u(x)|dz
    ≤ ∫_{B(0,r)} ‖z‖ ∫₀¹ ‖Du(x+τz)‖ dτ dz              (ray bound, pointwise + monotone)
    = ∫₀¹ ∫_{B(0,r)} ‖z‖ ‖Du(x+τz)‖ dz dτ                (Tonelli, integrand ≥ 0)
    = ∫₀¹ τ^{-n-1} ∫_{B(0,τr)} ‖w‖ ‖Du(x+w)‖ dw dτ        (dilate w=τz: dz=τ^{-n}dw, ‖z‖=‖w‖/τ)
    = ∫_{B(0,r)} ‖w‖‖Du(x+w)‖ ∫_{‖w‖/r}^1 τ^{-n-1} dτ dw  (Tonelli back; w∈B(0,τr) ⟺ τ>‖w‖/r)
    ≤ (rⁿ/n) ∫_{B(0,r)} ‖Du(x+w)‖/‖w‖^{n-1} dw            (∫_{s}^1 τ^{-n-1}dτ = (s^{-n}-1)/n ≤ rⁿ/(n‖w‖ⁿ))
  Dilation CoV: `MeasureTheory.Measure.addHaar_smul` / `integral_comp_smul`. Integrability of the
  Riesz kernel ‖·‖^{-(n-1)} on the ball via `integrableOn_norm_rpow_unitBall` (p=-(n-1)>-n ⟺ n≥1...
  need n≥2 for strict; check). Parametric-integral measurability of z↦∫₀¹‖Du(x+τz)‖ is the fiddly bit.
-/

open MeasureTheory InnerProductSpace Set Topology Sobolev
open scoped ENNReal NNReal RealInnerProductSpace

namespace Morrey

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Ray bound.** From the segment FTC, the increment of a `C¹` function along `h` is
    controlled by `‖h‖` times the average size of `Du` on the segment. -/
lemma norm_sub_le_norm_mul_integral_fderiv {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (x h : ℝⁿ) :
    ‖u (x + h) - u x‖ ≤ ‖h‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ u (x + t • h)‖ := by
  have hcont : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h)) :=
    (hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hint_bd : IntervalIntegrable (fun t : ℝ => ‖fderiv ℝ u (x + t • h)‖) volume 0 1 :=
    (hcont.norm).intervalIntegrable 0 1
  rw [sub_eq_integral_fderiv_segment hu x h]
  calc ‖∫ t in (0:ℝ)..1, fderiv ℝ u (x + t • h) h‖
      ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ u (x + t • h) h‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ u (x + t • h)‖ * ‖h‖ := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          ((hcont.clm_apply continuous_const).norm.intervalIntegrable 0 1)
          ((hcont.norm.mul_const _).intervalIntegrable 0 1) ?_
        intro t _
        exact (fderiv ℝ u (x + t • h)).le_opNorm h
    _ = ‖h‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ u (x + t • h)‖ := by
        rw [intervalIntegral.integral_mul_const, mul_comm]

/-- **Tail integral** (the 1-D core of the dilation step in the potential estimate):
    `∫_s^1 τ^{-n-1} dτ = (s^{-n}-1)/n ≤ s^{-n}/n` for `0 < s`, `n ≥ 1`. -/
lemma integral_rpow_tail_le {s : ℝ} (hs0 : 0 < s) (hn : 1 ≤ n) :
    ∫ τ in s..1, τ ^ (-(n:ℝ) - 1) ≤ s ^ (-(n:ℝ)) / n := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hrne : (-(n:ℝ) - 1) ≠ -1 := fun h => hn0 (by linarith)
  have h0 : (0:ℝ) ∉ Set.uIcc s 1 := Set.notMem_uIcc_of_lt hs0 (by norm_num)
  rw [integral_rpow (Or.inr ⟨hrne, h0⟩)]
  have he : (-(n:ℝ) - 1) + 1 = -(n:ℝ) := by ring
  rw [he, Real.one_rpow]
  have hn0' : -(n:ℝ) ≠ 0 := neg_ne_zero.mpr hn0
  have key : (1 - s ^ (-(n:ℝ))) / (-(n:ℝ)) = s ^ (-(n:ℝ)) / n - 1 / n := by
    field_simp
    ring
  rw [key]
  exact sub_le_self _ (by positivity)

/-- **Per-`τ` dilation.** Change of variables `w = τ•z` (`0 < τ`) in the gradient integral:
    `∫_{B(0,r)} ‖z‖‖Du(x+τz)‖ dz = τ^{-n-1} ∫_{B(0,τr)} ‖w‖‖Du(x+w)‖ dw`. -/
lemma dilate_ball_integral {u : ℝⁿ → ℝ} (x : ℝⁿ) (r : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖
      = τ ^ (-(n:ℝ) - 1) * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), ‖w‖ * ‖fderiv ℝ u (x + w)‖ := by
  set f : ℝⁿ → ℝ := fun w => ‖w‖ * ‖fderiv ℝ u (x + w)‖ with hf
  have hpt : ∀ z : ℝⁿ, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖ = τ⁻¹ * f (τ • z) := fun z => by
    have hns : ‖(τ:ℝ) • z‖ = τ * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    simp only [hf, hns]
    field_simp
  have hcoef : τ ^ (-(n:ℝ) - 1) = τ⁻¹ * (τ ^ n)⁻¹ := by
    rw [Real.rpow_sub hτ, Real.rpow_neg hτ.le, Real.rpow_natCast, Real.rpow_one, div_eq_mul_inv]
    ring
  calc ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖
      = ∫ z in Metric.ball (0:ℝⁿ) r, τ⁻¹ * f (τ • z) :=
        setIntegral_congr_fun measurableSet_ball (fun z _ => hpt z)
    _ = τ⁻¹ * ∫ z in Metric.ball (0:ℝⁿ) r, f (τ • z) := by rw [integral_const_mul]
    _ = τ⁻¹ * ((τ ^ n)⁻¹ * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), f w) := by
        rw [Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball 0 r) hτ,
          finrank_euclideanSpace_fin, smul_eq_mul, smul_ball hτ.ne' (0:ℝⁿ) r, smul_zero,
          Real.norm_eq_abs, abs_of_pos hτ]
    _ = τ ^ (-(n:ℝ) - 1) * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), f w := by rw [hcoef]; ring

/-- **Integrated ray bound** (Morrey step 2a): integrate the pointwise ray bound over `B(0,r)`.
    The parametric integral `z ↦ ∫₀¹ ‖Du(x+τz)‖dτ` is continuous, so both sides are integrable. -/
lemma integrated_ray_bound {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝⁿ) (r : ℝ) :
    ∫ z in Metric.ball (0:ℝⁿ) r, |u (x + z) - u x|
      ≤ ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ∫ τ in (0:ℝ)..1, ‖fderiv ℝ u (x + τ • z)‖ := by
  have hxz : Continuous (fun z : ℝⁿ => u (x + z)) :=
    hu.continuous.comp (continuous_const.add continuous_id)
  have hL : Continuous (fun z : ℝⁿ => |u (x + z) - u x|) := (hxz.sub continuous_const).abs
  have hunc : Continuous (Function.uncurry (fun (z : ℝⁿ) (τ : ℝ) => ‖fderiv ℝ u (x + τ • z)‖)) := by
    show Continuous (fun p : ℝⁿ × ℝ => ‖fderiv ℝ u (x + p.2 • p.1)‖)
    exact ((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_snd.smul continuous_fst))).norm
  have hG : Continuous (fun z : ℝⁿ => ∫ τ in (0:ℝ)..1, ‖fderiv ℝ u (x + τ • z)‖) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hunc 0 1
  have hR : Continuous (fun z : ℝⁿ => ‖z‖ * ∫ τ in (0:ℝ)..1, ‖fderiv ℝ u (x + τ • z)‖) :=
    continuous_norm.mul hG
  have hintL : IntegrableOn (fun z : ℝⁿ => |u (x + z) - u x|) (Metric.ball 0 r) :=
    (hL.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall 0 r)).mono_set
      Metric.ball_subset_closedBall
  have hintR : IntegrableOn
      (fun z : ℝⁿ => ‖z‖ * ∫ τ in (0:ℝ)..1, ‖fderiv ℝ u (x + τ • z)‖) (Metric.ball 0 r) :=
    (hR.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall 0 r)).mono_set
      Metric.ball_subset_closedBall
  refine setIntegral_mono_on hintL hintR measurableSet_ball (fun z _ => ?_)
  rw [← Real.norm_eq_abs]
  exact norm_sub_le_norm_mul_integral_fderiv hu x z

/-- **Tonelli swap #1** (Morrey step 2b): exchange the ball integral and the ray integral.
    Both nonneg and jointly bounded-continuous on `B(0,r) × (0,1]`, hence product-integrable. -/
lemma tonelli_swap1 {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝⁿ) (r : ℝ) :
    ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ∫ τ in (0:ℝ)..1, ‖fderiv ℝ u (x + τ • z)‖
      = ∫ τ in (0:ℝ)..1, ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖ := by
  have hcont : Continuous
      (Function.uncurry (fun (z : ℝⁿ) (τ : ℝ) => ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖)) := by
    show Continuous (fun p : ℝⁿ × ℝ => ‖p.1‖ * ‖fderiv ℝ u (x + p.2 • p.1)‖)
    exact continuous_fst.norm.mul (((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_snd.smul continuous_fst))).norm)
  have hInt : Integrable
      (Function.uncurry (fun (z : ℝⁿ) (τ : ℝ) => ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖))
      ((volume.restrict (Metric.ball (0:ℝⁿ) r)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hsub : Metric.ball (0:ℝⁿ) r ×ˢ Set.Ioc (0:ℝ) 1
        ⊆ Metric.closedBall 0 r ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.prod_mono Metric.ball_subset_closedBall Set.Ioc_subset_Icc_self
    exact (hcont.locallyIntegrable.integrableOn_isCompact
      ((isCompact_closedBall 0 r).prod isCompact_Icc)).mono_set hsub
  rw [setIntegral_congr_fun measurableSet_ball
      (g := fun z => ∫ τ in (0:ℝ)..1, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖)
      (fun z _ => (intervalIntegral.integral_const_mul (‖z‖)
        (fun τ => ‖fderiv ℝ u (x + τ • z)‖)).symm)]
  simp_rw [intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1)]
  exact integral_integral_swap hInt

/-- **Half potential estimate**: chain bricks 4 → 5 → 3 (ray bound, swap #1, dilation). -/
lemma potential_half {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝⁿ) (r : ℝ) :
    ∫ z in Metric.ball (0:ℝⁿ) r, |u (x + z) - u x|
      ≤ ∫ τ in Set.Ioc (0:ℝ) 1, τ ^ (-(n:ℝ) - 1)
          * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), ‖w‖ * ‖fderiv ℝ u (x + w)‖ := by
  calc ∫ z in Metric.ball (0:ℝⁿ) r, |u (x + z) - u x|
      ≤ ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ∫ τ in (0:ℝ)..1, ‖fderiv ℝ u (x + τ • z)‖ :=
        integrated_ray_bound hu x r
    _ = ∫ τ in (0:ℝ)..1, ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖ :=
        tonelli_swap1 hu x r
    _ = ∫ τ in Set.Ioc (0:ℝ) 1, ∫ z in Metric.ball (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖ :=
        intervalIntegral.integral_of_le zero_le_one
    _ = ∫ τ in Set.Ioc (0:ℝ) 1, τ ^ (-(n:ℝ) - 1)
          * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), ‖w‖ * ‖fderiv ℝ u (x + w)‖ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ hτ
        exact dilate_ball_integral x r hτ.1

/-- Inner `τ`-lintegral bound (brick 2 in `ℝ≥0∞`): for `0 < s ≤ 1`,
    `∫⁻_{Ioc s 1} ofReal(τ^{-n-1}) ≤ ofReal(s^{-n}/n)`. -/
lemma inner_tau_lintegral_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hn : 1 ≤ n) :
    ∫⁻ τ in Set.Ioc s 1, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
      ≤ ENNReal.ofReal (s ^ (-(n:ℝ)) / n) := by
  have hcont : ContinuousOn (fun τ : ℝ => τ ^ (-(n:ℝ) - 1)) (Set.Icc s 1) := fun τ hτ =>
    (Real.continuousAt_rpow_const τ _ (Or.inl (ne_of_gt (lt_of_lt_of_le hs0 hτ.1)))).continuousWithinAt
  have hint : IntegrableOn (fun τ : ℝ => τ ^ (-(n:ℝ) - 1)) (Set.Ioc s 1) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc s 1)] (fun τ : ℝ => τ ^ (-(n:ℝ) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact Real.rpow_nonneg (le_of_lt (lt_trans hs0 hτ.1)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← intervalIntegral.integral_of_le hs1]
  exact integral_rpow_tail_le hs0 hn

/-- **Tonelli swap #2** (raw ℝ≥0∞ swap with the fixed ball `B(0,r)` + indicator cutting to
    `B(0,τr)`). The `τ`-dependent domain becomes the indicator `𝟙_{‖w‖<τr}`. -/
lemma swap2_lint {g : ℝⁿ → ℝ} (hg : Continuous g) (r : ℝ) :
    ∫⁻ τ in Set.Ioc (0:ℝ) 1, ∫⁻ w in Metric.ball (0:ℝⁿ) r,
        ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
          * (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) w
      = ∫⁻ w in Metric.ball (0:ℝⁿ) r, ∫⁻ τ in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
          * (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) w := by
  apply lintegral_lintegral_swap
  apply Measurable.aemeasurable
  show Measurable (fun p : ℝ × ℝⁿ => ENNReal.ofReal (p.1 ^ (-(n:ℝ) - 1))
    * (Metric.ball (0:ℝⁿ) (p.1 * r)).indicator (fun w => ENNReal.ofReal (g w)) p.2)
  have hset : MeasurableSet {p : ℝ × ℝⁿ | ‖p.2‖ < p.1 * r} :=
    measurableSet_lt (measurable_snd.norm) (measurable_fst.mul_const r)
  have hind : Measurable (fun p : ℝ × ℝⁿ =>
      (Metric.ball (0:ℝⁿ) (p.1 * r)).indicator (fun w => ENNReal.ofReal (g w)) p.2) := by
    have hrw : (fun p : ℝ × ℝⁿ =>
        (Metric.ball (0:ℝⁿ) (p.1 * r)).indicator (fun w => ENNReal.ofReal (g w)) p.2)
        = {p : ℝ × ℝⁿ | ‖p.2‖ < p.1 * r}.indicator (fun p => ENNReal.ofReal (g p.2)) := by
      funext p
      simp only [Set.indicator, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
    rw [hrw]
    exact (ENNReal.measurable_ofReal.comp (hg.measurable.comp measurable_snd)).indicator hset
  refine Measurable.mul ?_ hind
  fun_prop

/-- LHS recognition: pull the `τ`-constant out and collapse the indicator to the ball `B(0,τr)`. -/
lemma lhs_recog {g : ℝⁿ → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r) :
    ∫⁻ τ in Set.Ioc (0:ℝ) 1, ∫⁻ w in Metric.ball (0:ℝⁿ) r,
        ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
          * (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) w
      = ∫⁻ τ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
          * ∫⁻ w in Metric.ball (0:ℝⁿ) (τ * r), ENNReal.ofReal (g w) := by
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro τ hτ
  dsimp only
  have hindmeas : Measurable (fun w : ℝⁿ =>
      (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) w) :=
    (ENNReal.measurable_ofReal.comp hg.measurable).indicator measurableSet_ball
  rw [lintegral_const_mul _ hindmeas, setLIntegral_indicator measurableSet_ball,
    Set.inter_eq_left.mpr (Metric.ball_subset_ball (by nlinarith [hτ.2, hr] : τ * r ≤ r))]

/-- Per-`w` inner bound: recognize the ball indicator as the `τ`-interval `(‖w‖/r, 1]`,
    then apply brick 2a. Holds for `0 < ‖w‖ < r`. -/
lemma inner_w_bound {g : ℝⁿ → ℝ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {w : ℝⁿ}
    (hw0 : 0 < ‖w‖) (hwr : ‖w‖ < r) :
    ∫⁻ τ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
        * (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) w
      ≤ ENNReal.ofReal (g w) * ENNReal.ofReal ((‖w‖ / r) ^ (-(n:ℝ)) / n) := by
  have hs01 : ‖w‖ / r ≤ 1 := by rw [div_le_one hr]; exact hwr.le
  have hspos : 0 < ‖w‖ / r := div_pos hw0 hr
  have hpt : ∀ τ : ℝ, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
      * (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) w
      = (Set.Ioi (‖w‖ / r)).indicator
          (fun τ => ENNReal.ofReal (τ ^ (-(n:ℝ) - 1)) * ENNReal.ofReal (g w)) τ := by
    intro τ
    by_cases hτw : ‖w‖ / r < τ
    · have hmem : w ∈ Metric.ball (0:ℝⁿ) (τ * r) := by
        rw [Metric.mem_ball, dist_zero_right]; exact (div_lt_iff₀ hr).mp hτw
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Ioi.mpr hτw)]
    · have hnmem : w ∉ Metric.ball (0:ℝⁿ) (τ * r) := by
        rw [Metric.mem_ball, dist_zero_right, not_lt]
        exact (le_div_iff₀ hr).mp (not_lt.mp hτw)
      rw [Set.indicator_of_notMem hnmem, mul_zero,
        Set.indicator_of_notMem (fun h => hτw (Set.mem_Ioi.mp h))]
  have hseteq : Set.Ioi (‖w‖ / r) ∩ Set.Ioc (0:ℝ) 1 = Set.Ioc (‖w‖ / r) 1 := by
    ext τ
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, lt_trans hspos h1, h2⟩⟩
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun τ _ => hpt τ),
    setLIntegral_indicator measurableSet_Ioi, hseteq,
    lintegral_mul_const _ (by fun_prop), mul_comm]
  exact mul_le_mul_left' (inner_tau_lintegral_le hspos hs01 hn) _

/-- Full lintegral bound: chain lhs_recog + swap #2 + inner bound (`lintegral_mono_ae`,
    with `w = 0` handled by `g 0 = 0`). -/
lemma lint_bound {g : ℝⁿ → ℝ} (hg : Continuous g) (hg0 : g 0 = 0) (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ τ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
        * ∫⁻ w in Metric.ball (0:ℝⁿ) (τ * r), ENNReal.ofReal (g w)
      ≤ ∫⁻ w in Metric.ball (0:ℝⁿ) r,
          ENNReal.ofReal (g w) * ENNReal.ofReal ((‖w‖ / r) ^ (-(n:ℝ)) / n) := by
  rw [← lhs_recog hg hr, swap2_lint hg r]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  by_cases hw0 : w = 0
  · subst hw0
    have hz : ∀ τ : ℝ, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
        * (Metric.ball (0:ℝⁿ) (τ * r)).indicator (fun w => ENNReal.ofReal (g w)) 0 = 0 := by
      intro τ
      by_cases h0 : (0:ℝⁿ) ∈ Metric.ball (0:ℝⁿ) (τ * r)
      · rw [Set.indicator_of_mem h0]; simp [hg0]
      · rw [Set.indicator_of_notMem h0, mul_zero]
    simp_rw [hz]
    simp
  · exact inner_w_bound hn hr (norm_pos_iff.mpr hw0) hw

/-- Pointwise rpow identity for the RHS conversion (`w ≠ 0`):
    `(s·A)·((s/r)^{-n}/n) = (rⁿ/n)·(A/s^{n-1})`. -/
lemma rhs_ptwise (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) {s A : ℝ} (hs : 0 < s) :
    (s * A) * ((s / r) ^ (-(n:ℝ)) / n) = (r ^ (n:ℝ) / n) * (A / s ^ ((n:ℝ) - 1)) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hsr : (s / r) ^ (-(n:ℝ)) = r ^ (n:ℝ) / s ^ (n:ℝ) := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hs.le hr.le, inv_div]
  have hsn : s ^ (n:ℝ) = s ^ ((n:ℝ) - 1) * s := by
    have h := Real.rpow_add hs ((n:ℝ) - 1) 1
    rw [Real.rpow_one, show (n:ℝ) - 1 + 1 = (n:ℝ) by ring] at h
    exact h
  have hsn1 : (0:ℝ) < s ^ ((n:ℝ) - 1) := Real.rpow_pos_of_pos hs _
  rw [hsr, hsn]
  field_simp

/-- Ball-`r` version of radial `‖·‖^p` integrability (mirrors the project's unit-ball lemma). -/
lemma integrableOn_norm_rpow_ball (hn : 1 ≤ n) {p : ℝ} (hp : -(n:ℝ) < p) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝⁿ => ‖y‖ ^ p) (Metric.ball 0 r) := by
  haveI : Nontrivial ℝⁿ :=
    ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, by
      intro h
      have h0 : (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) : Fin n → ℝ) ⟨0, hn⟩ = 0 := by
        rw [← h]; simp
      simp at h0⟩
  rw [← integrable_indicator_iff measurableSet_ball]
  have hGball : (Metric.ball (0 : ℝⁿ) r).indicator (fun y => ‖y‖ ^ p)
      = fun y => (Set.Iio r).indicator (fun t => t ^ p) ‖y‖ := by
    funext y
    by_cases hy : ‖y‖ < r <;>
      simp [Metric.mem_ball, dist_zero_right, Set.mem_Iio, hy]
  rw [hGball, integrable_fun_norm_addHaar (volume : Measure ℝⁿ), finrank_euclideanSpace_fin]
  have hk : (fun t : ℝ => t ^ (n - 1) • (Set.Iio r).indicator (fun t => t ^ p) t)
      = (Set.Iio r).indicator (fun t => t ^ (n - 1) * t ^ p) := by
    funext t; simp only [smul_eq_mul, Set.indicator_apply]; split_ifs <;> ring
  rw [hk, integrableOn_indicator_iff measurableSet_Iio,
    show Set.Iio r ∩ Set.Ioi 0 = Set.Ioo 0 r from by rw [Set.inter_comm]; exact Set.Ioi_inter_Iio]
  have hs : (-1 : ℝ) < (n : ℝ) - 1 + p := by linarith
  refine MeasureTheory.IntegrableOn.congr_fun
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := (n : ℝ) - 1 + p) hr).mpr hs)
    ?_ measurableSet_Ioo
  intro t ht
  change t ^ ((n : ℝ) - 1 + p) = t ^ (n - 1) * t ^ p
  rw [← Real.rpow_natCast t (n - 1), ← Real.rpow_add ht.1, Nat.cast_sub hn, Nat.cast_one]

/-- The Riesz integrand `‖Du(x+w)‖/‖w‖^{n-1}` is integrable on `B(0,r)` (`n ≥ 2`):
    bounded `‖Du‖` times the integrable radial kernel. -/
lemma rhsint_integrable {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (hn : 1 ≤ n) (x : ℝⁿ) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun w : ℝⁿ => ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)) (Metric.ball 0 r) := by
  have hg_int : IntegrableOn (fun w : ℝⁿ => ‖w‖ ^ (-((n:ℝ) - 1))) (Metric.ball 0 r) :=
    integrableOn_norm_rpow_ball hn (by linarith : -(n:ℝ) < -((n:ℝ) - 1)) hr
  have hfcont : Continuous (fun w : ℝⁿ => ‖fderiv ℝ u (x + w)‖) :=
    ((hu.continuous_fderiv one_ne_zero).comp (continuous_const.add continuous_id)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℝⁿ) r).exists_bound_of_continuousOn hfcont.continuousOn
  have hbound : ∀ᵐ w ∂(volume.restrict (Metric.ball (0:ℝⁿ) r)), ‖‖fderiv ℝ u (x + w)‖‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact hC w (Metric.ball_subset_closedBall hw)
  have hprod : IntegrableOn
      (fun w : ℝⁿ => ‖fderiv ℝ u (x + w)‖ * ‖w‖ ^ (-((n:ℝ) - 1))) (Metric.ball 0 r) :=
    Integrable.bdd_mul hg_int hfcont.aestronglyMeasurable hbound
  refine hprod.congr_fun ?_ measurableSet_ball
  intro w _
  dsimp only
  rw [Real.rpow_neg (norm_nonneg w), ← div_eq_mul_inv]

/-- RHS conversion: the `ℝ≥0∞` product integral equals `ofReal` of the (scaled) Riesz Bochner
    integral. Per-`w` (a.e., `w ≠ 0`) via `rhs_ptwise`, then `ofReal_integral`. -/
lemma rhs_lint_eq {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (hn : 1 ≤ n) (x : ℝⁿ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ w in Metric.ball (0:ℝⁿ) r,
        ENNReal.ofReal (‖w‖ * ‖fderiv ℝ u (x + w)‖) * ENNReal.ofReal ((‖w‖ / r) ^ (-(n:ℝ)) / n)
      = ENNReal.ofReal ((r ^ (n:ℝ) / n)
          * ∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  haveI : Nontrivial ℝⁿ :=
    ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, by
      intro h
      have h0 : (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) : Fin n → ℝ) ⟨0, hn⟩ = 0 := by
        rw [← h]; simp
      simp at h0⟩
  have hne : ∀ᵐ w ∂(volume.restrict (Metric.ball (0:ℝⁿ) r)), w ≠ 0 := by
    apply ae_restrict_of_ae
    have hset : {w : ℝⁿ | ¬ (w ≠ 0)} = {0} := by ext w; simp
    rw [ae_iff, hset]
    exact measure_singleton 0
  have hcongr : (fun w : ℝⁿ => ENNReal.ofReal (‖w‖ * ‖fderiv ℝ u (x + w)‖)
        * ENNReal.ofReal ((‖w‖ / r) ^ (-(n:ℝ)) / n))
      =ᵐ[volume.restrict (Metric.ball (0:ℝⁿ) r)]
      (fun w => ENNReal.ofReal ((r ^ (n:ℝ) / n)
        * (‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)))) := by
    filter_upwards [hne] with w hw
    rw [← ENNReal.ofReal_mul (by positivity), rhs_ptwise hn hr (norm_pos_iff.mpr hw)]
  have hRnn : 0 ≤ᵐ[volume.restrict (Metric.ball (0:ℝⁿ) r)]
      (fun w => (r ^ (n:ℝ) / n) * (‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1))) :=
    Filter.Eventually.of_forall (fun w => by positivity)
  rw [lintegral_congr_ae hcongr,
    ← ofReal_integral_eq_lintegral_ofReal
      (Integrable.const_mul (rhsint_integrable hu hn x hr) (r ^ (n:ℝ) / n)) hRnn,
    integral_const_mul]

/-- **Bochner ↔ ℝ≥0∞ bridge** for the outer `τ`-integral. The integrand equals the continuous
    `Fswap τ = ∫_{closedBall} ‖z‖‖Du(x+τz)‖` on `(0,1]` (via brick 3 + null sphere), hence
    integrable, so `ofReal` commutes with the integral. -/
lemma bochner_eq_lint {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (hn : 1 ≤ n) (x : ℝⁿ) {r : ℝ}
    (hr : 0 < r) :
    ENNReal.ofReal (∫ τ in Set.Ioc (0:ℝ) 1,
        τ ^ (-(n:ℝ) - 1) * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), ‖w‖ * ‖fderiv ℝ u (x + w)‖)
      = ∫⁻ τ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (τ ^ (-(n:ℝ) - 1))
          * ∫⁻ w in Metric.ball (0:ℝⁿ) (τ * r), ENNReal.ofReal (‖w‖ * ‖fderiv ℝ u (x + w)‖) := by
  haveI : Nontrivial ℝⁿ :=
    ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, by
      intro h
      have h0 : (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) : Fin n → ℝ) ⟨0, hn⟩ = 0 := by rw [← h]; simp
      simp at h0⟩
  have hgcont : Continuous (fun w : ℝⁿ => ‖w‖ * ‖fderiv ℝ u (x + w)‖) :=
    continuous_norm.mul (((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add continuous_id)).norm)
  have hballeq : (Metric.ball (0:ℝⁿ) r : Set ℝⁿ) =ᵐ[volume] Metric.closedBall 0 r := by
    rw [ae_eq_set]
    refine ⟨by rw [Set.diff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty], ?_⟩
    have hsph : volume (Metric.sphere (0:ℝⁿ) r) = 0 := Measure.addHaar_sphere _ _ _
    refine measure_mono_null ?_ hsph
    intro z hz
    rw [Set.mem_diff, Metric.mem_closedBall, dist_zero_right, Metric.mem_ball, dist_zero_right,
      not_lt] at hz
    rw [Metric.mem_sphere, dist_zero_right]
    exact le_antisymm hz.1 hz.2
  have hcontf : Continuous (fun p : ℝ × ℝⁿ => ‖p.2‖ * ‖fderiv ℝ u (x + p.1 • p.2)‖) :=
    continuous_snd.norm.mul (((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_fst.smul continuous_snd))).norm)
  have hFswap_cont : Continuous (fun τ : ℝ =>
      ∫ z in Metric.closedBall (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖) :=
    continuous_parametric_integral_of_continuous hcontf (isCompact_closedBall 0 r)
  have hFF : Set.EqOn
      (fun τ => τ ^ (-(n:ℝ) - 1) * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), ‖w‖ * ‖fderiv ℝ u (x + w)‖)
      (fun τ => ∫ z in Metric.closedBall (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖)
      (Set.Ioc 0 1) := by
    intro τ hτ
    dsimp only
    rw [← dilate_ball_integral x r hτ.1, setIntegral_congr_set hballeq]
  have hFswap_int : IntegrableOn
      (fun τ : ℝ => ∫ z in Metric.closedBall (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖)
      (Set.Ioc 0 1) :=
    (hFswap_cont.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hFswap_nn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)]
      (fun τ => ∫ z in Metric.closedBall (0:ℝⁿ) r, ‖z‖ * ‖fderiv ℝ u (x + τ • z)‖) :=
    Filter.Eventually.of_forall
      (fun τ => setIntegral_nonneg measurableSet_closedBall (fun z _ => by positivity))
  rw [setIntegral_congr_fun measurableSet_Ioc hFF,
    ofReal_integral_eq_lintegral_ofReal hFswap_int hFswap_nn]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro τ hτ
  dsimp only
  have hFFτ := hFF hτ
  dsimp only at hFFτ
  rw [← hFFτ, ENNReal.ofReal_mul (Real.rpow_nonneg hτ.1.le _)]
  congr 1
  exact ofReal_integral_eq_lintegral_ofReal
    ((hgcont.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall 0 (τ * r))).mono_set
      Metric.ball_subset_closedBall)
    (Filter.Eventually.of_forall (fun w => by positivity))

/-- **Morrey potential estimate** (Evans §5.6.2, step 2): for `n ≥ 2`,
    `∫_{B(0,r)} |u(x+z)−u(x)| dz ≤ (rⁿ/n) ∫_{B(0,r)} ‖Du(x+w)‖/‖w‖^{n-1} dw`. -/
theorem potential_estimate {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (hn : 2 ≤ n) (x : ℝⁿ) {r : ℝ}
    (hr : 0 < r) :
    ∫ z in Metric.ball (0:ℝⁿ) r, |u (x + z) - u x|
      ≤ (r ^ n / n) * ∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1) := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hgcont : Continuous (fun w : ℝⁿ => ‖w‖ * ‖fderiv ℝ u (x + w)‖) :=
    continuous_norm.mul (((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add continuous_id)).norm)
  have hg0 : (fun w : ℝⁿ => ‖w‖ * ‖fderiv ℝ u (x + w)‖) 0 = 0 := by simp
  have hRHSnn : 0 ≤ (r ^ n / n)
      * ∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1) := by
    refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_ball (fun w _ => by positivity))
  refine (potential_half hu x r).trans ?_
  have hchain : ENNReal.ofReal (∫ τ in Set.Ioc (0:ℝ) 1,
        τ ^ (-(n:ℝ) - 1) * ∫ w in Metric.ball (0:ℝⁿ) (τ * r), ‖w‖ * ‖fderiv ℝ u (x + w)‖)
      ≤ ENNReal.ofReal ((r ^ n / n)
        * ∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)) := by
    rw [bochner_eq_lint hu hn1 x hr]
    refine (lint_bound hgcont hg0 hn1 hr).trans_eq ?_
    rw [rhs_lint_eq hu hn1 x hr, Real.rpow_natCast]
  exact (ENNReal.ofReal_le_ofReal_iff hRHSnn).mp hchain

/-! ### Step 3: the Hölder step (`p > n`) — infrastructure -/

/-- **Hölder step** (Morrey step 3a): apply Hölder to the Riesz potential integrand
    `‖Du(x+w)‖/‖w‖^{n-1} = ‖Du(x+w)‖ · ‖w‖^{-(n-1)}`. -/
lemma riesz_holder {u : ℝⁿ → ℝ} (x : ℝⁿ) {r : ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : MemLp (fun w : ℝⁿ => ‖fderiv ℝ u (x + w)‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball 0 r)))
    (hg : MemLp (fun w : ℝⁿ => ‖w‖ ^ (-((n:ℝ) - 1))) (ENNReal.ofReal q)
      (volume.restrict (Metric.ball 0 r))) :
    ∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)
      ≤ (∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ ^ p) ^ (1 / p)
        * (∫ w in Metric.ball (0:ℝⁿ) r, (‖w‖ ^ (-((n:ℝ) - 1))) ^ q) ^ (1 / q) := by
  have hEq : ∀ w : ℝⁿ, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)
      = ‖fderiv ℝ u (x + w)‖ * ‖w‖ ^ (-((n:ℝ) - 1)) :=
    fun w => by rw [Real.rpow_neg (norm_nonneg w), div_eq_mul_inv]
  rw [setIntegral_congr_fun measurableSet_ball (fun w _ => hEq w)]
  exact integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun w => norm_nonneg _))
    (Filter.Eventually.of_forall (fun w => Real.rpow_nonneg (norm_nonneg w) _)) hf hg

/-- `‖Du(x+·)‖ ∈ L^p(B(0,r))` for any `p`: bounded-continuous on a finite-measure ball. -/
lemma memLp_fderiv_ball {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝⁿ) {r : ℝ} (hr : 0 < r)
    (p : ℝ≥0∞) :
    MemLp (fun w : ℝⁿ => ‖fderiv ℝ u (x + w)‖) p (volume.restrict (Metric.ball 0 r)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℝⁿ) r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hfcont : Continuous (fun w : ℝⁿ => ‖fderiv ℝ u (x + w)‖) :=
    ((hu.continuous_fderiv one_ne_zero).comp (continuous_const.add continuous_id)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℝⁿ) r).exists_bound_of_continuousOn hfcont.continuousOn
  refine MemLp.of_bound hfcont.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact hC w (Metric.ball_subset_closedBall hw)

/-- Kernel `MemLp`: `‖·‖^{-(n-1)} ∈ L^q(B(0,r))` when `(n-1)q < n` (⟺ `p > n`). -/
lemma memLp_kernel_ball (hn : 2 ≤ n) {q : ℝ} (hq0 : 0 < q) {r : ℝ} (hr : 0 < r)
    (hqn : ((n:ℝ) - 1) * q < n) :
    MemLp (fun w : ℝⁿ => ‖w‖ ^ (-((n:ℝ) - 1))) (ENNReal.ofReal q)
      (volume.restrict (Metric.ball 0 r)) := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hint : IntegrableOn (fun w : ℝⁿ => ‖w‖ ^ (-((n:ℝ) - 1) * q)) (Metric.ball 0 r) :=
    integrableOn_norm_rpow_ball hn1 (by linarith : -(n:ℝ) < -((n:ℝ) - 1) * q) hr
  refine ⟨Measurable.aestronglyMeasurable (by fun_prop), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.mpr hq0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
  have hpt : ∀ w : ℝⁿ, ‖‖w‖ ^ (-((n:ℝ) - 1))‖ₑ ^ q
      = ENNReal.ofReal (‖w‖ ^ (-((n:ℝ) - 1) * q)) := by
    intro w
    have hnn : (0:ℝ) ≤ ‖w‖ ^ (-((n:ℝ) - 1)) := Real.rpow_nonneg (norm_nonneg w) _
    rw [Real.rpow_mul (norm_nonneg w), ← ENNReal.ofReal_rpow_of_nonneg hnn hq0.le,
      Real.enorm_eq_ofReal hnn]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun w => Real.rpow_nonneg (norm_nonneg w) _))]
  exact ENNReal.ofReal_lt_top

/-- **Radial scaling** of `∫_B ‖w‖^s` under `w = r·v`: `∫_{B(0,r)}‖w‖^s = r^{n+s}∫_{B(0,1)}‖v‖^s`. -/
lemma ball_rpow_integral_scale (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ w in Metric.ball (0:ℝⁿ) r, ‖w‖ ^ s
      = r ^ ((n:ℝ) + s) * ∫ v in Metric.ball (0:ℝⁿ) 1, ‖v‖ ^ s := by
  have hkey := Measure.setIntegral_comp_smul_of_pos volume
    (fun w : ℝⁿ => ‖w‖ ^ s) (Metric.ball 0 1) hr
  rw [finrank_euclideanSpace_fin, smul_eq_mul, smul_ball hr.ne' (0:ℝⁿ) 1, smul_zero,
    Real.norm_eq_abs, abs_of_pos hr, mul_one] at hkey
  have hpt : ∀ v : ℝⁿ, ‖(r:ℝ) • v‖ ^ s = r ^ s * ‖v‖ ^ s := fun v => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Real.mul_rpow hr.le (norm_nonneg v)]
  simp_rw [hpt, integral_const_mul] at hkey
  have hrn : (r:ℝ) ^ n ≠ 0 := by positivity
  rw [Real.rpow_add hr, Real.rpow_natCast, eq_comm, mul_assoc, hkey, ← mul_assoc,
    mul_inv_cancel₀ hrn, one_mul]

/-- **Step 3 assembled**: the `p > n` Hölder bound with the `r^{1−n/p}` scaling.
    `∫_B ‖Du‖/‖w‖^{n-1} ≤ (∫_B ‖Du‖^p)^{1/p} · r^{1−n/p} · C` (`C` a `p`,`n`-dependent constant). -/
lemma riesz_bound {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (hn : 2 ≤ n) (x : ℝⁿ) {r : ℝ} (hr : 0 < r)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hqn : ((n:ℝ) - 1) * q < n) :
    ∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ / ‖w‖ ^ ((n:ℝ) - 1)
      ≤ (∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ ^ p) ^ (1 / p)
        * (r ^ (1 - (n:ℝ) / p)
          * (∫ v in Metric.ball (0:ℝⁿ) 1, ‖v‖ ^ (-((n:ℝ) - 1) * q)) ^ (1 / q)) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hpne : p ≠ 0 := hp0.ne'
  have hqne : q ≠ 0 := hq0.ne'
  have hconj : p⁻¹ + q⁻¹ = 1 := by have h := hpq.inv_add_inv_eq_inv; simpa using h
  refine (riesz_holder x hpq (memLp_fderiv_ball hu x hr _)
    (memLp_kernel_ball hn hq0 hr hqn)).trans (le_of_eq ?_)
  congr 1
  have hcongr : ∫ w in Metric.ball (0:ℝⁿ) r, (‖w‖ ^ (-((n:ℝ) - 1))) ^ q
      = ∫ w in Metric.ball (0:ℝⁿ) r, ‖w‖ ^ (-((n:ℝ) - 1) * q) :=
    setIntegral_congr_fun measurableSet_ball
      (fun w _ => (Real.rpow_mul (norm_nonneg w) _ _).symm)
  have hpqmul : p * q = p + q := by field_simp at hconj; linarith [hconj]
  have hexp : ((n:ℝ) + -((n:ℝ) - 1) * q) * (1 / q) = 1 - (n:ℝ) / p := by
    rw [mul_one_div]
    field_simp
    nlinarith [hpqmul, hp0, hq0]
  rw [hcongr, ball_rpow_integral_scale (-((n:ℝ) - 1) * q) hr,
    Real.mul_rpow (Real.rpow_nonneg hr.le _)
      (integral_nonneg (fun v => Real.rpow_nonneg (norm_nonneg v) _)),
    ← Real.rpow_mul hr.le, hexp]

/-! ### Step 4: toward the `C^{0,1−n/p}` statement -/

/-- Compose steps 2 + 3: `∫_B|u(x+z)−u(x)| ≤ (rⁿ/n)·(∫_B‖Du‖^p)^{1/p}·r^{1−n/p}·C`.
    The direct input to the two-point lens argument. -/
lemma potential_holder {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (hn : 2 ≤ n) (x : ℝⁿ) {r : ℝ}
    (hr : 0 < r) {p q : ℝ} (hpq : p.HolderConjugate q) (hqn : ((n:ℝ) - 1) * q < n) :
    ∫ z in Metric.ball (0:ℝⁿ) r, |u (x + z) - u x|
      ≤ (r ^ n / n) * ((∫ w in Metric.ball (0:ℝⁿ) r, ‖fderiv ℝ u (x + w)‖ ^ p) ^ (1 / p)
        * (r ^ (1 - (n:ℝ) / p)
          * (∫ v in Metric.ball (0:ℝⁿ) 1, ‖v‖ ^ (-((n:ℝ) - 1) * q)) ^ (1 / q))) :=
  (potential_estimate hu hn x hr).trans
    (mul_le_mul_of_nonneg_left (riesz_bound hu hn x hr hpq hqn) (by positivity))

end Morrey
