import MyProject.Sobolev.ExtensionOperator

/-!
# Sobolev extension operator (Evans §5.4) — the general `C¹`-domain operator

Continues `MyProject.Sobolev.ExtensionOperator`.  This file assembles the general bounded-`C¹`-domain
extension operator from the flat half-space operator and the boundary-flattening shear: the
restricted (subgraph → half-space) `W^{1,p}` chain rule, and the partition-of-unity gluing over a
finite boundary atlas of the domain.

The heavy mollification-based lemmas (e.g. `isWeakDerivInDir_test_contDiff1`) live here to keep
`ExtensionOperator.lean` fast to recompile.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff ENNReal Topology Convolution Manifold

namespace Sobolev

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Weak-derivative relation extends to `C¹` test functions.**  If `v` is the weak `e`-derivative
of `u` on the open set `U` (tested against `C^∞` functions), and `ψ` is merely `C¹` with compact
support in `U`, then the integration-by-parts identity `∫ u·∂ₑψ = −∫ v·ψ` still holds.  Proved by
mollifying `ψ` and passing to the limit. -/
theorem isWeakDerivInDir_test_contDiff1 {U : Set ℝⁿ} (hU : IsOpen U) {e : ℝⁿ} {u v : ℝⁿ → ℝ}
    (hw : IsWeakDerivInDir U e u v) (huloc : LocallyIntegrable u volume)
    (hvloc : LocallyIntegrable v volume) {ψ : ℝⁿ → ℝ}
    (hψcd : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) (hψsub : tsupport ψ ⊆ U) :
    ∫ x, u x * fderiv ℝ ψ x e = -∫ x, v x * ψ x := by
  classical
  haveI : IsLocallyFiniteMeasure (volume : Measure ℝⁿ) := by infer_instance
  haveI : (volume : Measure ℝⁿ).IsOpenPosMeasure := by infer_instance
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hψcs.exists_cthickening_subset_open hU hψsub
  set K : Set ℝⁿ := Metric.cthickening δ₀ (tsupport ψ) with hKdef
  have hKcpt : IsCompact K := hψcs.cthickening
  have hψcont : Continuous ψ := hψcd.continuous
  set φ : ℕ → ContDiffBump (0 : ℝⁿ) := fun m =>
    { rIn := δ₀ / (2 * ((m : ℝ) + 2)), rOut := δ₀ / ((m : ℝ) + 2), rIn_pos := by positivity,
      rIn_lt_rOut := by
        rw [show δ₀ / (2 * ((m : ℝ) + 2)) = (δ₀ / ((m : ℝ) + 2)) / 2 by
          rw [div_div, mul_comm 2 ((m : ℝ) + 2)]]
        exact half_lt_self (by positivity) } with hφdef
  set ρ : ℕ → ℝⁿ → ℝ := fun m => (φ m).normed volume with hρdef
  set ψm : ℕ → ℝⁿ → ℝ :=
    fun m => ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ with hψmdef
  have hρcd : ∀ m, ContDiff ℝ ∞ (ρ m) := fun m => (φ m).contDiff_normed
  have hρcs : ∀ m, HasCompactSupport (ρ m) := fun m => (φ m).hasCompactSupport_normed
  have hψmcd : ∀ m, ContDiff ℝ ∞ (ψm m) := fun m =>
    (hρcs m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρcd m)
      hψcont.locallyIntegrable
  have hrle : ∀ m, (φ m).rOut ≤ δ₀ := fun m => by
    have hr : (φ m).rOut = δ₀ / ((m : ℝ) + 2) := rfl
    rw [hr, div_le_iff₀ (by positivity)]
    nlinarith [hδ₀pos.le, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  have hψm_tsub : ∀ m, tsupport (ψm m) ⊆ K := fun m => by
    refine closure_minimal (fun z hz => ?_) hKcpt.isClosed
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Set.mem_add.1 (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hz)
    have haball : ‖a‖ < (φ m).rOut := by
      have ha' : a ∈ Function.support ((φ m).normed volume) := ha
      rw [(φ m).support_normed_eq] at ha'
      simpa [Metric.mem_ball] using ha'
    rw [hKdef]
    refine Metric.mem_cthickening_of_dist_le (a + b) b δ₀ (tsupport ψ)
      (subset_tsupport ψ hb) ?_
    calc dist (a + b) b = ‖a‖ := by rw [dist_eq_norm]; simp
      _ ≤ δ₀ := haball.le.trans (hrle m)
  have hψmcs : ∀ m, HasCompactSupport (ψm m) := fun m =>
    HasCompactSupport.intro hKcpt (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hψm_tsub m h)))
  have identity : ∀ m, ∫ x, u x * fderiv ℝ (ψm m) x e = -∫ x, v x * ψm m x := fun m =>
    hw (ψm m) ⟨hψmcd m, hψmcs m, (hψm_tsub m).trans hδ₀⟩
  have hderiv : ∀ m x, fderiv ℝ (ψm m) x e
      = (ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => fderiv ℝ ψ y e)) x := by
    intro m x
    rw [fderiv_convolution_apply (hρcd m) (hρcs m) hψcont.locallyIntegrable x e]
    exact convolution_deriv_eq (hρcd m) (hρcs m) e
      (isWeakDerivInDir_of_contDiff Set.univ e hψcd) x
  -- radius → 0
  have hrOut : Tendsto (fun m => (φ m).rOut) atTop (𝓝 (0 : ℝ)) := by
    have hr : ∀ m, (φ m).rOut = δ₀ / ((m : ℝ) + 2) := fun _ => rfl
    simp only [hr]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hdψcont : Continuous (fun y => fderiv ℝ ψ y e) :=
    (hψcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdψcs : HasCompactSupport (fun y => fderiv ℝ ψ y e) :=
    HasCompactSupport.intro hψcs.isCompact (fun x hx => by
      rw [(notMem_tsupport_iff_eventuallyEq.1 hx).fderiv_eq]; simp)
  -- global bound for a continuous compactly-supported function
  have hgbound : ∀ f : ℝⁿ → ℝ, Continuous f → HasCompactSupport f →
      ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
    intro f hfc hfcs
    obtain ⟨C, hC⟩ := hfcs.isCompact.exists_bound_of_continuousOn hfc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · rw [← Real.norm_eq_abs]; exact (hC x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  obtain ⟨C₁, hC₁0, hC₁⟩ := hgbound _ hdψcont hdψcs
  obtain ⟨C₂, hC₂0, hC₂⟩ := hgbound ψ hψcont hψcs
  -- convolution against a globally bounded function stays bounded by the same constant
  have hconv_bound : ∀ (f : ℝⁿ → ℝ) (Cf : ℝ), Continuous f → 0 ≤ Cf → (∀ y, |f y| ≤ Cf) →
      ∀ m x, |(ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x| ≤ Cf := by
    intro f Cf hfc hCf0 hf m x
    simp only [hρdef]
    rw [convolution_def]
    have hcont1 : Continuous (fun t => |(φ m).normed volume t| * |f (x - t)|) :=
      (((φ m).contDiff_normed (n := 1)).continuous.abs).mul
        ((hfc.comp (continuous_const.sub continuous_id)).abs)
    have hint1 : Integrable (fun t => |(φ m).normed volume t| * |f (x - t)|) volume :=
      hcont1.integrable_of_hasCompactSupport ((φ m).hasCompactSupport_normed.abs.mul_right)
    have hint2 : Integrable (fun t => (φ m).normed volume t * Cf) volume :=
      (((φ m).contDiff_normed (n := 1)).continuous.integrable_of_hasCompactSupport
        (φ m).hasCompactSupport_normed).mul_const Cf
    calc |∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).normed volume t) (f (x - t))|
        ≤ ∫ t, |(φ m).normed volume t| * |f (x - t)| := by
          refine abs_integral_le_integral_abs.trans (le_of_eq (integral_congr_ae
            (Eventually.of_forall fun t => ?_)))
          simp [abs_mul]
      _ ≤ ∫ t, (φ m).normed volume t * Cf := by
          refine integral_mono_ae hint1 hint2 (Eventually.of_forall fun t => ?_)
          dsimp only
          rw [abs_of_nonneg ((φ m).nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left (hf _) ((φ m).nonneg_normed t)
      _ = Cf := by rw [integral_mul_const, (φ m).integral_normed, one_mul]
  -- pointwise convergence of values and derivatives
  have hconvψ : ∀ x, Tendsto (fun m => ψm m x) atTop (𝓝 (ψ x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hrOut hψcont x
  have hconvdψ : ∀ x, Tendsto (fun m => fderiv ℝ (ψm m) x e) atTop (𝓝 (fderiv ℝ ψ x e)) := by
    intro x
    refine Filter.Tendsto.congr (fun m => (hderiv m x).symm) ?_
    exact ContDiffBump.convolution_tendsto_right_of_continuous hrOut hdψcont x
  -- supports of `ψm m` and its derivative lie in `K`
  have hdψm0 : ∀ m x, x ∉ K → fderiv ℝ (ψm m) x e = 0 := by
    intro m x hx
    have : x ∉ tsupport (ψm m) := fun h => hx (hψm_tsub m h)
    rw [(notMem_tsupport_iff_eventuallyEq.1 this).fderiv_eq]; simp
  have hψm0 : ∀ m x, x ∉ K → ψm m x = 0 := fun m x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hψm_tsub m h))
  -- integrable dominating profiles
  have hdomu : Integrable (fun x => C₁ * K.indicator (fun x => |u x|) x) volume :=
    (((integrable_indicator_iff hKcpt.measurableSet).2
      ((huloc.integrableOn_isCompact hKcpt).abs))).const_mul C₁
  have hdomv : Integrable (fun x => C₂ * K.indicator (fun x => |v x|) x) volume :=
    (((integrable_indicator_iff hKcpt.measurableSet).2
      ((hvloc.integrableOn_isCompact hKcpt).abs))).const_mul C₂
  -- DCT on both sides
  have hL : Tendsto (fun m => ∫ x, u x * fderiv ℝ (ψm m) x e) atTop
      (𝓝 (∫ x, u x * fderiv ℝ ψ x e)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => C₁ * K.indicator (fun x => |u x|) x) (fun m => ?_) hdomu (fun m => ?_)
      (Eventually.of_forall fun x => (hconvdψ x).const_mul (u x))
    · exact huloc.aestronglyMeasurable.mul
        (((hψmcd m).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      dsimp only
      by_cases hx : x ∈ K
      · rw [Real.norm_eq_abs, abs_mul, Set.indicator_of_mem hx, hderiv m x, mul_comm C₁]
        exact mul_le_mul_of_nonneg_left (hconv_bound _ C₁ hdψcont hC₁0 hC₁ m x) (abs_nonneg _)
      · rw [hdψm0 m x hx, mul_zero, Set.indicator_of_notMem hx, mul_zero]
        exact le_of_eq (by simp)
  have hR : Tendsto (fun m => ∫ x, v x * ψm m x) atTop (𝓝 (∫ x, v x * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => C₂ * K.indicator (fun x => |v x|) x) (fun m => ?_) hdomv (fun m => ?_)
      (Eventually.of_forall fun x => (hconvψ x).const_mul (v x))
    · exact hvloc.aestronglyMeasurable.mul (hψmcd m).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      dsimp only
      by_cases hx : x ∈ K
      · rw [Real.norm_eq_abs, abs_mul, Set.indicator_of_mem hx, mul_comm C₂]
        exact mul_le_mul_of_nonneg_left (hconv_bound ψ C₂ hψcont hC₂0 hC₂ m x) (abs_nonneg _)
      · rw [hψm0 m x hx, mul_zero, Set.indicator_of_notMem hx, mul_zero]
        exact le_of_eq (by simp)
  have := hR.neg
  simp_rw [← identity] at this
  exact tendsto_nhds_unique hL this



/-- **The crux, generalized to `C¹` test functions.**  Same as `weakDeriv_mul_indep` but `ψ` is
only `C¹` (using `isWeakDerivInDir_test_contDiff1` for the mollified test function). -/
theorem weakDeriv_mul_indep_contDiff1 {U : Set ℝⁿ} (hU : IsOpen U) {i : Fin n} {w wi h : ℝⁿ → ℝ}
    (hw : IsWeakDerivInDir U (EuclideanSpace.single i (1 : ℝ)) w wi)
    (hwloc : LocallyIntegrable w volume) (hwiloc : LocallyIntegrable wi volume)
    (hh : Continuous h)
    (hhindep : ∀ (y : ℝⁿ) (t : ℝ), h (y + t • EuclideanSpace.single i (1 : ℝ)) = h y)
    {ψ : ℝⁿ → ℝ} (hψcd : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) (hψsub : tsupport ψ ⊆ U) :
    ∫ x, w x * (h x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x, wi x * (h x * ψ x) := by
  classical
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  -- the mollifier family, radius `1/(m+1) → 0`
  set φ : ℕ → ContDiffBump (0 : ℝⁿ) := fun m =>
    { rIn := 1 / (m + 2), rOut := 1 / (m + 1), rIn_pos := by positivity,
      rIn_lt_rOut := by
        apply one_div_lt_one_div_of_lt <;> [positivity; · push_cast; linarith] } with hφdef
  set hm : ℕ → ℝⁿ → ℝ :=
    fun m => (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h with hmdef
  have hmcd : ∀ m, ContDiff ℝ ∞ (hm m) := fun m =>
    (φ m).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ m).contDiff_normed (hh.locallyIntegrable (μ := volume))
  have hm_fderiv0 : ∀ m x, fderiv ℝ (hm m) x eᵢ = 0 := by
    intro m x
    have hind : ∀ (y : ℝⁿ) (t : ℝ), hm m (y + t • EuclideanSpace.single i (1 : ℝ)) = hm m y := by
      intro y t; rw [hmdef]; exact convolution_indep hhindep t y
    exact fderiv_single_eq_zero_of_indep ((hmcd m).of_le (by norm_num)) hind x
  -- per-`m`: `hm m · ψ` is a test function, and IBP gives the identity
  have identity : ∀ m, ∫ x, w x * (hm m x * fderiv ℝ ψ x eᵢ)
      = -∫ x, wi x * (hm m x * ψ x) := by
    intro m
    have key := isWeakDerivInDir_test_contDiff1 hU hw hwloc hwiloc
      (((hmcd m).of_le (by norm_num)).mul hψcd) hψcs.mul_left
      (tsupport_mul_subset_right.trans hψsub)
    have hfd : ∀ x, fderiv ℝ (fun x => hm m x * ψ x) x eᵢ = hm m x * fderiv ℝ ψ x eᵢ := by
      intro x
      have h1 : HasFDerivAt (hm m) (fderiv ℝ (hm m) x) x :=
        ((hmcd m).differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h2 : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
        (hψcd.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hHF : HasFDerivAt (fun x => hm m x * ψ x)
          (hm m x • fderiv ℝ ψ x + ψ x • fderiv ℝ (hm m) x) x := h1.mul h2
      rw [hHF.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        hm_fderiv0 m x, mul_zero, add_zero]
    calc ∫ x, w x * (hm m x * fderiv ℝ ψ x eᵢ)
        = ∫ x, w x * fderiv ℝ (fun x => hm m x * ψ x) x eᵢ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only [hfd]
      _ = -∫ x, wi x * (hm m x * ψ x) := key
  -- pass to the limit as the mollifier radius → 0
  have hrOut : Tendsto (fun m => (φ m).rOut) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv : ∀ x, Tendsto (fun m => hm m x) atTop (𝓝 (h x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hrOut hh x
  -- a ball containing `tsupport ψ`, and a uniform bound `C` on `|h|` over its `1`-enlargement
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hψcs.isBounded
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝⁿ) (R + 1)).exists_bound_of_continuousOn
    hh.continuousOn
  -- `|hm m x| ≤ C` on `closedBall 0 R`
  have hnormed_cont : ∀ m, Continuous ((φ m).normed volume) := fun m =>
    ((φ m).contDiff_normed (n := 1)).continuous
  have hnormed_int : ∀ m, Integrable ((φ m).normed volume) volume := fun m =>
    (hnormed_cont m).integrable_of_hasCompactSupport (φ m).hasCompactSupport_normed
  have hbound_hm : ∀ m x, x ∈ Metric.closedBall (0 : ℝⁿ) R → |hm m x| ≤ C := by
    intro m x hx
    rw [Metric.mem_closedBall] at hx
    have hrle : (φ m).rOut ≤ 1 := by
      have h1 : (φ m).rOut = 1 / ((m : ℝ) + 1) := rfl
      rw [h1, div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hLHSint : Integrable (fun t => |(φ m).normed volume t| * |h (x - t)|) volume :=
      Continuous.integrable_of_hasCompactSupport
        ((hnormed_cont m).abs.mul ((hh.comp (continuous_const.sub continuous_id)).abs))
        (((φ m).hasCompactSupport_normed.abs).mul_right)
    have hpt : ∀ t, |(φ m).normed volume t| * |h (x - t)| ≤ (φ m).normed volume t * C := by
      intro t
      rcases eq_or_ne ((φ m).normed volume t) 0 with h0 | h0
      · simp [h0]
      · rw [abs_of_nonneg ((φ m).nonneg_normed t)]
        refine mul_le_mul_of_nonneg_left ?_ ((φ m).nonneg_normed t)
        have ht : dist t 0 < (φ m).rOut := by
          have hts := Function.mem_support.2 h0
          rw [(φ m).support_normed_eq] at hts
          simpa [Metric.mem_ball] using hts
        refine hC (x - t) ?_
        rw [Metric.mem_closedBall]
        calc dist (x - t) 0 = ‖x - t‖ := by rw [dist_zero_right]
          _ ≤ ‖x‖ + ‖t‖ := norm_sub_le x t
          _ = dist x 0 + dist t 0 := by rw [dist_zero_right, dist_zero_right]
          _ ≤ R + 1 := add_le_add hx (le_of_lt (ht.trans_le hrle))
    simp only [hmdef]; rw [convolution_def]
    calc |∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).normed volume t) (h (x - t))|
        ≤ ∫ t, |(φ m).normed volume t| * |h (x - t)| := by
          refine abs_integral_le_integral_abs.trans (le_of_eq (integral_congr_ae
            (Eventually.of_forall fun t => ?_)))
          simp [abs_mul]
      _ ≤ ∫ t, (φ m).normed volume t * C :=
          integral_mono_ae hLHSint ((hnormed_int m).mul_const _) (Eventually.of_forall hpt)
      _ = C := by rw [integral_mul_const, (φ m).integral_normed, one_mul]
  -- `∂ᵢψ` is continuous with compact support inside the ball
  have hdψcont : Continuous (fun x => fderiv ℝ ψ x eᵢ) :=
    (hψcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdψcs : HasCompactSupport (fun x => fderiv ℝ ψ x eᵢ) :=
    HasCompactSupport.intro hψcs (fun x hx => by
      rw [(notMem_tsupport_iff_eventuallyEq.1 hx).fderiv_eq]; simp)
  have hdψ0 : ∀ x, fderiv ℝ ψ x eᵢ ≠ 0 → x ∈ Metric.closedBall (0 : ℝⁿ) R := by
    intro x hx; refine hR ?_; by_contra hc
    exact hx (by rw [(notMem_tsupport_iff_eventuallyEq.1 hc).fderiv_eq]; simp)
  have hψ0 : ∀ x, ψ x ≠ 0 → x ∈ Metric.closedBall (0 : ℝⁿ) R := fun x hx =>
    hR (subset_tsupport ψ hx)
  have hint_wdψ : Integrable (fun x => w x * fderiv ℝ ψ x eᵢ) volume := by
    simpa only [smul_eq_mul] using
      hwloc.integrable_smul_right_of_hasCompactSupport hdψcont hdψcs
  have hint_wiψ : Integrable (fun x => wi x * ψ x) volume := by
    simpa only [smul_eq_mul] using
      hwiloc.integrable_smul_right_of_hasCompactSupport hψcd.continuous hψcs
  -- the two dominated-convergence limits
  have hL : Tendsto (fun m => ∫ x, w x * (hm m x * fderiv ℝ ψ x eᵢ)) atTop
      (𝓝 (∫ x, w x * (h x * fderiv ℝ ψ x eᵢ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => C * |w x * fderiv ℝ ψ x eᵢ|) (fun m => ?_) (hint_wdψ.abs.const_mul C)
      (fun m => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact hwloc.aestronglyMeasurable.mul
        ((hmcd m).continuous.aestronglyMeasurable.mul hdψcont.aestronglyMeasurable)
    · by_cases h0 : fderiv ℝ ψ x eᵢ = 0
      · simp [h0]
      · have hb := hbound_hm m x (hdψ0 x h0)
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc |w x| * (|hm m x| * |fderiv ℝ ψ x eᵢ|)
            = |hm m x| * (|w x| * |fderiv ℝ ψ x eᵢ|) := by ring
          _ ≤ C * (|w x| * |fderiv ℝ ψ x eᵢ|) := by
              exact mul_le_mul_of_nonneg_right hb (by positivity)
          _ = C * |w x * fderiv ℝ ψ x eᵢ| := by rw [abs_mul]
    · exact ((hconv x).mul_const _).const_mul (w x)
  have hRlim : Tendsto (fun m => ∫ x, wi x * (hm m x * ψ x)) atTop
      (𝓝 (∫ x, wi x * (h x * ψ x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => C * |wi x * ψ x|) (fun m => ?_) (hint_wiψ.abs.const_mul C)
      (fun m => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact hwiloc.aestronglyMeasurable.mul
        ((hmcd m).continuous.aestronglyMeasurable.mul hψcd.continuous.aestronglyMeasurable)
    · by_cases h0 : ψ x = 0
      · simp [h0]
      · have hb := hbound_hm m x (hψ0 x h0)
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc |wi x| * (|hm m x| * |ψ x|)
            = |hm m x| * (|wi x| * |ψ x|) := by ring
          _ ≤ C * (|wi x| * |ψ x|) := mul_le_mul_of_nonneg_right hb (by positivity)
          _ = C * |wi x * ψ x| := by rw [abs_mul]
    · exact ((hconv x).mul_const _).const_mul (wi x)
  -- combine: `identity` says the two sequences are negatives of each other
  have hL2 : Tendsto (fun m => ∫ x, w x * (hm m x * fderiv ℝ ψ x eᵢ)) atTop
      (𝓝 (-∫ x, wi x * (h x * ψ x))) := by
    have := hRlim.neg
    simp_rw [← identity] at this
    exact this
  exact tendsto_nhds_unique hL hL2

end Sobolev
