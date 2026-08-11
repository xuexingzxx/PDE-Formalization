import MyProject.Sobolev.ExtensionOperator
import MyProject.Common.AreaFormula

/-!
# Sobolev extension operator (Evans §5.4) — the general `C¹`-domain operator

Continues `MyProject.Sobolev.ExtensionOperator`.  This file assembles the general bounded-`C¹`-domain
extension operator from the flat half-space operator and the boundary-flattening shear: the
restricted (subgraph → half-space) `W^{1,p}` chain rule, and the partition-of-unity gluing over a
finite boundary atlas of the domain.

The heavy mollification-based lemmas (e.g. `isWeakDerivInDir_test_contDiff1`) live here to keep
`ExtensionOperator.lean` fast to recompile.
-/

open MeasureTheory Filter AreaFormula
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


/-- `∂ⱼγ` is itself independent of coordinate `i` (differentiate `hindep` in `j`). -/
theorem fderiv_indep_of_indep {γ : ℝⁿ → ℝ} {i : Fin n} (hγ : ContDiff ℝ 1 γ)
    (hindep : ∀ (y : ℝⁿ) (t : ℝ), γ (y + t • EuclideanSpace.single i (1 : ℝ)) = γ y)
    (j : Fin n) (y : ℝⁿ) (t : ℝ) :
    fderiv ℝ γ (y + t • EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
      = fderiv ℝ γ y (EuclideanSpace.single j (1 : ℝ)) := by
  have hcomp : (fun z => γ (z + t • EuclideanSpace.single i (1 : ℝ))) = γ := funext fun z =>
    hindep z t
  have h1 : HasFDerivAt (fun z => γ (z + t • EuclideanSpace.single i (1 : ℝ)))
      ((fderiv ℝ γ (y + t • EuclideanSpace.single i (1 : ℝ))).comp
        (ContinuousLinearMap.id ℝ ℝⁿ)) y := by
    have hg : HasFDerivAt γ (fderiv ℝ γ (y + t • EuclideanSpace.single i (1 : ℝ)))
        (y + t • EuclideanSpace.single i (1 : ℝ)) :=
      (hγ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    exact hg.comp y ((hasFDerivAt_id y).add_const _)
  rw [hcomp] at h1
  have h2 : HasFDerivAt γ (fderiv ℝ γ y) y :=
    (hγ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have := h1.unique h2
  rw [← this]; simp

/-- **Restricted chain rule (weak-derivative relation) for the shear.**  If `u` has weak `eⱼ`- and
`eᵢ`-derivatives `vⱼ, vᵢ` on the open set `W`, then `u ∘ Ψ` (`Ψ = shearEquiv`) has weak
`eⱼ`-derivative `vⱼ∘Ψ + (∂ⱼγ)·(vᵢ∘Ψ)` on `Ψ⁻¹(W)`. -/
theorem isWeakDerivInDir_comp_shearEquiv {W : Set ℝⁿ} (hW : IsOpen W) {γ : ℝⁿ → ℝ} {i j : Fin n}
    (hindep : ∀ (y : ℝⁿ) (t : ℝ), γ (y + t • EuclideanSpace.single i (1 : ℝ)) = γ y)
    (hγ : ContDiff ℝ 1 γ) {u vⱼ vᵢ : ℝⁿ → ℝ}
    (huloc : LocallyIntegrable u volume) (hvⱼloc : LocallyIntegrable vⱼ volume)
    (hvᵢloc : LocallyIntegrable vᵢ volume)
    (hwⱼ : IsWeakDerivInDir W (EuclideanSpace.single j (1 : ℝ)) u vⱼ)
    (hwᵢ : IsWeakDerivInDir W (EuclideanSpace.single i (1 : ℝ)) u vᵢ) :
    IsWeakDerivInDir (shearEquiv hindep ⁻¹' W) (EuclideanSpace.single j (1 : ℝ))
      (fun z => u (shearEquiv hindep z))
      (fun z => vⱼ (shearEquiv hindep z) +
        fderiv ℝ γ z (EuclideanSpace.single j (1 : ℝ)) * vᵢ (shearEquiv hindep z)) := by
  intro φ hφ
  obtain ⟨hφcd, hφcs, hφsub⟩ := hφ
  set Ψ := shearEquiv hindep with hΨdef
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  have hΨmp : MeasurePreserving (Ψ : ℝⁿ → ℝⁿ) volume volume :=
    measurePreserving_shearEquiv hindep hγ
  have hΨcont : Continuous (Ψ : ℝⁿ → ℝⁿ) := continuous_id.add (hγ.continuous.smul continuous_const)
  have hΨsymm_cont : Continuous (Ψ.symm : ℝⁿ → ℝⁿ) :=
    continuous_id.add (hγ.neg.continuous.smul continuous_const)
  have hΨme : MeasurableEmbedding (Ψ : ℝⁿ → ℝⁿ) :=
    (⟨shearEquiv hindep, hΨcont, hΨsymm_cont⟩ : Homeomorph ℝⁿ ℝⁿ).measurableEmbedding
  set ψ : ℝⁿ → ℝ := fun y => φ (Ψ.symm y) with hψdef
  have hΨsymm_cd : ContDiff ℝ 1 (Ψ.symm : ℝⁿ → ℝⁿ) :=
    contDiff_id.add (hγ.neg.smul contDiff_const)
  have hψcd : ContDiff ℝ 1 ψ := (hφcd.of_le (by norm_num)).comp hΨsymm_cd
  have hImg_cpt : IsCompact (Ψ '' tsupport φ) := hφcs.isCompact.image hΨcont
  have hsupp_sub : Function.support ψ ⊆ Ψ '' tsupport φ := fun y hy =>
    ⟨Ψ.symm y, subset_tsupport φ hy, Ψ.apply_symm_apply y⟩
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.intro hImg_cpt
      (fun x hx => not_not.1 fun hne => hx (hsupp_sub (Function.mem_support.2 hne)))
  have hψsub : tsupport ψ ⊆ W :=
    (closure_minimal hsupp_sub hImg_cpt.isClosed).trans
      ((Set.image_mono hφsub).trans (le_of_eq (Set.image_preimage_eq W Ψ.surjective)))
  -- `φ = ψ ∘ Ψ`, so the chain rule gives `∂ⱼφ`
  have hφfun : φ = fun z => ψ (Ψ z) := funext fun z => by
    simp only [hψdef, Equiv.symm_apply_apply]
  have hchain : ∀ z, fderiv ℝ φ z eⱼ
      = fderiv ℝ ψ (Ψ z) eⱼ + fderiv ℝ γ z eⱼ * fderiv ℝ ψ (Ψ z) eᵢ := by
    intro z
    conv_lhs => rw [hφfun]
    exact fderiv_comp_shearMap_single ψ γ i j hψcd hγ z
  -- change of variables + the two identities
  have hcov : ∫ z, u (Ψ z) * fderiv ℝ φ z eⱼ
      = ∫ y, u y * (fderiv ℝ ψ y eⱼ + fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ) := by
    rw [← hΨmp.integral_comp hΨme
      (fun y => u y * (fderiv ℝ ψ y eⱼ + fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ))]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hchain z, show fderiv ℝ γ z eⱼ = fderiv ℝ γ (Ψ z) eⱼ from
      (fderiv_indep_of_indep hγ hindep j z (γ z)).symm]
  have hA : ∫ y, u y * fderiv ℝ ψ y eⱼ = -∫ y, vⱼ y * ψ y :=
    isWeakDerivInDir_test_contDiff1 hW hwⱼ huloc hvⱼloc hψcd hψcs hψsub
  have hB : ∫ y, u y * (fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ)
      = -∫ y, vᵢ y * (fderiv ℝ γ y eⱼ * ψ y) :=
    weakDeriv_mul_indep_contDiff1 hW hwᵢ huloc hvᵢloc
      ((hγ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (fun y t => fderiv_indep_of_indep hγ hindep j y t) hψcd hψcs hψsub
  -- continuity / compact support of the derivative factors
  have hdψcont : ∀ k : Fin n, Continuous (fun y => fderiv ℝ ψ y (EuclideanSpace.single k (1 : ℝ))) :=
    fun k => (hψcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdψcs : ∀ k : Fin n, HasCompactSupport
      (fun y => fderiv ℝ ψ y (EuclideanSpace.single k (1 : ℝ))) := fun k =>
    HasCompactSupport.intro hψcs.isCompact (fun x hx => by
      rw [(notMem_tsupport_iff_eventuallyEq.1 hx).fderiv_eq]; simp)
  have hγⱼcont : Continuous (fun y => fderiv ℝ γ y eⱼ) :=
    (hγ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsplit : ∫ y, u y * (fderiv ℝ ψ y eⱼ + fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ)
      = -∫ y, (vⱼ y + fderiv ℝ γ y eⱼ * vᵢ y) * ψ y := by
    have hIA : Integrable (fun y => u y * fderiv ℝ ψ y eⱼ) volume := by
      simpa only [smul_eq_mul] using
        huloc.integrable_smul_right_of_hasCompactSupport (hdψcont j) (hdψcs j)
    have hIB : Integrable (fun y => u y * (fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ)) volume := by
      simpa only [smul_eq_mul] using huloc.integrable_smul_right_of_hasCompactSupport
        (hγⱼcont.mul (hdψcont i)) ((hdψcs i).mul_left)
    have hIvⱼ : Integrable (fun y => vⱼ y * ψ y) volume := by
      simpa only [smul_eq_mul] using
        hvⱼloc.integrable_smul_right_of_hasCompactSupport hψcd.continuous hψcs
    have hIvᵢ : Integrable (fun y => vᵢ y * (fderiv ℝ γ y eⱼ * ψ y)) volume := by
      simpa only [smul_eq_mul] using hvᵢloc.integrable_smul_right_of_hasCompactSupport
        (hγⱼcont.mul hψcd.continuous) (hψcs.mul_left)
    rw [show (fun y => u y * (fderiv ℝ ψ y eⱼ + fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ))
        = fun y => u y * fderiv ℝ ψ y eⱼ + u y * (fderiv ℝ γ y eⱼ * fderiv ℝ ψ y eᵢ) from
        funext fun y => by ring, integral_add hIA hIB, hA, hB,
      show (fun y => (vⱼ y + fderiv ℝ γ y eⱼ * vᵢ y) * ψ y)
        = fun y => vⱼ y * ψ y + vᵢ y * (fderiv ℝ γ y eⱼ * ψ y) from funext fun y => by ring,
      integral_add hIvⱼ hIvᵢ]
    ring
  rw [show (fun z => vⱼ (Ψ z) + fderiv ℝ γ z eⱼ * vᵢ (Ψ z)) = _ from rfl]
  rw [hcov, hsplit]
  rw [← hΨmp.integral_comp hΨme (fun y => (vⱼ y + fderiv ℝ γ y eⱼ * vᵢ y) * ψ y)]
  refine congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun z => ?_))
  simp only [hψdef, Equiv.symm_apply_apply]
  rw [show fderiv ℝ γ (Ψ z) eⱼ = fderiv ℝ γ z eⱼ from
    fderiv_indep_of_indep hγ hindep j z (γ z)]



/-- **Restricted linear change of variables for the weak-derivative relation.**  If `v` is the weak
`(L e)`-derivative of `u` on the open set `W`, then `u ∘ L` has weak `e`-derivative `v ∘ L` on
`L ⁻¹' W`. -/
theorem isWeakDerivInDir_comp_linear_restrict (L : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ) {W : Set ℝⁿ} (hW : IsOpen W)
    (e : ℝⁿ) {u v : ℝⁿ → ℝ} (h : IsWeakDerivInDir W (L e) u v) :
    IsWeakDerivInDir (L ⁻¹' W) e (fun x => u (L x)) (fun x => v (L x)) := by
  intro φ hφ
  obtain ⟨hφcd, hφcs, hφsub⟩ := hφ
  have hLmp : MeasurePreserving (L : ℝⁿ → ℝⁿ) volume volume := L.measurePreserving
  have hLme : MeasurableEmbedding (L : ℝⁿ → ℝⁿ) := L.toHomeomorph.measurableEmbedding
  have hinvsymm : ∀ x, L.symm (L x) = x := L.symm_apply_apply
  set ψ : ℝⁿ → ℝ := fun z => φ (L.symm z) with hψdef
  -- `ψ = φ ∘ L.symm` is a test function on `W`
  have hsupp_sub : Function.support ψ ⊆ L '' tsupport φ := fun y hy =>
    ⟨L.symm y, subset_tsupport φ hy, L.apply_symm_apply y⟩
  have hImg_cpt : IsCompact (L '' tsupport φ) := hφcs.isCompact.image L.continuous
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.intro hImg_cpt
      (fun x hx => not_not.1 fun hne => hx (hsupp_sub (Function.mem_support.2 hne)))
  have hψsub : tsupport ψ ⊆ W :=
    (closure_minimal hsupp_sub hImg_cpt.isClosed).trans
      ((Set.image_mono hφsub).trans (le_of_eq (Set.image_preimage_eq W L.surjective)))
  have hψtest : IsTestFunction W ψ :=
    ⟨hφcd.comp L.symm.toContinuousLinearEquiv.contDiff, hψcs, hψsub⟩
  -- chain rule: `∂_e φ` at `L.symm y` equals `∂_{L e}ψ` at `y`
  have hpt : ∀ y, fderiv ℝ φ (L.symm y) e = fderiv ℝ ψ y (L e) := by
    intro y
    have hcomp : HasFDerivAt ψ
        ((fderiv ℝ φ (L.symm y)).comp (L.symm.toContinuousLinearEquiv : ℝⁿ →L[ℝ] ℝⁿ)) y :=
      (hφcd.differentiable (by norm_num) (L.symm y)).hasFDerivAt.comp y
        L.symm.toContinuousLinearEquiv.hasFDerivAt
    rw [hψdef, hcomp.fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ φ (L.symm y) e = fderiv ℝ φ (L.symm y) (L.symm (L e))
    rw [hinvsymm e]
  -- change variables `x = L.symm y` on both sides
  have hcovL : ∫ x, u (L x) * fderiv ℝ φ x e = ∫ y, u y * fderiv ℝ φ (L.symm y) e := by
    have key := hLmp.integral_comp hLme (fun y => u y * fderiv ℝ φ (L.symm y) e)
    simp only [hinvsymm] at key; exact key
  have hcovR : ∫ x, v (L x) * φ x = ∫ y, v y * φ (L.symm y) := by
    have key := hLmp.integral_comp hLme (fun y => v y * φ (L.symm y))
    simp only [hinvsymm] at key; exact key
  rw [hcovL,
    show (∫ y, u y * fderiv ℝ φ (L.symm y) e) = ∫ y, u y * fderiv ℝ ψ y (L e) from
      integral_congr_ae (Eventually.of_forall (fun y => by dsimp only; rw [hpt y])),
    h ψ hψtest, ← hcovR]

/-- **Restricted translation change of variables for the weak-derivative relation.**  If `v` is the
weak `e`-derivative of `u` on the open set `W`, then `u(· + t)` has weak `e`-derivative `v(· + t)`
on `W - t = (· + t) ⁻¹' W`. -/
theorem isWeakDerivInDir_comp_translate_restrict (t : ℝⁿ) {W : Set ℝⁿ} (hW : IsOpen W)
    (e : ℝⁿ) {u v : ℝⁿ → ℝ} (h : IsWeakDerivInDir W e u v) :
    IsWeakDerivInDir ((fun x => x + t) ⁻¹' W) e (fun x => u (x + t)) (fun x => v (x + t)) := by
  intro φ hφ
  obtain ⟨hφcd, hφcs, hφsub⟩ := hφ
  have htmp : MeasurePreserving (fun x : ℝⁿ => x + t) volume volume :=
    measurePreserving_add_right volume t
  have htme : MeasurableEmbedding (fun x : ℝⁿ => x + t) :=
    (Homeomorph.addRight t).measurableEmbedding
  set ψ : ℝⁿ → ℝ := fun z => φ (z - t) with hψdef
  have hsupp_sub : Function.support ψ ⊆ (fun x => x + t) '' tsupport φ := fun y hy =>
    ⟨y - t, subset_tsupport φ hy, by simp⟩
  have hImg_cpt : IsCompact ((fun x => x + t) '' tsupport φ) :=
    hφcs.isCompact.image (continuous_id.add continuous_const)
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.intro hImg_cpt
      (fun x hx => not_not.1 fun hne => hx (hsupp_sub (Function.mem_support.2 hne)))
  have hψsub : tsupport ψ ⊆ W :=
    (closure_minimal hsupp_sub hImg_cpt.isClosed).trans
      ((Set.image_mono hφsub).trans
        (le_of_eq (Set.image_preimage_eq W (Equiv.addRight t).surjective)))
  have hψtest : IsTestFunction W ψ :=
    ⟨hφcd.comp (contDiff_id.sub contDiff_const), hψcs, hψsub⟩
  have hpt : ∀ y, fderiv ℝ φ (y - t) e = fderiv ℝ ψ y e := by
    intro y
    have hcomp : HasFDerivAt ψ ((fderiv ℝ φ (y - t)).comp (ContinuousLinearMap.id ℝ ℝⁿ)) y := by
      have hg : HasFDerivAt φ (fderiv ℝ φ (y - t)) (y - t) :=
        (hφcd.differentiable (by norm_num) (y - t)).hasFDerivAt
      exact hg.comp y ((hasFDerivAt_id y).sub_const t)
    rw [hψdef, hcomp.fderiv]; simp
  have hcovL : ∫ x, u (x + t) * fderiv ℝ φ x e = ∫ y, u y * fderiv ℝ φ (y - t) e := by
    have key := htmp.integral_comp htme (fun y => u y * fderiv ℝ φ (y - t) e)
    simp only [add_sub_cancel_right] at key; exact key
  have hcovR : ∫ x, v (x + t) * φ x = ∫ y, v y * φ (y - t) := by
    have key := htmp.integral_comp htme (fun y => v y * φ (y - t))
    simp only [add_sub_cancel_right] at key; exact key
  rw [hcovL,
    show (∫ y, u y * fderiv ℝ φ (y - t) e) = ∫ y, u y * fderiv ℝ ψ y e from
      integral_congr_ae (Eventually.of_forall (fun y => by dsimp only; rw [hpt y])),
    h ψ hψtest, ← hcovR]


/-- The height vector is `±` the last standard basis vector (sign undetermined because
`stdOrthonormalBasis ℝ ℝ` is only pinned up to sign). -/
theorem heightVec_eq_single_or_neg (m : ℕ) :
    heightVec m = EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ) ∨
      heightVec m = -EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ) := by
  have hbasis : flatten m (((EuclideanSpace.basisFun (Fin (m + 1)) ℝ).prod
      (stdOrthonormalBasis ℝ ℝ)) (Sum.inr ⟨0, by simp⟩))
      = EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ) := by
    rw [flatten, OrthonormalBasis.equiv_apply_basis, ← EuclideanSpace.basisFun_apply]; congr 1
  rw [OrthonormalBasis.prod_apply] at hbasis
  simp only [Sum.elim_inr, Function.comp_apply, LinearMap.coe_inr] at hbasis
  rcases orthonormalBasis_one_dim (stdOrthonormalBasis ℝ ℝ) with h | h <;>
    simp only [h] at hbasis
  · left; rw [heightVec]; exact hbasis
  · right; rw [heightVec, ← neg_eq_iff_eq_neg, ← map_neg]; convert hbasis using 3; ext <;> simp

/-- The base part `((flatten.symm ·).ofLp).1` is independent of the last coordinate: shifting the
argument along `single (last)` leaves it unchanged. (Because `flatten.symm (heightVec) = (0,1)` has
zero base part, and `single (last) = ± heightVec`.) -/
theorem flatten_symm_fst_indep_last (m : ℕ) (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ) :
    (((flatten m).symm (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ))).ofLp).1
      = (((flatten m).symm y).ofLp).1 := by
  have hhv : (flatten m).symm (heightVec m)
      = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (m + 1))), (1 : ℝ)) := by
    rw [heightVec, LinearIsometryEquiv.symm_apply_apply]
  have key : ∀ s : ℝ, (((flatten m).symm (y + s • heightVec m)).ofLp).1
      = (((flatten m).symm y).ofLp).1 := by
    intro s; rw [map_add, map_smul, hhv]; simp
  rcases heightVec_eq_single_or_neg m with h | h
  · rw [show EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ) = heightVec m from h.symm]; exact key t
  · rw [show EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ) = -heightVec m from by rw [h, neg_neg],
      show t • (-heightVec m) = (-t) • heightVec m from by rw [neg_smul, smul_neg]]
    exact key (-t)


/-- The chart "base" map `y ↦ ((flatten.symm y).ofLp).1` is a continuous linear map
(`fst ∘ flattenCLE`), hence smooth. -/
theorem contDiff_flatten_base (m : ℕ) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (m + 2)) => (((flatten m).symm y).ofLp).1) := by
  have hbase : (fun y : EuclideanSpace ℝ (Fin (m + 2)) => (((flatten m).symm y).ofLp).1)
      = fun y => (flattenCLE m y).1 := rfl
  rw [hbase]
  exact (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (m + 1))) ℝ).contDiff.comp
    (flattenCLE m).contDiff

/-- The chart shift `γ ∘ base` is `C¹`. -/
theorem contDiff_gamma_base (m : ℕ) {γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hγ : ContDiff ℝ 1 γ) :
    ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (m + 2)) => γ ((((flatten m).symm y).ofLp).1)) :=
  hγ.comp ((contDiff_flatten_base m).of_le (by norm_num))

/-- The chart shift `γ ∘ base` is independent of the last coordinate. -/
theorem gamma_base_indep_last (m : ℕ) (γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ) :
    γ ((((flatten m).symm (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ))).ofLp).1)
      = γ ((((flatten m).symm y).ofLp).1) := by
  rw [flatten_symm_fst_indep_last]

/-- **`MemLp` transfer on a restricted set under a measure-preserving map.** If `u ∈ Lᵖ` on the
restricted measure `volume.restrict S` and `f` is measure-preserving, then `u ∘ f ∈ Lᵖ` on
`volume.restrict (f ⁻¹' S)`. -/
theorem MemLp.comp_measurePreserving_restrict {p : ℝ≥0∞} {u : ℝⁿ → ℝ} {S : Set ℝⁿ} {f : ℝⁿ → ℝⁿ}
    (hu : MemLp u p (volume.restrict S)) (hf : MeasurePreserving f volume volume)
    (hfm : MeasurableEmbedding f) :
    MemLp (u ∘ f) p (volume.restrict (f ⁻¹' S)) :=
  hu.comp_measurePreserving (hf.restrict_preimage_emb hfm S)


/-- **`W^{1,p}` transfer under a translation on an open set.** If `u ∈ W^{1,p}(S)` with `S` open,
then `u(· + t) ∈ W^{1,p}((· + t) ⁻¹' S)`. Translation preserves coordinate directions, so no
direction mixing occurs. -/
theorem MemW1p.comp_translate_restrict (t : ℝⁿ) {S : Set ℝⁿ} (hS : IsOpen S) {p : ℝ≥0∞}
    {u : ℝⁿ → ℝ} (hu : MemW1p S p u) :
    MemW1p ((fun x => x + t) ⁻¹' S) p (fun x => u (x + t)) := by
  have htmp : MeasurePreserving (fun x : ℝⁿ => x + t) volume volume :=
    measurePreserving_add_right volume t
  have htme : MeasurableEmbedding (fun x : ℝⁿ => x + t) :=
    (Homeomorph.addRight t).measurableEmbedding
  refine ⟨MemLp.comp_measurePreserving_restrict hu.memLp htmp htme, fun j => ?_⟩
  obtain ⟨v, hv, hvLp⟩ := hu.exists_weakDeriv j
  exact ⟨fun x => v (x + t),
    isWeakDerivInDir_comp_translate_restrict t hS (EuclideanSpace.single j (1 : ℝ)) hv,
    MemLp.comp_measurePreserving_restrict hvLp htmp htme⟩

/-- **`W^{1,p}` transfer under a linear isometry on an open set.** If `u ∈ W^{1,p}(S)` (`S` open),
then `u ∘ L ∈ W^{1,p}(L ⁻¹' S)`; the rotated direction `L eᵢ` is expanded over the standard basis. -/
theorem MemW1p.comp_linearIsometry_restrict (L : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ) {S : Set ℝⁿ} (hS : IsOpen S)
    {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hu : MemW1p S p u) :
    MemW1p (L ⁻¹' S) p (fun x => u (L x)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hLmp : MeasurePreserving (L : ℝⁿ → ℝⁿ) volume volume := L.measurePreserving
  have hLme : MeasurableEmbedding (L : ℝⁿ → ℝⁿ) := L.toHomeomorph.measurableEmbedding
  have hSm : MeasurableSet S := hS.measurableSet
  choose v hv_weak hv_mem using hu.exists_weakDeriv
  have huLI : LocallyIntegrable u (volume.restrict S) := hu.memLp.locallyIntegrable hp1
  have hvLI : ∀ k, LocallyIntegrable (v k) (volume.restrict S) :=
    fun k => (hv_mem k).locallyIntegrable hp1
  have hbasis : ∀ w : ℝⁿ, (∑ k, w k • EuclideanSpace.single k (1 : ℝ)) = w := by
    intro w
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h
  refine ⟨MemLp.comp_measurePreserving_restrict hu.memLp hLmp hLme, fun i => ?_⟩
  refine ⟨fun x => ∑ k, (L (EuclideanSpace.single i (1 : ℝ))) k * v k (L x), ?_, ?_⟩
  · have hdir : IsWeakDerivInDir S (L (EuclideanSpace.single i (1 : ℝ))) u
        (fun x => ∑ k, (L (EuclideanSpace.single i (1 : ℝ))) k * v k x) := by
      have hsum := IsWeakDerivInDir.dir_sum hSm huLI
        (V := fun k => fun x => (L (EuclideanSpace.single i (1 : ℝ))) k * v k x)
        (fun k => (hvLI k).smul ((L (EuclideanSpace.single i (1 : ℝ))) k))
        (fun k => IsWeakDerivInDir.dir_smul ((L (EuclideanSpace.single i (1 : ℝ))) k) (hv_weak k))
        Finset.univ
      rwa [hbasis (L (EuclideanSpace.single i (1 : ℝ)))] at hsum
    exact isWeakDerivInDir_comp_linear_restrict L hS (EuclideanSpace.single i (1 : ℝ)) hdir
  · exact memLp_finset_sum Finset.univ
      (fun k _ => (MemLp.comp_measurePreserving_restrict (hv_mem k) hLmp hLme).const_mul _)


/-- **Restricting a weak derivative to its set.** If `v` is a weak `e`-derivative of `u` on the open
set `U`, so is `U.indicator v` (they agree on `U`, which contains the support of every test
function). This gives a representative that vanishes off `U`, hence is globally `Lᵖ`/integrable. -/
theorem IsWeakDerivInDir.indicator {U : Set ℝⁿ} {e : ℝⁿ} {u v : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir U e u v) : IsWeakDerivInDir U e u (U.indicator v) := by
  intro φ hφ
  rw [h φ hφ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ U
  · simp [Set.indicator_of_mem hx]
  · simp [image_eq_zero_of_notMem_tsupport (fun hc => hx (hφ.2.2 hc))]

/-- **`W^{1,p}` transfer under the boundary shear on an open set.** If `u ∈ W^{1,p}(S)` with support
in `S` and the shear shift `g` is `C¹` with globally bounded gradient, then `u ∘ Ψ ∈ W^{1,p}(Ψ⁻¹S)`.
The transferred `eⱼ`-derivative picks up the cross term `(∂ⱼg)·(vᵢ∘Ψ)`. -/
theorem MemW1p.comp_shearEquiv_restrict {g : ℝⁿ → ℝ} {i : Fin n}
    (hindep : ∀ (y : ℝⁿ) (t : ℝ), g (y + t • EuclideanSpace.single i (1 : ℝ)) = g y)
    (hg : ContDiff ℝ 1 g) (hg_bdd : ∀ j : Fin n, ∃ M : ℝ, ∀ x,
      |fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))| ≤ M)
    {S : Set ℝⁿ} (hS : IsOpen S) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hu : MemW1p S p u) (hu_sub : tsupport u ⊆ S) :
    MemW1p (shearEquiv hindep ⁻¹' S) p (fun x => u (shearEquiv hindep x)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hSm : MeasurableSet S := hS.measurableSet
  have hΨmp : MeasurePreserving (shearEquiv hindep : ℝⁿ → ℝⁿ) volume volume :=
    measurePreserving_shearEquiv hindep hg
  have hΨcont : Continuous (shearEquiv hindep : ℝⁿ → ℝⁿ) :=
    continuous_id.add (hg.continuous.smul continuous_const)
  have hΨsymm_cont : Continuous ((shearEquiv hindep).symm : ℝⁿ → ℝⁿ) :=
    continuous_id.add (hg.neg.continuous.smul continuous_const)
  have hΨme : MeasurableEmbedding (shearEquiv hindep : ℝⁿ → ℝⁿ) :=
    (⟨shearEquiv hindep, hΨcont, hΨsymm_cont⟩ : Homeomorph ℝⁿ ℝⁿ).measurableEmbedding
  have hu_LI : LocallyIntegrable u volume :=
    (memLp_of_restrict_of_tsupport_subset hSm hu.memLp hu_sub).locallyIntegrable hp1
  choose v hv_weak hv_mem using hu.exists_weakDeriv
  have hvind_weak : ∀ k, IsWeakDerivInDir S (EuclideanSpace.single k (1 : ℝ)) u (S.indicator (v k)) :=
    fun k => (hv_weak k).indicator
  have hvind_mem_restrict : ∀ k, MemLp (S.indicator (v k)) p (volume.restrict S) := fun k =>
    (memLp_congr_ae (by
      filter_upwards [ae_restrict_mem hSm] with x hx
      rw [Set.indicator_of_mem hx])).mp (hv_mem k)
  have hvind_LI : ∀ k, LocallyIntegrable (S.indicator (v k)) volume := fun k =>
    ((memLp_indicator_iff_restrict hSm).2 (hv_mem k)).locallyIntegrable hp1
  refine ⟨MemLp.comp_measurePreserving_restrict hu.memLp hΨmp hΨme, fun j => ?_⟩
  refine ⟨fun z => S.indicator (v j) (shearEquiv hindep z)
      + fderiv ℝ g z (EuclideanSpace.single j (1 : ℝ)) * S.indicator (v i) (shearEquiv hindep z), ?_, ?_⟩
  · exact isWeakDerivInDir_comp_shearEquiv hS hindep hg hu_LI (hvind_LI j) (hvind_LI i)
      (hvind_weak j) (hvind_weak i)
  · obtain ⟨M, hM⟩ := hg_bdd j
    have hgⱼcont : Continuous (fun z => fderiv ℝ g z (EuclideanSpace.single j (1 : ℝ))) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have h1 : MemLp (fun z => S.indicator (v j) (shearEquiv hindep z)) p
        (volume.restrict (shearEquiv hindep ⁻¹' S)) :=
      MemLp.comp_measurePreserving_restrict (hvind_mem_restrict j) hΨmp hΨme
    have h2 : MemLp (fun z => S.indicator (v i) (shearEquiv hindep z)) p
        (volume.restrict (shearEquiv hindep ⁻¹' S)) :=
      MemLp.comp_measurePreserving_restrict (hvind_mem_restrict i) hΨmp hΨme
    have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
    have h2' : MemLp (fun z => fderiv ℝ g z (EuclideanSpace.single j (1 : ℝ))
        * S.indicator (v i) (shearEquiv hindep z)) p (volume.restrict (shearEquiv hindep ⁻¹' S)) := by
      refine ⟨hgⱼcont.aestronglyMeasurable.mul h2.1, ?_⟩
      have hbound : eLpNorm (fun z => fderiv ℝ g z (EuclideanSpace.single j (1 : ℝ))
            * S.indicator (v i) (shearEquiv hindep z)) p (volume.restrict (shearEquiv hindep ⁻¹' S))
          ≤ eLpNorm (M • fun z => S.indicator (v i) (shearEquiv hindep z)) p
            (volume.restrict (shearEquiv hindep ⁻¹' S)) := by
        refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, Pi.smul_apply, Real.norm_eq_abs, smul_eq_mul, abs_mul,
          abs_of_nonneg hM0]
        exact mul_le_mul_of_nonneg_right (hM z) (abs_nonneg _)
      refine lt_of_le_of_lt (hbound.trans eLpNorm_const_smul_le) ?_
      rw [Real.enorm_eq_ofReal hM0]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2.2
    exact h1.add h2'


/-- A `C¹`, compactly supported function has bounded directional derivatives. -/
theorem exists_bound_fderiv_of_compactSupport {f : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) (j : Fin n) :
    ∃ M : ℝ, ∀ x, |fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))| ≤ M := by
  have hcont : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) :=
    hfs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j (1 : ℝ))
  obtain ⟨C, hC⟩ := hcs.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)))
  · rw [← Real.norm_eq_abs]; exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx]; simp

/-- A `C¹` function can be modified to be compactly supported (hence bounded-gradient) while agreeing
with the original on a prescribed compact set. Multiply by a smooth bump that is `1` on a ball
covering `K`. -/
theorem exists_contDiff_compactSupport_eqOn {γ : ℝⁿ → ℝ} (hγ : ContDiff ℝ 1 γ)
    {K : Set ℝⁿ} (hK : IsCompact K) :
    ∃ γ' : ℝⁿ → ℝ, ContDiff ℝ 1 γ' ∧ HasCompactSupport γ' ∧ Set.EqOn γ' γ K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝⁿ)
  set χ : ContDiffBump (0 : ℝⁿ) :=
    { rIn := |R| + 1, rOut := |R| + 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith } with hχ
  refine ⟨fun x => χ x * γ x, χ.contDiff.mul hγ,
    χ.hasCompactSupport.mul_right, fun x hx => ?_⟩
  have hxb : x ∈ Metric.closedBall (0 : ℝⁿ) χ.rIn := by
    refine Metric.closedBall_subset_closedBall ?_ (hR hx)
    show R ≤ |R| + 1
    exact le_trans (le_abs_self R) (by linarith)
  show χ x * γ x = γ x
  rw [χ.one_of_mem_closedBall hxb, one_mul]


/-- A `C¹` compactly supported function has a uniformly bounded derivative (operator norm). -/
theorem exists_bound_norm_fderiv {f : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) : ∃ M : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ M := by
  have hcont : Continuous (fun y => fderiv ℝ f y) := hf.continuous_fderiv (by norm_num)
  have hcs : HasCompactSupport (fun y => fderiv ℝ f y) := hfs.fderiv ℝ
  obtain ⟨C, hC⟩ := hcs.isCompact.exists_bound_of_continuousOn hcont.norm.continuousOn
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ tsupport (fun y => fderiv ℝ f y)
  · exact (norm_norm (fderiv ℝ f y) ▸ hC y hy).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]; exact le_max_right _ _

/-- The chart shift `γ' ∘ base` (with `γ'` compactly supported) has bounded directional derivatives:
by the chain rule `∂ⱼ(γ'∘base) = Dγ'(base ·) (base eⱼ)`, bounded by `‖Dγ'‖·‖base eⱼ‖`. -/
theorem exists_bound_fderiv_gamma_base {m : ℕ} {γ' : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hγ' : ContDiff ℝ 1 γ') (hγ's : HasCompactSupport γ') (j : Fin (m + 2)) :
    ∃ M : ℝ, ∀ x, |fderiv ℝ (fun w => γ' ((((flatten m).symm w).ofLp).1)) x
      (EuclideanSpace.single j (1 : ℝ))| ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_norm_fderiv hγ' hγ's
  set L : EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (m + 1))) ℝ).comp
      ((flattenCLE m) : _ →L[ℝ] _) with hL
  have hfun : (fun w => γ' ((((flatten m).symm w).ofLp).1)) = fun w => γ' (L w) := rfl
  refine ⟨M * ‖L (EuclideanSpace.single j (1 : ℝ))‖, fun x => ?_⟩
  rw [hfun]
  have hchain : fderiv ℝ (fun w => γ' (L w)) x = (fderiv ℝ γ' (L x)).comp L :=
    ((hγ'.differentiable (by norm_num) (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  rw [hchain, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
  exact le_trans ((fderiv ℝ γ' (L x)).le_opNorm _) (by gcongr; exact hM (L x))


/-- **`W^{1,p}` transfer under an affine isometry `x ↦ e x + c` on an open set.** Composition of the
translation and linear-isometry restricted transfers. -/
theorem MemW1p.comp_affineIsometry_restrict (e : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ) (c : ℝⁿ) {S : Set ℝⁿ}
    (hS : IsOpen S) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hu : MemW1p S p u) :
    MemW1p ((fun x => e x + c) ⁻¹' S) p (fun x => u (e x + c)) := by
  have h1 : MemW1p ((fun x => x + c) ⁻¹' S) p (fun x => u (x + c)) :=
    hu.comp_translate_restrict c hS
  have h2 := h1.comp_linearIsometry_restrict e
    (by exact (continuous_id.add continuous_const).isOpen_preimage _ hS)
  exact h2

section FlattenCoord
variable {m : ℕ}

/-- Shifting the argument by `t • heightVec` raises the extracted height coordinate by exactly `t`.
(`flatten.symm heightVec = (0,1)` has height `1`.) -/
theorem flatten_symm_snd_shift_hv (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ) :
    (((flatten m).symm (y + t • heightVec m)).ofLp).2 = (((flatten m).symm y).ofLp).2 + t := by
  have hhv : (flatten m).symm (heightVec m)
      = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (m + 1))), (1 : ℝ)) := by
    rw [heightVec, LinearIsometryEquiv.symm_apply_apply]
  rw [map_add, map_smul, hhv]; simp

/-- The base part is unchanged by a `heightVec`-shift. -/
theorem flatten_symm_fst_shift_hv (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ) :
    (((flatten m).symm (y + t • heightVec m)).ofLp).1 = (((flatten m).symm y).ofLp).1 := by
  have hhv : (flatten m).symm (heightVec m)
      = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (m + 1))), (1 : ℝ)) := by
    rw [heightVec, LinearIsometryEquiv.symm_apply_apply]
  rw [map_add, map_smul, hhv]; simp

/-- Robust `⟪z, single k 1⟫ = z k` bridging the `RealInnerProductSpace` notation instance to the
generic `EuclideanSpace.inner_single_right` (the two `RCLike` instances are defeq but not
syntactically equal, so `rw`/`simp` won't match — `simpa`'s closing `exact` bridges them). -/
theorem inner_single_one_eq (z : EuclideanSpace ℝ (Fin (m + 2))) (k : Fin (m + 2)) :
    ⟪z, EuclideanSpace.single k (1 : ℝ)⟫ = z k := by
  simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) k (1 : ℝ) z

/-- The extracted height coordinate equals `±` the last Euclidean coordinate (sign = that of
`heightVec`). -/
theorem flatten_symm_snd_eq_last (z : EuclideanSpace ℝ (Fin (m + 2))) :
    (((flatten m).symm z).ofLp).2 = z (Fin.last (m + 1)) ∨
      (((flatten m).symm z).ofLp).2 = - z (Fin.last (m + 1)) := by
  rw [flatten_symm_snd]
  rcases heightVec_eq_single_or_neg m with h | h
  · left; rw [h, inner_single_one_eq]
  · right; rw [h, inner_neg_right, inner_single_one_eq]


/-- **Shear flattening (height).**  A last-coordinate shear whose shift `g` satisfies the flattening
relation `g w • single(last) = -(γ∘base)(w) • heightVec` lowers the height coordinate by exactly
`γ∘base`. -/
theorem shear_flatten_snd {g : EuclideanSpace ℝ (Fin (m + 2)) → ℝ}
    (hindep : ∀ (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ),
      g (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) = g y)
    (γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : ∀ w, g w • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)
      = -(γ ((((flatten m).symm w).ofLp).1)) • heightVec m)
    (y : EuclideanSpace ℝ (Fin (m + 2))) :
    (((flatten m).symm (shearEquiv hindep y)).ofLp).2
      = (((flatten m).symm y).ofLp).2 - γ ((((flatten m).symm y).ofLp).1) := by
  show (((flatten m).symm (y + g y • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ))).ofLp).2 = _
  rw [hg y, flatten_symm_snd_shift_hv]; ring

/-- **Shear flattening (base).**  The same shear leaves the base part fixed. -/
theorem shear_flatten_fst {g : EuclideanSpace ℝ (Fin (m + 2)) → ℝ}
    (hindep : ∀ (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ),
      g (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) = g y)
    (γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : ∀ w, g w • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)
      = -(γ ((((flatten m).symm w).ofLp).1)) • heightVec m)
    (y : EuclideanSpace ℝ (Fin (m + 2))) :
    (((flatten m).symm (shearEquiv hindep y)).ofLp).1 = (((flatten m).symm y).ofLp).1 := by
  show (((flatten m).symm (y + g y • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ))).ofLp).1 = _
  rw [hg y, flatten_symm_fst_shift_hv]

/-- **The boundary shear generator.**  For a `C¹` graph `γ`, there is a `C¹` last-coordinate-
independent shift `g` whose shear flattens the standard subgraph: `g` satisfies the flattening
relation `g w • single(last) = -(γ∘base)(w) • heightVec`. -/
theorem exists_chart_shear_generator {γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hγ : ContDiff ℝ 1 γ) :
    ∃ g : EuclideanSpace ℝ (Fin (m + 2)) → ℝ, ContDiff ℝ 1 g ∧
      (∀ (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ),
        g (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) = g y) ∧
      (∀ w, g w • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)
        = -(γ ((((flatten m).symm w).ofLp).1)) • heightVec m) := by
  rcases heightVec_eq_single_or_neg m with h | h
  · refine ⟨fun w => -(γ ((((flatten m).symm w).ofLp).1)), (contDiff_gamma_base m hγ).neg,
      fun y t => by simp only [gamma_base_indep_last], fun w => ?_⟩
    rw [h]
  · refine ⟨fun w => γ ((((flatten m).symm w).ofLp).1), contDiff_gamma_base m hγ,
      fun y t => by simp only [gamma_base_indep_last], fun w => ?_⟩
    rw [h]; simp [smul_neg, neg_smul]


/-- **Flattening set identity.**  The shear pulls the flat lower half-space
`{(flatten.symm z).2 < 0}` back to the standard subgraph `{(flatten.symm y).2 < γ(base y)}`. -/
theorem shear_preimage_halfspace {g : EuclideanSpace ℝ (Fin (m + 2)) → ℝ}
    (hindep : ∀ (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ),
      g (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) = g y)
    (γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : ∀ w, g w • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)
      = -(γ ((((flatten m).symm w).ofLp).1)) • heightVec m) :
    shearEquiv hindep ⁻¹' {z | (((flatten m).symm z).ofLp).2 < 0}
      = {y | (((flatten m).symm y).ofLp).2 < γ ((((flatten m).symm y).ofLp).1)} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, shear_flatten_snd hindep γ hg y]
  constructor <;> intro h <;> linarith

/-- The flat lower half-space is a coordinate half-space (last coordinate), up to sign. -/
theorem halfspace_flat_eq_coord :
    {z : EuclideanSpace ℝ (Fin (m + 2)) | (((flatten m).symm z).ofLp).2 < 0}
      = {z | z (Fin.last (m + 1)) < 0} ∨
    {z : EuclideanSpace ℝ (Fin (m + 2)) | (((flatten m).symm z).ofLp).2 < 0}
      = {z | 0 < z (Fin.last (m + 1))} := by
  rcases heightVec_eq_single_or_neg m with h | h
  · left
    have hpt : ∀ z : EuclideanSpace ℝ (Fin (m + 2)),
        (((flatten m).symm z).ofLp).2 = z (Fin.last (m + 1)) :=
      fun z => by rw [flatten_symm_snd, h, inner_single_one_eq]
    ext z; simp only [Set.mem_setOf_eq, hpt]
  · right
    have hpt : ∀ z : EuclideanSpace ℝ (Fin (m + 2)),
        (((flatten m).symm z).ofLp).2 = - z (Fin.last (m + 1)) :=
      fun z => by rw [flatten_symm_snd, h, inner_neg_right, inner_single_one_eq]
    ext z; simp only [Set.mem_setOf_eq, hpt]
    constructor <;> intro hz <;> linarith


/-- **Packaged chart shear.** For a `C¹` chart graph `γ` and a compact base region `K`, there is a
cut-off graph `γ'` (equal to `γ` on `K`) and a shear shift `g = ∓ γ'∘base` that is `C¹`,
last-coordinate independent, has globally bounded gradient, and satisfies the flattening relation. -/
theorem exists_bounded_chart_shear {γ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hγ : ContDiff ℝ 1 γ) {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : IsCompact K) :
    ∃ (γ' : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (g : EuclideanSpace ℝ (Fin (m + 2)) → ℝ)
      (hindep : ∀ (y : EuclideanSpace ℝ (Fin (m + 2))) (t : ℝ),
        g (y + t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) = g y),
      ContDiff ℝ 1 g ∧
      (∀ j : Fin (m + 2), ∃ M : ℝ, ∀ x, |fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))| ≤ M) ∧
      Set.EqOn γ' γ K ∧
      (∀ w, g w • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)
        = -(γ' ((((flatten m).symm w).ofLp).1)) • heightVec m) := by
  obtain ⟨γ', hγ'cd, hγ'cs, hγ'eq⟩ := exists_contDiff_compactSupport_eqOn hγ hK
  have hbdd : ∀ j : Fin (m + 2), ∃ M : ℝ, ∀ x,
      |fderiv ℝ (fun w => γ' ((((flatten m).symm w).ofLp).1)) x (EuclideanSpace.single j (1 : ℝ))|
        ≤ M := fun j => exists_bound_fderiv_gamma_base hγ'cd hγ'cs j
  rcases heightVec_eq_single_or_neg m with h | h
  · refine ⟨γ', fun w => -(γ' ((((flatten m).symm w).ofLp).1)),
      fun y t => by simp only [gamma_base_indep_last], (contDiff_gamma_base m hγ'cd).neg,
      fun j => ?_, hγ'eq, fun w => by rw [h]⟩
    obtain ⟨M, hM⟩ := hbdd j
    refine ⟨M, fun x => ?_⟩
    have hd : HasFDerivAt (fun w => γ' ((((flatten m).symm w).ofLp).1))
        (fderiv ℝ (fun w => γ' ((((flatten m).symm w).ofLp).1)) x) x :=
      ((contDiff_gamma_base m hγ'cd).differentiable (by norm_num) x).hasFDerivAt
    have heq : (fun w => -(γ' ((((flatten m).symm w).ofLp).1)))
        = -(fun w => γ' ((((flatten m).symm w).ofLp).1)) := rfl
    rw [heq, hd.neg.fderiv, ContinuousLinearMap.neg_apply, abs_neg]
    exact hM x
  · refine ⟨γ', fun w => γ' ((((flatten m).symm w).ofLp).1),
      fun y t => by simp only [gamma_base_indep_last], contDiff_gamma_base m hγ'cd,
      hbdd, hγ'eq, fun w => by rw [h]; simp [smul_neg, neg_smul]⟩


end FlattenCoord

end Sobolev
