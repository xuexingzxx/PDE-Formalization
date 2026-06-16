import MyProject.Sobolev

open MeasureTheory InnerProductSpace Set Topology
open scoped ContDiff ENNReal

/-!
# Higher-order Sobolev spaces (Evans PDE, §5.2)

Building on the first-order theory in `Sobolev.lean`, this file introduces **iterated weak
derivatives** and the spaces `W^{k,p}`.

* `dirDerivList es u` — the iterated classical directional derivative of `u`, applying `∂_e` once
  for each direction `e` in the list `es`.
* `IsWeakDerivList U es u v` — `v` is the iterated weak derivative of `u` along `es`: a chain of
  single-direction weak derivatives.
* `MemWkp U k p u` — `u ∈ W^{k,p}(U)`: `u ∈ Lᵖ(U)` together with all iterated weak derivatives of
  order `≤ k` along the coordinate directions, each in `Lᵖ(U)`.

Key results: the classical ⟹ weak bridge `isWeakDerivList_of_contDiff` (the iterated classical
derivative of a smooth function is its iterated weak derivative),
`memWkp_of_contDiff_hasCompactSupport` (smooth compactly supported functions lie in every
`W^{k,p}`), homogeneity of the iterated weak derivative `IsWeakDerivList.const_smul`, and the
identification `memW1p_iff_memWkp_one` of the first-order space with the order-`1` higher space.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-- The iterated directional derivative of `u` along the directions in `es`
(apply `∂_e` once for each `e`, in order). -/
noncomputable def dirDerivList : List ℝⁿ → (ℝⁿ → ℝ) → (ℝⁿ → ℝ)
  | [], u => u
  | e :: es, u => dirDerivList es (fun x => fderiv ℝ u x e)

/-- `v` is the **iterated weak derivative** of `u` along the directions `es` on `U`:
a chain of single-direction weak derivatives, one per entry of `es`. -/
def IsWeakDerivList (U : Set ℝⁿ) : List ℝⁿ → (ℝⁿ → ℝ) → (ℝⁿ → ℝ) → Prop
  | [], u, v => v = u
  | e :: es, u, v => ∃ w, IsWeakDerivInDir U e u w ∧ IsWeakDerivList U es w v

/-- The iterated classical directional derivative of a smooth function is smooth. -/
theorem contDiff_dirDerivList {u : ℝⁿ → ℝ} (hu : ContDiff ℝ ∞ u) (es : List ℝⁿ) :
    ContDiff ℝ ∞ (dirDerivList es u) := by
  induction es generalizing u with
  | nil => exact hu
  | cons e es ih => exact ih ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

/-- The iterated derivative of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_dirDerivList {u : ℝⁿ → ℝ} (hcu : HasCompactSupport u) (es : List ℝⁿ) :
    HasCompactSupport (dirDerivList es u) := by
  induction es generalizing u with
  | nil => exact hcu
  | cons e es ih =>
    simp only [dirDerivList]
    exact ih (hcu.fderiv_apply (𝕜 := ℝ) e)

/-- **Classical ⟹ iterated weak derivative.** For a smooth `u`, the iterated classical directional
derivative `dirDerivList es u` is its iterated weak derivative along `es`. -/
theorem isWeakDerivList_of_contDiff {U : Set ℝⁿ} {u : ℝⁿ → ℝ} (hu : ContDiff ℝ ∞ u)
    (es : List ℝⁿ) : IsWeakDerivList U es u (dirDerivList es u) := by
  induction es generalizing u with
  | nil => rfl
  | cons e es ih =>
    have hw : ContDiff ℝ ∞ (fun x => fderiv ℝ u x e) :=
      (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hbridge : IsWeakDerivInDir U e u (fun x => fderiv ℝ u x e) :=
      isWeakDerivInDir_of_contDiff U e (hu.of_le (by norm_num))
    exact ⟨fun x => fderiv ℝ u x e, hbridge, ih hw⟩

/-- `u ∈ W^{k,p}(U)`: `u ∈ Lᵖ(U)` and every iterated weak derivative of order `≤ k` along the
coordinate directions exists and lies in `Lᵖ(U)`. -/
def MemWkp (U : Set ℝⁿ) (k : ℕ) (p : ℝ≥0∞) (u : ℝⁿ → ℝ) : Prop :=
  MemLp u p (volume.restrict U) ∧
    ∀ l : List (Fin n), l.length ≤ k →
      ∃ v, IsWeakDerivList U (l.map fun i => EuclideanSpace.single i (1 : ℝ)) u v ∧
        MemLp v p (volume.restrict U)

/-- **Every smooth, compactly supported function lies in `W^{k,p}(U)`** for all `k` and `p`: its
iterated weak derivatives are the (smooth, compactly supported, hence `Lᵖ`) classical ones. -/
theorem memWkp_of_contDiff_hasCompactSupport {U : Set ℝⁿ} {k : ℕ} {p : ℝ≥0∞} {u : ℝⁿ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) : MemWkp U k p u := by
  have hmem : ∀ {w : ℝⁿ → ℝ}, ContDiff ℝ ∞ w → HasCompactSupport w →
      MemLp w p (volume.restrict U) := fun hw hcw =>
    ((hw.continuous.memLp_of_hasCompactSupport (μ := volume) hcw).restrict _)
  refine ⟨hmem hu hcu, fun l _ => ⟨dirDerivList (l.map fun i => EuclideanSpace.single i 1) u,
    isWeakDerivList_of_contDiff hu _, hmem (contDiff_dirDerivList hu _) ?_⟩⟩
  exact hasCompactSupport_dirDerivList hcu _

/-- **Homogeneity of the iterated weak derivative.** If `v` is the iterated weak derivative of `u`
along `es`, then `c • v` is the iterated weak derivative of `c • u` along `es`. -/
theorem IsWeakDerivList.const_smul {U : Set ℝⁿ} {u v : ℝⁿ → ℝ} (c : ℝ) (es : List ℝⁿ)
    (h : IsWeakDerivList U es u v) :
    IsWeakDerivList U es (fun x => c * u x) (fun x => c * v x) := by
  induction es generalizing u v with
  | nil =>
    simp only [IsWeakDerivList] at h ⊢
    subst h; rfl
  | cons e es ih =>
    obtain ⟨w, hw, hl⟩ := h
    exact ⟨fun x => c * w x, hw.const_smul c, ih hl⟩

/-- **`W^{1,p}` is exactly `W^{1,p}` viewed as the order-`1` higher Sobolev space.** A function lies
in the first-order space `MemW1p U p` iff it lies in `MemWkp U 1 p`: a length-`≤ 1` list of
directions is either empty (recovering `u ∈ Lᵖ`) or a single coordinate (recovering a
single-direction weak derivative). -/
theorem memW1p_iff_memWkp_one {U : Set ℝⁿ} {p : ℝ≥0∞} {u : ℝⁿ → ℝ} :
    MemW1p U p u ↔ MemWkp U 1 p u := by
  constructor
  · intro h
    refine ⟨h.memLp, ?_⟩
    intro l hl
    rcases l with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact ⟨u, rfl, h.memLp⟩
    · obtain ⟨v, hv, hvLp⟩ := h.exists_weakDeriv i
      exact ⟨v, ⟨v, hv, rfl⟩, hvLp⟩
    · simp at hl
  · intro h
    refine ⟨h.1, fun i => ?_⟩
    obtain ⟨v, hwl, hvLp⟩ := h.2 [i] (by simp)
    obtain ⟨w, hw, heq⟩ := hwl
    exact ⟨w, hw, heq ▸ hvLp⟩

end Sobolev
