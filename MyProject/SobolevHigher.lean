import MyProject.Sobolev

open MeasureTheory InnerProductSpace Set Topology
open scoped ContDiff ENNReal RealInnerProductSpace

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

/-! ### Symmetry of mixed weak partial derivatives -/

/-- Classical Clairaut for a smooth function, directional form: `∂_{e₁}∂_{e₂}φ = ∂_{e₂}∂_{e₁}φ`.
A specialization of Mathlib's symmetric-second-derivative theorem `ContDiffAt.isSymmSndFDerivAt`. -/
lemma fderiv_dirDeriv_comm {φ : ℝⁿ → ℝ} (hφ : ContDiff ℝ ∞ φ) (e₁ e₂ : ℝⁿ) (x : ℝⁿ) :
    fderiv ℝ (fun y => fderiv ℝ φ y e₂) x e₁ = fderiv ℝ (fun y => fderiv ℝ φ y e₁) x e₂ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := by
    have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
    exact (h1.differentiable (by norm_num)).differentiableAt
  have key : ∀ a b : ℝⁿ, fderiv ℝ (fun y => fderiv ℝ φ y a) x b
      = fderiv ℝ (fderiv ℝ φ) x b a := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp [ContinuousLinearMap.flip_apply]
  have hsymm : IsSymmSndFDerivAt ℝ φ x :=
    hφ.contDiffAt.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  rw [key e₂ e₁, key e₁ e₂]
  exact hsymm e₁ e₂

/-- **Symmetry of mixed weak partial derivatives (a.e.).** Suppose, on all of `ℝⁿ`, `w₁` is the
weak `e₁`-derivative of `u` and `z` the weak `e₂`-derivative of `w₁`; and symmetrically `w₂` is the
weak `e₂`-derivative of `u` and `z'` the weak `e₁`-derivative of `w₂`. Then the two mixed second
derivatives agree almost everywhere: `z = z'`. Proved by moving both derivatives onto a test
function (using the weak-derivative identity twice), where classical Clairaut
`fderiv_dirDeriv_comm` applies, then the fundamental lemma of the calculus of variations
(via the a.e.-uniqueness route of `isWeakDerivInDir_ae_unique`). -/
theorem isWeakDerivInDir_comm {u w₁ w₂ z z' : ℝⁿ → ℝ} {e₁ e₂ : ℝⁿ}
    (hz : LocallyIntegrable z volume) (hz' : LocallyIntegrable z' volume)
    (h1a : IsWeakDerivInDir univ e₁ u w₁) (h1b : IsWeakDerivInDir univ e₂ w₁ z)
    (h2a : IsWeakDerivInDir univ e₂ u w₂) (h2b : IsWeakDerivInDir univ e₁ w₂ z') :
    ∀ᵐ x ∂volume, z x = z' x := by
  have key : ∀ g : ℝⁿ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ univ →
      ∫ x, g x • (z x - z' x) = 0 := by
    intro g hg hgc hgsub
    have hg_test : IsTestFunction univ g := ⟨hg, hgc, hgsub⟩
    have hψ₂ : IsTestFunction univ (fun x => fderiv ℝ g x e₂) :=
      ⟨(hg.fderiv_right (by norm_num)).clm_apply contDiff_const,
        hg_test.hasCompactSupport_dirDeriv e₂, subset_univ _⟩
    have hψ₁ : IsTestFunction univ (fun x => fderiv ℝ g x e₁) :=
      ⟨(hg.fderiv_right (by norm_num)).clm_apply contDiff_const,
        hg_test.hasCompactSupport_dirDeriv e₁, subset_univ _⟩
    have ez : ∫ x, z x * g x = ∫ x, u x * fderiv ℝ (fun y => fderiv ℝ g y e₂) x e₁ := by
      have hb := h1b g hg_test
      have ha := h1a (fun x => fderiv ℝ g x e₂) hψ₂
      dsimp only [] at ha
      linarith [hb, ha]
    have ez' : ∫ x, z' x * g x = ∫ x, u x * fderiv ℝ (fun y => fderiv ℝ g y e₁) x e₂ := by
      have hb := h2b g hg_test
      have ha := h2a (fun x => fderiv ℝ g x e₁) hψ₁
      dsimp only [] at ha
      linarith [hb, ha]
    have hcomm : ∫ x, u x * fderiv ℝ (fun y => fderiv ℝ g y e₂) x e₁
        = ∫ x, u x * fderiv ℝ (fun y => fderiv ℝ g y e₁) x e₂ :=
      integral_congr_ae (ae_of_all _ fun x => by
        dsimp only []; rw [fderiv_dirDeriv_comm hg e₁ e₂ x])
    have hvv : ∫ x, z x * g x = ∫ x, z' x * g x := ez.trans (hcomm.trans ez'.symm)
    have hint1 : Integrable (fun x => g x * z x) volume :=
      hz.integrable_smul_left_of_hasCompactSupport hg_test.continuous hg_test.hasCompactSupport
    have hint2 : Integrable (fun x => g x * z' x) volume :=
      hz'.integrable_smul_left_of_hasCompactSupport hg_test.continuous hg_test.hasCompactSupport
    calc ∫ x, g x • (z x - z' x)
        = ∫ x, (g x * z x - g x * z' x) := by simp_rw [smul_eq_mul, mul_sub]
      _ = (∫ x, g x * z x) - ∫ x, g x * z' x := integral_sub hint1 hint2
      _ = (∫ x, z x * g x) - ∫ x, z' x * g x := by simp_rw [mul_comm]
      _ = 0 := by rw [hvv]; ring
  have hae := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => z x - z' x) ((hz.sub hz').locallyIntegrableOn univ) key
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (hx (mem_univ x))

/-! ### The Sobolev space `W^{k,p}(ℝⁿ)` as a Banach space

Mirroring the `W^{1,p}` construction in `Sobolev.lean`, we realise `W^{k,p}(ℝⁿ)` carrying its
genuine Sobolev norm as a closed subspace of `PiLp p (DerivIdx → Lᵖ)`.  The index `DerivIdx n k`
runs over all direction-sequences of length `≤ k`; the component at a sequence `l` is the iterated
weak derivative `D^l u`, and the defining relation says the component at `i :: t` is the weak
`∂ᵢ`-derivative of the component at `t`.  Each such relation is a single-direction weak-derivative
graph, closed by the cornerstone `isClosed_isWeakDerivInDir_graph`, so the intersection over all
`(i, t)` is closed and the space is complete.  The `PiLp` norm is then the genuine `ℓᵖ` Sobolev
norm `(∑_{|l|≤k} ‖D^l u‖ₚᵖ)^{1/p}` (summed over direction-sequences, i.e.\ mixed partials with
multiplicity — an equivalent Sobolev norm). -/

/-- Index type for the higher-order Sobolev norm: direction-sequences of length `≤ k`. -/
abbrev DerivIdx (n k : ℕ) := {l : List (Fin n) // l.length ≤ k}

instance (k : ℕ) : Finite (DerivIdx n k) :=
  Finite.of_surjective
    (fun p : Σ j : Fin (k + 1), List.Vector (Fin n) j =>
      (⟨p.2.val, by have := p.1.isLt; rw [p.2.2]; omega⟩ : DerivIdx n k))
    (fun l => ⟨⟨⟨l.val.length, by have := l.2; omega⟩, ⟨l.val, rfl⟩⟩, rfl⟩)

noncomputable instance (k : ℕ) : Fintype (DerivIdx n k) := Fintype.ofFinite _

/-- Tail index: drop the head direction (the length bound is automatic). -/
def DerivIdx.tail {k : ℕ} (i : Fin n) (t : List (Fin n)) (h : (i :: t).length ≤ k) :
    DerivIdx n k := ⟨t, by have h' := h; simp only [List.length_cons] at h'; omega⟩

/-- **`W^{k,p}(ℝⁿ)` with the genuine Sobolev norm**, as a submodule of `PiLp p (DerivIdx → Lᵖ)`:
the component at a direction-sequence `l` is `D^l u`, and the defining relation is that the
component at `i :: t` is the weak `∂ᵢ`-derivative of the component at `t`.  Subspace axioms follow
from linearity of the weak derivative together with `congr_ae`. -/
def wkpSpace (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Submodule ℝ (PiLp p (fun _ : DerivIdx n k => Lp ℝ p (volume : Measure ℝⁿ))) where
  carrier := {x | ∀ (i : Fin n) (t : List (Fin n)) (h : (i :: t).length ≤ k),
    IsWeakDerivInDir Set.univ (EuclideanSpace.single i (1 : ℝ))
      ⇑(x (DerivIdx.tail i t h)) ⇑(x ⟨i :: t, h⟩)}
  zero_mem' := by
    intro i t h
    have h0 : IsWeakDerivInDir Set.univ (EuclideanSpace.single i (1 : ℝ))
        (fun _ : ℝⁿ => (0 : ℝ)) (fun _ => 0) := by intro φ _; simp
    exact h0.congr_ae (Lp.coeFn_zero ..).symm (Lp.coeFn_zero ..).symm
  add_mem' := by
    intro a b ha hb i t h
    have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
    have key := IsWeakDerivInDir.add
      ((Lp.memLp (a (DerivIdx.tail i t h))).locallyIntegrable hp1)
      ((Lp.memLp (b (DerivIdx.tail i t h))).locallyIntegrable hp1)
      ((Lp.memLp (a ⟨i :: t, h⟩)).locallyIntegrable hp1)
      ((Lp.memLp (b ⟨i :: t, h⟩)).locallyIntegrable hp1)
      (ha i t h) (hb i t h)
    exact key.congr_ae (Lp.coeFn_add _ _).symm (Lp.coeFn_add _ _).symm
  smul_mem' := by
    intro c a ha i t h
    exact ((ha i t h).const_smul c).congr_ae (Lp.coeFn_smul c _).symm (Lp.coeFn_smul c _).symm

/-- The norm on `wkpSpace` is the genuine **Sobolev norm** `(∑_{|l|≤k} ‖D^l u‖ₚᵖ)^{1/p}` — the
`ℓᵖ` norm over all derivative components. -/
lemma norm_eq_wkp (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_ne : p ≠ ⊤)
    (x : PiLp p (fun _ : DerivIdx n k => Lp ℝ p (volume : Measure ℝⁿ))) :
    ‖x‖ = (∑ l, ‖x l‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hpos : (0 : ℝ) < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp1).ne' hp_ne
  exact PiLp.norm_eq_sum hpos x

/-- `W^{k,p}(ℝⁿ)` is closed in `PiLp p (DerivIdx → Lᵖ)`: the intersection over `(i, t)` of the
single-direction weak-derivative graphs, pulled back along the continuous projection
`x ↦ (x ⟨t⟩, x ⟨i :: t⟩)`. -/
theorem isClosed_wkpSpace (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_ne : p ≠ ⊤) :
    IsClosed (wkpSpace (n := n) k (p := p) :
      Set (PiLp p (fun _ : DerivIdx n k => Lp ℝ p (volume : Measure ℝⁿ)))) := by
  have hset : (wkpSpace (n := n) k (p := p) :
        Set (PiLp p (fun _ : DerivIdx n k => Lp ℝ p (volume : Measure ℝⁿ))))
      = ⋂ (i : Fin n), ⋂ (t : List (Fin n)), ⋂ (h : (i :: t).length ≤ k),
          (fun x : PiLp p (fun _ : DerivIdx n k => Lp ℝ p (volume : Measure ℝⁿ)) =>
            (x (DerivIdx.tail i t h), x ⟨i :: t, h⟩)) ⁻¹'
          {ab : Lp ℝ p (volume : Measure ℝⁿ) × Lp ℝ p (volume : Measure ℝⁿ) |
            IsWeakDerivInDir Set.univ (EuclideanSpace.single i (1 : ℝ)) ⇑ab.1 ⇑ab.2} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    rfl
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun t => isClosed_iInter fun h => ?_
  have hc : Continuous
      (fun x : PiLp p (fun _ : DerivIdx n k => Lp ℝ p (volume : Measure ℝⁿ)) =>
        (x (DerivIdx.tail i t h), x ⟨i :: t, h⟩)) := by fun_prop
  exact (isClosed_isWeakDerivInDir_graph hp_ne (EuclideanSpace.single i (1 : ℝ))).preimage hc

/-- **`W^{k,p}(ℝⁿ)` with the Sobolev norm is a Banach space** (`1 ≤ p < ∞`): `wkpSpace k` is a
closed subspace of the complete space `PiLp p (DerivIdx → Lᵖ)`. -/
theorem completeSpace_wkpSpace (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_ne : p ≠ ⊤) :
    CompleteSpace (wkpSpace (n := n) k (p := p)) :=
  completeSpace_coe_iff_isComplete.mpr (isClosed_wkpSpace k hp_ne).isComplete

/-! ### The Hilbert space `H^k(ℝⁿ) = W^{k,2}(ℝⁿ)`

For the exponent `p = 2`, `Lᵖ` is a Hilbert space and so is the ambient `PiLp 2 (DerivIdx → L²)`;
`wkpSpace k` then inherits an `InnerProductSpace ℝ` structure (automatic for a submodule) and is
complete by `completeSpace_wkpSpace`, so `H^k(ℝⁿ) = W^{k,2}(ℝⁿ)` is a **Hilbert space**. Its inner
product and norm are the expected `H^k` ones, summed over the derivative components. -/

/-- The `H^k` inner product is the sum over derivative components of the `L²` inner products:
`⟪u, v⟫_{H^k} = ∑_{|l|≤k} ∫ D^l u · D^l v`. -/
lemma inner_wkpSpace {k : ℕ} (u v : wkpSpace (n := n) k (p := 2)) :
    ⟪u, v⟫ = ∑ l, ∫ x, (u : PiLp 2 (fun _ : DerivIdx n k => Lp ℝ 2 (volume : Measure ℝⁿ))) l x
        * (v : PiLp 2 (fun _ : DerivIdx n k => Lp ℝ 2 (volume : Measure ℝⁿ))) l x := by
  have h1 : ⟪u, v⟫ = ⟪(u : PiLp 2 (fun _ : DerivIdx n k => Lp ℝ 2 (volume : Measure ℝⁿ))),
      (v : PiLp 2 (fun _ : DerivIdx n k => Lp ℝ 2 (volume : Measure ℝⁿ)))⟫ := rfl
  rw [h1, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only []
  rw [real_inner_comm]; rfl

/-- The squared `H^k` norm is the sum over derivative components of the squared `L²` norms:
`‖u‖² = ∑_{|l|≤k} ∫ |D^l u|²`. -/
lemma norm_sq_wkpSpace {k : ℕ} (u : wkpSpace (n := n) k (p := 2)) :
    ‖u‖ ^ 2 = ∑ l, ∫ x, (u : PiLp 2 (fun _ : DerivIdx n k => Lp ℝ 2 (volume : Measure ℝⁿ))) l x
        ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_wkpSpace]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only []; ring

end Sobolev
