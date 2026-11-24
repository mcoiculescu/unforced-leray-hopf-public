import UnforcedLeray.Lib.Sobolev.Space
import UnforcedLeray.Lib.Sobolev.Cylinder
import UnforcedLeray.Lib.SobolevC.Weights
import UnforcedLeray.Lib.Cylinder.Lebesgue

/-!
# CY06: the periodic weighted Sobolev scale `H^k_m(C_c)` as an instance of `Sob.W`


(§5 Layer 1), built as decision D3 of the scoping README asks: `Cyl.H c m k` is the abbreviation
`Sob.W (Sob.cylinder c) (ρw c ^ m) 𝕜 F k 2`.

Manuscript: `paper/main.tex` lines 4569–4578 (blueprint unit B0271: `X^k = H^k_m(C_c)` with
periodic weak derivatives and a smooth periodic weight comparable to `(1+q²+η²)^m`, "not Sobolev
norms of zero extensions") and lines 13869–13890 (B0656: `ρ_ℓ = 1 + (ℓ/π)² sin²(πq/ℓ) + η²`,
`X_m = L²(ρ_ℓ^m)`, `H^k_m = {D^α f ∈ X_m, |α| ≤ k}`, unweighted pairing `H^{-k}_m = (H^k_{-m})*`).

## Main declarations
* `ρwW c`: the smooth periodic weight `ρw c` as a `Sob.Weight`;
* `H 𝕜 F c m k`: the Hilbert space `H^k_m(C_c; F)`;
* `cylinder_μ_eq`, `wμ_ρwW`, `wμ_ρwW_inv`: the pairing measure of `Sob.cylinder c` is the cell
  measure `cellμ c` of `Lib/Cylinder`, and the `L²` spaces of the scale are the spaces
  `X c m` and `X c (-m)` of CY03 (`ρw^m` and `(ρw^m)⁻¹ = ρw^{-m}`);
* `iQ`, `iEta`: the first-order multi-indices `∂_q`, `∂_η`; `H.dQ`, `H.dEta`: the weak partial
  derivatives as continuous linear maps `H^{k+1}_m → H^k_m`;
* `H.norm_sq_one`: `‖f‖²_{H¹_m} = ‖f‖²_{X_m} + ‖∂_q f‖²_{X_m} + ‖∂_η f‖²_{X_m}`;
* `H.inner_one`: the same for the inner product;
* `H.hasWeakDeriv_q`, `H.hasWeakDeriv_eta`: the components are periodic weak derivatives.

The Leibniz bound `normH_mul_le` and the density theorem `dense_smooth_periodic_compactEta` of
the scoping signature are not built here (density on the cylinder is also open in `Lib/SobolevB`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-- The smooth periodic weight `ρw c` (`paper/main.tex` line 13871, B0656) as a `Sob.Weight`. -/
def ρwW (c : ℝ) : Sob.Weight Plane :=
  Sob.Weight.ofContinuous (ρw c) (contDiff_ρw c).continuous (ρw_pos c)

@[simp] theorem ρwW_rpow_apply (c m : ℝ) (z : Plane) : (ρwW c ^ m) z = ρw c z ^ m := rfl

@[simp] theorem ρwW_rpow_inv_apply (c m : ℝ) (z : Plane) : (ρwW c ^ m).inv z = ρw c z ^ (-m) := by
  rw [Sob.Weight.inv_apply, ρwW_rpow_apply, Real.rpow_neg (ρw_pos c z).le]

/-- **CY06** (D3; B0271 tex 4569–4578, B0656 tex 13869–13890): the periodic weighted Sobolev
space `H^k_m(C_c; F) = Sob.W (Sob.cylinder c) (ρw c ^ m) 𝕜 F k 2`. Elements are tuples
`(D^α f)_{|α| ≤ k}` in `L²(cell, ρw^m dq dη; F)` with periodic weak derivatives. -/
abbrev H (𝕜 : Type*) [RCLike 𝕜] (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] (c m : ℝ) (k : ℕ) : Type _ :=
  Sob.W (Sob.cylinder c) (ρwW c ^ m) 𝕜 F k 2

theorem cylCell_eq_cell (c : ℝ) : Sob.cylCell c = cell c := by
  simp only [Sob.cylCell, cell, neg_div]

/-- The pairing measure of `Sob.cylinder c` is the cell measure of CY01. -/
theorem cylinder_μ_eq (c : ℝ) : (Sob.cylinder c).μ = cellμ c := by
  rw [Sob.cylinder_μ, cylCell_eq_cell]; rfl

/-- The order-zero measure of `H c m k` is the measure of `X c m` (CY03). -/
theorem wμ_ρwW (c m : ℝ) : Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m) = wμ c m := by
  rw [cylinder_μ_eq]; rfl

/-- The order-zero measure of the dual weight `(ρw^m)⁻¹` is the measure of `X c (-m)`. -/
theorem wμ_ρwW_inv (c m : ℝ) : Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m).inv = wμ c (-m) := by
  rw [cylinder_μ_eq, Sob.wμ, wμ]
  congr 1
  funext z
  rw [ρwW_rpow_inv_apply]

/-- **CY07** `H^{-k}_m(C_c) := (H^k_{-m})^*` (B0579 tex 9370–9387, B0656 tex 13869–13890,
B0897 tex 9472–9478), for real fields, under the unweighted pairing: the generic
`Sob.Hneg` of `Lib/SobolevC` for the test domain `Sob.cylinder c` and the weight `ρw^m`
(its dual space is built on the weight `(ρw^m)⁻¹ = ρw^{-m}`, `wμ_ρwW_inv`). -/
abbrev Hneg (c m : ℝ) (k : ℕ) : Type _ := Sob.Hneg (Sob.cylinder c) (ρwW c ^ m) ℝ ℝ k

/-- The unweighted space `H¹(C_c)` on which `Hneg c 0 1` acts. -/
abbrev H10 (c : ℝ) : Type _ := Sob.W (Sob.cylinder c) (ρwW c ^ (0 : ℝ)).inv ℝ ℝ 1 2

theorem wμ_ρwW_zero_inv (c : ℝ) : Sob.wμ (Sob.cylinder c).μ (ρwW c ^ (0 : ℝ)).inv = cellμ c := by
  rw [wμ_ρwW_inv, wμ]
  have : (fun z => ENNReal.ofReal (ρw c z ^ (-(0 : ℝ)))) = 1 := by
    funext z; simp
  rw [this, withDensity_one]

/-! ### First-order indices and derivatives -/

/-- The multi-index of `∂_q` (direction `(1,0)`). -/
def iQ {k : ℕ} : Sob.Idx 2 (k + 1) := Sob.Idx.cons 0 Sob.Idx.zero

/-- The multi-index of `∂_η` (direction `(0,1)`). -/
def iEta {k : ℕ} : Sob.Idx 2 (k + 1) := Sob.Idx.cons 1 Sob.Idx.zero

theorem word_iQ (c : ℝ) {k : ℕ} : (Sob.cylinder c).word (iQ (k := k)) = [((1 : ℝ), (0 : ℝ))] := by
  simp [iQ, Sob.TestDomain.word, Sob.Idx.cons, Sob.Idx.zero, Sob.cylDir]; rfl

theorem word_iEta (c : ℝ) {k : ℕ} :
    (Sob.cylinder c).word (iEta (k := k)) = [((0 : ℝ), (1 : ℝ))] := by
  simp [iEta, Sob.TestDomain.word, Sob.Idx.cons, Sob.Idx.zero, Sob.cylDir]; rfl

theorem word_zero (c : ℝ) {k : ℕ} : (Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 k) = [] := by
  simp [Sob.TestDomain.word, Sob.Idx.zero]

/-- The three multi-indices of order `≤ 1` in two variables. -/
theorem univ_idx_two_one :
    (Finset.univ : Finset (Sob.Idx 2 1)) = {Sob.Idx.zero, iQ, iEta} := by
  ext ⟨j, α⟩
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  fin_cases j
  · left
    simp only [Sob.Idx.zero]
    congr 1
    funext i; exact i.elim0
  · right
    have h : α = fun _ => α 0 := by funext i; fin_cases i; rfl
    rcases Fin.exists_fin_two.mp ⟨α 0, rfl⟩ with h0 | h1
    · left
      simp only [iQ, Sob.Idx.cons, Sob.Idx.zero]
      refine Sigma.ext rfl (heq_of_eq ?_)
      funext i; fin_cases i; simp [h0]
    · right
      simp only [iEta, Sob.Idx.cons, Sob.Idx.zero]
      refine Sigma.ext rfl (heq_of_eq ?_)
      funext i; fin_cases i; simp [h1]

theorem idx_ne : (Sob.Idx.zero : Sob.Idx 2 1) ≠ iQ ∧ (Sob.Idx.zero : Sob.Idx 2 1) ≠ iEta ∧
    (iQ : Sob.Idx 2 1) ≠ iEta := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun a : Sob.Idx 2 1 => (a.1 : ℕ)) h
    simp [Sob.Idx.zero, iQ, Sob.Idx.cons] at this
  · have := congrArg (fun a : Sob.Idx 2 1 => (a.1 : ℕ)) h
    simp [Sob.Idx.zero, iEta, Sob.Idx.cons] at this
  · have h2 := congrArg (Sob.cylinder 1).word h
    rw [word_iQ, word_iEta] at h2
    simp at h2

section Ops

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] {c m : ℝ} {k : ℕ}

namespace H

/-- The weak partial derivative `∂_q : H^{k+1}_m → H^k_m`. -/
def dQ : H 𝕜 F c m (k + 1) →L[𝕜] H 𝕜 F c m k := Sob.W.partialDeriv 0

/-- The weak partial derivative `∂_η : H^{k+1}_m → H^k_m`. -/
def dEta : H 𝕜 F c m (k + 1) →L[𝕜] H 𝕜 F c m k := Sob.W.partialDeriv 1

/-- The field of an element. -/
abbrev val (x : H 𝕜 F c m k) : Lp F 2 (Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m)) :=
  Sob.W.value (Sob.cylinder c) (ρwW c ^ m) 𝕜 F k 2 x

/-- The component along a multi-index. -/
abbrev der (α : Sob.Idx 2 k) (x : H 𝕜 F c m k) : Lp F 2 (Sob.wμ (Sob.cylinder c).μ (ρwW c ^ m)) :=
  Sob.W.deriv (Sob.cylinder c) (ρwW c ^ m) 𝕜 F k 2 α x

theorem val_dQ (x : H 𝕜 F c m (k + 1)) : val (dQ x) = der iQ x := rfl

theorem val_dEta (x : H 𝕜 F c m (k + 1)) : val (dEta x) = der iEta x := rfl

/-- `∂_q f` is the periodic weak derivative of `f` in the direction `(1,0)`. -/
theorem hasWeakDeriv_q (x : H 𝕜 F c m (k + 1)) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((1 : ℝ), (0 : ℝ))] (val x : Plane → F) (der iQ x) := by
  have h := Sob.W.hasWeakDeriv x iQ
  rwa [word_iQ] at h

/-- `∂_η f` is the periodic weak derivative of `f` in the direction `(0,1)`. -/
theorem hasWeakDeriv_eta (x : H 𝕜 F c m (k + 1)) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((0 : ℝ), (1 : ℝ))] (val x : Plane → F) (der iEta x) := by
  have h := Sob.W.hasWeakDeriv x iEta
  rwa [word_iEta] at h

/-- **The `H¹_m` norm**: `‖f‖² = ‖f‖²_{X_m} + ‖∂_q f‖²_{X_m} + ‖∂_η f‖²_{X_m}`. -/
theorem norm_sq_one (x : H 𝕜 F c m 1) :
    ‖x‖ ^ 2 = ‖val x‖ ^ 2 + ‖der iQ x‖ ^ 2 + ‖der iEta x‖ ^ 2 := by
  rw [Sob.W.norm_sq, univ_idx_two_one, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_singleton]
  · rw [← add_assoc]; rfl
  · simpa using idx_ne.2.2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨idx_ne.1, idx_ne.2.1⟩

/-- The `H¹_m` inner product. -/
theorem inner_one (x y : H 𝕜 F c m 1) :
    inner 𝕜 x y = inner 𝕜 (val x) (val y) + inner 𝕜 (der iQ x) (der iQ y) +
      inner 𝕜 (der iEta x) (der iEta y) := by
  rw [Sob.W.inner_eq, univ_idx_two_one, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_singleton]
  · rw [← add_assoc]; rfl
  · simpa using idx_ne.2.2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨idx_ne.1, idx_ne.2.1⟩

end H

end Ops

end UnforcedLeray.Cyl
