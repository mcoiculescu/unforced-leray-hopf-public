import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Convolution

/-!
# Periodic mollification and the order `-1` bound (shared by the bootstrap and the time jets)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(the weighted energies `E_j` of the reverse-time adjoint, squared weighted `H^j_{-m}` norms, used
as classical quantities of the reverse time), 3044-3050 (the weight and its logarithmic
derivatives), 3052-3058 (the adjoint localized interaction `K_c^T(·∇E)` maps `X_{-m}` to
`H^1_{-m}`: an operator of order `-1`; near/far split of the kernel, the horizontal mean).

This file is shared by `PartIII-a:T21/2/7/2/1/1/5/org` (the bootstrap `AdjHkStep`,
`HkStep/Defs.lean`, `HkStep/Assembly.lean`) and `PartIII-a:T21/2/7/2/1/1/6/org` (the time jets
`AdjTimeJetsOf`).  The source treats `E_j` as classical; a weak solution is regularized in `x` to
justify this: the regularization is the convolution `cellMoll n` on the plane with the normalized
bump `molKer n` of radius `1/(n+1)` (sup norm), applied to the `c`-periodic representative.

## Objects
* `molBump`, `molKer`, `cellConv`, `cellMoll`: the bump, the kernel, convolution of a periodic
  field with a real kernel on the plane, the mollification;
* `pdWordR`: iterated classical partials of a real kernel (the real analogue of `adjSpatial`);
* `perKer`: the `c`-periodization `Σ_k K(y₁ + kc, y₂)` of a compactly supported kernel;
* `wordsLE`, `jetNorm`, `cellEnergy`: the words of length `≤ j`; the `H^k_{-m,c}` norm of a jet
  (sum of the `X_{-m,c}` norms of its fields); the energy `Σ_{|w| ≤ j} ‖∂^w F‖²_{X_{-m,c}}` of a
  smooth field (the `E_0 + ⋯ + E_j` of SP 3060-3061 with the weight `⟨x⟩^{-2m}` of `X_{-m,c}`,
  equivalent on the cell to `p_c⁻¹`, SP 3044-3047).

## The shared leaves (task ids `PartIII-a:T21/2/7/2/1/1/5/<k>`)
* (a) mollification: `CellPeriodicLocInt` (periodic fields of `X_{-m,c}` are locally integrable
  on the plane), `CellShiftBound` (translates by `‖y‖ ≤ 1` are bounded on the periodic `X_{-m,c}`),
  `CellConvBound` (weighted Young inequality for periodic fields), `CellConvDeriv` (smoothness,
  periodicity, derivatives fall on the kernel), `CellPeriodize` (periodization of a compactly
  supported kernel is a cylinder test, with the same pairing), `CellDenseCont`,
  `CellMollTendstoCont`, and the consequences `CellMollSmooth`, `CellMollBound`, `CellMollTendsto`,
  `CellMollWeakDeriv`;
* (c) the order `-1` bound at every level: `KTOrderMinusOne`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The mollifier -/

/-- The bump of `cellMoll n`: `ContDiffBump` at `0` of the plane with radii `1/(2(n+1)) < 1/(n+1)`
(sup norm of `ℝ × ℝ`). -/
def molBump (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    linarith

/-- The mollifier kernel `ρ_n`: smooth, nonnegative, `∫ ρ_n = 1`, supported in the closed
(sup-norm) ball of radius `1/(n+1)`, even (`ContDiffBump.normed`). -/
def molKer (n : ℕ) : ℝ × ℝ → ℝ := (molBump n).normed volume

/-- Convolution on the plane of a complex field with a real kernel:
`cellConv K f x = ∫ K(y) f(x - y) dy` (`= (K ⋆ f)(x)`, `cellConv_eq_convolution`). Applied to
`c`-periodic fields it is the convolution on the cylinder. -/
def cellConv (K : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∫ y, K y • f (x - y)

/-- The mollification `ρ_n ⋆ f` of a field on the plane (of the `c`-periodic representative). -/
def cellMoll (n : ℕ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := cellConv (molKer n) f

theorem cellConv_eq_convolution (K : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) :
    cellConv K f = MeasureTheory.convolution K f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  simp [cellConv, MeasureTheory.convolution_def]

/-- The iterated classical partial `∂^w K` of a real kernel (`B0579.pd`; the convention of
`adjSpatial`: `pdWordR (j :: w) K = ∂_j (pdWordR w K)`). -/
def pdWordR : List (Fin 2) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], K => K
  | j :: w, K => B0579.pd j (pdWordR w K)

/-- The `c`-periodization `Σ_{k ∈ ℤ} K(y₁ + kc, y₂)` of a real kernel (a locally finite sum for
compactly supported `K`). -/
def perKer (c : ℝ) (K : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  ∑' k : ℤ, K (y.1 + k * c, y.2)

/-! ## Words, jet norms, energies -/

/-- The words of length `≤ j` in the two coordinate directions. -/
def wordsLE : ℕ → Finset (List (Fin 2))
  | 0 => {[]}
  | j + 1 => insert [] (((Finset.univ : Finset (Fin 2)) ×ˢ wordsLE j).image fun p => p.1 :: p.2)

theorem mem_wordsLE {j : ℕ} {w : List (Fin 2)} : w ∈ wordsLE j ↔ w.length ≤ j := by
  induction j generalizing w with
  | zero =>
    cases w with
    | nil => simp [wordsLE]
    | cons a w => simp [wordsLE]
  | succ j ih =>
    cases w with
    | nil => simp [wordsLE]
    | cons a w =>
      simp only [wordsLE, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_image,
        Finset.mem_product, Finset.mem_univ, true_and, Prod.exists, List.cons.injEq,
        List.length_cons, Nat.add_le_add_iff_right]
      constructor
      · rintro ⟨b, v, hv, rfl, rfl⟩
        exact ih.1 hv
      · intro h
        exact ⟨a, w, ih.2 h, rfl, rfl⟩

/-- The `H^k_{-m,c}` norm of a jet: `Σ_{|w| ≤ k} ‖D w‖_{X_{-m,c}}` (equivalent to the Hilbert
norm `(Σ ‖D w‖²)^{1/2}`; SP 3060-3061). -/
def jetNorm (c m : ℝ) (k : ℕ) (D : List (Fin 2) → ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  ∑ w ∈ wordsLE k, xNorm c (-m) (D w)

/-- The energy `Σ_{|w| ≤ j} ‖∂^w F‖²_{X_{-m,c}}` of a smooth field `F` (classical partials
`adjSpatial`): `E_0 + ⋯ + E_j` of SP 3060-3061 with the weight `⟨x⟩^{-2m}` of `X_{-m,c}`
(equivalent on the cell to the periodic weight `p_c⁻¹` of SP 3044-3047). -/
def cellEnergy (c m : ℝ) (j : ℕ) (F : ℝ × ℝ → ℂ) : ℝ :=
  ∑ w ∈ wordsLE j, (xNorm c (-m) (adjSpatial w F)).toReal ^ 2

theorem cellEnergy_nonneg (c m : ℝ) (j : ℕ) (F : ℝ × ℝ → ℂ) : 0 ≤ cellEnergy c m j F :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_toReal_le_cellEnergy (c m : ℝ) {j : ℕ} (F : ℝ × ℝ → ℂ) {w : List (Fin 2)}
    (hw : w.length ≤ j) : (xNorm c (-m) (adjSpatial w F)).toReal ^ 2 ≤ cellEnergy c m j F :=
  Finset.single_le_sum (f := fun w => (xNorm c (-m) (adjSpatial w F)).toReal ^ 2)
    (fun _ _ => sq_nonneg _) (mem_wordsLE.2 hw)

/-! ## (a) Mollification of periodic fields in `X_{-m,c}` -/

/-- **(a0) Periodic fields of `X_{-m,c}` are locally integrable on the plane** (measure theory):
`f` is a.e. strongly measurable on the cell (`B0579.ac_cellMeasure`: Lebesgue measure on the cell is
absolutely continuous with respect to `cellMeasure`), hence on each translate `C_c + kc e₁` (`f` is
the translate of itself), hence on the plane (countable union, `aestronglyMeasurable_iUnion_iff`);
on a compact set, covered by finitely many translates intersected with a band `|x₂| ≤ R`, `f` is in
`L²` (the weight `jb^{-m}` is bounded below there), so in `L¹`. -/
def CellPeriodicLocInt : Prop :=
  ∀ (c m : ℝ) (f : ℝ × ℝ → ℂ), 0 < c → (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    MemLp f 2 (B0579.cellMeasure c (-m)) →
    AEStronglyMeasurable f volume ∧ LocallyIntegrable f volume

/-- **(a0') Translates are bounded on the periodic `X_{-m,c}`** (SP 3044-3047: the weight is
translation quasi-invariant). There is `C = C(c, m)` with
`‖f(· - y)‖_{X_{-m,c}} ≤ C ‖f‖_{X_{-m,c}}` for every `c`-periodic `f ∈ X_{-m,c}` and `‖y‖ ≤ 1`
(sup norm). Proof: `∫_{C_c} jb(x)^{-m} |f(x - y)|² dx = ∫_{C_c - y} jb(z + y)^{-m} |f(z)|² dz`
(`measurePreserving_sub_right`); `jb(z + y) ≍ jb(z)` within the factor `6^{|m|}` (Peetre:
`jb(u) ≤ 2 jb(u - v) jb(v)`, `jb(v) ≤ 3`); the shifted cell lies in the union of `C_c` and its
neighbours `C_c ± c e₁` restricted to `|z₁ ∓ c| ≤ c/2 + 1`, and by periodicity each piece is a piece
of the cell where `jb` changes by a factor depending on `c` only. -/
def CellShiftBound : Prop :=
  ∀ c m : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ),
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) → ‖y‖ ≤ 1 →
    MemLp (fun x => f (x - y)) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (fun x => f (x - y)) ≤ ENNReal.ofReal C * xNorm c (-m) f

/-- **(a1) Weighted Young inequality for periodic fields** (SP 3044-3047: the weight is
translation quasi-invariant). There is `C = C(c, m)` such that for every continuous real kernel `K`
vanishing outside the closed unit (sup-norm) ball and every `c`-periodic `f ∈ X_{-m,c}`:
`K ⋆ f ∈ X_{-m,c}` and `‖K ⋆ f‖_{X_{-m,c}} ≤ C (∫|K|) ‖f‖_{X_{-m,c}}`.
Proof (from `CellPeriodicLocInt`, `CellShiftBound`): pointwise Cauchy-Schwarz
`|∫ K(y) f(x - y) dy|² ≤ (∫|K|) ∫ |K(y)| |f(x - y)|² dy`, then Tonelli on `cell × plane` and
`CellShiftBound` for `‖y‖ ≤ 1` (where `K ≠ 0`); `cellConv K f` is continuous
(`HasCompactSupport.continuous_convolution_left`, `cellConv_eq_convolution`), so measurable. -/
def CellConvBound : Prop :=
  ∀ c m : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ), Continuous K →
    (∀ y : ℝ × ℝ, 1 < ‖y‖ → K y = 0) → (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    MemLp f 2 (B0579.cellMeasure c (-m)) →
    MemLp (cellConv K f) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (cellConv K f) ≤ ENNReal.ofReal (C * ∫ y, |K y|) * xNorm c (-m) f

/-- **(a2) Smoothness of the convolution** (calculus): for a smooth compactly supported real kernel
`K` and a `c`-periodic `f ∈ X_{-m,c}` (hence locally integrable on the plane: periodic, and
`L²` on bounded parts of the cell where `jb^{-m}` is bounded below), `K ⋆ f` is smooth and
`c`-periodic, and every classical partial falls on the kernel: `∂^w(K ⋆ f) = (∂^w K) ⋆ f`
(`HasCompactSupport.contDiff_convolution_left`, `HasCompactSupport.hasFDerivAt_convolution_left`,
`cellConv_eq_convolution`). -/
def CellConvDeriv : Prop :=
  ∀ (c m : ℝ) (K : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ K → HasCompactSupport K →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
    ContDiff ℝ ∞ (cellConv K f) ∧ (∀ x : ℝ × ℝ, cellConv K f (x.1 + c, x.2) = cellConv K f x) ∧
      ∀ w : List (Fin 2), adjSpatial w (cellConv K f) = cellConv (pdWordR w K) f

/-- **(a3) Periodization of a compactly supported kernel** (the plane pairing of a periodic field
is a cell pairing): for a smooth compactly supported real `K`, `perKer c K` is a cylinder test,
`∂_j (perKer c K) = perKer c (∂_j K)`, and for every `c`-periodic `f ∈ X_{-m,c}`,
`K f` is integrable on the plane with `∫_{ℝ²} K f = ∫_{C_c} (perKer c K) f`.
Proof: the sum is locally finite (`K` vanishes off a compact set), so smooth termwise, `c`-periodic
(reindex `k ↦ k + 1`) and zero for `|y₂|` large; the plane is the disjoint union of the translates
`C_c + kc e₁` (`Cyl.isAddFundamentalDomain_cell` or directly), on which `f` is the translate of
`f|_{C_c}`; only finitely many translates meet the support of `K`. -/
def CellPeriodize : Prop :=
  ∀ (c m : ℝ) (K : ℝ × ℝ → ℝ), 0 < c → ContDiff ℝ ∞ K → HasCompactSupport K →
    B0579.IsCylTest c (perKer c K) ∧
    (∀ j : Fin 2, B0579.pd j (perKer c K) = perKer c (B0579.pd j K)) ∧
    ∀ f : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
      MemLp f 2 (B0579.cellMeasure c (-m)) →
      Integrable (fun y => K y • f y) ∧
        ∫ y, K y • f y = ∫ y in B0579.cell c, perKer c K y • f y

/-- **(a4) Density of continuous periodic band-limited fields** in the periodic `X_{-m,c}`
(measure theory): every `c`-periodic `f ∈ X_{-m,c}` is approximated in `X_{-m,c}` by continuous
`c`-periodic fields vanishing for `|x₂|` large. Proof: truncate `f` to compact boxes inside the
open cell `(-c/2, c/2) × ℝ` (dominated convergence; the seam `x₁ = -c/2` is null), approximate the
truncation in `L²(cellMeasure)` by a continuous compactly supported field
(`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), multiply by a continuous cutoff
equal to `1` on the box and supported in the open cell (this does not increase the error), and take
the `c`-periodic extension (continuous: the support avoids the seam). -/
def CellDenseCont : Prop :=
  ∀ (c m : ℝ) (f : ℝ × ℝ → ℂ), 0 < c → (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    MemLp f 2 (B0579.cellMeasure c (-m)) → ∀ ε : ℝ, 0 < ε →
    ∃ h : ℝ × ℝ → ℂ, Continuous h ∧ (∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) ∧
      (∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → h x = 0) ∧
      xNorm c (-m) (f - h) ≤ ENNReal.ofReal ε

/-- **(a5) Mollification of continuous periodic band-limited fields converges** (calculus): such a
field `h` is uniformly continuous on the plane (periodic in `x₁`, zero for `|x₂| > R`), so
`|ρ_n ⋆ h - h| ≤ sup_{‖y‖ ≤ 1/(n+1)} |h(· - y) - h| → 0` uniformly (`∫ ρ_n = 1`, `ρ_n ≥ 0`), and
`ρ_n ⋆ h - h` vanishes for `|x₂| > R + 1`; the band `|x₂| ≤ R + 1` of the cell has finite
`cellMeasure`, so the `X_{-m,c}` norm is at most the sup norm times its square root. -/
def CellMollTendstoCont : Prop :=
  ∀ (c m : ℝ) (h : ℝ × ℝ → ℂ), 0 < c → Continuous h → (∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) →
    (∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → h x = 0) →
    Tendsto (fun n : ℕ => xNorm c (-m) (cellMoll n h - h)) atTop (𝓝 0)

/-- **The mollified field is smooth, periodic, with every partial in `X_{-m,c}`** (from `CellConvDeriv`
with `K = molKer n` and `CellConvBound` with `K = pdWordR w (molKer n)`, smooth and supported in
the ball of radius `1/(n+1) ≤ 1`). -/
def CellMollSmooth : Prop :=
  ∀ (c m : ℝ) (n : ℕ) (f : ℝ × ℝ → ℂ), 0 < c → (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    MemLp f 2 (B0579.cellMeasure c (-m)) →
    ContDiff ℝ ∞ (cellMoll n f) ∧ (∀ x : ℝ × ℝ, cellMoll n f (x.1 + c, x.2) = cellMoll n f x) ∧
      ∀ w : List (Fin 2), MemLp (adjSpatial w (cellMoll n f)) 2 (B0579.cellMeasure c (-m))

/-- **Mollification is bounded on the periodic `X_{-m,c}`, uniformly in `n`** (`CellConvBound` with
`K = molKer n`: `∫ |ρ_n| = ∫ ρ_n = 1`, support in the ball of radius `1/(n+1) ≤ 1`). -/
def CellMollBound : Prop :=
  ∀ c m : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (f : ℝ × ℝ → ℂ),
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
    xNorm c (-m) (cellMoll n f) ≤ ENNReal.ofReal C * xNorm c (-m) f

/-- **Mollification converges in `X_{-m,c}`** (`ε/3`: `CellDenseCont`, `CellMollTendstoCont` and
the uniform bound `CellMollBound` applied to `f - h`). -/
def CellMollTendsto : Prop :=
  ∀ (c m : ℝ) (f : ℝ × ℝ → ℂ), 0 < c → (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    MemLp f 2 (B0579.cellMeasure c (-m)) →
    Tendsto (fun n : ℕ => xNorm c (-m) (cellMoll n f - f)) atTop (𝓝 0)

/-- **Mollification commutes with periodic weak derivatives** (from `CellConvDeriv` with `w = [j]`
and `CellPeriodize`): if `g = ∂_j f` weakly on the cylinder (`HasWeakCellDerivC`), both periodic
in `X_{-m,c}`, then `∂_j(ρ_n ⋆ f) = ρ_n ⋆ g` everywhere. Proof at `x`: with `K_x(z) = ρ_n(x - z)`,
`∂_j(ρ_n ⋆ f)(x) = ∫ (∂_jρ_n)(x - z) f(z) dz = -∫ ∂_jK_x f = -∫_{C_c} ∂_j(perKer c K_x) f
= ∫_{C_c} (perKer c K_x) g = ∫ K_x g = (ρ_n ⋆ g)(x)` (change of variables `z = x - y`). -/
def CellMollWeakDeriv : Prop :=
  ∀ (c m : ℝ) (j : Fin 2) (f g : ℝ × ℝ → ℂ), 0 < c → (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
    MemLp g 2 (B0579.cellMeasure c (-m)) → HasWeakCellDerivC c j f g →
    ∀ n : ℕ, pdCx j (cellMoll n f) = cellMoll n g

/-! ## (c) The adjoint localized interaction is of order `-1` at every level -/

/-- **`K_c^T(f B) ∈ H^{j+1}_{-m,c}` for `f ∈ H^j_{-m,c}`** (SP 3052-3058: the localized source is in
`L¹ ∩ L²` by weighted Cauchy-Schwarz, the kernel splits into an integrable near part and a bounded
far part, and the derivative is an order-zero multiplier including the horizontal mean; at higher
levels the derivatives commute with the translation-invariant kernel, `∂^w K_c^T F = K_c^T ∂^w F`,
and fall on `f B` by Leibniz). For `m > 1`, `c ≥ 1`, `j : ℕ`, and a smooth `c`-periodic real
coefficient field `B` (in the applications `B = ∇E(r)`, SP 3052-3058, or its age derivatives
`∂_r^i∇E(r)` for the time jets, from `TrainSTJets`) with
`(1 + x₂²)^{(m+1)/2} ‖D^i B_l(x)‖ ≤ A` for `i ≤ j`: there is `C` such that every jet
`f ∈ H^j_{-m,c}` (`IsCellJet c m j f D`) has an adjoint `χ = K_c^T(f B)`, characterised by
`∫_{C_c} χ ψ = ∫_{C_c} f (K_cψ · B)` for every cylinder test `ψ` of any circulation with its
kernel velocity `K_cψ` (`IsKernelBiotSavart`), lying in `H^{j+1}_{-m,c}` with every field bounded by
`C ‖f‖_{H^j_{-m,c}}` (`jetNorm`). The level `j = 0` is `KernelAdjointBound`
(`Sub/PartIIIa_T21_2_1.lean`, proved: `kernelAdjointBound`) applied to `F_l = f B_l`, with the
periodic representative (`perRep`) of `χ` and of its derivatives. -/
def KTOrderMinusOne (m : ℝ) : Prop :=
  1 < m → ∀ c : ℝ, 1 ≤ c → ∀ (j : ℕ) (B : Fin 2 → ℝ × ℝ → ℝ) (A : ℝ),
    (∀ l, ContDiff ℝ ∞ (B l)) → (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    (∀ l (i : ℕ), i ≤ j → ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖iteratedFDeriv ℝ i (B l) x‖ ≤ A) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m j f D →
      ∃ (χ : ℝ × ℝ → ℂ) (Dχ : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m (j + 1) χ Dχ ∧
        (∀ w : List (Fin 2), w.length ≤ j + 1 →
          xNorm c (-m) (Dχ w) ≤ ENNReal.ofReal C * jetNorm c m j D) ∧
        ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ →
          IsKernelBiotSavart c ψ uψ →
          IntegrableOn (fun x => f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ))
              (B0579.cell c) ∧
            ∫ x in B0579.cell c, χ x * (ψ x : ℂ) =
              ∫ x in B0579.cell c, f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ)

end UnforcedLeray.Short.IIIa
