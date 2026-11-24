import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatCurlTerm
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# `FlatForceSmooth` from three source facts (decomposition of `PartIII-b:C/flatset/col/1/2`)

Source of record `the November 2 reference manuscript`: 4594-4596, 4976, 4988
("the sums and their required derivatives converge by Gaussian decay").

`f_A = -∑'_j fTerm`, and by `ft_fTerm_closed` the two meridional components of the `j`-th term are
`ftF1, ftF2 (ageA ν s) B` (a Gaussian times a polynomial) evaluated at `x_j = (q - jc, η)`.  So the
components are (minus) the `c`-periodization in `q` of the Schwartz functions `ftF1, ftF2`, and the
periodization of a Schwartz function is `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Leaf 1** (source 4594-4596, 4976): the components of `f_A` as lattice sums of the explicit
Gaussian-times-polynomial profiles `ftF1`, `ftF2`.  Route: unfold `fA`, `merOf`, `emb`, `mv`;
`ft_fTerm_closed`; the coordinate projections commute with the `tsum` by summability (Leaf 3 plus
Schwartz decay, see `Concrete/SummableProof.lean`); `mv B (emb V) = emb (merApply B V)` since
`emb V` has vanishing middle entry. -/
def FlatForceClosed : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    fMer ν μ χ A s 0 x =
        -∑' j : ℤ, ftF1 (ageA ν s) (Bmat ν μ χ A s) (xj ν j x).1 (xj ν j x).2 ∧
      fMer ν μ χ A s 1 x =
        -∑' j : ℤ, ftF2 (ageA ν s) (Bmat ν μ χ A s) (xj ν j x).1 (xj ν j x).2

/-- **Leaf 2** (source 4988): the `c`-periodization in `q` of a Schwartz function on the plane is
`C^∞`.  Route: induction on the order `k` of the statement "periodization of every Schwartz
function is `C^k`" (also for vector-valued Schwartz functions, applied to `fderiv f`); the one-step
fact `HasFDerivAt (periodize f) (periodize (fderiv f)) x` is `hasFDerivAt_tsum_of_isPreconnected`
on a ball around `x`, with the summable majorant
`C (1 + |j c| - R)^(-3)` (from the Schwartz seminorm bound, `SchwartzMap.le_seminorm`) on `‖y‖ ≤ R`. -/
def PeriodizeSchwartzSmooth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : SchwartzMap (ℝ × ℝ) ℝ,
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => ∑' j : ℤ, f (x.1 - j * c, x.2))

/-- **Leaf 3** (source 4976, 4988): `ftF1`, `ftF2` are Schwartz functions of `(u,v)` for `a > 0`
(Gaussian `exp(-(u²+v²)/(4a))` times a polynomial in `u, v`). -/
def FlatTermSchwartz : Prop :=
  ∀ (a : ℝ) (B : Mat3), 0 < a → ∃ f1 f2 : SchwartzMap (ℝ × ℝ) ℝ,
    (∀ y : ℝ × ℝ, f1 y = ftF1 a B y.1 y.2) ∧ ∀ y : ℝ × ℝ, f2 y = ftF2 a B y.1 y.2

theorem cOf_pos {ν : ℝ} (hν : 0 < ν) : 0 < cOf ν := by
  unfold cOf
  positivity

theorem ageA_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 0 < ageA ν s := by
  unfold ageA
  positivity

/-- `FlatForceSmooth` from the three leaves. -/
theorem flatForceSmooth_of (h1 : FlatForceClosed) (h2 : PeriodizeSchwartzSmooth)
    (h3 : FlatTermSchwartz) : FlatForceSmooth := by
  intro ν μ χ A s hν hs i
  obtain ⟨f1, f2, e1, e2⟩ := h3 (ageA ν s) (Bmat ν μ χ A s) (ageA_pos hν hs)
  have hc := cOf_pos hν
  fin_cases i
  · have : fMer ν μ χ A s 0 =
        fun x => -∑' j : ℤ, f1 (x.1 - j * cOf ν, x.2) := by
      funext x
      rw [(h1 ν μ χ A s hν hs x).1]
      simp only [e1]
      rfl
    simp only [Fin.zero_eta]
    rw [this]
    exact (h2 _ hc f1).neg
  · have : fMer ν μ χ A s 1 =
        fun x => -∑' j : ℤ, f2 (x.1 - j * cOf ν, x.2) := by
      funext x
      rw [(h1 ν μ χ A s hν hs x).2]
      simp only [e2]
      rfl
    simp only [Fin.mk_one]
    rw [this]
    exact (h2 _ hc f2).neg

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
