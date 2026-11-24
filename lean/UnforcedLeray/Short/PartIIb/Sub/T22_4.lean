import UnforcedLeray.Short.PartIIb.Sub.T22

/-!
# Decomposition of `PartII-b:T22/4` (`CylDiffusionBound`)

Source: `the November 2 reference manuscript` lines 2092-2101 ("its distributional
Laplacian is bounded above by `C_m` times the weight") and 2103-2104 (smoothing).

Route: with `w = jb^m` and `g` in `CylSmoothDecay c`, `div (g w ∇g) = w |∇g|² + g ∇w·∇g + g w Δg`;
the cell integral of the divergence vanishes (seam terms cancel by `c`-periodicity of `g`, `∇g` and
evenness of `jb` in `q`; the `η` ends are removed by a cut-off and the decay).  Hence

`2 ∫ g Δg w = -2 ∫ w |∇g|² - 2 ∫ g ∇w·∇g ≤ 2 m² ∫ g² w`,

using `|∂_i w| ≤ m w` (`t22_pd_jb_le`) and `2 m |g||p| ≤ p² + m² g²`; `C_m = 2 m²`.
The leaves are `DbInt1`, `DbInt2` (integrability), `DbCutId` (cut-off identity), `DbCutoff` (family
of cut-offs), `DbLimit` (removing the cut-off), assembled to `DbIdentity`; this file proves
`cylDiffusionBound_of` from `DbInt1`, `DbInt2`, `DbIdentity`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Leaf `/1` (SP 2092-2101): for `g ∈ CylSmoothDecay c` the integrands `g² w` and `g Δg w` are
integrable on the cell (the decay `(1+η²)^N` against `∫_cell jb^m (1+η²)^N`-type integrability;
`integrable_jb_neg4` and `CylSmoothDecay.cell_decay`). -/
def DbInt1 : Prop :=
  ∀ m : ℝ, 0 < m → ∀ c : ℝ, 0 < c → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
    IntegrableOn (fun x => g x ^ 2 * (B0579.density m x : ℝ)) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * lapP g x * (B0579.density m x : ℝ)) (B0579.cell c)

/-- Leaf `/2` (SP 2092-2101): integrability on the cell of the two gradient terms
`w |∇g|²` and `g ∇w·∇g`, `w = jb^m`. -/
def DbInt2 : Prop :=
  ∀ m : ℝ, 0 < m → ∀ c : ℝ, 0 < c → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
    IntegrableOn (fun x => (B0579.density m x : ℝ) *
        (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
        B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x)) (B0579.cell c)

/-- Leaf `/3` (SP 2092-2101): the integration by parts on the cell against a cut-off `χ(η)` of
compact support: `∫ χ² (g Δg w + w|∇g|² + g ∇w·∇g) = -∫ 2 χ χ' g w ∂_η g`.  Seam terms cancel by
periodicity (`integral_cell_deriv_q`), the `η`-terms by `integral_cell_deriv_eta`. -/
def DbCutId : Prop :=
  ∀ m : ℝ, 0 < m → ∀ c : ℝ, 0 < c → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
    ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ x in B0579.cell c, χ x.2 ^ 2 * (g x * lapP g x * (B0579.density m x : ℝ)) =
        -(∫ x in B0579.cell c, χ x.2 ^ 2 * ((B0579.density m x : ℝ) *
            (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2))) -
        (∫ x in B0579.cell c, χ x.2 ^ 2 * (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x *
            B0579.pd 0 g x + B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x))) -
        (∫ x in B0579.cell c, 2 * χ x.2 * deriv χ x.2 *
            (g x * (B0579.density m x : ℝ) * B0579.pd 1 g x))

/-- Leaf `/4` (SP 2103-2104): a family of smooth compactly supported cut-offs in `η`:
`0 ≤ χ_n ≤ 1`, `χ_n = 1` on `[-n, n]`, `|χ_n'| ≤ K / (n+1)` (e.g. `χ_n(t) = ψ(t/(n+1))`). -/
def DbCutoff : Prop :=
  ∃ χ : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
    (∀ n t, 0 ≤ χ n t ∧ χ n t ≤ 1) ∧ (∀ n : ℕ, ∀ t ∈ Icc (-(n : ℝ)) n, χ n t = 1) ∧
    ∃ K : ℝ, ∀ (n : ℕ) (t : ℝ), |deriv (χ n) t| ≤ K / ((n : ℝ) + 1)

/-- The identity after removing the cut-off. -/
def DbIdentity : Prop :=
  ∀ m : ℝ, 0 < m → ∀ c : ℝ, 0 < c → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
    2 * ∫ x in B0579.cell c, g x * lapP g x * (B0579.density m x : ℝ) =
      -2 * (∫ x in B0579.cell c, (B0579.density m x : ℝ) *
          (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) -
      2 * (∫ x in B0579.cell c, g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
          B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x))

/-- Leaf `/5` (SP 2103-2104): `R → ∞` in `DbCutId` by dominated convergence (integrands of
`DbInt1`, `DbInt2`, `|χ_n'| ≤ K/(n+1)` against the integrable `|g| w |∂_η g|`). -/
def DbLimitStmt : Prop := DbInt1 → DbInt2 → DbCutId → DbCutoff → DbIdentity

theorem db_cross (m w g a u : ℝ) (hw : 0 ≤ w) (hu : |u| ≤ m * w) :
    -(2 * (g * (u * a))) ≤ w * (a ^ 2 + m ^ 2 * g ^ 2) := by
  have h2 : |g * (u * a)| ≤ |g| * |a| * (m * w) := by
    rw [abs_mul, abs_mul]
    calc |g| * (|u| * |a|) = |g| * |a| * |u| := by ring
      _ ≤ |g| * |a| * (m * w) := by gcongr
  have h3 : 0 ≤ w * (|a| - m * |g|) ^ 2 := by positivity
  have e : |a| ^ 2 = a ^ 2 := sq_abs a
  have e' : |g| ^ 2 = g ^ 2 := sq_abs g
  rw [show w * (|a| - m * |g|) ^ 2 = w * (|a| ^ 2 + m ^ 2 * |g| ^ 2) - 2 * (|g| * |a| * (m * w))
    by ring, e, e'] at h3
  linarith [neg_abs_le (g * (u * a))]

theorem db_pointwise (m : ℝ) (hm : 0 < m) (x : B0579.Plane) (g a b : ℝ) :
    -2 * ((B0579.density m x : ℝ) * (a ^ 2 + b ^ 2)) -
        2 * (g * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * a +
          B0579.pd 1 (fun y => B0579.jb y ^ m) x * b)) ≤
      2 * m ^ 2 * (g ^ 2 * (B0579.density m x : ℝ)) := by
  have hd : (B0579.density m x : ℝ) = B0579.jb x ^ m :=
    Real.coe_toNNReal _ (Real.rpow_nonneg (B0579.jb_pos x).le _)
  obtain ⟨h0, h1⟩ := t22_pd_jb_le hm.le x
  have hw0 : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [hd]
  have e1 := db_cross m _ g a _ hw0 h0
  have e2 := db_cross m _ g b _ hw0 h1
  nlinarith

theorem cylDiffusionBound_of (h1 : DbInt1) (h2 : DbInt2) (h3 : DbIdentity) :
    CylDiffusionBound := by
  intro m hm
  refine ⟨2 * m ^ 2, fun c hc g hg => ?_⟩
  obtain ⟨i1, i2⟩ := h1 m hm c hc g hg
  obtain ⟨j1, j2⟩ := h2 m hm c hc g hg
  refine ⟨i1, i2, ?_⟩
  rw [h3 m hm c hc g hg]
  have hint : IntegrableOn (fun x => -2 * ((B0579.density m x : ℝ) *
        (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) -
      2 * (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
          B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x))) (B0579.cell c) :=
    (j1.const_mul (-2)).sub (j2.const_mul 2)
  have hrhs : IntegrableOn (fun x => 2 * m ^ 2 * (g x ^ 2 * (B0579.density m x : ℝ)))
      (B0579.cell c) := i1.const_mul _
  have key := integral_mono hint hrhs
    (fun x => db_pointwise m hm x (g x) (B0579.pd 0 g x) (B0579.pd 1 g x))
  have e1 : ∫ x in B0579.cell c, (-2 * ((B0579.density m x : ℝ) *
        (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) -
      2 * (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
          B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x))) =
      -2 * (∫ x in B0579.cell c, (B0579.density m x : ℝ) *
          (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) -
      2 * (∫ x in B0579.cell c, g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
          B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x)) := by
    rw [integral_sub (j1.const_mul (-2)) (j2.const_mul 2), integral_const_mul, integral_const_mul]
  rw [e1, integral_const_mul] at key
  unfold cylEnergy
  linarith

end UnforcedLeray.Short.IIb
