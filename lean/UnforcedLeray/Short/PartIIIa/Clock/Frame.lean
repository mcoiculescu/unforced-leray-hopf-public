import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# Part III-a full clock: the periodized moving frame (SP 2891-2897)

The frame `E(z), Λ(z)` of `MovingFrame` is built from the planar growing pair of Part I
(Proposition `short-gaussian-seed`, `IsSeedXG`):

* `PlanarFrameKernels`: the two planar growing vectors `e_i` (Gaussian tails) and the planar dual
  kernels `λ_i` (decay `O(|y|^{-2})`, from `eq:short-seed-green`, `eq:short-seed-functional`),
  biorthogonal on the plane.
* The cell has period `d = c/√a` in the first coordinate (`B0579.cell`), so the periodization is
  `P_d f (y) = Σ_{n∈ℤ} f(y₁ + n d, y₂)` (`perSum`), `E_i = P_d e_i`, `Λ⁰_i = P_d λ_i`, and the
  rows are normalised by the finite Gram inverse `Λ = G⁻¹ Λ⁰`, `G_{ij} = ∫_cell Λ⁰_i E_j`
  (SP 2891-2897).
* `periodizedFrame`: the `MovingFrame` with these `E, Λ`, once its three analytic fields hold
  (`PerFrameFacts`: invertible Gram, `Λ E = I₂`, the uniform bounds; SP 2894-2897).
* `GoodFrameExists_of`: the assembly from the facts, the stability `FrameStableAll`
  (SP 2960-2990, leaf `T21/c3`) and amplitude `FrameAmplitudeAll` (SP 2991-3000, leaf `T21/c5`)
  for the periodized frame, in the "all large `C`" form (a larger constant only weakens the
  statements).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The complex number of a planar point `(y₁, y₂)`. -/
def planeToC (y : ℝ × ℝ) : ℂ := ⟨y.1, y.2⟩

/-- Planar growing vectors `e_i` and planar dual kernels `λ_i`, `i ∈ Fin 2` (SP 2891-2897):
`e_i` has Gaussian tails, `λ_i` has the decay `O(|y|^{-2})` (`eq:short-seed-green`,
`eq:short-seed-functional`), and `∫ λ_i e_j = δ_{ij}` over the plane. -/
structure PlanarFrameKernels where
  e : Fin 2 → ℝ × ℝ → ℂ
  lamP : Fin 2 → ℝ × ℝ → ℂ
  e_cont : ∀ i, Continuous (e i)
  lamP_cont : ∀ i, Continuous (lamP i)
  e_decay : ∃ C : ℝ, ∀ i y, ‖e i y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)
  lamP_decay : ∃ C : ℝ, ∀ i y, ‖lamP i y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2
  biorth : ∀ i j, ∫ y, lamP i y * e j y = if i = j then 1 else 0

/-- The kernels come from the Part I seed (`IsSeedXG`): `e₀ = q = h(r)e^{2iϑ}`, `e₁ = \bar q`, and
`λ₀, λ₁` represent `ℓ` on the sectors `2` and `-2`: `∫ λ₀ f = ℓ(f₂)` and
`∫ λ₁ f = \overline{ℓ(\overline{f_{-2}})}`-type conjugate functional of `seedProjFun`
(`seedEll`, `eq:short-seed-functional`), for smooth compactly supported planar `f`
(SP 593-610, 2891-2897). -/
def IsSeedKernels (κ : PlanarFrameKernels) : Prop :=
  ∃ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ ∧
    (∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) ∧
    (∀ y, κ.e 1 y = conj (PartI.seedPlanar h (planeToC y))) ∧
    (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y, κ.lamP 0 y * f (planeToC y) = PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
      ∫ y, κ.lamP 1 y * f (planeToC y) =
        conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r))))

/-- The planar kernels of Part I exist (the leaf `T21/c1/a`). -/
def PlanarFrameKernelsExist : Prop := ∃ κ : PlanarFrameKernels, IsSeedKernels κ

/-- Periodization with period `d` in the first coordinate. -/
def perSum (d : ℝ) (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ := ∑' n : ℤ, f (y.1 + n * d, y.2)

/-- Periodized growing vectors `E_i = P_d e_i`. -/
def perE (κ : PlanarFrameKernels) (d : ℝ) (i : Fin 2) : ℝ × ℝ → ℂ := perSum d (κ.e i)

/-- Unnormalised periodized dual rows `Λ⁰_i = P_d λ_i`. -/
def perLam0 (κ : PlanarFrameKernels) (d : ℝ) (i : Fin 2) : ℝ × ℝ → ℂ := perSum d (κ.lamP i)

/-- The finite Gram matrix `G_{ij} = ∫_cell Λ⁰_i E_j`. -/
def perGram (κ : PlanarFrameKernels) (d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∫ x in B0579.cell d, perLam0 κ d i x * perE κ d j x

/-- `x^{-2} = (x⁻¹)²` for `x ≥ 0`. -/
lemma perCont_rpow_neg_two_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = (x⁻¹) ^ 2 := by
  rw [Real.rpow_neg hx, Real.rpow_two, inv_pow]

/-- The Gaussian is dominated by the translate weight: `e^{-(a²+b²)/8} ≤ 16 (1+|a|)^{-2}`. -/
lemma perCont_exp_le_translate_weight (a b : ℝ) :
    Real.exp (-(a ^ 2 + b ^ 2) / 8) ≤ 16 * (1 + |a|) ^ (-(2 : ℝ)) := by
  have hpos : 0 < 1 + |a| := by positivity
  rw [perCont_rpow_neg_two_eq _ hpos.le, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : Real.exp (-(a ^ 2 + b ^ 2) / 8) ≤ Real.exp (-(a ^ 2) / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg b])
  have h2 : a ^ 2 / 8 + 1 ≤ Real.exp (a ^ 2 / 8) := Real.add_one_le_exp _
  have h3 : Real.exp (-(a ^ 2) / 8) * Real.exp (a ^ 2 / 8) = 1 := by
    rw [← Real.exp_add]
    have : -(a ^ 2) / 8 + a ^ 2 / 8 = 0 := by ring
    rw [this, Real.exp_zero]
  have h4 : (1 + |a|) ^ 2 ≤ 16 * Real.exp (a ^ 2 / 8) := by
    nlinarith [abs_nonneg a, sq_abs a, sq_nonneg (|a| - 1)]
  calc Real.exp (-(a ^ 2 + b ^ 2) / 8) * (1 + |a|) ^ 2
      ≤ Real.exp (-(a ^ 2) / 8) * (16 * Real.exp (a ^ 2 / 8)) :=
        mul_le_mul h1 h4 (by positivity) (Real.exp_pos _).le
    _ = 16 * (Real.exp (-(a ^ 2) / 8) * Real.exp (a ^ 2 / 8)) := by ring
    _ = 16 := by rw [h3, mul_one]

/-- `E_i = P_d e_i` is continuous for `d > 0` (for the measurability field of `MovingFrame`). -/
theorem perE_continuous_aux (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d) (i : Fin 2) :
    Continuous (perE κ d i) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  have hT : ∀ z : ℝ × ℝ, ‖κ.e i z‖ ≤ (16 * |C|) * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z =>
    calc ‖κ.e i z‖ ≤ C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := hC i z
      _ ≤ |C| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (perCont_exp_le_translate_weight z.1 z.2) (abs_nonneg C)
      _ = 16 * |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
  have heq : perE κ d i = fun y => ∑' n : ℤ, κ.e i (y - Gaussian.shiftVec (-d) n) := by
    funext y
    unfold perE perSum
    refine tsum_congr fun n => ?_
    congr 1
    ext <;> simp [Gaussian.shiftVec]
  rw [heq]
  exact Gaussian.continuous_tsum_translates (κ.e_cont i) (s := 2) (c := -d) (C := 16 * |C|)
    (by norm_num) (neg_ne_zero.2 hd.ne') hT

/-- Normalised dual rows `Λ = G⁻¹ Λ⁰` (SP 2891-2897). -/
def perLam (κ : PlanarFrameKernels) (d : ℝ) (i : Fin 2) : ℝ × ℝ → ℂ :=
  fun x => ∑ j, (perGram κ d)⁻¹ i j * perLam0 κ d j x

/-- The three analytic fields of `MovingFrame` for the periodized `E, Λ` at the cell lengths
`d(s) = c/√a(s)`, `c = ν^{-2}` (SP 2891-2897: invertible Gram, `ΛE = I₂`, uniform bounds). -/
def PerFrameFacts (κ : PlanarFrameKernels) (ν m b K : ℝ) : Prop :=
  (∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i j : Fin 2,
    ∫ x in movingCell ν (ν ^ (-2 : ℝ)) s,
      perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j x = if i = j then 1 else 0) ∧
  (∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i,
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m
        (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i) ≤ ENNReal.ofReal K) ∧
  (∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i (W : ℝ × ℝ → ℂ),
    ENNReal.ofReal ‖∫ x in movingCell ν (ν ^ (-2 : ℝ)) s,
        perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x * W x‖ ≤
      ENNReal.ofReal K * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m W)

/-- The periodized moving frame, given its analytic facts. -/
def periodizedFrame (κ : PlanarFrameKernels) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) :
    MovingFrame ν (ν ^ (-2 : ℝ)) m b K where
  E := fun s => perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
  lam := fun s => perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
  dual := hF.1
  E_meas := fun s hs _ i => by
    have ha : 0 < clockA ν s := by unfold clockA; positivity
    have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := by
      unfold cellLen; positivity
    exact (perE_continuous_aux κ hd i).aestronglyMeasurable
  E_bdd := hF.2.1
  lam_bdd := hF.2.2

/-- Leaf `T21/c1/b`: uniform frame facts (SP 2894-2897: Gram inverse exists uniformly, direct
columns have Gaussian tails, dual error `O(d^{-2})`). -/
def PerFrameFactsAll (κ : PlanarFrameKernels) : Prop :=
  ∀ m : ℝ, 8 < m → ∃ (K b₀ : ℝ), ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, PerFrameFacts κ ν m b K

/-- Leaf `T21/c3`: block-product stability of the periodized frame (SP 2960-2990). -/
def FrameStableAll (κ : PlanarFrameKernels) : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : ℝ,
    ∃ (C₀ h₀ b₀ : ℝ), 0 < h₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ ν (hν : ν ∈ Ioc 0 ν₀), ∀ hF : PerFrameFacts κ ν m b K,
        FrameStable P (periodizedFrame κ ν m b K (hν.1) hF) C h₀

/-- Leaf `T21/c5`: amplitude equation of the periodized frame (SP 2921-2933, 2991-3000). -/
def FrameAmplitudeAll (κ : PlanarFrameKernels) : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : ℝ,
    ∃ (C₀ b₀ : ℝ), ∀ C : ℝ, C₀ ≤ C → ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ ν (hν : ν ∈ Ioc 0 ν₀), ∀ hF : PerFrameFacts κ ν m b K,
        FrameAmplitude P (periodizedFrame κ ν m b K (hν.1) hF) C

/-- Assembly: a good frame exists. -/
theorem GoodFrameExists_of (κ : PlanarFrameKernels) (hF : PerFrameFactsAll κ)
    (hS : FrameStableAll κ) (hA : FrameAmplitudeAll κ) : GoodFrameExists := by
  intro P hP m hm
  obtain ⟨K, b₁, hb₁⟩ := hF m hm
  obtain ⟨C₁, h₀, b₂, hh₀, hS'⟩ := hS P hP m hm K
  obtain ⟨C₂, b₃, hA'⟩ := hA P hP m hm K
  refine ⟨K, max C₁ C₂, h₀, max b₁ (max b₂ b₃), hh₀, fun b hb => ?_⟩
  have hb1 : b₁ ≤ b := le_trans (le_max_left _ _) hb
  have hb2 : b₂ ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hb3 : b₃ ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨ν₁, hν₁, h1⟩ := hb₁ b hb1
  obtain ⟨ν₂, hν₂, h2⟩ := hS' (max C₁ C₂) (le_max_left _ _) b hb2
  obtain ⟨ν₃, hν₃, h3⟩ := hA' (max C₁ C₂) (le_max_right _ _) b hb3
  refine ⟨min ν₁ (min ν₂ ν₃), lt_min hν₁ (lt_min hν₂ hν₃), fun ν hν => ?_⟩
  have hν1 : ν ∈ Ioc 0 ν₁ := ⟨hν.1, le_trans hν.2 (min_le_left _ _)⟩
  have hν2 : ν ∈ Ioc 0 ν₂ :=
    ⟨hν.1, le_trans hν.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν3 : ν ∈ Ioc 0 ν₃ :=
    ⟨hν.1, le_trans hν.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hfact := h1 ν hν1
  exact ⟨periodizedFrame κ ν m b K hν.1 hfact, h2 ν hν2 hfact, h3 ν hν3 hfact⟩

/-- Unconditional-in-structure form: with the Part I kernels, the three leaves give the frame. -/
theorem goodFrameExists_of_leaves (hK : PlanarFrameKernelsExist)
    (hF : ∀ κ : PlanarFrameKernels, IsSeedKernels κ → PerFrameFactsAll κ)
    (hS : ∀ κ : PlanarFrameKernels, IsSeedKernels κ → FrameStableAll κ)
    (hA : ∀ κ : PlanarFrameKernels, IsSeedKernels κ → FrameAmplitudeAll κ) :
    GoodFrameExists := by
  obtain ⟨κ, hκ⟩ := hK
  exact GoodFrameExists_of κ (hF κ hκ) (hS κ hκ) (hA κ hκ)

end UnforcedLeray.Short.IIIa
