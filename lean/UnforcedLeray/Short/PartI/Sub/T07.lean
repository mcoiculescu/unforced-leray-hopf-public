import UnforcedLeray.Lib.Train.Datum
import UnforcedLeray.Units.B0151.Linf

/-!
# Part I, task `PartI:T07`: period-independent interpolation on the cylinder (conditional)

Source of record: `the November 2 reference manuscript`, lines 355-357
("Its constants are independent of the period: integration by parts gives
`‖D^l f‖_{2m/l} ≤ C_m ‖f‖_∞^{1-l/m} ‖D^m f‖_2^{l/m}`") and lines 366-374 (the cylinder interpolation
inequality `‖f‖_∞ ≤ C‖f‖_2^{1/2}‖D²f‖_2^{1/2} + C c^{-1/2}‖f‖_2^{1/2}‖∇f‖_2^{1/2}`, "includes the

centred cell `Cyl.cell c` with the library vocabulary of `Lib/Train/Datum.lean`
(`Train.jet j f = D^j f`, `Train.cellL2 c f = ‖f‖_{L²(cell)}` in `ℝ≥0∞`) and `‖f‖_∞ = ⨆ z, ‖f z‖ₑ`.
All derivatives of `f` are assumed to lie in `L²(cell)`, which makes every norm finite, so no
inequality is made true by a junk value; the constants do not depend on `c ≥ 1`. For `l = 0` the
exponent `2m/l` is undefined, so conjunct 2 is stated for `1 ≤ l ≤ m` (`l = 0` is trivial).

## Decomposition

* `CylSupInterp` (conjunct 1) follows from `CylAgmonL2` and `CylGradInterpL2` (`cylSupInterp_of`,
  proved below): the scale-invariant Agmon step
  `‖f‖_∞² ≤ 2(c⁻¹‖f‖‖Df‖ + ‖Df‖² + ‖f‖‖D²f‖)` (this is the proof of `B0151.enorm_le_H2` with the
  AM-GM step replaced by the line bound for `h ∂_q h`), and the gradient interpolation
  `‖Df‖² ≤ 4‖f‖‖D²f‖` (`B0151.interpolation_q`, `interpolation_η`).
* `CylGN` (conjunct 2) is split into `LogConvexChain` (pure real analysis), `CylMixedGN` (the
  integration-by-parts/Hölder step `‖∂_v u‖_r² ≤ (r-1)‖u‖_s‖∂_v² u‖_t`, `1/s + 1/t = 2/r`),
  `CylJetWord` (jets versus coordinate words), `CylDerivFinite` (all derivatives bounded and in every
  `L^p`, `p ≥ 2`) and `CylCellEtaZero` (the `η`-direction integration by parts on the cell).
  `CylCellBridge` transports statements between the library cell `(0, c]` of `Units/B0151` and the
  centred cell `Cyl.cell c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### The two conjuncts of the target -/

/-- **Conjunct 1** (source lines 366-374): uniform cylinder interpolation for the sup norm. -/
def CylSupInterp : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ f : Cyl.Plane → ℝ, ContDiff ℝ ∞ f → Cyl.IsPeriodic c f →
    MemLp f 2 (Cyl.cellμ c) → MemLp (Train.jet 1 f) 2 (Cyl.cellμ c) →
    MemLp (Train.jet 2 f) 2 (Cyl.cellμ c) →
    ∀ z : Cyl.Plane, ‖f z‖ₑ ≤
      ENNReal.ofReal C * (Train.cellL2 c f * Train.cellL2 c (Train.jet 2 f)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (C * c ^ (-(1 / 2 : ℝ))) *
          (Train.cellL2 c f * Train.cellL2 c (Train.jet 1 f)) ^ (1 / 2 : ℝ)

/-- **Conjunct 2** (source lines 355-357): the period-independent Gagliardo-Nirenberg inequality
`‖D^l f‖_{2m/l} ≤ C_m ‖f‖_∞^{1-l/m} ‖D^m f‖_2^{l/m}`, `1 ≤ l ≤ m`. -/
def CylGN : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ c : ℝ, 1 ≤ c → ∀ f : Cyl.Plane → ℝ,
    ContDiff ℝ ∞ f → Cyl.IsPeriodic c f → (∀ j : ℕ, MemLp (Train.jet j f) 2 (Cyl.cellμ c)) →
    ∀ l : ℕ, 1 ≤ l → l ≤ m →
      eLpNorm (Train.jet l f) (ENNReal.ofReal (2 * m / l)) (Cyl.cellμ c) ≤
        ENNReal.ofReal Cm * (⨆ z, ‖f z‖ₑ) ^ (1 - (l : ℝ) / m) *
          Train.cellL2 c (Train.jet m f) ^ ((l : ℝ) / m)

/---/
def CylinderInterpolationUniform : Prop := CylSupInterp ∧ CylGN

/-! ### Conjunct 1: Agmon step and gradient interpolation -/

/-- **Agmon step on the cylinder** (scale-invariant): for smooth `c`-periodic `f` with
`f, Df, D²f ∈ L²(cell)` and every `z`,
`‖f z‖² ≤ 2 (c⁻¹ ‖f‖₂‖Df‖₂ + ‖Df‖₂² + ‖f‖₂‖D²f‖₂)`.
Proof: `f(q₀,η₀)² ≤ c⁻¹ ∫_q f(q,η₀)² dq + ∫_q |2 f ∂_q f|(q,η₀) dq` (circle bound, `B0151.sq_le_circle`);
the line bound in `η` (`B0151.ae_sq_le_line`, `abs_le_integral_deriv`) gives
`∫_q f(q,η₀)² ≤ ∫_cell |2 f ∂_η f|` and `∫_q |f ∂_q f|(q,η₀) ≤ ∫_cell |∂_η(f ∂_q f)|`; then
`|∂_η f|, |∂_q f| ≤ ‖Df‖`, `|∂_q∂_η f| ≤ ‖D²f‖` and Cauchy-Schwarz. -/
def CylAgmonL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Cyl.Plane → ℝ, ContDiff ℝ ∞ f → Cyl.IsPeriodic c f →
    MemLp f 2 (Cyl.cellμ c) → MemLp (Train.jet 1 f) 2 (Cyl.cellμ c) →
    MemLp (Train.jet 2 f) 2 (Cyl.cellμ c) → ∀ z : Cyl.Plane,
      ‖f z‖ₑ ^ 2 ≤ 2 * (ENNReal.ofReal c⁻¹ * (Train.cellL2 c f * Train.cellL2 c (Train.jet 1 f)) +
        Train.cellL2 c (Train.jet 1 f) ^ 2 + Train.cellL2 c f * Train.cellL2 c (Train.jet 2 f))

/-- **Gradient interpolation on the cylinder** (`B0151.interpolation_q`, `interpolation_η`,
`‖∂h‖₂² ≤ ‖h‖₂‖∂²h‖₂` in each direction; `‖Df‖ = |∂_q f| + |∂_η f|` pointwise):
`‖Df‖₂² ≤ 4 ‖f‖₂ ‖D²f‖₂`. -/
def CylGradInterpL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Cyl.Plane → ℝ, ContDiff ℝ ∞ f → Cyl.IsPeriodic c f →
    MemLp f 2 (Cyl.cellμ c) → MemLp (Train.jet 1 f) 2 (Cyl.cellμ c) →
    MemLp (Train.jet 2 f) 2 (Cyl.cellμ c) →
      Train.cellL2 c (Train.jet 1 f) ^ 2 ≤ 4 * (Train.cellL2 c f * Train.cellL2 c (Train.jet 2 f))

/-- Conjunct 1 from the Agmon step and the gradient interpolation, with `C = 4`. -/
theorem cylSupInterp_of (hA : CylAgmonL2) (hB : CylGradInterpL2) : CylSupInterp := by
  refine ⟨4, by norm_num, ?_⟩
  intro c hc f hf hper h0 h1 h2 z
  have hcpos : 0 < c := by linarith
  have hAz := hA c hcpos f hf hper h0 h1 h2 z
  have hBz := hB c hcpos f hf hper h0 h1 h2
  set F := Train.cellL2 c f with hF
  set D1 := Train.cellL2 c (Train.jet 1 f) with hD1
  set D2 := Train.cellL2 c (Train.jet 2 f) with hD2
  have hsq : ‖f z‖ₑ ^ 2 ≤
      16 * (ENNReal.ofReal c⁻¹ * (F * D1)) + 16 * (F * D2) := by
    calc ‖f z‖ₑ ^ 2
        ≤ 2 * (ENNReal.ofReal c⁻¹ * (F * D1) + D1 ^ 2 + F * D2) := hAz
      _ ≤ 2 * (ENNReal.ofReal c⁻¹ * (F * D1) + 4 * (F * D2) + F * D2) := by gcongr
      _ = 2 * (ENNReal.ofReal c⁻¹ * (F * D1)) + 10 * (F * D2) := by ring
      _ ≤ 16 * (ENNReal.ofReal c⁻¹ * (F * D1)) + 16 * (F * D2) := by
        gcongr <;> norm_num
  have hroot : (‖f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) = ‖f z‖ₑ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h16 : (16 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 4 := by
    have : (16 : ℝ≥0∞) = 4 ^ (2 : ℕ) := by norm_num
    rw [this, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hle : ‖f z‖ₑ ≤ (16 * (ENNReal.ofReal c⁻¹ * (F * D1)) + 16 * (F * D2)) ^ (1 / 2 : ℝ) := by
    rw [← hroot]
    exact ENNReal.rpow_le_rpow hsq (by norm_num)
  have hadd := ENNReal.rpow_add_le_add_rpow (16 * (ENNReal.ofReal c⁻¹ * (F * D1)))
    (16 * (F * D2)) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hc12 : (ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) = ENNReal.ofReal (c ^ (-(1 / 2 : ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_pos (inv_pos.2 hcpos), Real.inv_rpow hcpos.le, Real.rpow_neg hcpos.le]
  have hX : (16 * (ENNReal.ofReal c⁻¹ * (F * D1))) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (4 * c ^ (-(1 / 2 : ℝ))) * (F * D1) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), h16, hc12,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    simp [mul_assoc]
  have hY : (16 * (F * D2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal 4 * (F * D2) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), h16]
    simp
  calc ‖f z‖ₑ ≤ _ := hle
    _ ≤ _ := hadd
    _ = ENNReal.ofReal 4 * (F * D2) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (4 * c ^ (-(1 / 2 : ℝ))) * (F * D1) ^ (1 / 2 : ℝ) := by
      rw [hX, hY, add_comm]

/-! ### Conjunct 2: leaf statements -/

/-- Transport between the library cell `(0, c]` of `Units/B0151` and the centred cell: integrals of
nonnegative measurable `c`-periodic functions agree (`Cyl.lintegral_strip_eq_cell`). -/
def CylCellBridge : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g : Cyl.Plane → ℝ≥0∞, Measurable g → Cyl.IsPeriodic c g →
    ∫⁻ z, g z ∂(B0151.cellMeasure c) = ∫⁻ z, g z ∂(Cyl.cellμ c)

/-- **`η`-integration by parts on the cell**: if `H` is `C¹`, in `L^x` for some `0 < x < ∞`, and
`∂_η H ∈ L¹(cell)`, then `∫_cell ∂_η H = 0`. (Fubini: for a.e. `q` the line `H(q, ·)` is in `L^x(ℝ)`
with integrable derivative, hence has limits at `±∞`, which vanish.) -/
def CylCellEtaZero : Prop :=
  ∀ c : ℝ, 0 < c → ∀ H : Cyl.Plane → ℝ, ContDiff ℝ 1 H → ∀ x : ℝ≥0∞, 0 < x → x ≠ ⊤ →
    MemLp H x (Cyl.cellμ c) → Integrable (Cyl.partialEta H) (Cyl.cellμ c) →
      ∫ z, Cyl.partialEta H z ∂(Cyl.cellμ c) = 0

/-- **Mixed Gagliardo-Nirenberg step on the cylinder** (three exponents; the `s = ∞`, `t = r/2` case
is `Sob.GN.gn_mixed`): for smooth `c`-periodic `u`, a direction `v` (`true` is `∂_q`, `false` is
`∂_η`) and exponents `2 ≤ r ≤ s`, `s⁻¹ + t⁻¹ = 2 r⁻¹`, with `u ∈ L^s`, `∂_v u ∈ L^r`,
`∂_v² u ∈ L^t`: `‖∂_v u‖_r² ≤ (r - 1) ‖u‖_s ‖∂_v² u‖_t`.
Proof: with `a = ∂_v u`, `∫|a|^r = ∫ a (|a|^{r-2} a) = -(r-1) ∫ u |a|^{r-2} ∂_v a` (periodic IBP in `q`,
`CylCellEtaZero` in `η`; `u |a|^{r-2} a ∈ L^x` with `x⁻¹ = s⁻¹ + (r-1)/r`), then Hölder with exponents
`s, r/(r-2), t` and division by `‖a‖_r^{r-2}`. -/
def CylMixedGN : Prop :=
  ∀ c : ℝ, 0 < c → ∀ u : Cyl.Plane → ℝ, ContDiff ℝ ∞ u → Cyl.IsPeriodic c u → ∀ v : Bool,
    ∀ r s t : ℝ≥0∞, r ≠ ⊤ → 2 ≤ r → r ≤ s → s⁻¹ + t⁻¹ = 2 * r⁻¹ →
      MemLp u s (Cyl.cellμ c) → MemLp (B0151.derivWord [v] u) r (Cyl.cellμ c) →
      MemLp (B0151.derivWord [v, v] u) t (Cyl.cellμ c) →
        eLpNorm (B0151.derivWord [v] u) r (Cyl.cellμ c) ^ 2 ≤
          ENNReal.ofReal (r.toReal - 1) *
            (eLpNorm u s (Cyl.cellμ c) * eLpNorm (B0151.derivWord [v, v] u) t (Cyl.cellμ c))

/-- The (finite) set of words of length `l` in `{true, false}` (`true` is `∂_q`, `false` is `∂_η`). -/
def wordsOfLength (l : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin l → Bool)).image List.ofFn

/-- **Jets versus coordinate words**: for smooth `f`, every coordinate derivative of order `l` is
bounded by the operator norm `‖D^l f z‖` (on `ℝ × ℝ` with the sup norm), and `‖D^l f z‖` is bounded by
the sum of the `2^l` coordinate derivatives. -/
def CylJetWord : Prop :=
  ∀ f : Cyl.Plane → ℝ, ContDiff ℝ ∞ f → ∀ (l : ℕ) (z : Cyl.Plane),
    (∀ w : List Bool, w.length = l → |B0151.derivWord w f z| ≤ ‖Train.jet l f z‖) ∧
      ‖Train.jet l f z‖ ≤ ∑ w ∈ wordsOfLength l, |B0151.derivWord w f z|

/-- **Finiteness of all derivatives**: if every `D^j f` is in `L²(cell)` (and `f` is smooth and
`c`-periodic, `c ≥ 1`), then every coordinate derivative is bounded and lies in every `L^p`,
`p ≥ 2`. (Qualitative: use `B0151.enorm_derivWord_le` with its constant 3 and `CylCellBridge`,
then `L² ∩ L^∞ ⊂ L^p`.) -/
def CylDerivFinite : Prop :=
  ∀ c : ℝ, 1 ≤ c → ∀ f : Cyl.Plane → ℝ, ContDiff ℝ ∞ f → Cyl.IsPeriodic c f →
    (∀ j : ℕ, MemLp (Train.jet j f) 2 (Cyl.cellμ c)) → ∀ w : List Bool,
      (⨆ z, ‖B0151.derivWord w f z‖ₑ) ≠ ⊤ ∧
        ∀ p : ℝ≥0∞, 2 ≤ p → MemLp (B0151.derivWord w f) p (Cyl.cellμ c)

/-- **Log-convex chain** (pure real analysis): if `a_j² ≤ K a_{j-1} a_{j+1}` for `1 ≤ j < m`, `K ≥ 1`,
`a_j ≥ 0`, then `a_l ≤ K^{l(m-l)/2} a_0^{1-l/m} a_m^{l/m}` for `l ≤ m`. (Put `b_j = a_j K^{j²/2}`,
which is log-convex; zeros propagate: `a_0 = 0` forces all `a_j = 0`.) -/
def LogConvexChain : Prop :=
  ∀ (m : ℕ) (K : ℝ) (a : ℕ → ℝ), 1 ≤ K → (∀ j, 0 ≤ a j) →
    (∀ j, 1 ≤ j → j < m → a j ^ 2 ≤ K * (a (j - 1) * a (j + 1))) →
    ∀ l, l ≤ m →
      a l ≤ K ^ ((l : ℝ) * ((m : ℝ) - l) / 2) * a 0 ^ (1 - (l : ℝ) / m) * a m ^ ((l : ℝ) / m)

/-! ### The conditional theorem -/

/-- **`PartI:T07`, conditional**: the target `cylinder_interpolation_uniform` follows from the Agmon
step, the gradient interpolation and the cylinder Gagliardo-Nirenberg inequality. -/
theorem cylinder_interpolation_uniform_of (hA : CylAgmonL2) (hB : CylGradInterpL2)
    (hGN : CylGN) : CylinderInterpolationUniform :=
  ⟨cylSupInterp_of hA hB, hGN⟩

end UnforcedLeray.Short.PartI
