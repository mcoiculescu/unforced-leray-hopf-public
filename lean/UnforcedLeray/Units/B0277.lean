import UnforcedLeray.Units.B0146
import Mathlib.Order.CompletePartialOrder

/-!
# B0277 `mixed-background:C.8`: uniform coefficient derivative bounds

Unit B0277 of `paper/main.tex`, label `mixed-background:C.8`, tex lines 4835–4854
(§ "mixed background", source range 4092–5062). The train estimates it combines are those of
§`sec:train` (tex lines 2038–3243): the isolated Gaussian bound and the derivative comparison
before overlap (`eq:st18-t00145`, tex lines 2217–2234, unit B0147; `eq:st18-t00148`,
tex lines 2263–2346, unit B0153) and the overlap variables with the higher postoverlap norms
(`eq:st18-t00153`, tex lines 2357–2369, unit B0155; `eq:st18-t00163`, tex lines 2454–2467,
unit B0164).

**Statement (tex lines 4835–4854).** For the train velocity `v`,
`sup_{s ≥ 0} ∑_{j=0}^3 ‖D^j v(s)‖_∞ ≤ C_*` with `C_*` independent of small `ν`, of
`c = ν^{-ρ}` (`ρ > 1/2`, tex line 2044) and of `S`. Before overlap (`1 ≤ a ≤ c²`, `a = 1 + νs`)
the order-`j` error bound is `C_j ν^{-1} a^{-(5+j)/2} e^{-b_j c²/a}`, and
`sup_{1 ≤ a ≤ c²} ν^{-1} a^{-(5+j)/2} e^{-b_j c²/a} ≤ C_j ν^{-1} c^{-(5+j)} = C_j ν^{(5+j)ρ-1} ≤ C_j`
for `0 ≤ j ≤ 3`. The isolated Gaussian derivatives are uniformly bounded, and the postoverlap
inverse spatial scaling only decreases the derivative bounds.

**What is proved here.**
* `inv_rpow_mul_exp_neg_le` (the elementary maximization): `a^{-k} e^{-B/a} ≤ k^k e^{-k} B^{-k}`
  for all `a, B, k > 0`, with the sharp constant `peakConst`.
* `preoverlap_sup_chain`: the displayed chain of tex lines 4846–4851, for every `j : ℕ`
  (the manuscript needs `0 ≤ j ≤ 3`), with the explicit constant `errorConst j b`;
  `preoverlap_sSup_chain` states it with the literal supremum over `1 ≤ a ≤ c²` (nonempty and
  bounded above, so the real `sSup` carries no junk value).
* `norm_iteratedFDeriv_rescale_le`, `rescale_bound`: if `v(x) = c^{-3} U(x/c)` then
  `‖D^j v(x)‖ ≤ c^{-3-j} ‖D^j U(x/c)‖`; for `c ≥ 1` the bounds only decrease (tex lines
  4853–4854, with the overlap variables `U = c³ v`, `X = q/c` of `eq:st18-t00153`).
* `uniform_coefficient_bounds` (the unit, conditional on the train estimates): if the train
  estimates hold with constants `Cg, Ce, be, Cu` (bundled in `TrainDerivativeEstimates`), then
  for every `s ≥ 0`, `∑_{j<4} ‖D^j v(s)‖_∞ ≤ Cstar Cg Ce be Cu`, an explicit constant depending
  only on the train constants, hence independent of `ν`, `c` and `S`.
  `uniform_coefficient_bounds_train` specializes `V_c` to B0146's `periodicVelocity`, and
  `exists_uniform_coefficient_bound` is the `∃ C_*` form.

**Lean conventions.** Spatial fields are maps `E → F` between real normed spaces (for the train,
`Plane → Plane`, the periodic lift of the cylinder field; a sup norm over the cylinder equals
the sup norm of the lift). `D^j f(x)` is `iteratedFDeriv ℝ j f x`, and
`‖D^j f‖_∞ = supNormD j f := ⨆ x, ‖D^j f(x)‖ₑ ∈ [0, ∞]`, so no junk value of a real supremum
enters. Since `iteratedFDeriv` is `0` at non-differentiable points, every field whose
derivatives are bounded is assumed `C³` (`ContDiff ℝ 3`), as the manuscript's smooth fields are.
The age variable is `s`, `a = heatWidth ν s = 1 + νs` (unit B0113), `s_c = overlapAge ν c =
(c² - 1)/ν` (unit B0146), and the overlap time is `T = ν(s - s_c)/c²` (`eq:st18-t00153`).
The train constants `C_j`, `b_j` are inputs `ℕ → ℝ`; only `b_j > 0` is assumed (their
nonnegativity is derived from the bounds). The bound `‖D^j U(T)‖_∞ ≤ Cu j` for `T ≥ 0` is the
consequence of `eq:st18-t00163` (`U = b e₁ + W`, `‖D^j b‖_∞ ≤ C(1+T)^{-1-j/2}`,
`‖D^α W‖_∞ ≤ C e^{-λT}`) that tex line 4836 uses.

**Missing.** The train estimates themselves (`eq:st18-t00145`, `eq:st18-t00148`,
`eq:st18-t00163`, from the Gallay–Slijepčević train of §`sec:train`) are not formalized; they
enter `uniform_coefficient_bounds` as the explicit hypotheses `TrainDerivativeEstimates`.
-/

set_option autoImplicit false

noncomputable section

open Real Finset
open scoped ENNReal

namespace UnforcedLeray.B0277

open UnforcedLeray.B0113 (heatWidth)
open UnforcedLeray.B0146 (overlapAge periodicVelocity)
open UnforcedLeray.GaussianVortex (Plane)

/-! ### The elementary maximization `sup_{a>0} a^{-k} e^{-B/a}` -/

/-- The sharp constant `k^k e^{-k} B^{-k} = (k/(eB))^k = sup_{a>0} a^{-k} e^{-B/a}`. -/
def peakConst (k B : ℝ) : ℝ := k ^ k * Real.exp (-k) * B ^ (-k)

theorem peakConst_nonneg {k B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B) : 0 ≤ peakConst k B := by
  unfold peakConst
  have := Real.rpow_nonneg hk k
  have := Real.rpow_nonneg hB (-k)
  positivity

/-- `t^k e^{-t} ≤ k^k e^{-k}` for `t ≥ 0`, `k > 0` (from `t/k ≤ e^{t/k-1}`). -/
theorem rpow_mul_exp_neg_le_peak {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    t ^ k * Real.exp (-t) ≤ k ^ k * Real.exp (-k) := by
  have h1 : t / k ≤ Real.exp (t / k - 1) := by
    have := Real.add_one_le_exp (t / k - 1); linarith
  have h2 : (t / k) ^ k ≤ Real.exp (t / k - 1) ^ k :=
    Real.rpow_le_rpow (div_nonneg ht hk.le) h1 hk.le
  rw [← Real.exp_mul, Real.div_rpow ht hk.le] at h2
  have h3 : (t / k - 1) * k = t - k := by field_simp
  rw [h3, div_le_iff₀ (Real.rpow_pos_of_pos hk k)] at h2
  have he : Real.exp (t - k) * Real.exp (-t) = Real.exp (-k) := by
    rw [← Real.exp_add]; ring_nf
  calc t ^ k * Real.exp (-t) ≤ Real.exp (t - k) * k ^ k * Real.exp (-t) := by
        gcongr
    _ = k ^ k * Real.exp (-k) := by rw [← he]; ring

/-- **The elementary maximization** (tex lines 4846–4848): `a^{-k} e^{-B/a} ≤ k^k e^{-k} B^{-k}`
for all `a > 0`, `B > 0`, `k > 0`. -/
theorem inv_rpow_mul_exp_neg_le {k B a : ℝ} (hk : 0 < k) (hB : 0 < B) (ha : 0 < a) :
    a ^ (-k) * Real.exp (-B / a) ≤ peakConst k B := by
  have hta : 0 ≤ B / a := (div_pos hB ha).le
  have key := rpow_mul_exp_neg_le_peak hk hta
  have haB : a ^ (-k) = (B / a) ^ k * B ^ (-k) := by
    rw [Real.div_rpow hB.le ha.le, Real.rpow_neg ha.le, Real.rpow_neg hB.le]
    have : 0 < B ^ k := Real.rpow_pos_of_pos hB k
    have : 0 < a ^ k := Real.rpow_pos_of_pos ha k
    field_simp
  have hBk : 0 ≤ B ^ (-k) := Real.rpow_nonneg hB.le _
  rw [haB, neg_div]
  unfold peakConst
  calc (B / a) ^ k * B ^ (-k) * Real.exp (-(B / a))
      = ((B / a) ^ k * Real.exp (-(B / a))) * B ^ (-k) := by ring
    _ ≤ (k ^ k * Real.exp (-k)) * B ^ (-k) := by gcongr

/-! ### The preoverlap chain (tex lines 4843–4851) -/

/-- The constant of the preoverlap supremum at order `j`: with `k = (5+j)/2`,
`sup_{a>0} a^{-k} e^{-b c²/a} = errorConst j b · c^{-(5+j)}`. It depends only on `j` and `b`. -/
def errorConst (j : ℕ) (b : ℝ) : ℝ := peakConst ((5 + j : ℝ) / 2) 1 * b ^ (-((5 + j : ℝ) / 2))

theorem errorConst_nonneg (j : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ errorConst j b := by
  unfold errorConst
  have := peakConst_nonneg (k := (5 + j : ℝ) / 2) (B := 1) (by positivity) zero_le_one
  have := Real.rpow_nonneg hb (-((5 + j : ℝ) / 2))
  positivity

/-- The supremum step of tex lines 4846–4848: for every `a > 0` (in particular on
`1 ≤ a ≤ c²`), `ν^{-1} a^{-(5+j)/2} e^{-b c²/a} ≤ errorConst j b · ν^{-1} c^{-(5+j)}`. -/
theorem preoverlap_sup_le {ν b c a : ℝ} (j : ℕ) (hν : 0 < ν) (hb : 0 < b) (hc : 0 < c)
    (ha : 0 < a) :
    ν⁻¹ * a ^ (-((5 + j : ℝ) / 2)) * Real.exp (-b * c ^ 2 / a) ≤
      errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) := by
  set k : ℝ := (5 + j : ℝ) / 2 with hk_def
  have hk : 0 < k := by positivity
  have hB : 0 < b * c ^ 2 := by positivity
  have h := inv_rpow_mul_exp_neg_le hk hB ha
  have hpk : peakConst k (b * c ^ 2) = errorConst j b * c ^ (-(5 + j : ℝ)) := by
    unfold errorConst peakConst
    rw [← hk_def, Real.one_rpow, Real.mul_rpow hb.le (by positivity)]
    have hc2 : (c ^ 2) ^ (-k) = c ^ (-(5 + j : ℝ)) := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le, hk_def]
      congr 1; push_cast; ring
    rw [hc2]; ring
  rw [hpk] at h
  have hν' : 0 ≤ ν⁻¹ := (inv_pos.2 hν).le
  calc ν⁻¹ * a ^ (-k) * Real.exp (-b * c ^ 2 / a)
      = ν⁻¹ * (a ^ (-k) * Real.exp (-(b * c ^ 2) / a)) := by rw [neg_mul, mul_assoc]
    _ ≤ ν⁻¹ * (errorConst j b * c ^ (-(5 + j : ℝ))) := by gcongr
    _ = errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) := by ring

/-- The identity of tex line 4850: `ν^{-1} c^{-(5+j)} = ν^{(5+j)ρ - 1}` for `c = ν^{-ρ}`. -/
theorem nu_inv_mul_rpow_eq {ν ρ c : ℝ} (j : ℕ) (hν : 0 < ν) (hc : c = ν ^ (-ρ)) :
    ν⁻¹ * c ^ (-(5 + j : ℝ)) = ν ^ ((5 + j : ℝ) * ρ - 1) := by
  rw [hc, ← Real.rpow_mul hν.le, ← Real.rpow_neg_one ν, ← Real.rpow_add hν]
  congr 1; ring

/-- The last step of tex line 4850: `ν^{(5+j)ρ - 1} ≤ 1` for `0 < ν ≤ 1`, `ρ > 1/2`. -/
theorem nu_rpow_le_one {ν ρ : ℝ} (j : ℕ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hρ : 1 / 2 < ρ) :
    ν ^ ((5 + j : ℝ) * ρ - 1) ≤ 1 := by
  apply Real.rpow_le_one hν0.le hν1
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- **The displayed chain of tex lines 4846–4851.** For `0 < ν ≤ 1`, `ρ > 1/2`, `c = ν^{-ρ}`,
`b > 0` and every `a > 0` (the manuscript takes `1 ≤ a ≤ c²`), at every order `j`:
`ν^{-1} a^{-(5+j)/2} e^{-b c²/a} ≤ C ν^{-1} c^{-(5+j)} = C ν^{(5+j)ρ-1} ≤ C`
with `C = errorConst j b`, which depends only on `j` and `b`. -/
theorem preoverlap_sup_chain {ν ρ b c a : ℝ} (j : ℕ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ)) (hb : 0 < b) (ha : 0 < a) :
    ν⁻¹ * a ^ (-((5 + j : ℝ) / 2)) * Real.exp (-b * c ^ 2 / a) ≤
        errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) ∧
      errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) =
        errorConst j b * ν ^ ((5 + j : ℝ) * ρ - 1) ∧
      errorConst j b * ν ^ ((5 + j : ℝ) * ρ - 1) ≤ errorConst j b := by
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hν0 _
  refine ⟨preoverlap_sup_le j hν0 hb hcpos ha, ?_, ?_⟩
  · rw [mul_assoc, nu_inv_mul_rpow_eq j hν0 hc]
  · have := nu_rpow_le_one j hν0 hν1 hρ
    have := errorConst_nonneg j hb.le
    nlinarith

/-- The order-`j` preoverlap profile `a ↦ ν^{-1} a^{-(5+j)/2} e^{-b c²/a}` of tex line 4847. -/
def preoverlapProfile (ν b c : ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  ν⁻¹ * a ^ (-((5 + j : ℝ) / 2)) * Real.exp (-b * c ^ 2 / a)

/-- **The displayed chain of tex lines 4846–4851, with the literal supremum over
`1 ≤ a ≤ c²`.** For `0 < ν ≤ 1`, `ρ > 1/2`, `c = ν^{-ρ}` and `b > 0`, the set of values of the
profile on `[1, c²]` is nonempty and bounded above (so its real `sSup` is the true supremum, not
a junk value), and
`sup_{1 ≤ a ≤ c²} ν^{-1} a^{-(5+j)/2} e^{-b c²/a} ≤ C ν^{-1} c^{-(5+j)} = C ν^{(5+j)ρ-1} ≤ C`
with `C = errorConst j b`, depending only on `j` and `b`. -/
theorem preoverlap_sSup_chain {ν ρ b c : ℝ} (j : ℕ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ)) (hb : 0 < b) :
    (preoverlapProfile ν b c j '' Set.Icc 1 (c ^ 2)).Nonempty ∧
      BddAbove (preoverlapProfile ν b c j '' Set.Icc 1 (c ^ 2)) ∧
      sSup (preoverlapProfile ν b c j '' Set.Icc 1 (c ^ 2)) ≤
        errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) ∧
      errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) =
        errorConst j b * ν ^ ((5 + j : ℝ) * ρ - 1) ∧
      errorConst j b * ν ^ ((5 + j : ℝ) * ρ - 1) ≤ errorConst j b := by
  have hc1 : 1 ≤ c := by
    rw [hc]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by linarith)
  have hne : (Set.Icc (1 : ℝ) (c ^ 2)).Nonempty := ⟨1, le_refl _, one_le_pow₀ hc1⟩
  have hub : ∀ y ∈ preoverlapProfile ν b c j '' Set.Icc 1 (c ^ 2),
      y ≤ errorConst j b * ν⁻¹ * c ^ (-(5 + j : ℝ)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact (preoverlap_sup_chain j hν0 hν1 hρ hc hb (by linarith [ha.1] : (0 : ℝ) < a)).1
  obtain ⟨-, h2, h3⟩ := preoverlap_sup_chain j hν0 hν1 hρ hc hb one_pos
  exact ⟨hne.image _, ⟨_, fun y hy => hub y hy⟩, csSup_le (hne.image _) hub, h2, h3⟩

/-- The preoverlap error is uniformly bounded (tex lines 4843–4851): under the hypotheses of
`preoverlap_sup_chain`, `C_j ν^{-1} a^{-(5+j)/2} e^{-b_j c²/a} ≤ C_j · errorConst j b_j`. -/
theorem preoverlap_error_le {ν ρ b c a Cj : ℝ} (j : ℕ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ)) (hb : 0 < b) (ha : 0 < a) (hCj : 0 ≤ Cj) :
    Cj * ν⁻¹ * a ^ (-((5 + j : ℝ) / 2)) * Real.exp (-b * c ^ 2 / a) ≤
      Cj * errorConst j b := by
  obtain ⟨h1, h2, h3⟩ := preoverlap_sup_chain j hν0 hν1 hρ hc hb ha
  calc Cj * ν⁻¹ * a ^ (-((5 + j : ℝ) / 2)) * Real.exp (-b * c ^ 2 / a)
      = Cj * (ν⁻¹ * a ^ (-((5 + j : ℝ) / 2)) * Real.exp (-b * c ^ 2 / a)) := by ring
    _ ≤ Cj * errorConst j b := by
        gcongr
        exact h1.trans (h2 ▸ h3)

/-! ### Derivative sup norms and the postoverlap inverse scaling (tex lines 4853–4854) -/

section Scaling

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `‖D^j f‖_∞ := sup_x ‖D^j f(x)‖`, valued in `[0, ∞]` (no junk value of a real supremum). -/
def supNormD (j : ℕ) (f : E → F) : ℝ≥0∞ := ⨆ x, ‖iteratedFDeriv ℝ j f x‖ₑ

/-- A pointwise bound `‖D^j f(x)‖ ≤ M` for all `x` is the bound `‖D^j f‖_∞ ≤ M`. -/
theorem supNormD_le_ofReal {j : ℕ} {f : E → F} {M : ℝ}
    (h : ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M) : supNormD j f ≤ ENNReal.ofReal M :=
  iSup_le fun x => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (h x)

/-- Conversely, `‖D^j f‖_∞ ≤ M` gives the pointwise bound. -/
theorem norm_le_of_supNormD_le {j : ℕ} {f : E → F} {M : ℝ} (hM : 0 ≤ M)
    (h : supNormD j f ≤ ENNReal.ofReal M) (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
  have hx : ‖iteratedFDeriv ℝ j f x‖ₑ ≤ ENNReal.ofReal M := (le_iSup _ x).trans h
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 hx

/-- The inverse spatial scaling `v(x) = c^{-3} U(x/c)` of the overlap variables
(`eq:st18-t00153`, `U = c³ v`, `X = q/c`) multiplies the `j`-th derivative by `c^{-3-j}`:
`‖D^j v(x)‖ ≤ c^{-3} c^{-j} ‖D^j U(x/c)‖`. -/
theorem norm_iteratedFDeriv_rescale_le {U : E → F} {n : ℕ} (hU : ContDiff ℝ n U) {j : ℕ}
    (hj : j ≤ n) {c : ℝ} (hc : 0 < c) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (c ^ 3)⁻¹ • U (c⁻¹ • y)) x‖ ≤
      (c ^ 3)⁻¹ * (c⁻¹) ^ j * ‖iteratedFDeriv ℝ j U (c⁻¹ • x)‖ := by
  set L : E →L[ℝ] E := c⁻¹ • ContinuousLinearMap.id ℝ E with hL_def
  have hLx : ∀ y, L y = c⁻¹ • y := fun y => by simp [hL_def]
  have hfun : (fun y => (c ^ 3)⁻¹ • U (c⁻¹ • y)) = (c ^ 3)⁻¹ • (U ∘ L) := by
    funext y; simp [hLx]
  have hjn : (j : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hj
  have hcomp : ContDiffAt ℝ j (U ∘ L) x :=
    ((hU.comp L.contDiff).of_le hjn).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply hcomp, L.iteratedFDeriv_comp_right hU x hjn,
    hLx, norm_smul]
  have hnL : ‖L‖ ≤ c⁻¹ :=
    L.opNorm_le_bound (inv_pos.2 hc).le fun y => by
      rw [hLx, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  have hcomp_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j U (c⁻¹ • x)) (fun _ : Fin j => L)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp_le
  have hc3 : ‖(c ^ 3)⁻¹‖ = (c ^ 3)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc3]
  have hpow : ‖L‖ ^ j ≤ (c⁻¹) ^ j := pow_le_pow_left₀ (norm_nonneg _) hnL j
  have hc3pos : 0 ≤ (c ^ 3)⁻¹ := by positivity
  calc (c ^ 3)⁻¹ * ‖(iteratedFDeriv ℝ j U (c⁻¹ • x)).compContinuousLinearMap fun _ => L‖
      ≤ (c ^ 3)⁻¹ * (‖iteratedFDeriv ℝ j U (c⁻¹ • x)‖ * ‖L‖ ^ j) := by gcongr
    _ ≤ (c ^ 3)⁻¹ * (‖iteratedFDeriv ℝ j U (c⁻¹ • x)‖ * (c⁻¹) ^ j) := by gcongr
    _ = (c ^ 3)⁻¹ * (c⁻¹) ^ j * ‖iteratedFDeriv ℝ j U (c⁻¹ • x)‖ := by ring

/-- **The postoverlap inverse scaling only decreases the derivative bounds** (tex lines
4853–4854): for `c ≥ 1`, if `‖D^j U‖_∞ ≤ M` then `‖D^j v‖_∞ ≤ c^{-3-j} M ≤ M` for
`v(x) = c^{-3} U(x/c)`. -/
theorem rescale_bound {U : E → F} {n : ℕ} (hU : ContDiff ℝ n U) {j : ℕ} (hj : j ≤ n)
    {c M : ℝ} (hc : 1 ≤ c) (hM : ∀ y, ‖iteratedFDeriv ℝ j U y‖ ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (c ^ 3)⁻¹ • U (c⁻¹ • y)) x‖ ≤ M := by
  have hc0 : 0 < c := by linarith
  have h := norm_iteratedFDeriv_rescale_le hU hj hc0 x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  have hf1 : (c ^ 3)⁻¹ * (c⁻¹) ^ j ≤ 1 := by
    have h1 : (c ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc)
    have h2 : (c⁻¹) ^ j ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hc)
    have h3 : 0 ≤ (c⁻¹) ^ j := by positivity
    nlinarith
  have hf0 : 0 ≤ (c ^ 3)⁻¹ * (c⁻¹) ^ j := by positivity
  calc _ ≤ (c ^ 3)⁻¹ * (c⁻¹) ^ j * ‖iteratedFDeriv ℝ j U (c⁻¹ • x)‖ := h
    _ ≤ (c ^ 3)⁻¹ * (c⁻¹) ^ j * M := by gcongr; exact hM _
    _ ≤ 1 * M := by gcongr
    _ = M := one_mul M

end Scaling

/-! ### The train estimates and the uniform bound `mixed-background:C.8` -/

section Uniform

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The train estimates that tex line 4836 combines, at viscosity `ν` and period `c`, with
order-`j` constants `Cg j` (isolated Gaussian), `Ce j`, `be j` (preoverlap error) and `Cu j`
(rescaled postoverlap field), for `0 ≤ j ≤ 3`.
* Before overlap, `0 ≤ s ≤ s_c` (i.e. `1 ≤ a ≤ c²`, `a = 1 + νs`): `v(s)` and `V_c(s)` are `C³`,
  `‖D^j V_c(s)‖_∞ ≤ C_j a^{-(3+j)/2}` (`eq:st18-t00145`, tex line 2219) and
  `‖D^j (v - V_c)(s)‖_∞ ≤ C_j ν^{-1} a^{-(5+j)/2} e^{-b_j c²/a}` (`eq:st18-t00148`,
  tex lines 2265–2268).
* After overlap, `s ≥ s_c`: `v(s, x) = c^{-3} U(T, x/c)` with `T = ν(s - s_c)/c²`
  (`eq:st18-t00153`, tex lines 2357–2363), `U(T)` is `C³` and `‖D^j U(T)‖_∞ ≤ Cu j` for `T ≥ 0`
  (consequence of `eq:st18-t00163`, tex lines 2454–2467). -/
structure TrainDerivativeEstimates (ν c : ℝ) (v Vc U : ℝ → E → F) (Cg Ce be Cu : ℕ → ℝ) :
    Prop where
  contDiff_pre : ∀ s, 0 ≤ s → s ≤ overlapAge ν c → ContDiff ℝ 3 (v s) ∧ ContDiff ℝ 3 (Vc s)
  gaussian : ∀ s, 0 ≤ s → s ≤ overlapAge ν c → ∀ j ≤ 3, ∀ x,
    ‖iteratedFDeriv ℝ j (Vc s) x‖ ≤ Cg j * heatWidth ν s ^ (-((3 + j : ℝ) / 2))
  error : ∀ s, 0 ≤ s → s ≤ overlapAge ν c → ∀ j ≤ 3, ∀ x,
    ‖iteratedFDeriv ℝ j (v s - Vc s) x‖ ≤
      Ce j * ν⁻¹ * heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
        Real.exp (-be j * c ^ 2 / heatWidth ν s)
  rescaled : ∀ s, overlapAge ν c ≤ s → ∀ x,
    v s x = (c ^ 3)⁻¹ • U (ν * (s - overlapAge ν c) / c ^ 2) (c⁻¹ • x)
  contDiff_post : ∀ T, 0 ≤ T → ContDiff ℝ 3 (U T)
  post : ∀ T, 0 ≤ T → ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j (U T) y‖ ≤ Cu j

/-- The order-`j` uniform constant: the larger of the preoverlap bound
`Cg j + Ce j · errorConst j (be j)` and the postoverlap bound `Cu j` (and `0`). -/
def orderConst (Cg Ce be Cu : ℕ → ℝ) (j : ℕ) : ℝ :=
  max (max (Cg j + Ce j * errorConst j (be j)) (Cu j)) 0

/-- The constant `C_*` of `mixed-background:C.8`: it depends only on the train constants. -/
def Cstar (Cg Ce be Cu : ℕ → ℝ) : ℝ := ∑ j ∈ range 4, orderConst Cg Ce be Cu j

theorem orderConst_nonneg (Cg Ce be Cu : ℕ → ℝ) (j : ℕ) : 0 ≤ orderConst Cg Ce be Cu j :=
  le_max_right _ _

/-- The order-`j` bound `‖D^j v(s)‖_∞ ≤ orderConst j` for every `s ≥ 0` and `j ≤ 3`. -/
theorem supNormD_le_orderConst {ν ρ c : ℝ} {v Vc U : ℝ → E → F} {Cg Ce be Cu : ℕ → ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ))
    (hbe : ∀ j, 0 < be j) (hT : TrainDerivativeEstimates ν c v Vc U Cg Ce be Cu)
    {s : ℝ} (hs : 0 ≤ s) {j : ℕ} (hj : j ≤ 3) :
    supNormD j (v s) ≤ ENNReal.ofReal (orderConst Cg Ce be Cu j) := by
  apply supNormD_le_ofReal
  intro x
  have hc1 : 1 ≤ c := by
    rw [hc]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by linarith)
  have hc0 : 0 < c := by linarith
  rcases le_total s (overlapAge ν c) with hpre | hpost
  · -- before overlap: `v = V_c + e`
    obtain ⟨hv, hV⟩ := hT.contDiff_pre s hs hpre
    have hj' : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
    have ha1 : 1 ≤ heatWidth ν s := by
      unfold heatWidth; nlinarith
    have ha0 : 0 < heatWidth ν s := by linarith
    have hsplit : iteratedFDeriv ℝ j (v s) x =
        iteratedFDeriv ℝ j (Vc s) x + iteratedFDeriv ℝ j (v s - Vc s) x := by
      have hvs : v s = Vc s + (v s - Vc s) := by abel
      conv_lhs => rw [hvs]
      exact iteratedFDeriv_add_apply (hV.of_le hj').contDiffAt
        ((hv.sub hV).of_le hj').contDiffAt
    have hG := hT.gaussian s hs hpre j hj x
    have hE := hT.error s hs hpre j hj x
    -- nonnegativity of the constants, from the bounds
    have hA0 : 0 < heatWidth ν s ^ (-((3 + j : ℝ) / 2)) := Real.rpow_pos_of_pos ha0 _
    have hA1 : heatWidth ν s ^ (-((3 + j : ℝ) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1 (by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith)
    have hCg : 0 ≤ Cg j := by
      by_contra hneg'
      have hneg := lt_of_not_ge hneg'
      have := mul_neg_of_neg_of_pos hneg hA0
      linarith [norm_nonneg (iteratedFDeriv ℝ j (Vc s) x)]
    have hB0 : 0 < ν⁻¹ * heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
        Real.exp (-be j * c ^ 2 / heatWidth ν s) := by
      have := Real.rpow_pos_of_pos ha0 (-((5 + j : ℝ) / 2))
      have := Real.exp_pos (-be j * c ^ 2 / heatWidth ν s)
      have := inv_pos.2 hν0
      positivity
    have hCe : 0 ≤ Ce j := by
      by_contra hneg'
      have hneg := lt_of_not_ge hneg'
      have := mul_neg_of_neg_of_pos hneg hB0
      have h0 := norm_nonneg (iteratedFDeriv ℝ j (v s - Vc s) x)
      have : Ce j * ν⁻¹ * heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
          Real.exp (-be j * c ^ 2 / heatWidth ν s) =
          Ce j * (ν⁻¹ * heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
            Real.exp (-be j * c ^ 2 / heatWidth ν s)) := by ring
      linarith
    have hEb := preoverlap_error_le j hν0 hν1 hρ hc (hbe j) ha0 hCe
    have hGb : Cg j * heatWidth ν s ^ (-((3 + j : ℝ) / 2)) ≤ Cg j := by
      nlinarith
    rw [hsplit]
    calc ‖iteratedFDeriv ℝ j (Vc s) x + iteratedFDeriv ℝ j (v s - Vc s) x‖
        ≤ ‖iteratedFDeriv ℝ j (Vc s) x‖ + ‖iteratedFDeriv ℝ j (v s - Vc s) x‖ :=
          norm_add_le _ _
      _ ≤ Cg j + Ce j * errorConst j (be j) := by linarith
      _ ≤ orderConst Cg Ce be Cu j := (le_max_left _ _).trans (le_max_left _ _)
  · -- after overlap: inverse spatial scaling of `U`
    set T := ν * (s - overlapAge ν c) / c ^ 2 with hT_def
    have hT0 : 0 ≤ T := by
      rw [hT_def]
      have : 0 ≤ s - overlapAge ν c := by linarith
      positivity
    have hvs : v s = fun y => (c ^ 3)⁻¹ • U T (c⁻¹ • y) := by
      funext y; exact hT.rescaled s hpost y
    rw [hvs]
    have h := rescale_bound (n := 3) (hT.contDiff_post T hT0) hj hc1
      (hT.post T hT0 j hj) x
    exact h.trans ((le_max_right _ _).trans (le_max_left _ _))

/-- **`mixed-background:C.8` (tex lines 4835–4842), conditional on the train estimates.**
For `0 < ν ≤ 1`, `ρ > 1/2` and `c = ν^{-ρ}`, if the train estimates
`TrainDerivativeEstimates` hold with constants `Cg, Ce, be, Cu` (`be j > 0`), then
`sup_{s ≥ 0} ∑_{j=0}^3 ‖D^j v(s)‖_∞ ≤ C_*` with `C_* = Cstar Cg Ce be Cu`, a function of the
train constants alone, hence independent of `ν`, of `c` and of `S`. -/
theorem uniform_coefficient_bounds {ν ρ c : ℝ} {v Vc U : ℝ → E → F} {Cg Ce be Cu : ℕ → ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ))
    (hbe : ∀ j, 0 < be j) (hT : TrainDerivativeEstimates ν c v Vc U Cg Ce be Cu) :
    ∀ s, 0 ≤ s → ∑ j ∈ range 4, supNormD j (v s) ≤ ENNReal.ofReal (Cstar Cg Ce be Cu) := by
  intro s hs
  unfold Cstar
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => orderConst_nonneg Cg Ce be Cu j)]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj3 : j ≤ 3 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  exact supNormD_le_orderConst hν0 hν1 hρ hc hbe hT hs hj3

/-- The supremum form of `mixed-background:C.8`: `⨆_{s ≥ 0} ∑_{j=0}^3 ‖D^j v(s)‖_∞ ≤ C_*`. -/
theorem iSup_uniform_coefficient_bounds {ν ρ c : ℝ} {v Vc U : ℝ → E → F}
    {Cg Ce be Cu : ℕ → ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ))
    (hbe : ∀ j, 0 < be j) (hT : TrainDerivativeEstimates ν c v Vc U Cg Ce be Cu) :
    ⨆ s ∈ Set.Ici (0 : ℝ), ∑ j ∈ range 4, supNormD j (v s) ≤
      ENNReal.ofReal (Cstar Cg Ce be Cu) :=
  iSup₂_le fun s hs => uniform_coefficient_bounds hν0 hν1 hρ hc hbe hT s hs

/-- The `∃ C_*` form, with the uniformity explicit: given the train constants, one `C_*` serves
every `ν ∈ (0,1]`, every `c = ν^{-ρ}` (`ρ > 1/2`) and every train satisfying the train
estimates with those constants. -/
theorem exists_uniform_coefficient_bound (Cg Ce be Cu : ℕ → ℝ) (hbe : ∀ j, 0 < be j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ρ c : ℝ) (v Vc U : ℝ → E → F), 0 < ν → ν ≤ 1 → 1 / 2 < ρ →
      c = ν ^ (-ρ) → TrainDerivativeEstimates ν c v Vc U Cg Ce be Cu →
      ∀ s, 0 ≤ s → ∑ j ∈ range 4, supNormD j (v s) ≤ ENNReal.ofReal C :=
  ⟨Cstar Cg Ce be Cu, Finset.sum_nonneg fun j _ => orderConst_nonneg Cg Ce be Cu j,
    fun _ _ _ _ _ _ hν0 hν1 hρ hc hT => uniform_coefficient_bounds hν0 hν1 hρ hc hbe hT⟩

end Uniform

/-- `mixed-background:C.8` for the manuscript's train on the lifted cylinder `Plane`: the
preoverlap reference field is B0146's periodized heat vortex `V_c = periodicVelocity ν c`
(`eq:st18-t00144`). -/
theorem uniform_coefficient_bounds_train {ν ρ c : ℝ} {v U : ℝ → Plane → Plane}
    {Cg Ce be Cu : ℕ → ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hρ : 1 / 2 < ρ) (hc : c = ν ^ (-ρ))
    (hbe : ∀ j, 0 < be j)
    (hT : TrainDerivativeEstimates ν c v (periodicVelocity ν c) U Cg Ce be Cu) :
    ∀ s, 0 ≤ s → ∑ j ∈ range 4, supNormD j (v s) ≤ ENNReal.ofReal (Cstar Cg Ce be Cu) :=
  uniform_coefficient_bounds hν0 hν1 hρ hc hbe hT

end UnforcedLeray.B0277
