import UnforcedLeray.Units.B0284
import UnforcedLeray.Units.B0289
import UnforcedLeray.Units.B0140
import UnforcedLeray.Lib.Cylinder

/-!
# B0285, definitions: exponents, the source `curl(B_v b₀)`, the norms

Unit B0285 of `paper/main.tex` (unlabelled lemma, tex lines 4653–4677, §`sec:st18-5365`
"Source completion for the background equation"); blueprint unit B0285 of

definitions and the pointwise (in space) algebra; the estimates are in
`UnforcedLeray.Units.B0285.Holder`, `.Age` and `.Circulation`.

Conventions.
* Exponents (tex lines 4655–4657): `p = 11/4` (`pB`), `a_p = p/2 - 5/2 = -9/8` (`aB`),
  `b_p = a_p + p = 13/8` (`bB`); the spatial Hölder partner of `p` in `L²` is `r = 22/3`
  (`rB`, `1/2 = 1/r + 1/p`; scoping note `ExternalInputs.md`, row `STD:holder-cauchy-schwarz`).
* Fields on the cylinder are `c`-periodic functions on `Plane = ℝ × ℝ`, coordinates
  `(q, η) = (z.1, z.2)`, vector values in `Plane` (max norm), as in B0284 (`b₀ = T̄F` is
  `B0284.flatInverse`) and B0289 (its weak derivatives). Component `i` of a vector is
  `cmpL i` (`cmpL 0 = fst`, `cmpL 1 = snd`); the directions are `Sob.cylDir 0 = (1,0)`,
  `Sob.cylDir 1 = (0,1)`.
* The source. For a coefficient field `V` (the train velocity `v` at a fixed age, tex line
  4664) and a field `b` with first and second derivative jets `Db j = ∂_j b`,
  `D2b j k = ∂_j ∂_k b`:
  - `bvField V b Db = B_V b = V·∇b + b·∇V = Σ_k (V_k ∂_k b + b_k ∂_k V)` (the operator
    `B_V w = V·∇w + w·∇V` of tex line 5162);
  - `bvDeriv V b Db D2b j = ∂_j (B_V b)`, expanded by the product rule;
  - `curlSource V b Db D2b = ∂_q (B_V b)₂ - ∂_η (B_V b)₁ = curl(B_V b)`.
  The derivatives of `V` are classical (`dV`, `d2V`, Fréchet derivatives along `Sob.cylDir`);
  those of `b` are the given jets. For `b₀ ∈ W^{2,p}` the jets are the periodic weak
  derivatives (B0289), and `curlSource` is the manuscript's `curl(B_v b₀)` as an `L¹_loc`
  function: it is the weak curl of `B_v b₀` (`Circulation.isWeakCurl_curlSource`), and for
  `C²` fields with classical jets it is the classical curl (`Classical.curl_bvField`).
* `XcNorm c m ω = ‖ω‖_{X_c}`, `X_c = L²(C_c, (1+q²+η²)^m dq dη)` (tex line 4175): the norm of
  the complexified `ω` in `Cyl.Xc c m = Lp ℂ 2 (Cyl.wμc c m)` (centred cell
  `[-c/2, c/2) × ℝ`, weight `Cyl.ρc z = 1 + q² + η²`).
* `spNorm c f = ‖f‖_p`, the normalized spatial norm `L^p(dq/c dη)` of B0284 (`cellMeasure`),
  `p = 11/4`; `‖Db‖_p = Σ_j ‖∂_j b‖_p` (`spNorm1`), `‖D²b‖_p = Σ_{j,k} ‖∂_j∂_k b‖_p`
  (`spNorm2`).
* `coeffNorm c m V = Σ_{l ≤ 2} ‖ρc^{m/2} |D^l V|‖_{L^{22/3}(cell, dq dη)}`, the localized
  coefficient norm of the train (tex line 4664; INF16 O1 in
  `scoping/INF16-Cylinder2DNS.md`, row 42: "polynomial `L^r` bounds (`r = 22/3`) … of `v` on
  `(0,S)`").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal ContDiff

namespace UnforcedLeray.B0285

open UnforcedLeray.GaussianVortex (Plane)

/-! ## 1. Exponents (tex lines 4655–4657, 4671–4674) -/

/-- `p = 11/4` (tex line 4655). -/
def pB : ℝ := 11 / 4

/-- `a_p = p/2 - 5/2` (tex line 4655). -/
def aB : ℝ := pB / 2 - 5 / 2

/-- `b_p = a_p + p` (tex line 4656). -/
def bB : ℝ := aB + pB

/-- The spatial Hölder partner `r = 22/3` of `p` in `L²`: `1/2 = 1/r + 1/p`. -/
def rB : ℝ := 22 / 3

theorem pB_pos : 0 < pB := by unfold pB; norm_num

theorem one_lt_pB : 1 < pB := by unfold pB; norm_num

theorem aB_eq : aB = -9 / 8 := by unfold aB pB; norm_num

theorem bB_eq : bB = 13 / 8 := by unfold bB aB pB; norm_num

/-- `b_p/(p-1) = 13/14` (tex line 4673). -/
theorem bB_div_eq : bB / (pB - 1) = 13 / 14 := by rw [bB_eq]; unfold pB; norm_num

/-- `b_p/(p-1) < 1` (tex line 4673). -/
theorem bB_div_lt_one : bB / (pB - 1) < 1 := by rw [bB_div_eq]; norm_num

theorem holder_exponents : (1 : ℝ) / 2 = 1 / rB + 1 / pB := by unfold rB pB; norm_num

instance holderTriple_rB_pB :
    ENNReal.HolderTriple (ENNReal.ofReal rB) (ENNReal.ofReal pB) 2 := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by unfold rB; norm_num),
    ← ENNReal.ofReal_inv_of_pos pB_pos, ← ENNReal.ofReal_add (by unfold rB; norm_num)
    (by unfold pB; norm_num)]
  unfold rB pB
  rw [show ((22 / 3 : ℝ)⁻¹ + (11 / 4 : ℝ)⁻¹) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- `∫_0^S s^{-b_p/(p-1)} ds < ∞` (tex line 4674). -/
theorem integrableOn_rpow_neg (S : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ (-(bB / (pB - 1)))) (Ioo 0 S) := by
  rcases le_or_gt S 0 with hS | hS
  · rw [Ioo_eq_empty (not_lt.2 hS)]; exact integrableOn_empty
  · rw [intervalIntegral.integrableOn_Ioo_rpow_iff hS, bB_div_eq]; norm_num

theorem lintegral_rpow_neg_lt_top (S : ℝ) :
    ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-(bB / (pB - 1)))) < ⊤ :=
  (integrableOn_rpow_neg S).lintegral_lt_top

/-! ## 2. Components, jets and the source -/

/-- The coordinate functionals of `Plane`: `cmpL 0 = fst`, `cmpL 1 = snd`. -/
def cmpL (i : Fin 2) : Plane →L[ℝ] ℝ :=
  ![ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ] i

@[simp] theorem cmpL_zero (w : Plane) : cmpL 0 w = w.1 := rfl

@[simp] theorem cmpL_one (w : Plane) : cmpL 1 w = w.2 := rfl

theorem abs_cmpL_le (i : Fin 2) (w : Plane) : |cmpL i w| ≤ ‖w‖ := by
  fin_cases i
  · show |w.1| ≤ ‖w‖
    rw [← Real.norm_eq_abs]; exact norm_fst_le w
  · show |w.2| ≤ ‖w‖
    rw [← Real.norm_eq_abs]; exact norm_snd_le w

/-- The classical derivative `∂_j V` of a coefficient field. -/
def dV (V : Plane → Plane) (j : Fin 2) (z : Plane) : Plane := fderiv ℝ V z (Sob.cylDir j)

/-- The classical second derivative `∂_j ∂_k V`. -/
def d2V (V : Plane → Plane) (j k : Fin 2) (z : Plane) : Plane :=
  fderiv ℝ (dV V k) z (Sob.cylDir j)

/-- `B_V b = V·∇b + b·∇V = Σ_k (V_k ∂_k b + b_k ∂_k V)` (tex lines 4667, 5162), with the jet
`Db k = ∂_k b`. -/
def bvField (V b : Plane → Plane) (Db : Fin 2 → Plane → Plane) (z : Plane) : Plane :=
  ∑ k : Fin 2, (cmpL k (V z) • Db k z + cmpL k (b z) • dV V k z)

/-- `∂_j (B_V b)`, by the product rule, with the jets `Db k = ∂_k b`, `D2b j k = ∂_j ∂_k b`. -/
def bvDeriv (V b : Plane → Plane) (Db : Fin 2 → Plane → Plane)
    (D2b : Fin 2 → Fin 2 → Plane → Plane) (j : Fin 2) (z : Plane) : Plane :=
  ∑ k : Fin 2, (cmpL k (dV V j z) • Db k z + cmpL k (V z) • D2b j k z +
    cmpL k (Db j z) • dV V k z + cmpL k (b z) • d2V V j k z)

/-- **The source** `curl(B_V b) = ∂_q (B_V b)₂ - ∂_η (B_V b)₁` (tex line 4667). -/
def curlSource (V b : Plane → Plane) (Db : Fin 2 → Plane → Plane)
    (D2b : Fin 2 → Fin 2 → Plane → Plane) (z : Plane) : ℝ :=
  (bvDeriv V b Db D2b 0 z).2 - (bvDeriv V b Db D2b 1 z).1

/-- The size `Σ_j |∂_j f|` of a first-derivative jet. -/
def jet1 (D : Fin 2 → Plane → Plane) (z : Plane) : ℝ := ∑ j : Fin 2, ‖D j z‖

/-- The size `Σ_{j,k} |∂_j∂_k f|` of a second-derivative jet. -/
def jet2 (D : Fin 2 → Fin 2 → Plane → Plane) (z : Plane) : ℝ := ∑ j : Fin 2, ∑ k : Fin 2, ‖D j k z‖

theorem jet1_nonneg (D : Fin 2 → Plane → Plane) (z : Plane) : 0 ≤ jet1 D z :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem jet2_nonneg (D : Fin 2 → Fin 2 → Plane → Plane) (z : Plane) : 0 ≤ jet2 D z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_cmpL_smul_le (i : Fin 2) (w u : Plane) : ‖cmpL i w • u‖ ≤ ‖w‖ * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_cmpL_le i w) (norm_nonneg _)

/-- Pointwise size of `B_V b`: `|B_V b| ≤ |V| |Db| + |DV| |b|`. -/
theorem norm_bvField_le (V b : Plane → Plane) (Db : Fin 2 → Plane → Plane) (z : Plane) :
    ‖bvField V b Db z‖ ≤ ‖V z‖ * jet1 Db z + jet1 (dV V) z * ‖b z‖ := by
  unfold bvField jet1
  simp only [Fin.sum_univ_two]
  have h1 := norm_cmpL_smul_le 0 (V z) (Db 0 z)
  have h2 := norm_cmpL_smul_le 0 (b z) (dV V 0 z)
  have h3 := norm_cmpL_smul_le 1 (V z) (Db 1 z)
  have h4 := norm_cmpL_smul_le 1 (b z) (dV V 1 z)
  calc _ ≤ ‖cmpL 0 (V z) • Db 0 z‖ + ‖cmpL 0 (b z) • dV V 0 z‖ +
        (‖cmpL 1 (V z) • Db 1 z‖ + ‖cmpL 1 (b z) • dV V 1 z‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ ‖V z‖ * ‖Db 0 z‖ + ‖b z‖ * ‖dV V 0 z‖ + (‖V z‖ * ‖Db 1 z‖ + ‖b z‖ * ‖dV V 1 z‖) := by
        gcongr
    _ = _ := by ring

theorem norm_bvDeriv_le (V b : Plane → Plane) (Db : Fin 2 → Plane → Plane)
    (D2b : Fin 2 → Fin 2 → Plane → Plane) (j : Fin 2) (z : Plane) :
    ‖bvDeriv V b Db D2b j z‖ ≤ ∑ k : Fin 2, (‖dV V j z‖ * ‖Db k z‖ + ‖V z‖ * ‖D2b j k z‖ +
      ‖Db j z‖ * ‖dV V k z‖ + ‖b z‖ * ‖d2V V j k z‖) := by
  unfold bvDeriv
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;> exact norm_cmpL_smul_le _ _ _

/-- Pointwise size of the source:
`|curl(B_V b)| ≤ |V| |D²b| + 2 |DV| |Db| + |D²V| |b|`. -/
theorem abs_curlSource_le (V b : Plane → Plane) (Db : Fin 2 → Plane → Plane)
    (D2b : Fin 2 → Fin 2 → Plane → Plane) (z : Plane) :
    |curlSource V b Db D2b z| ≤
      ‖V z‖ * jet2 D2b z + 2 * (jet1 (dV V) z * jet1 Db z) + jet2 (d2V V) z * ‖b z‖ := by
  have h0 := norm_bvDeriv_le V b Db D2b 0 z
  have h1 := norm_bvDeriv_le V b Db D2b 1 z
  have e0 : |(bvDeriv V b Db D2b 0 z).2| ≤ ‖bvDeriv V b Db D2b 0 z‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le _
  have e1 : |(bvDeriv V b Db D2b 1 z).1| ≤ ‖bvDeriv V b Db D2b 1 z‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le _
  have hsum : (∑ k : Fin 2, (‖dV V 0 z‖ * ‖Db k z‖ + ‖V z‖ * ‖D2b 0 k z‖ +
      ‖Db 0 z‖ * ‖dV V k z‖ + ‖b z‖ * ‖d2V V 0 k z‖)) +
      (∑ k : Fin 2, (‖dV V 1 z‖ * ‖Db k z‖ + ‖V z‖ * ‖D2b 1 k z‖ +
      ‖Db 1 z‖ * ‖dV V k z‖ + ‖b z‖ * ‖d2V V 1 k z‖)) =
      ‖V z‖ * jet2 D2b z + 2 * (jet1 (dV V) z * jet1 Db z) + jet2 (d2V V) z * ‖b z‖ := by
    unfold jet1 jet2
    simp only [Fin.sum_univ_two]
    ring
  unfold curlSource
  calc _ ≤ |(bvDeriv V b Db D2b 0 z).2| + |(bvDeriv V b Db D2b 1 z).1| := abs_sub _ _
    _ ≤ _ := add_le_add (e0.trans h0) (e1.trans h1)
    _ = _ := hsum

/-! ## 3. Norms -/

/-- `‖ω‖_{X_c}`, `X_c = L²(C_c, (1+q²+η²)^m dq dη)` (tex line 4175), for a real `om`: the norm
of the complexified `om` in `Cyl.Xc c m`. -/
def XcNorm (c m : ℝ) (om : Plane → ℝ) : ℝ≥0∞ := eLpNorm (fun z => (om z : ℂ)) 2 (Cyl.wμc c m)

/-- The weight factor `ρc^{m/2} = (1+q²+η²)^{m/2}`. -/
def wt (m : ℝ) (z : Plane) : ℝ := Cyl.ρc z ^ (m / 2)

theorem wt_nonneg (m : ℝ) (z : Plane) : 0 ≤ wt m z := Real.rpow_nonneg (Cyl.ρc_pos z).le _

theorem continuous_wt (m : ℝ) : Continuous (wt m) := by
  unfold wt
  have := Cyl.continuous_rpow_ρc (m / 2)
  exact this

/-- The localized coefficient norm
`Σ_{l ≤ 2} ‖ρc^{m/2} |D^l V|‖_{L^{22/3}(cell, dq dη)}` (tex line 4664). -/
def coeffNorm (c m : ℝ) (V : Plane → Plane) : ℝ≥0∞ :=
  eLpNorm (fun z => wt m z * ‖V z‖) (ENNReal.ofReal rB) (Cyl.cellμ c) +
    eLpNorm (fun z => wt m z * jet1 (dV V) z) (ENNReal.ofReal rB) (Cyl.cellμ c) +
    eLpNorm (fun z => wt m z * jet2 (d2V V) z) (ENNReal.ofReal rB) (Cyl.cellμ c)

/-- The normalized spatial norm `‖f‖_p = ‖f‖_{L^p(dq/c dη)}`, `p = 11/4` (tex lines 4659,
4667; the measure of B0284). -/
def spNorm (c : ℝ) (f : Plane → Plane) : ℝ≥0∞ :=
  eLpNorm f (ENNReal.ofReal pB) (B0284.cellMeasure c)

/-- `‖Db‖_p = Σ_j ‖∂_j b‖_p`. -/
def spNorm1 (c : ℝ) (D : Fin 2 → Plane → Plane) : ℝ≥0∞ := ∑ j : Fin 2, spNorm c (D j)

/-- `‖D²b‖_p = Σ_{j,k} ‖∂_j∂_k b‖_p`. -/
def spNorm2 (c : ℝ) (D : Fin 2 → Fin 2 → Plane → Plane) : ℝ≥0∞ :=
  ∑ j : Fin 2, ∑ k : Fin 2, spNorm c (D j k)

/-- The constant `P = 2 c^{1/p} K` of the source bound, for a coefficient bound `K`. -/
def srcConst (c : ℝ) (K : ℝ≥0∞) : ℝ≥0∞ := 2 * ENNReal.ofReal (c ^ (1 / pB)) * K

theorem srcConst_lt_top (c : ℝ) {K : ℝ≥0∞} (hK : K < ⊤) : srcConst c K < ⊤ := by
  unfold srcConst
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hK

/-- The age measure `s^{α} ds` on `(0, S)`. -/
def ageWeightS (S α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) S)).withDensity fun s => ENNReal.ofReal (s ^ α)

instance sigmaFinite_ageWeightS (S α : ℝ) : SigmaFinite (ageWeightS S α) := by
  unfold ageWeightS; infer_instance

theorem ageWeightS_ac (S α : ℝ) : ageWeightS S α ≪ volume.restrict (Ioo 0 S) :=
  withDensity_absolutelyContinuous _ _

end UnforcedLeray.B0285
