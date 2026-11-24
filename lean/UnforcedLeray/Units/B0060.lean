import UnforcedLeray.Units.B0060.Estimate
import UnforcedLeray.Units.B0060.Coeff

/-!
# B0060: the Schwartz-coefficient smoothing estimate `‖b Kf‖_{H^{j+1}_M} ≤ C_{b,j,M} ‖f‖_{H^j_M}`

Blueprint unit **B0060**, label `eq:st18-t00049`, `paper/main.tex` lines 1215–1220 (proof of
"Compactness of the Euler interaction", section `sec:st18-1373`). Dependency: B0059
(`eq:st18-t00048`, `UnforcedLeray.B0059`: Biot–Savart bounds on the weighted spaces), and through
it B0008 (the weighted spaces `H^j_M`, `UnforcedLeray.B0008`) and B0009 (the planar Biot–Savart
velocity `biotSavart f i`, `UnforcedLeray.B0009`).

**Statement (tex 1215–1220).** For any Schwartz coefficient `b`, Leibniz and the kernel split of
B0059 give `‖b Kf‖_{H^{j+1}_M} ≤ C_{b,j,M} ‖f‖_{H^j_M}`. Terms with a derivative on `Kf` use its
unweighted `L²` bound and a weighted `L^∞` coefficient bound; terms with no derivative on `Kf` use
its near `L²` part with weighted `L^∞`, and its far `L^∞` part with weighted `L²` coefficient
bounds.

**Formalization.** Throughout `M > 1` and `j ≥ 0` (the range of the spaces `H^j_M`, tex 655), the
velocity is taken componentwise, `(Kf)_i = biotSavart f i`, `i = 0, 1`, and `b : 𝓢(ℝ², ℂ)` is a
complex Schwartz function on `ℂ = ℝ²`. The function `b (Kf)_i` is a pointwise product of a
Schwartz function with a locally integrable function; the estimate asserts that it lies in
`H^{j+1}_M` (`MemHjM`, distributional derivatives) and that the element `G ∈ H^{j+1}_M` it defines
(unique, `HjM.ext`) satisfies `‖G‖ ≤ C ‖f‖_{H^j_M}`.
* `unit_statement`: the unit, with `C = C_{b,j,M}` depending only on `b`, `j`, `M`;
* `bound_of_coeff_bounds`: the quantitative form used by the consumer B0061 (tex 1222, "the
  omitted operator norm tends to zero by (49) because all required weighted coefficient
  seminorms tend to zero"): for any smooth `b` with weighted `L^∞` coefficient bounds
  `⟨y⟩^M |∂^β b| ≤ A` and weighted `L²` coefficient bounds `‖⟨y⟩^M ∂^β b‖₂ ≤ B`, `|β| ≤ j + 1`,
  the constant is `C_{j,M} (A + B)` with `C_{j,M} = leibConst j M` independent of `b`;
* `mulBiotSavart`: `f ↦ b (Kf)_i` as a bounded linear operator `H^j_M → H^{j+1}_M`.

**Proof route.** `Units/B0060/Leibniz.lean`: the weak Leibniz rule for a smooth coefficient
(adapted from the NonUniqueEuler reference
`NonUniqueEuler/lean/NonUniqueEuler/H/Infra/Sobolev/Leibniz/Product.lean`).
`Units/B0060/Estimate.lean`: the term-by-term bounds of tex 1219–1220 from B0059
(`exists_weakDeriv_biotSavart`, `gradL2Bound_two`, `memLp_nearPart`, `norm_farPart_le`,
`integral_norm_value_le`). `Units/B0060/Coeff.lean`: the weighted coefficient seminorms of a
Schwartz function are finite (Mathlib `SchwartzMap.one_add_le_sup_seminorm_apply`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal ContDiff

namespace UnforcedLeray.B0060

open NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0009

/-- **B0060, quantitative form** (`paper/main.tex:1215–1220`, `eq:st18-t00049`, with the
constant's dependence on the coefficient as used at tex 1222). For `M > 1` and every `j` there is
`C_{j,M} ≥ 0` such that for every smooth `b : ℝ² → ℂ` and all `A, B ≥ 0` with
`⟨y⟩^M |∂^β b(y)| ≤ A` for all `y` (weighted `L^∞` coefficient bounds) and
`‖⟨y⟩^M ∂^β b‖₂ ≤ B` (weighted `L²` coefficient bounds) for all `|β| ≤ j + 1`, every
`f ∈ H^j_M` and each component `i`: `b (Kf)_i ∈ H^{j+1}_M`, and the element `G ∈ H^{j+1}_M` with
`G = b (Kf)_i` a.e. has `‖G‖_{H^{j+1}_M} ≤ C_{j,M} (A + B) ‖f‖_{H^j_M}`. -/
theorem bound_of_coeff_bounds {M : ℝ} (hM : 1 < M) (j : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (b : ℂ → ℂ), ContDiff ℝ ∞ b → ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ β ∈ multiIdx (j + 1), ∀ y, bracket y ^ M * ‖partialD β b y‖ ≤ A) →
      (∀ β ∈ multiIdx (j + 1),
        eLpNorm (fun y => bracket y ^ M • partialD β b y) 2 volume ≤ ENNReal.ofReal B) →
      ∀ (F : HjM j M) (i : Fin 2),
        MemHjM (j + 1) M (fun y => b y * biotSavart F.value i y) ∧
          ∃ G : HjM (j + 1) M,
            (G.value : ℂ → ℂ) =ᵐ[volume] (fun y => b y * biotSavart F.value i y) ∧
              ‖G‖ ≤ C₀ * (A + B) * ‖F‖ :=
  ⟨leibConst j M, leibConst_nonneg j M, fun _ hb _ _ hA0 hB0 hA hB F i =>
    exists_bound_of_coeff hM hb hA0 hB0 hA hB F i⟩

/-- **B0060** (`paper/main.tex:1215–1220`, `eq:st18-t00049`): **for every Schwartz coefficient
`b`, `‖b Kf‖_{H^{j+1}_M} ≤ C_{b,j,M} ‖f‖_{H^j_M}`.** For `M > 1`, every `j` and every
`b ∈ 𝓢(ℝ², ℂ)` there is `C_{b,j,M} ≥ 0` such that for every `f ∈ H^j_M` and each component `i`
of the Biot–Savart velocity `Kf`: the product `b (Kf)_i` lies in `H^{j+1}_M` (`MemHjM`:
`⟨y⟩^M ∂^α (b (Kf)_i) ∈ L²` for all `|α| ≤ j + 1`, distributional derivatives), and the element
`G ∈ H^{j+1}_M` it defines (`G = b (Kf)_i` a.e.) has `‖G‖_{H^{j+1}_M} ≤ C_{b,j,M} ‖f‖_{H^j_M}`. -/
theorem unit_statement {M : ℝ} (hM : 1 < M) (j : ℕ) (b : 𝓢(ℂ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : HjM j M) (i : Fin 2),
      MemHjM (j + 1) M (fun y => b y * biotSavart F.value i y) ∧
        ∃ G : HjM (j + 1) M,
          (G.value : ℂ → ℂ) =ᵐ[volume] (fun y => b y * biotSavart F.value i y) ∧
            ‖G‖ ≤ C * ‖F‖ := by
  obtain ⟨A, B, hA0, hB0, hA, hB⟩ := exists_coeff_bounds b M (multiIdx (j + 1))
  refine ⟨leibConst j M * (A + B), mul_nonneg (leibConst_nonneg j M) (add_nonneg hA0 hB0),
    fun F i => ?_⟩
  exact exists_bound_of_coeff hM (b.smooth ⊤) hA0 hB0 hA hB F i

/-! ### The bounded operator `f ↦ b (Kf)_i` -/

section Operator

variable {j : ℕ} {M : ℝ}

/-- Two elements of `H^k_M` with a.e. equal functions are equal. -/
theorem HjM_eq_of_ae {k : ℕ} {G G' : HjM k M}
    (h : (G.value : ℂ → ℂ) =ᵐ[volume] (G'.value : ℂ → ℂ)) : G = G' :=
  B0008.HjM.ext (Lp.ext ((wMeasure_ac M).ae_le h))

theorem memHjM_mul_biotSavart (hM : 1 < M) (b : 𝓢(ℂ, ℂ)) (F : HjM j M) (i : Fin 2) :
    MemHjM (j + 1) M (fun y => b y * biotSavart F.value i y) :=
  ((unit_statement hM j b).choose_spec.2 F i).1

/-- `b (Kf)_i` as an element of `H^{j+1}_M`. -/
def mulBiotSavartFun (hM : 1 < M) (b : 𝓢(ℂ, ℂ)) (i : Fin 2) (F : HjM j M) : HjM (j + 1) M :=
  HjM.ofMemHjM (memHjM_mul_biotSavart hM b F i)

theorem mulBiotSavartFun_value (hM : 1 < M) (b : 𝓢(ℂ, ℂ)) (i : Fin 2) (F : HjM j M) :
    ((mulBiotSavartFun hM b i F).value : ℂ → ℂ) =ᵐ[volume]
      (fun y => b y * biotSavart F.value i y) :=
  HjM.value_ofMemHjM _

theorem mulBiotSavartFun_add (hM : 1 < M) (b : 𝓢(ℂ, ℂ)) (i : Fin 2) (F G : HjM j M) :
    mulBiotSavartFun hM b i (F + G) = mulBiotSavartFun hM b i F + mulBiotSavartFun hM b i G := by
  apply HjM_eq_of_ae
  have h2 : ((F + G).value : ℂ → ℂ) =ᵐ[volume] (F.value : ℂ → ℂ) + (G.value : ℂ → ℂ) := by
    rw [B0008.HjM.value_add]
    exact (volume_ac M).ae_le (Lp.coeFn_add _ _)
  have h3 : biotSavart (F + G).value i =ᵐ[volume] biotSavart F.value i + biotSavart G.value i := by
    rw [biotSavart_congr_ae h2 i]
    exact biotSavart_add_ae (B0008.HjM.integrable_value hM F)
      (B0008.HjM.integrable_value hM G) i
  have h4 : ((mulBiotSavartFun hM b i F + mulBiotSavartFun hM b i G).value : ℂ → ℂ) =ᵐ[volume]
      ((mulBiotSavartFun hM b i F).value : ℂ → ℂ) + ((mulBiotSavartFun hM b i G).value) := by
    rw [B0008.HjM.value_add]
    exact (volume_ac M).ae_le (Lp.coeFn_add _ _)
  filter_upwards [mulBiotSavartFun_value hM b i (F + G), h3, h4, mulBiotSavartFun_value hM b i F,
    mulBiotSavartFun_value hM b i G] with y e1 e3 e4 e5 e6
  rw [e1, e4, Pi.add_apply, e5, e6, e3, Pi.add_apply, mul_add]

theorem mulBiotSavartFun_smul (hM : 1 < M) (b : 𝓢(ℂ, ℂ)) (i : Fin 2) (c : ℂ) (F : HjM j M) :
    mulBiotSavartFun hM b i (c • F) = c • mulBiotSavartFun hM b i F := by
  apply HjM_eq_of_ae
  have h2 : ((c • F).value : ℂ → ℂ) =ᵐ[volume] c • (F.value : ℂ → ℂ) := by
    rw [B0008.HjM.value_smul]
    exact (volume_ac M).ae_le (Lp.coeFn_smul _ _)
  have h4 : ((c • mulBiotSavartFun hM b i F).value : ℂ → ℂ) =ᵐ[volume]
      c • ((mulBiotSavartFun hM b i F).value : ℂ → ℂ) := by
    rw [B0008.HjM.value_smul]
    exact (volume_ac M).ae_le (Lp.coeFn_smul _ _)
  filter_upwards [mulBiotSavartFun_value hM b i (c • F), h4, mulBiotSavartFun_value hM b i F]
    with y e1 e4 e5
  rw [e1, e4, Pi.smul_apply, e5, biotSavart_congr_ae h2 i, biotSavart_smul, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **The operator `f ↦ b (Kf)_i` is bounded `H^j_M → H^{j+1}_M`** (tex 1220, the operator form
of `eq:st18-t00049` used at tex 1222), for a Schwartz coefficient `b` and `M > 1`. -/
def mulBiotSavart (hM : 1 < M) (j : ℕ) (b : 𝓢(ℂ, ℂ)) (i : Fin 2) :
    HjM j M →L[ℂ] HjM (j + 1) M :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := mulBiotSavartFun hM b i
      map_add' := mulBiotSavartFun_add hM b i
      map_smul' := fun c F => by
        rw [RingHom.id_apply]
        exact mulBiotSavartFun_smul hM b i c F }
    (by
      obtain ⟨C, -, hC⟩ := unit_statement hM j b
      refine ⟨C, fun F => ?_⟩
      obtain ⟨-, G, hGv, hGn⟩ := hC F i
      have hEq : mulBiotSavartFun hM b i F = G :=
        HjM_eq_of_ae ((mulBiotSavartFun_value hM b i F).trans hGv.symm)
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hEq]
      exact hGn)

/-- The operator `mulBiotSavart` is multiplication of the velocity component by `b`. -/
theorem mulBiotSavart_value (hM : 1 < M) (b : 𝓢(ℂ, ℂ)) (i : Fin 2) (F : HjM j M) :
    ((mulBiotSavart hM j b i F).value : ℂ → ℂ) =ᵐ[volume]
      (fun y => b y * biotSavart F.value i y) :=
  mulBiotSavartFun_value hM b i F

end Operator

end UnforcedLeray.B0060
