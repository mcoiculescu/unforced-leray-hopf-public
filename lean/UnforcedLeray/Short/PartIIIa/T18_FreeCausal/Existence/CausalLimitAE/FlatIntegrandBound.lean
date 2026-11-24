import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Gain
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.ClassicalToWeakFlat

/-!
# Part III-a, task `PartIII-a:T18/2/1/7`: the tested free equation is a bounded functional

Proves `FlatIntegrandBound` (`Sub/T18_2_1.lean`, line 177). Source of record:
`the November 2 reference manuscript`, lines 3427-3440 (`Φ` bounded with compact
support in `s ∈ [s₁, s₂]` and `|η| ≤ R`; `|μ/s| ≤ |μ|/s₁`; Cauchy-Schwarz against `ageμ`).

Route.
1. The integrand `flatIntegrand ν μ 0 F b Φ` is a sum of `b`, `F` times four coefficient fields
   built from `Φ` (`cwPhi`, `cwDt`, `cwDx` of `ClassicalToWeakFlat.lean`). These are continuous on
   `ℝ × (ℝ × ℝ)` and vanish on the open set `cwV s₁ s₂ R`, so they are bounded on the compact box
   `[s₁, s₂] × box c R`; outside `fibK1` (inside `Ioi 0 × cell c`) the integrand vanishes.
2. Pointwise on `fibK1 c s₁ s₂ R`: `|integrand| ≤ A (|b| + |F|)`, using `|μ/s| ≤ |μ|/s₁`.
3. `|b| = g |g⁻¹ b| ≤ e^{|γ|/ν} |g⁻¹ b|` (`gainG_bounds`), and the weighted comparison
   `∫⁻_{fibK1} w ≤ C eLpNorm w 2 (ageμ c a)` for `a ≤ 0` (Hölder on the finite-measure set
   `fibK1`, with `ageμ c a ≥ c⁻¹ s₂^{a}`-density comparison). Here `a = -3/2` for `𝓗` and
   `a = -1/2` for `𝒯`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Pointwise norms -/

theorem fib_vnorm2_nonneg (a : Fin 2 → ℂ) : 0 ≤ vnorm2 a := Real.sqrt_nonneg _

theorem fib_tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T := Real.sqrt_nonneg _

theorem fib_norm_le_vnorm2 (a : Fin 2 → ℂ) (i : Fin 2) : ‖a i‖ ≤ vnorm2 a := by
  unfold vnorm2
  have h1 : ‖a i‖ ^ 2 ≤ ∑ k : Fin 2, ‖a k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k : Fin 2 => ‖a k‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc ‖a i‖ = Real.sqrt (‖a i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ k : Fin 2, ‖a k‖ ^ 2) := Real.sqrt_le_sqrt h1

theorem fib_norm_le_tnorm2 (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) : ‖T i j‖ ≤ tnorm2 T := by
  unfold tnorm2
  have h2 : ‖T i j‖ ^ 2 ≤ ∑ l : Fin 2, ‖T i l‖ ^ 2 :=
    Finset.single_le_sum (f := fun l : Fin 2 => ‖T i l‖ ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h3 : ∑ l : Fin 2, ‖T i l‖ ^ 2 ≤ ∑ k : Fin 2, ∑ l : Fin 2, ‖T k l‖ ^ 2 :=
    Finset.single_le_sum (f := fun k : Fin 2 => ∑ l : Fin 2, ‖T k l‖ ^ 2)
      (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖T i j‖ = Real.sqrt (‖T i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ k : Fin 2, ∑ l : Fin 2, ‖T k l‖ ^ 2) := Real.sqrt_le_sqrt (h2.trans h3)

theorem fib_vnorm2_smul (r : ℝ) (a : Fin 2 → ℂ) : vnorm2 (r • a) = |r| * vnorm2 a := by
  unfold vnorm2
  have h : ∑ i : Fin 2, ‖(r • a) i‖ ^ 2 = |r| ^ 2 * ∑ i : Fin 2, ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

theorem fib_tnorm2_smul (r : ℝ) (T : Fin 2 → Fin 2 → ℂ) : tnorm2 (r • T) = |r| * tnorm2 T := by
  unfold tnorm2
  have h : ∑ i : Fin 2, ∑ j : Fin 2, ‖(r • T) i j‖ ^ 2 =
      |r| ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

theorem fib_vnorm2_gain {g : ℝ} (hg : 0 < g) (x : Fin 2 → ℂ) :
    vnorm2 x = g * vnorm2 (g⁻¹ • x) := by
  calc vnorm2 x = vnorm2 (g • (g⁻¹ • x)) := by rw [smul_smul, mul_inv_cancel₀ hg.ne', one_smul]
    _ = g * vnorm2 (g⁻¹ • x) := by rw [fib_vnorm2_smul, abs_of_pos hg]

theorem fib_tnorm2_gain {g : ℝ} (hg : 0 < g) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T = g * tnorm2 (g⁻¹ • T) := by
  calc tnorm2 T = tnorm2 (g • (g⁻¹ • T)) := by rw [smul_smul, mul_inv_cancel₀ hg.ne', one_smul]
    _ = g * tnorm2 (g⁻¹ • T) := by rw [fib_tnorm2_smul, abs_of_pos hg]

theorem fib_continuous_vnorm2 : Continuous vnorm2 := by
  unfold vnorm2
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun i _ => ((continuous_apply i).norm).pow 2)

theorem fib_continuous_tnorm2 : Continuous tnorm2 := by
  unfold tnorm2
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => (((continuous_apply j).comp (continuous_apply i)).norm).pow 2)

theorem fib_measurable_tensor {X : Type*} [MeasurableSpace X] (F : X → Fin 2 → Fin 2 → ℂ)
    (hF : ∀ i j, Measurable fun p => F p i j) : Measurable F :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hF i j

theorem fib_measurable_vec {X : Type*} [MeasurableSpace X] (b : X → Fin 2 → ℂ)
    (hb : ∀ i, Measurable fun p => b p i) : Measurable b :=
  measurable_pi_lambda _ hb

/-! ## Gain conjugation is measurable -/

theorem fib_measurable_gainConj_vec {γ ν : ℝ} {b : CwPt → Fin 2 → ℂ} (hb : Measurable b) :
    Measurable (gainConj γ ν b) := by
  unfold gainConj
  have hg : Measurable fun p : CwPt => (gainG γ ν p.1)⁻¹ := by
    unfold gainG
    exact ((Real.continuous_exp.measurable).comp
      ((measurable_const.mul measurable_fst).div
        (measurable_const.add (measurable_const.mul measurable_fst)))).inv
  exact hg.smul hb

theorem fib_measurable_gainConj_ten {γ ν : ℝ} {F : CwPt → Fin 2 → Fin 2 → ℂ}
    (hF : Measurable F) : Measurable (gainConj γ ν F) := by
  unfold gainConj
  have hg : Measurable fun p : CwPt => (gainG γ ν p.1)⁻¹ := by
    unfold gainG
    exact ((Real.continuous_exp.measurable).comp
      ((measurable_const.mul measurable_fst).div
        (measurable_const.add (measurable_const.mul measurable_fst)))).inv
  exact hg.smul hF

/-! ## The coefficient fields of the tested integrand -/

/-- `Φ_i` as a function of the joint point (complex valued). -/
def fibP0 (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : CwPt → Fin 2 → ℂ := fun p i => cwPhi Φ i p

/-- `∂_s Φ_i`. -/
def fibP1 (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : CwPt → Fin 2 → ℂ :=
  fun p i => cwDt (cwPhi Φ i) p

/-- `ΔΦ_i`. -/
def fibP2 (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : CwPt → Fin 2 → ℂ :=
  fun p i => cwDx 0 (cwDx 0 (cwPhi Φ i)) p + cwDx 1 (cwDx 1 (cwPhi Φ i)) p

/-- `∂_j Φ_i`. -/
def fibP3 (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : CwPt → Fin 2 → Fin 2 → ℂ :=
  fun p i j => cwDx j (cwPhi Φ i) p

theorem fib_cwPhi_contDiff {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (i : Fin 2) : ContDiff ℝ ∞ (cwPhi Φ i) :=
  Complex.ofRealCLM.contDiff.comp (hΦ.smooth i)

theorem fibP0_continuous {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    Continuous (fibP0 Φ) :=
  continuous_pi fun i => (fib_cwPhi_contDiff hΦ i).continuous

theorem fibP1_continuous {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    Continuous (fibP1 Φ) :=
  continuous_pi fun i => (cw_dt_contDiff (fib_cwPhi_contDiff hΦ i)).continuous

theorem fibP2_continuous {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    Continuous (fibP2 Φ) :=
  continuous_pi fun i =>
    ((cw_dx_contDiff (cw_dx_contDiff (fib_cwPhi_contDiff hΦ i) 0) 0).continuous.add
      (cw_dx_contDiff (cw_dx_contDiff (fib_cwPhi_contDiff hΦ i) 1) 1).continuous)

theorem fibP3_continuous {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    Continuous (fibP3 Φ) :=
  continuous_pi fun i => continuous_pi fun j =>
    (cw_dx_contDiff (fib_cwPhi_contDiff hΦ i) j).continuous

/-- Bounded on a compact set, with a nonnegative bound. -/
theorem fib_bound {E : Type*} [NormedAddCommGroup E] {g : CwPt → E} {K : Set CwPt}
    (hK : IsCompact K) (hg : Continuous g) : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ‖g p‖ ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

/-! ## Support: the coefficient fields vanish on `cwV` -/

theorem fib_cwPhi_zero {s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) (i : Fin 2) :
    ∀ p ∈ cwV s1 s2 R, cwPhi Φ i p = 0 := by
  intro p hp
  rw [mem_cwV] at hp
  simp only [cwPhi, hsupp p.1 p.2 i hp, Complex.ofReal_zero]

theorem fibP0_zero {s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) :
    ∀ p ∈ cwV s1 s2 R, ∀ i, fibP0 Φ p i = 0 :=
  fun p hp i => fib_cwPhi_zero hsupp i p hp

theorem fibP1_zero {s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) :
    ∀ p ∈ cwV s1 s2 R, ∀ i, fibP1 Φ p i = 0 :=
  fun p hp i => cw_Dt_zero (cwV_open s1 s2 R) (fib_cwPhi_zero hsupp i) hp

theorem fibP2_zero {s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) :
    ∀ p ∈ cwV s1 s2 R, ∀ i, fibP2 Φ p i = 0 := by
  intro p hp i
  have h1 : ∀ j, ∀ q ∈ cwV s1 s2 R, cwDx j (cwPhi Φ i) q = 0 := fun j q hq =>
    cw_Dx_zero (cwV_open s1 s2 R) (fib_cwPhi_zero hsupp i) hq j
  unfold fibP2
  rw [cw_Dx_zero (cwV_open s1 s2 R) (f := cwDx 0 (cwPhi Φ i)) (fun q hq => h1 0 q hq) hp 0,
    cw_Dx_zero (cwV_open s1 s2 R) (f := cwDx 1 (cwPhi Φ i)) (fun q hq => h1 1 q hq) hp 1]
  simp

theorem fibP3_zero {s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) :
    ∀ p ∈ cwV s1 s2 R, ∀ i j, fibP3 Φ p i j = 0 :=
  fun p hp i j => cw_Dx_zero (cwV_open s1 s2 R) (fib_cwPhi_zero hsupp i) hp j

/-! ## The integrand in terms of the coefficient fields -/

theorem fib_rep {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (ν : ℝ) (μ : ℂ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : CwPt) :
    flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p =
      ∑ i : Fin 2, (-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i + ∑ j : Fin 2, F p i j * fibP3 Φ p i j) := by
  unfold flatIntegrand
  refine Finset.sum_congr rfl fun i _ => ?_
  have hΦi := hΦ.smooth i
  simp only [fibP0, fibP1, fibP2, fibP3, cwPhi, cw_cast_dt Φ i hΦi, cw_cast_lap Φ i hΦi,
    cw_cast_grad Φ i hΦi, Prod.mk.eta, Complex.ofReal_zero, zero_mul, mul_zero, add_zero,
    sub_zero]

theorem fib_rep_zero {c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) (ν : ℝ) (μ : ℂ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : CwPt)
    (hp : p ∈ cwV s1 s2 R) : flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p = 0 := by
  rw [fib_rep hΦ]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [fibP0_zero hsupp p hp, fibP1_zero hsupp p hp, fibP2_zero hsupp p hp,
    fibP3_zero hsupp p hp, mul_zero, zero_mul, add_zero, sub_zero, neg_zero, Finset.sum_const_zero]

theorem fib_integrand_measurable {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (hF : ∀ i j, Measurable fun p => F p i j)
    (hb : ∀ i, Measurable fun p => b p i) :
    Measurable (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ) := by
  have hfun : flatIntegrand ν μ (fun _ _ _ => 0) F b Φ = fun p => ∑ i : Fin 2,
      (-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i + ∑ j : Fin 2, F p i j * fibP3 Φ p i j) :=
    funext fun p => fib_rep hΦ ν μ F b p
  rw [hfun]
  have hP0 : ∀ i, Measurable fun p => fibP0 Φ p i := fun i =>
    (continuous_apply i).measurable.comp (fibP0_continuous hΦ).measurable
  have hP1 : ∀ i, Measurable fun p => fibP1 Φ p i := fun i =>
    (continuous_apply i).measurable.comp (fibP1_continuous hΦ).measurable
  have hP2 : ∀ i, Measurable fun p => fibP2 Φ p i := fun i =>
    (continuous_apply i).measurable.comp (fibP2_continuous hΦ).measurable
  have hP3 : ∀ i j, Measurable fun p => fibP3 Φ p i j := fun i j =>
    (continuous_apply j).measurable.comp
      ((continuous_apply i).comp (fibP3_continuous hΦ)).measurable
  have hmu : Measurable fun p : CwPt => μ / ((p.1 : ℝ) : ℂ) :=
    measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((((hb i).mul (hP1 i)).neg.add ((hmu.mul (hb i)).mul (hP0 i))).sub
    ((measurable_const.mul (hb i)).mul (hP2 i))).add
    (Finset.measurable_sum _ fun j _ => (hF i j).mul (hP3 i j))

/-! ## The integrand is small on `fibK1` -/

/-- The integration set in the `Ioi 0 × cell` picture: the support of the test in `s ∈ [s₁, s₂]`,
`|η| ≤ R`, and the cell. -/
def fibK1 (c s1 s2 R : ℝ) : Set CwPt :=
  Icc s1 s2 ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)

theorem fibK1_mem {c s1 s2 R : ℝ} {p : CwPt} :
    p ∈ fibK1 c s1 s2 R ↔ (s1 ≤ p.1 ∧ p.1 ≤ s2) ∧
      (-(c / 2) ≤ p.2.1 ∧ p.2.1 < c / 2) ∧ (-R ≤ p.2.2 ∧ p.2.2 ≤ R) :=
  Iff.rfl

theorem fibK1_measurable (c s1 s2 R : ℝ) : MeasurableSet (fibK1 c s1 s2 R) :=
  measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)

theorem fibK1_subset_Kc (c s1 s2 R : ℝ) :
    fibK1 c s1 s2 R ⊆ Icc s1 s2 ×ˢ B0579.box c R :=
  Set.prod_mono subset_rfl (Set.prod_mono Set.Ico_subset_Icc_self subset_rfl)

theorem fibK1_subset_cell {c s1 s2 R : ℝ} (hs1 : 0 < s1) :
    fibK1 c s1 s2 R ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
  Set.prod_mono (fun x hx => lt_of_lt_of_le hs1 hx.1)
    (Set.prod_mono subset_rfl (subset_univ _))

theorem fib_qCell_eq (c : ℝ) : UnforcedLeray.Axi.qCell c = B0579.cell c := by
  unfold UnforcedLeray.Axi.qCell B0579.cell
  rw [neg_div]

/-- A point of `Ioi 0 × cell` outside `fibK1` lies in the open set `cwV`. -/
theorem fib_outside {c s1 s2 R : ℝ} {p : CwPt} (hpS : p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c)
    (hpK : p ∉ fibK1 c s1 s2 R) : p ∈ cwV s1 s2 R := by
  rw [mem_cwV]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  apply hpK
  have hq : p.2.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.1 (Set.mem_prod.1 hpS).2).1
  exact fibK1_mem.2 ⟨⟨h1, h2⟩, hq, abs_le.1 h3⟩

/-- The pointwise bound of the tested integrand on `fibK1`. -/
theorem fib_pointwise {s1 : ℝ} (hs1 : 0 < s1) {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (ν : ℝ) (μ : ℂ)
    (F : CwPt → Fin 2 → Fin 2 → ℂ) (b : CwPt → Fin 2 → ℂ) (p : CwPt) (hp : s1 ≤ p.1)
    {M0 M1 M2 M3 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (h0 : ‖fibP0 Φ p‖ ≤ M0) (h1 : ‖fibP1 Φ p‖ ≤ M1) (h2 : ‖fibP2 Φ p‖ ≤ M2)
    (h3 : ‖fibP3 Φ p‖ ≤ M3) :
    ‖∑ i : Fin 2, (-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i + ∑ j : Fin 2, F p i j * fibP3 Φ p i j)‖ ≤
      (2 * (M1 + ‖μ‖ / s1 * M0 + ‖(ν : ℂ)‖ * M2) + 4 * M3) *
        (vnorm2 (b p) + tnorm2 (F p)) := by
  have hp0 : 0 < p.1 := lt_of_lt_of_le hs1 hp
  have hvb0 := fib_vnorm2_nonneg (b p)
  have htb0 := fib_tnorm2_nonneg (F p)
  have hbi : ∀ i, ‖b p i‖ ≤ vnorm2 (b p) := fun i => fib_norm_le_vnorm2 (b p) i
  have hFij : ∀ i j, ‖F p i j‖ ≤ tnorm2 (F p) := fun i j => fib_norm_le_tnorm2 (F p) i j
  have hLμ0 : 0 ≤ ‖μ‖ / s1 := div_nonneg (norm_nonneg _) hs1.le
  have hmu : ‖μ / (p.1 : ℂ)‖ ≤ ‖μ‖ / s1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hs1 hp
  have hP0 : ∀ i, ‖fibP0 Φ p i‖ ≤ M0 := fun i => (norm_le_pi_norm (fibP0 Φ p) i).trans h0
  have hP1 : ∀ i, ‖fibP1 Φ p i‖ ≤ M1 := fun i => (norm_le_pi_norm (fibP1 Φ p) i).trans h1
  have hP2 : ∀ i, ‖fibP2 Φ p i‖ ≤ M2 := fun i => (norm_le_pi_norm (fibP2 Φ p) i).trans h2
  have hP3 : ∀ i j, ‖fibP3 Φ p i j‖ ≤ M3 := fun i j =>
    ((norm_le_pi_norm (fibP3 Φ p i) j).trans (norm_le_pi_norm (fibP3 Φ p) i)).trans h3
  have hterm : ∀ i : Fin 2,
      ‖-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i + ∑ j : Fin 2, F p i j * fibP3 Φ p i j‖ ≤
      vnorm2 (b p) * M1 + ‖μ‖ / s1 * vnorm2 (b p) * M0 + ‖(ν : ℂ)‖ * vnorm2 (b p) * M2
        + 2 * (tnorm2 (F p) * M3) := by
    intro i
    have e1 : ‖-(b p i * fibP1 Φ p i)‖ ≤ vnorm2 (b p) * M1 := by
      rw [norm_neg, norm_mul]
      exact mul_le_mul (hbi i) (hP1 i) (norm_nonneg _) hvb0
    have e2 : ‖(μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i‖ ≤ ‖μ‖ / s1 * vnorm2 (b p) * M0 := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hmu (hbi i) (norm_nonneg _) hLμ0) (hP0 i) (norm_nonneg _)
        (mul_nonneg hLμ0 hvb0)
    have e3 : ‖(ν : ℂ) * b p i * fibP2 Φ p i‖ ≤ ‖(ν : ℂ)‖ * vnorm2 (b p) * M2 := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul le_rfl (hbi i) (norm_nonneg _) (norm_nonneg _)) (hP2 i)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) hvb0)
    have e4 : ‖∑ j : Fin 2, F p i j * fibP3 Φ p i j‖ ≤ 2 * (tnorm2 (F p) * M3) := by
      calc ‖∑ j : Fin 2, F p i j * fibP3 Φ p i j‖
          ≤ ∑ j : Fin 2, ‖F p i j * fibP3 Φ p i j‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin 2, tnorm2 (F p) * M3 := Finset.sum_le_sum fun j _ => by
            rw [norm_mul]
            exact mul_le_mul (hFij i j) (hP3 i j) (norm_nonneg _) htb0
        _ = 2 * (tnorm2 (F p) * M3) := by rw [Fin.sum_univ_two]; ring
    have t1 := norm_add_le (-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i) (∑ j : Fin 2, F p i j * fibP3 Φ p i j)
    have t2 := norm_sub_le (-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i)
        ((ν : ℂ) * b p i * fibP2 Φ p i)
    have t3 := norm_add_le (-(b p i * fibP1 Φ p i)) ((μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i)
    linarith
  have hAc0 : 0 ≤ M1 + ‖μ‖ / s1 * M0 + ‖(ν : ℂ)‖ * M2 := by
    have := mul_nonneg hLμ0 hM0
    have := mul_nonneg (norm_nonneg (ν : ℂ)) hM2
    linarith
  calc ‖∑ i : Fin 2, (-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i + ∑ j : Fin 2, F p i j * fibP3 Φ p i j)‖
      ≤ ∑ i : Fin 2, ‖-(b p i * fibP1 Φ p i) + (μ / (p.1 : ℂ)) * b p i * fibP0 Φ p i
        - (ν : ℂ) * b p i * fibP2 Φ p i + ∑ j : Fin 2, F p i j * fibP3 Φ p i j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, (vnorm2 (b p) * M1 + ‖μ‖ / s1 * vnorm2 (b p) * M0
          + ‖(ν : ℂ)‖ * vnorm2 (b p) * M2 + 2 * (tnorm2 (F p) * M3)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * (vnorm2 (b p) * (M1 + ‖μ‖ / s1 * M0 + ‖(ν : ℂ)‖ * M2)
          + 2 * (tnorm2 (F p) * M3)) := by
        rw [Fin.sum_univ_two]; ring
    _ ≤ (2 * (M1 + ‖μ‖ / s1 * M0 + ‖(ν : ℂ)‖ * M2) + 4 * M3) *
          (vnorm2 (b p) + tnorm2 (F p)) := by
        nlinarith [mul_nonneg hAc0 htb0, mul_nonneg hM3 hvb0]

/-! ## The comparison of `L¹(fibK1)` with the weighted `L²` norm -/

/-- The measure comparison: on `fibK1`, Lebesgue measure is at most `c s₂^{-a}`-times the age
measure `ageμ c a` (`a ≤ 0`), since `c⁻¹ s^a ≥ c⁻¹ s₂^a` for `s ≤ s₂`. -/
theorem fib_measure_le {c s1 s2 R : ℝ} (hc : 0 < c) (hs1 : 0 < s1) (a : ℝ) (ha : a ≤ 0) :
    (volume : Measure CwPt).restrict (fibK1 c s1 s2 R) ≤
      ENNReal.ofReal (c * (s2 ^ a)⁻¹) • (ageμ c a).restrict (fibK1 c s1 s2 R) := by
  rw [Measure.le_iff]
  intro T hT
  rw [Measure.restrict_apply hT, Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul]
  have hUm : MeasurableSet (T ∩ fibK1 c s1 s2 R) := hT.inter (fibK1_measurable c s1 s2 R)
  have hUK : T ∩ fibK1 c s1 s2 R ⊆ fibK1 c s1 s2 R := inter_subset_right
  have hUD : T ∩ fibK1 c s1 s2 R ⊆ Ioi (0 : ℝ) ×ˢ qCell c := by
    rw [fib_qCell_eq]
    exact hUK.trans (fibK1_subset_cell hs1)
  have hD : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell c) :=
    measurableSet_Ioi.prod (by unfold UnforcedLeray.Axi.qCell; exact
      (measurableSet_Ico.prod MeasurableSet.univ))
  have hvol : volume (T ∩ fibK1 c s1 s2 R) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, (T ∩ fibK1 c s1 s2 R).indicator 1 p := by
    rw [← lintegral_indicator hD, Set.indicator_indicator, Set.inter_eq_right.2 hUD,
      lintegral_indicator_one hUm]
  have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ qCell c,
      (T ∩ fibK1 c s1 s2 R).indicator (1 : CwPt → ℝ≥0∞) p ≤
        ENNReal.ofReal (c * (s2 ^ a)⁻¹) *
          (ENNReal.ofReal (c⁻¹ * p.1 ^ a) * (T ∩ fibK1 c s1 s2 R).indicator 1 p) := by
    intro p _
    by_cases hp : p ∈ T ∩ fibK1 c s1 s2 R
    · have hpK : p ∈ fibK1 c s1 s2 R := hUK hp
      obtain ⟨⟨h1, h2⟩, _, _⟩ := fibK1_mem.1 hpK
      have hpos : 0 < p.1 := lt_of_lt_of_le hs1 h1
      have hs2 : 0 < s2 := lt_of_lt_of_le hpos h2
      have hs2a : 0 < s2 ^ a := Real.rpow_pos_of_pos hs2 a
      have hle : s2 ^ a ≤ p.1 ^ a := Real.rpow_le_rpow_of_nonpos hpos h2 ha
      have hnn : 0 ≤ c * (s2 ^ a)⁻¹ := by positivity
      rw [Set.indicator_of_mem hp, Pi.one_apply, mul_one, ← ENNReal.ofReal_mul hnn]
      apply ENNReal.one_le_ofReal.2
      have e : c * (s2 ^ a)⁻¹ * (c⁻¹ * p.1 ^ a) = p.1 ^ a / s2 ^ a := by
        field_simp
      rw [e, one_le_div hs2a]
      exact hle
    · rw [Set.indicator_of_notMem hp]
      exact zero_le
  calc volume (T ∩ fibK1 c s1 s2 R)
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, (T ∩ fibK1 c s1 s2 R).indicator 1 p := hvol
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
          ENNReal.ofReal (c * (s2 ^ a)⁻¹) *
            (ENNReal.ofReal (c⁻¹ * p.1 ^ a) * (T ∩ fibK1 c s1 s2 R).indicator 1 p) :=
        setLIntegral_mono' hD hpt
    _ = ENNReal.ofReal (c * (s2 ^ a)⁻¹) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
            ENNReal.ofReal (c⁻¹ * p.1 ^ a) * (T ∩ fibK1 c s1 s2 R).indicator 1 p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (c * (s2 ^ a)⁻¹) * (ageμ c a) (T ∩ fibK1 c s1 s2 R) := by
        rw [← lintegral_indicator_one hUm,
          lintegral_ageμ hc a ((measurable_one).indicator hUm)]

/-- The weighted comparison: `∫⁻_{fibK1} w` is controlled by the `L²(ageμ c a)` norm of `w`. -/
theorem fib_key {c s1 s2 R : ℝ} (hc : 0 < c) (hs1 : 0 < s1) (a : ℝ) (ha : a ≤ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : CwPt → ℝ, Measurable w → (∀ p, 0 ≤ w p) →
      ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (w p) ≤ C * eLpNorm w 2 (ageμ c a) := by
  have hK1fin : volume (fibK1 c s1 s2 R) < ⊤ :=
    lt_of_le_of_lt (measure_mono (fibK1_subset_Kc c s1 s2 R))
      (isCompact_Icc.prod (B0579.isCompact_box c R)).measure_lt_top
  have hfin : (volume : Measure CwPt).restrict (fibK1 c s1 s2 R) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hK1fin.ne
  set V : ℝ≥0∞ := (volume : Measure CwPt).restrict (fibK1 c s1 s2 R) univ ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hV
  have hVtop : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin
  set T : ℝ≥0∞ := (ENNReal.ofReal (c * (s2 ^ a)⁻¹)) ^ (1 / (2 : ℝ≥0∞)).toReal with hT
  have hTtop : T ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  refine ⟨V * T, ENNReal.mul_ne_top hVtop hTtop, fun w hw hw0 => ?_⟩
  have step1 : ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (w p) =
      eLpNorm w 1 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_congr fun p => (Real.enorm_eq_ofReal (hw0 p)).symm
  have step2 : eLpNorm w 1 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) ≤
      eLpNorm w 2 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) * V :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hw.aestronglyMeasurable
  have step3 : eLpNorm w 2 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) ≤
      eLpNorm w 2 (ENNReal.ofReal (c * (s2 ^ a)⁻¹) •
        (ageμ c a).restrict (fibK1 c s1 s2 R)) :=
    eLpNorm_mono_measure w (fib_measure_le hc hs1 a ha)
  have step4 : eLpNorm w 2 (ENNReal.ofReal (c * (s2 ^ a)⁻¹) •
      (ageμ c a).restrict (fibK1 c s1 s2 R)) =
      T * eLpNorm w 2 ((ageμ c a).restrict (fibK1 c s1 s2 R)) := by
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) w, smul_eq_mul]
  have step5 : eLpNorm w 2 ((ageμ c a).restrict (fibK1 c s1 s2 R)) ≤
      eLpNorm w 2 (ageμ c a) := eLpNorm_mono_measure w Measure.restrict_le_self
  have hcomb : eLpNorm w 2 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) ≤
      T * eLpNorm w 2 (ageμ c a) :=
    calc eLpNorm w 2 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R))
        ≤ _ := step3
      _ = T * eLpNorm w 2 ((ageμ c a).restrict (fibK1 c s1 s2 R)) := step4
      _ ≤ T * eLpNorm w 2 (ageμ c a) := mul_le_mul_of_nonneg_left step5 zero_le
  calc ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (w p)
      = eLpNorm w 1 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) := step1
    _ ≤ eLpNorm w 2 ((volume : Measure CwPt).restrict (fibK1 c s1 s2 R)) * V := step2
    _ ≤ (T * eLpNorm w 2 (ageμ c a)) * V := mul_le_mul_of_nonneg_right hcomb zero_le
    _ = (V * T) * eLpNorm w 2 (ageμ c a) := by ring

/-! ## The integrand bound -/

/-- The majorant of the tested integrand on `fibK1`. -/
def fibG (A : ℝ) (b : CwPt → Fin 2 → ℂ) (F : CwPt → Fin 2 → Fin 2 → ℂ) (p : CwPt) : ℝ≥0∞ :=
  ENNReal.ofReal A * ENNReal.ofReal (vnorm2 (b p)) + ENNReal.ofReal A * ENNReal.ofReal (tnorm2 (F p))

/-- **`FlatIntegrandBound`** (`PartIII-a:T18/2/1/7`; SP 3427-3440). For `c, ν > 0`, `γ, μ` and a
fixed flat test `Φ` there is `C ≥ 0` such that for all measurable `F, b` with `‖g⁻¹F‖_𝒯 < ∞`
and `‖g⁻¹b‖_𝓗 < ∞` the tested integrand is integrable on `(0,∞) × cell` and
`|∫ flatIntegrand ν μ 0 F b Φ| ≤ C (‖g⁻¹b‖_𝓗 + ‖g⁻¹F‖_𝒯)`. -/
theorem flatIntegrandBound : FlatIntegrandBound := by
  unfold FlatIntegrandBound
  intro c ν γ μ hc hν Φ hΦ
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  have hKc : IsCompact (Icc s1 s2 ×ˢ B0579.box c R) :=
    isCompact_Icc.prod (B0579.isCompact_box c R)
  obtain ⟨M0, hM0, hb0⟩ := fib_bound hKc (fibP0_continuous hΦ)
  obtain ⟨M1, hM1, hb1⟩ := fib_bound hKc (fibP1_continuous hΦ)
  obtain ⟨M2, hM2, hb2⟩ := fib_bound hKc (fibP2_continuous hΦ)
  obtain ⟨M3, hM3, hb3⟩ := fib_bound hKc (fibP3_continuous hΦ)
  obtain ⟨C1, hC1top, hC1⟩ :=
    fib_key (s1 := s1) (s2 := s2) (R := R) hc hs1 (-3 / 2) (by norm_num)
  obtain ⟨C2, hC2top, hC2⟩ :=
    fib_key (s1 := s1) (s2 := s2) (R := R) hc hs1 (-1 / 2) (by norm_num)
  obtain ⟨c1, hc1eq, hc1⟩ : ∃ r : ℝ, C1 = ENNReal.ofReal r ∧ 0 ≤ r :=
    ⟨C1.toReal, (ENNReal.ofReal_toReal hC1top).symm, ENNReal.toReal_nonneg⟩
  obtain ⟨c2, hc2eq, hc2⟩ : ∃ r : ℝ, C2 = ENNReal.ofReal r ∧ 0 ≤ r :=
    ⟨C2.toReal, (ENNReal.ofReal_toReal hC2top).symm, ENNReal.toReal_nonneg⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (|γ| / ν) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; exact (Real.exp_pos _).le
  have hgE : ∀ s : ℝ, 0 ≤ s → gainG γ ν s ≤ E := fun s hs => by
    rw [hEdef]; exact (gainG_bounds hν hs).2
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * (M1 + ‖μ‖ / s1 * M0 + ‖(ν : ℂ)‖ * M2) + 4 * M3 :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have h1 : 0 ≤ ‖μ‖ / s1 * M0 := mul_nonneg (div_nonneg (norm_nonneg _) hs1.le) hM0
    have h2 : 0 ≤ ‖(ν : ℂ)‖ * M2 := mul_nonneg (norm_nonneg _) hM2
    linarith
  obtain ⟨Cc, hCcdef⟩ : ∃ C : ℝ, C = A * (E * (c1 + c2)) := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := by
    rw [hCcdef]; exact mul_nonneg hA0 (mul_nonneg hE0 (add_nonneg hc1 hc2))
  refine ⟨Cc, hCc0, fun F b hF hb hFfin hbfin => ?_⟩
  have hFv : Measurable F := fib_measurable_tensor F hF
  have hbv : Measurable b := fib_measurable_vec b hb
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hK1m : MeasurableSet (fibK1 c s1 s2 R) := fibK1_measurable c s1 s2 R
  have hfm : Measurable (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ) :=
    fib_integrand_measurable hΦ ν μ F b hF hb
  have hAtop : ENNReal.ofReal A ≠ ⊤ := ENNReal.ofReal_ne_top
  -- pointwise majorant on `Ioi 0 × cell`
  have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c,
      ENNReal.ofReal ‖flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ ≤
        (fibK1 c s1 s2 R).indicator (fibG A b F) p := by
    intro p hpS
    by_cases hpK : p ∈ fibK1 c s1 s2 R
    · rw [Set.indicator_of_mem hpK]
      have hp1 : s1 ≤ p.1 := (fibK1_mem.1 hpK).1.1
      have hpKc : p ∈ Icc s1 s2 ×ˢ B0579.box c R := fibK1_subset_Kc c s1 s2 R hpK
      have hpt' := fib_pointwise hs1 ν μ F b p hp1 hM0 hM1 hM2 hM3 (hb0 p hpKc) (hb1 p hpKc)
        (hb2 p hpKc) (hb3 p hpKc)
      rw [← hAdef] at hpt'
      rw [fib_rep hΦ]
      refine le_trans (ENNReal.ofReal_le_ofReal hpt') (le_of_eq ?_)
      unfold fibG
      rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_add (fib_vnorm2_nonneg _)
        (fib_tnorm2_nonneg _), mul_add]
    · rw [Set.indicator_of_notMem hpK, fib_rep_zero hΦ hsupp ν μ F b p
        (fib_outside hpS hpK)]
      simp
  -- integrate the majorant over `fibK1`
  have hm1 : Measurable fun p : CwPt => ENNReal.ofReal A * ENNReal.ofReal (vnorm2 (b p)) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (fib_continuous_vnorm2.measurable.comp hbv))
  have hG_eq : ∫⁻ p in fibK1 c s1 s2 R, fibG A b F p =
      ENNReal.ofReal A * (∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (b p))) +
        ENNReal.ofReal A * (∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (F p))) := by
    unfold fibG
    rw [lintegral_add_left hm1, lintegral_const_mul' _ _ hAtop,
      lintegral_const_mul' _ _ hAtop]
  -- the `𝓗` part
  have hwm : Measurable (fun p : CwPt => vnorm2 (gainConj γ ν b p)) :=
    fib_continuous_vnorm2.measurable.comp (fib_measurable_gainConj_vec hbv)
  have hw0 : ∀ p : CwPt, 0 ≤ vnorm2 (gainConj γ ν b p) := fun p => fib_vnorm2_nonneg _
  have hpw : ∀ p ∈ fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (b p)) ≤
      ENNReal.ofReal E * ENNReal.ofReal (vnorm2 (gainConj γ ν b p)) := by
    intro p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le hs1 (fibK1_mem.1 hp).1.1
    have hg0 : 0 < gainG γ ν p.1 := by unfold gainG; exact Real.exp_pos _
    rw [← ENNReal.ofReal_mul hE0]
    apply ENNReal.ofReal_le_ofReal
    rw [fib_vnorm2_gain hg0 (b p)]
    exact mul_le_mul_of_nonneg_right (hgE p.1 hp1.le) (fib_vnorm2_nonneg _)
  have hIb1 : ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (b p)) ≤
      ENNReal.ofReal E * ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (gainConj γ ν b p)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hK1m hpw
  have hIb : ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (b p)) ≤
      ENNReal.ofReal (E * c1) * hCalNorm c (gainConj γ ν b) := by
    have h2 := hC1 (fun p => vnorm2 (gainConj γ ν b p)) hwm hw0
    calc ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (b p))
        ≤ ENNReal.ofReal E * ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (gainConj γ ν b p)) :=
          hIb1
      _ ≤ ENNReal.ofReal E * (C1 * hCalNorm c (gainConj γ ν b)) :=
          mul_le_mul_of_nonneg_left h2 zero_le
      _ = ENNReal.ofReal (E * c1) * hCalNorm c (gainConj γ ν b) := by
          rw [hc1eq, ENNReal.ofReal_mul hE0]; ring
  -- the `𝒯` part
  have hwt : Measurable (fun p : CwPt => tnorm2 (gainConj γ ν F p)) :=
    fib_continuous_tnorm2.measurable.comp (fib_measurable_gainConj_ten hFv)
  have hw0t : ∀ p : CwPt, 0 ≤ tnorm2 (gainConj γ ν F p) := fun p => fib_tnorm2_nonneg _
  have hpwt : ∀ p ∈ fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (F p)) ≤
      ENNReal.ofReal E * ENNReal.ofReal (tnorm2 (gainConj γ ν F p)) := by
    intro p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le hs1 (fibK1_mem.1 hp).1.1
    have hg0 : 0 < gainG γ ν p.1 := by unfold gainG; exact Real.exp_pos _
    rw [← ENNReal.ofReal_mul hE0]
    apply ENNReal.ofReal_le_ofReal
    rw [fib_tnorm2_gain hg0 (F p)]
    exact mul_le_mul_of_nonneg_right (hgE p.1 hp1.le) (fib_tnorm2_nonneg _)
  have hIt1 : ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (F p)) ≤
      ENNReal.ofReal E * ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (gainConj γ ν F p)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hK1m hpwt
  have hIt : ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (F p)) ≤
      ENNReal.ofReal (E * c2) * tCalNorm c (gainConj γ ν F) := by
    have h2 := hC2 (fun p => tnorm2 (gainConj γ ν F p)) hwt hw0t
    calc ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (F p))
        ≤ ENNReal.ofReal E * ∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (gainConj γ ν F p)) :=
          hIt1
      _ ≤ ENNReal.ofReal E * (C2 * tCalNorm c (gainConj γ ν F)) :=
          mul_le_mul_of_nonneg_left h2 zero_le
      _ = ENNReal.ofReal (E * c2) * tCalNorm c (gainConj γ ν F) := by
          rw [hc2eq, ENNReal.ofReal_mul hE0]; ring
  -- combine
  have hA1 : ENNReal.ofReal A * ENNReal.ofReal (E * c1) ≤ ENNReal.ofReal Cc := by
    rw [← ENNReal.ofReal_mul hA0, hCcdef]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hE0) hA0)
  have hA2 : ENNReal.ofReal A * ENNReal.ofReal (E * c2) ≤ ENNReal.ofReal Cc := by
    rw [← ENNReal.ofReal_mul hA0, hCcdef]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hE0) hA0)
  have hfinal : ∫⁻ p in fibK1 c s1 s2 R, fibG A b F p ≤
      ENNReal.ofReal Cc * (hCalNorm c (gainConj γ ν b) + tCalNorm c (gainConj γ ν F)) := by
    rw [hG_eq]
    calc ENNReal.ofReal A * (∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (vnorm2 (b p))) +
          ENNReal.ofReal A * (∫⁻ p in fibK1 c s1 s2 R, ENNReal.ofReal (tnorm2 (F p)))
        ≤ ENNReal.ofReal A * (ENNReal.ofReal (E * c1) * hCalNorm c (gainConj γ ν b)) +
          ENNReal.ofReal A * (ENNReal.ofReal (E * c2) * tCalNorm c (gainConj γ ν F)) :=
          add_le_add (mul_le_mul_of_nonneg_left hIb zero_le) (mul_le_mul_of_nonneg_left hIt zero_le)
      _ = (ENNReal.ofReal A * ENNReal.ofReal (E * c1)) * hCalNorm c (gainConj γ ν b) +
          (ENNReal.ofReal A * ENNReal.ofReal (E * c2)) * tCalNorm c (gainConj γ ν F) := by
          ring
      _ ≤ ENNReal.ofReal Cc * hCalNorm c (gainConj γ ν b) +
          ENNReal.ofReal Cc * tCalNorm c (gainConj γ ν F) :=
          add_le_add (mul_le_mul_of_nonneg_right hA1 zero_le) (mul_le_mul_of_nonneg_right hA2 zero_le)
      _ = ENNReal.ofReal Cc * (hCalNorm c (gainConj γ ν b) + tCalNorm c (gainConj γ ν F)) := by
          ring
  have hmain : ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      ENNReal.ofReal ‖flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ ≤
        ENNReal.ofReal Cc * (hCalNorm c (gainConj γ ν b) + tCalNorm c (gainConj γ ν F)) := by
    refine le_trans (setLIntegral_mono' hS hpt) (le_trans (setLIntegral_le_lintegral _ _) ?_)
    rw [lintegral_indicator hK1m]
    exact hfinal
  have hlt : ENNReal.ofReal Cc * (hCalNorm c (gainConj γ ν b) + tCalNorm c (gainConj γ ν F)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hbfin, hFfin⟩)
  have hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      ENNReal.ofReal ‖flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ < ⊤ :=
    lt_of_le_of_lt hmain hlt
  refine ⟨⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).2 hfin⟩, ?_⟩
  calc ENNReal.ofReal ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖
      ≤ ENNReal.ofReal ((∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          ENNReal.ofReal ‖flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖).toReal) :=
        ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          ENNReal.ofReal ‖flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ :=
        ENNReal.ofReal_toReal hfin.ne
    _ ≤ ENNReal.ofReal Cc * (hCalNorm c (gainConj γ ν b) + tCalNorm c (gainConj γ ν F)) := hmain

end UnforcedLeray.Short.IIIa
