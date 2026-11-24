import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.LimitLinear

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the pointwise bound for the limit

On the box `[a, u] × cell` (where `ψ` may be nonzero) the coefficients `coefA`, `coefB` are bounded
by `K · q(p)`, where `q = vnorm2 b + tnorm2 G + tnorm2 F` is square integrable there (`energyLoc`,
`l2loc`). Writing `x = K q(p)` and using the elementary inequality
`x |y| ≤ (t/2) x² + y²/(2t)` for each of the six scalar differences, the difference of two
extended integrands is bounded by `3 t (K q)² + D(x)/(2t)`, where `D` is the sum of the squared
differences of the test fields and their gradients. The first term is independent of the
approximating sequence and the second one tends to `0` by hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `q(p) = |b(p)| + |G(p)| + |F(p)|` (Hilbert-Schmidt-type norms, `vnorm2`, `tnorm2`). -/
def qNorm (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) : ℝ :=
  vnorm2 (b p) + tnorm2 (G p) + tnorm2 (F p)

lemma vnorm2_nonneg' (a : Fin 2 → ℂ) : 0 ≤ vnorm2 a := by
  unfold vnorm2
  exact Real.sqrt_nonneg _

lemma tnorm2_nonneg' (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T := by
  unfold tnorm2
  exact Real.sqrt_nonneg _

lemma qNorm_nonneg (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) : 0 ≤ qNorm b G F p := by
  unfold qNorm
  linarith [vnorm2_nonneg' (b p), tnorm2_nonneg' (G p), tnorm2_nonneg' (F p)]

lemma norm_mu_div_le {μ : ℂ} {a s : ℝ} (ha : 0 < a) (has : a ≤ s) :
    ‖μ / (s : ℂ)‖ ≤ ‖μ‖ / a := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans_le has)]
  exact div_le_div_of_nonneg_left (norm_nonneg _) ha has

/-- The constant of the coefficient bounds. -/
def Kconst (ν : ℝ) (μ : ℂ) (a Cψ Cd : ℝ) : ℝ :=
  Cd + ‖μ‖ / a * Cψ + (‖ν‖ + 1) * Cψ

lemma coefA_le {ν : ℝ} {μ : ℂ} {ψ : ℝ → ℝ} {a Cψ Cd : ℝ} (ha : 0 < a)
    (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    (hψC : ∀ x, ‖ψ x‖ ≤ Cψ) (hdC : ∀ x, ‖deriv ψ x‖ ≤ Cd)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    {p : ℝ × (ℝ × ℝ)} (hp : a ≤ p.1) (i : Fin 2) :
    ‖coefA μ ψ b p i‖ ≤ Kconst ν μ a Cψ Cd * qNorm b G F p := by
  unfold coefA
  rw [norm_mul]
  have hfac : ‖-((deriv ψ p.1 : ℝ) : ℂ) + (μ / (p.1 : ℂ)) * ((ψ p.1 : ℝ) : ℂ)‖ ≤
      Cd + ‖μ‖ / a * Cψ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul]
    have h1 : ‖((deriv ψ p.1 : ℝ) : ℂ)‖ ≤ Cd := by
      rw [Complex.norm_real]
      exact hdC _
    have h2 : ‖μ / (p.1 : ℂ)‖ * ‖((ψ p.1 : ℝ) : ℂ)‖ ≤ ‖μ‖ / a * Cψ := by
      rw [Complex.norm_real]
      exact mul_le_mul (norm_mu_div_le ha hp) (hψC _) (norm_nonneg _)
        (div_nonneg (norm_nonneg _) ha.le)
    linarith
  have hV : vnorm2 (b p) ≤ qNorm b G F p := by
    unfold qNorm
    linarith [tnorm2_nonneg' (G p), tnorm2_nonneg' (F p)]
  have hX : 0 ≤ Cd + ‖μ‖ / a * Cψ :=
    add_nonneg hCd0 (mul_nonneg (div_nonneg (norm_nonneg _) ha.le) hCψ0)
  have hK : Cd + ‖μ‖ / a * Cψ ≤ Kconst ν μ a Cψ Cd := by
    unfold Kconst
    have : 0 ≤ (‖ν‖ + 1) * Cψ := mul_nonneg (by positivity) hCψ0
    linarith
  calc ‖b p i‖ * ‖-((deriv ψ p.1 : ℝ) : ℂ) + (μ / (p.1 : ℂ)) * ((ψ p.1 : ℝ) : ℂ)‖
      ≤ vnorm2 (b p) * (Cd + ‖μ‖ / a * Cψ) :=
        mul_le_mul (norm_le_vnorm2' _ _) hfac (norm_nonneg _) (vnorm2_nonneg' _)
    _ ≤ qNorm b G F p * (Cd + ‖μ‖ / a * Cψ) := mul_le_mul_of_nonneg_right hV hX
    _ ≤ qNorm b G F p * Kconst ν μ a Cψ Cd := mul_le_mul_of_nonneg_left hK (qNorm_nonneg _ _ _ _)
    _ = Kconst ν μ a Cψ Cd * qNorm b G F p := mul_comm _ _

lemma coefB_le {ν : ℝ} {μ : ℂ} {ψ : ℝ → ℝ} {a Cψ Cd : ℝ} (ha : 0 < a)
    (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    (hψC : ∀ x, ‖ψ x‖ ≤ Cψ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) :
    ‖coefB ν ψ F G p i j‖ ≤ Kconst ν μ a Cψ Cd * qNorm b G F p := by
  unfold coefB
  rw [norm_mul]
  have hG' : ‖(ν : ℂ) * G p i j + F p i j‖ ≤ ‖ν‖ * tnorm2 (G p) + tnorm2 (F p) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real]
    exact add_le_add (mul_le_mul_of_nonneg_left (norm_le_tnorm2' _ i j) (norm_nonneg _))
      (norm_le_tnorm2' _ i j)
  have hψ0 : ‖((ψ p.1 : ℝ) : ℂ)‖ ≤ Cψ := by
    rw [Complex.norm_real]
    exact hψC _
  have hq1 : tnorm2 (G p) ≤ qNorm b G F p := by
    unfold qNorm
    linarith [vnorm2_nonneg' (b p), tnorm2_nonneg' (F p)]
  have hq2 : tnorm2 (F p) ≤ qNorm b G F p := by
    unfold qNorm
    linarith [vnorm2_nonneg' (b p), tnorm2_nonneg' (G p)]
  have hqn := qNorm_nonneg b G F p
  have hK : (‖ν‖ + 1) * Cψ ≤ Kconst ν μ a Cψ Cd := by
    unfold Kconst
    have : 0 ≤ Cd + ‖μ‖ / a * Cψ := add_nonneg hCd0 (mul_nonneg (div_nonneg (norm_nonneg _) ha.le) hCψ0)
    linarith
  calc ‖(ν : ℂ) * G p i j + F p i j‖ * ‖((ψ p.1 : ℝ) : ℂ)‖
      ≤ (‖ν‖ * tnorm2 (G p) + tnorm2 (F p)) * Cψ :=
        mul_le_mul hG' hψ0 (norm_nonneg _)
          (add_nonneg (mul_nonneg (norm_nonneg _) (tnorm2_nonneg' _)) (tnorm2_nonneg' _))
    _ ≤ (‖ν‖ * qNorm b G F p + qNorm b G F p) * Cψ := by
        apply mul_le_mul_of_nonneg_right _ hCψ0
        exact add_le_add (mul_le_mul_of_nonneg_left hq1 (norm_nonneg _)) hq2
    _ = (‖ν‖ + 1) * Cψ * qNorm b G F p := by ring
    _ ≤ Kconst ν μ a Cψ Cd * qNorm b G F p := mul_le_mul_of_nonneg_right hK hqn
    _ = Kconst ν μ a Cψ Cd * qNorm b G F p := rfl

/-- The elementary inequality `x |y| ≤ (t/2) x² + y²/(2t)` for `t > 0`. -/
lemma amgm_sq (x y t : ℝ) (ht : 0 < t) : x * |y| ≤ t / 2 * x ^ 2 + y ^ 2 / (2 * t) := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t / 2 * x ^ 2 + y ^ 2 / (2 * t) - x * |y| = (t * x - |y|) ^ 2 / (2 * t) := by
    rw [sub_sq, sq_abs]
    field_simp
    ring
  have h0 : 0 ≤ (t * x - |y|) ^ 2 / (2 * t) := div_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- The linear form with bounded coefficients is controlled by the squared differences. -/
lemma lin_norm_le (A : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (d : Fin 2 → ℝ)
    (e : Fin 2 → Fin 2 → ℝ) {x t : ℝ} (ht : 0 < t) (hA : ∀ i, ‖A i‖ ≤ x)
    (hB : ∀ i j, ‖B i j‖ ≤ x) :
    ‖∑ i : Fin 2, (A i * (d i : ℂ) + ∑ j : Fin 2, B i j * (e i j : ℂ))‖ ≤
      3 * t * x ^ 2 + (∑ i : Fin 2, (d i ^ 2 + ∑ j : Fin 2, e i j ^ 2)) / (2 * t) := by
  have h1 : ‖∑ i : Fin 2, (A i * (d i : ℂ) + ∑ j : Fin 2, B i j * (e i j : ℂ))‖ ≤
      ∑ i : Fin 2, (‖A i‖ * |d i| + ∑ j : Fin 2, ‖B i j‖ * |e i j|) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ∑ i : Fin 2, (‖A i‖ * |d i| + ∑ j : Fin 2, ‖B i j‖ * |e i j|) ≤
      ∑ i : Fin 2, (x * |d i| + ∑ j : Fin 2, x * |e i j|) := by
    refine Finset.sum_le_sum fun i _ => add_le_add (mul_le_mul_of_nonneg_right (hA i) (abs_nonneg _)) ?_
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hB i j) (abs_nonneg _)
  have h3 : ∑ i : Fin 2, (x * |d i| + ∑ j : Fin 2, x * |e i j|) ≤
      3 * t * x ^ 2 + (∑ i : Fin 2, (d i ^ 2 + ∑ j : Fin 2, e i j ^ 2)) / (2 * t) := by
    simp only [Fin.sum_univ_two, add_div]
    have k0 := amgm_sq x (d 0) t ht
    have k1 := amgm_sq x (d 1) t ht
    have k2 := amgm_sq x (e 0 0) t ht
    have k3 := amgm_sq x (e 0 1) t ht
    have k4 := amgm_sq x (e 1 0) t ht
    have k5 := amgm_sq x (e 1 1) t ht
    linarith
  exact h1.trans (h2.trans h3)

/-- The difference of two extended integrands in linear form. -/
lemma extWeak_sub_lin (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (ψ : ℝ → ℝ) (φk φ : ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    extWeakIntegrand ν μ F b G ψ φk p - extWeakIntegrand ν μ F b G ψ φ p =
      ∑ i : Fin 2, (coefA μ ψ b p i * ((φk p.2 i - φ p.2 i : ℝ) : ℂ) +
        ∑ j : Fin 2, coefB ν ψ F G p i j *
          ((B0579.pd j (fun y => φk y i) p.2 - B0579.pd j (fun y => φ y i) p.2 : ℝ) : ℂ)) := by
  rw [extWeak_eq_lin, extWeak_eq_lin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.sum_univ_two]
  push_cast
  ring

/-- The pointwise bound for the difference of the extended integrands of `φk` and `φ`, on the
time interval `[a, ∞)` where the coefficient bounds hold. -/
lemma extWeak_sub_bound (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    {ψ : ℝ → ℝ} {a Cψ Cd : ℝ} (ha : 0 < a) (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    (hψC : ∀ x, ‖ψ x‖ ≤ Cψ) (hdC : ∀ x, ‖deriv ψ x‖ ≤ Cd)
    (φk φ : ℝ × ℝ → Fin 2 → ℝ) {p : ℝ × (ℝ × ℝ)} (hp : a ≤ p.1) {t : ℝ} (ht : 0 < t) :
    ‖extWeakIntegrand ν μ F b G ψ φk p - extWeakIntegrand ν μ F b G ψ φ p‖ ≤
      3 * t * (Kconst ν μ a Cψ Cd * qNorm b G F p) ^ 2 +
        (∑ i : Fin 2, ((φk p.2 i - φ p.2 i) ^ 2 +
          ∑ j : Fin 2, (B0579.pd j (fun y => φk y i) p.2 - B0579.pd j (fun y => φ y i) p.2) ^ 2)) /
          (2 * t) := by
  rw [extWeak_sub_lin]
  exact lin_norm_le (fun i => coefA μ ψ b p i) (fun i j => coefB ν ψ F G p i j)
    (fun i => φk p.2 i - φ p.2 i)
    (fun i j => B0579.pd j (fun y => φk y i) p.2 - B0579.pd j (fun y => φ y i) p.2) ht
    (fun i => coefA_le ha hCψ0 hCd0 hψC hdC b G F hp i)
    (fun i j => coefB_le ha hCψ0 hCd0 hψC b G F p i j)

/-- Square integrability of `q` on the box `[a, u] × cell`. -/
lemma qNorm_sq_integrableOn {c ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hdat : FreeSolData c ν μ F b G) {a u : ℝ} (ha : 0 < a) :
    IntegrableOn (fun p => qNorm b G F p ^ 2) (Icc a u ×ˢ B0579.cell c) := by
  have hs1 : 0 < a / 2 := by linarith
  have hs2 : a / 2 < max u a + 1 := by linarith [le_max_right u a]
  have hE := hdat.sol.energyLoc (a / 2) (max u a + 1) hs1 hs2
  have hF := hdat.l2loc (a / 2) (max u a + 1) hs1 hs2
  have hsub : Icc a u ×ˢ B0579.cell c ⊆ Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c :=
    prod_mono (Icc_subset_Icc (by linarith) (by linarith [le_max_left u a])) subset_rfl
  have hIE : IntegrableOn (fun p => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)
      (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c) := by
    refine ⟨((measurable_vnorm2' hdat.sol.measurable).pow_const 2 |>.add
      ((measurable_tnorm2' hdat.sol.gradMeasurable).pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)]
    exact hE
  have hIF : IntegrableOn (fun p => tnorm2 (F p) ^ 2)
      (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c) := by
    refine ⟨((measurable_tnorm2' hdat.meas).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)]
    exact hF
  have hsum0 : IntegrableOn (fun p => 3 * ((vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) + tnorm2 (F p) ^ 2))
      (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c) :=
    (hIE.add hIF).const_mul 3
  have hsum : IntegrableOn (fun p => 3 * ((vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) + tnorm2 (F p) ^ 2))
      (Icc a u ×ˢ B0579.cell c) :=
    hsum0.mono_set hsub
  refine Integrable.mono' hsum ?_ (Eventually.of_forall fun p => ?_)
  · unfold qNorm
    exact ((((measurable_vnorm2' hdat.sol.measurable).add
      (measurable_tnorm2' hdat.sol.gradMeasurable)).add
      (measurable_tnorm2' hdat.meas)).pow_const 2).aestronglyMeasurable
  · have hq := qNorm_nonneg b G F p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    unfold qNorm at hq ⊢
    nlinarith [sq_nonneg (vnorm2 (b p) - tnorm2 (G p)), sq_nonneg (vnorm2 (b p) - tnorm2 (F p)),
      sq_nonneg (tnorm2 (G p) - tnorm2 (F p)), vnorm2_nonneg' (b p), tnorm2_nonneg' (G p),
      tnorm2_nonneg' (F p)]

end UnforcedLeray.Short.IIIa
