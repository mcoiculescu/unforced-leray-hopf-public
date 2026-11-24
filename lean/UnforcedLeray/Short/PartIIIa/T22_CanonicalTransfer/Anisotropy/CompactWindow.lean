import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.Anisotropy.SymAndPlanar

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff Interval InnerProductSpace ComplexConjugate SchwartzMap

namespace UnforcedLeray.Short.IIIa.AnisoSynthAux

open UnforcedLeray.Short.IIIa

/-! ### Bilinear stress-defect integrand and heat-cell telescoping on `[s_B, s_r]` -/

def defectPairIntegrand (V : ℝ × ℝ → Fin 2 → ℝ) (U : ℝ × ℝ → Fin 2 → ℂ)
    (x : ℝ × ℝ) : ℂ :=
  (2 * (((V x 0 : ℝ) : ℂ) * U x 0) + 2 * (((V x 1 : ℝ) : ℂ) * U x 1)) -
    3 * (2 * (((V x 1 : ℝ) : ℂ) * U x 1) -
      Complex.I * ((((V x 0 : ℝ) : ℂ) * U x 1) + (((V x 1 : ℝ) : ℂ) * U x 0)))

lemma defectPairIntegrand_eq_four_terms (V : ℝ × ℝ → Fin 2 → ℝ)
    (U : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) :
    defectPairIntegrand V U x =
      (2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 1 : ℝ) : ℂ) * U x 0) := by
  unfold defectPairIntegrand; ring

lemma integrableOn_and_integral_defectPairIntegrand {D : ℝ}
    {V : ℝ × ℝ → Fin 2 → ℝ} {U : ℝ × ℝ → Fin 2 → ℂ}
    (hi : ∀ i j : Fin 2, IntegrableOn (fun x => ((V x i : ℝ) : ℂ) * U x j) (B0579.cell D)) :
    IntegrableOn (defectPairIntegrand V U) (B0579.cell D) ∧
      (∫ x in B0579.cell D, defectPairIntegrand V U x) =
        (2 : ℂ) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 0) +
        (-4 : ℂ) * (∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 1) +
        (3 * Complex.I) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 1) +
        (3 * Complex.I) * (∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 0) := by
  have i00 : IntegrableOn (fun x => (2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0)) (B0579.cell D) :=
    (hi 0 0).const_mul _
  have i11 : IntegrableOn (fun x => (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1)) (B0579.cell D) :=
    (hi 1 1).const_mul _
  have i01 : IntegrableOn (fun x => (3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1)) (B0579.cell D) :=
    (hi 0 1).const_mul _
  have i10 : IntegrableOn (fun x => (3 * Complex.I) * (((V x 1 : ℝ) : ℂ) * U x 0)) (B0579.cell D) :=
    (hi 1 0).const_mul _
  have i_a : IntegrableOn (fun x => (2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1)) (B0579.cell D) := i00.add i11
  have i_b : IntegrableOn (fun x => (2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1)) (B0579.cell D) := i_a.add i01
  have i_c : IntegrableOn (fun x => (2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 1 : ℝ) : ℂ) * U x 0)) (B0579.cell D) := i_b.add i10
  have hrew : defectPairIntegrand V U = fun x =>
      (2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 1 : ℝ) : ℂ) * U x 0) :=
    funext (defectPairIntegrand_eq_four_terms V U)
  rw [hrew]
  refine ⟨i_c, ?_⟩
  rw [integral_add i_b i10, integral_add i_a i01, integral_add i00 i11,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

lemma defectPairIntegrand_sub_left (V₁ V₂ : ℝ × ℝ → Fin 2 → ℝ)
    (U : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) :
    defectPairIntegrand V₁ U x - defectPairIntegrand V₂ U x =
      defectPairIntegrand (fun y i => V₁ y i - V₂ y i) U x := by
  unfold defectPairIntegrand; push_cast; ring

lemma defectPairIntegrand_sub_right (V : ℝ × ℝ → Fin 2 → ℝ)
    (U₁ U₂ : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) :
    defectPairIntegrand V U₁ x - defectPairIntegrand V U₂ x =
      defectPairIntegrand V (fun y j => U₁ y j - U₂ y j) x := by
  unfold defectPairIntegrand; ring

lemma norm_defectPairIntegrand_le (V : ℝ × ℝ → Fin 2 → ℝ)
    (U : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) :
    ‖defectPairIntegrand V U x‖ ≤
      4 * (|V x 0| + |V x 1|) * (‖U x 0‖ + ‖U x 1‖) := by
  rw [defectPairIntegrand_eq_four_terms]
  have t123 := norm_add_le
    ((2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) + (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1))
    ((3 * Complex.I) * (((V x 1 : ℝ) : ℂ) * U x 0))
  have t12 := norm_add_le
    ((2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0) + (-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1))
    ((3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1))
  have t1 := norm_add_le
    ((2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0))
    ((-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1))
  have n00 : ‖(2 : ℂ) * (((V x 0 : ℝ) : ℂ) * U x 0)‖ = 2 * (|V x 0| * ‖U x 0‖) := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  have n11 : ‖(-4 : ℂ) * (((V x 1 : ℝ) : ℂ) * U x 1)‖ = 4 * (|V x 1| * ‖U x 1‖) := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  have n01 : ‖(3 * Complex.I) * (((V x 0 : ℝ) : ℂ) * U x 1)‖ = 3 * (|V x 0| * ‖U x 1‖) := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  have n10 : ‖(3 * Complex.I) * (((V x 1 : ℝ) : ℂ) * U x 0)‖ = 3 * (|V x 1| * ‖U x 0‖) := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  have h0v : 0 ≤ |V x 0| := abs_nonneg _
  have h1v : 0 ≤ |V x 1| := abs_nonneg _
  have h0u : 0 ≤ ‖U x 0‖ := norm_nonneg _
  have h1u : 0 ≤ ‖U x 1‖ := norm_nonneg _
  nlinarith

lemma integrable_and_norm_defectPairIntegrand_cell {D B_V B_U : ℝ}
    (hBV : 0 ≤ B_V) (hBU : 0 ≤ B_U)
    {V : ℝ × ℝ → Fin 2 → ℝ} {U : ℝ × ℝ → Fin 2 → ℂ}
    (hV : ∀ i : Fin 2, MemLp (fun x => V x i) 2 (volume.restrict (B0579.cell D)))
    (hU : ∀ j : Fin 2, MemLp (fun x => U x j) 2 (volume.restrict (B0579.cell D)))
    (hV_bd : ∀ i : Fin 2,
      (eLpNorm (fun x => V x i) 2 (volume.restrict (B0579.cell D))).toReal ≤ B_V)
    (hU_bd : ∀ j : Fin 2,
      (eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell D))).toReal ≤ B_U) :
    IntegrableOn (defectPairIntegrand V U) (B0579.cell D) ∧
      ‖∫ x in B0579.cell D, defectPairIntegrand V U x‖ ≤ 12 * B_V * B_U := by
  have _ := hBU
  have hi : ∀ (i j : Fin 2),
      IntegrableOn (fun x => ((V x i : ℝ) : ℂ) * U x j) (B0579.cell D) :=
    fun i j => (hV i).ofReal.integrable_mul (hU j)
  have hcs : ∀ (i j : Fin 2),
      ‖∫ x in B0579.cell D, ((V x i : ℝ) : ℂ) * U x j‖ ≤ B_V * B_U := fun i j =>
    (norm_integral_mul_le_eLpNorm_two (hV i) (hU j)).trans
      (mul_le_mul (hV_bd i) (hU_bd j) ENNReal.toReal_nonneg hBV)
  obtain ⟨hint, h_int_eq⟩ := integrableOn_and_integral_defectPairIntegrand hi
  refine ⟨hint, ?_⟩
  rw [h_int_eq]
  have t123 := norm_add_le
    ((2 : ℂ) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 1) +
      (3 * Complex.I) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 1))
    ((3 * Complex.I) * (∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 0))
  have t12 := norm_add_le
    ((2 : ℂ) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 0) +
      (-4 : ℂ) * (∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 1))
    ((3 * Complex.I) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 1))
  have t1 := norm_add_le
    ((2 : ℂ) * (∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 0))
    ((-4 : ℂ) * (∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 1))
  have n00 : ‖(2 : ℂ) * ∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 0‖ ≤ 2 * (B_V * B_U) := by
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hcs 0 0) (by norm_num)
  have n11 : ‖(-4 : ℂ) * ∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 1‖ ≤ 4 * (B_V * B_U) := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hcs 1 1) (by norm_num)
  have n01 : ‖(3 * Complex.I) * ∫ x in B0579.cell D, ((V x 0 : ℝ) : ℂ) * U x 1‖ ≤
      3 * (B_V * B_U) := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hcs 0 1) (by norm_num)
  have n10 : ‖(3 * Complex.I) * ∫ x in B0579.cell D, ((V x 1 : ℝ) : ℂ) * U x 0‖ ≤
      3 * (B_V * B_U) := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hcs 1 0) (by norm_num)
  linarith

lemma pairs_defect_eq_defectPairIntegrand {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    {s : ℝ} (hs : 0 ≤ s)
    (hv_fin : UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) < ⊤)
    {om : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : IsBiotSavart (ν ^ (-2 : ℝ)) om u) :
    (pairEta tr μ u s + pairQ tr μ u s) -
        3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s) =
      (((ν ^ (-2 : ℝ))⁻¹ : ℝ) : ℂ) * (s : ℂ) ^ (-μ) *
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), defectPairIntegrand (fun z i => tr.v s z i) u x := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hν _).ne'
  have hv_mem : ∀ i : Fin 2, MemLp (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (memLp_train_coord_of_cellL2 hs tr hv_fin i).1
  have hij : ∀ i j : Fin 2,
      IntegrableOn (fun x => ((tr.v s x i : ℝ) : ℂ) * u x j) (B0579.cell c) :=
    fun i j => (hv_mem i).ofReal.integrable_mul (hu.1 j)
  have hpull : ∀ i j : Fin 2,
      (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j)) =
        (s : ℂ) ^ (-μ) * ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u x j := fun i j => by
    have hp : (fun x => ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j)) =
        fun x => (s : ℂ) ^ (-μ) * (((tr.v s x i : ℝ) : ℂ) * u x j) := by funext x; ring
    rw [hp, integral_const_mul]
  have hEta : pairEta tr μ u s =
      ((2 : ℂ) / (c : ℂ)) * ((s : ℂ) ^ (-μ) *
        ∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * u x 0) := by
    unfold pairEta; rw [hpull 0 0]
  have hQ : pairQ tr μ u s =
      ((2 : ℂ) / (c : ℂ)) * ((s : ℂ) ^ (-μ) *
        ∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * u x 1) := by
    unfold pairQ; rw [hpull 1 1]
  have hC' : pairC tr μ u s =
      ((1 : ℂ) / (c : ℂ)) * ((s : ℂ) ^ (-μ) *
        ((∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * u x 1) +
          ∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * u x 0)) := by
    unfold pairC
    have i01 : IntegrableOn (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1))
        (B0579.cell c) := by
      have hp : (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1)) =
          fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 0 : ℝ) : ℂ) * u x 1) := by funext x; ring
      rw [hp]; exact (hij 0 1).const_mul _
    have i10 : IntegrableOn (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0))
        (B0579.cell c) := by
      have hp : (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0)) =
          fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 1 : ℝ) : ℂ) * u x 0) := by funext x; ring
      rw [hp]; exact (hij 1 0).const_mul _
    rw [integral_add i01 i10, hpull 0 1, hpull 1 0]; ring
  have hdef_int := (integrableOn_and_integral_defectPairIntegrand
    (V := fun z i => tr.v s z i) (U := u) hij).2
  dsimp only [c] at hc_ne hEta hQ hC' hdef_int ⊢
  rw [hEta, hQ, hC', hdef_int, Complex.ofReal_inv]
  field_simp [hc_ne]
  ring

lemma velNorm_congr_ae_aniso {d : ℝ} {u v : ℝ × ℝ → Fin 2 → ℂ}
    (h : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), u x = v x) :
    velNorm d u = velNorm d v := by
  unfold velNorm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact eLpNorm_congr_ae (h.mono fun x hx => congrArg (fun f => f j) hx)

lemma kinNorm_eq_velNorm_aniso {d : ℝ} (hd : 0 < d) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hu : IsBiotSavart d f u) :
    kinNorm d f = velNorm d u := by
  apply le_antisymm (iInf₂_le u hu)
  refine le_iInf₂ fun v hv => le_of_eq ?_
  exact velNorm_congr_ae_aniso (CTE.isBiotSavart_unique d hd f u v hu hv)

lemma isBiotSavart_smul_aniso {d : ℝ} (α : ℂ) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hf_int : IntegrableOn f (B0579.cell d))
    (hu : IsBiotSavart d f u) :
    IsBiotSavart d (fun x => α * f x) (fun x j => α * u x j) := by
  refine ⟨fun j => (hu.1 j).const_mul α, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hpt : (fun x => (α * u x 0) * (B0579.pd 0 ψ x : ℂ) +
        (α * u x 1) * (B0579.pd 1 ψ x : ℂ)) =
        fun x => α * (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x; ring
    rw [hpt, integral_const_mul, hu.2.1 ψ hψ, mul_zero]
  · have hptL : (fun x => (α * f x) * (ψ x : ℂ)) = fun x => α * (f x * (ψ x : ℂ)) := by
      funext x; ring
    have hptR : (fun x => (α * u x 0) * (B0579.pd 1 ψ x : ℂ) -
        (α * u x 1) * (B0579.pd 0 ψ x : ℂ)) =
        fun x => α * (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      funext x; ring
    have _ := hf_int
    rw [hptL, hptR, integral_const_mul, integral_const_mul, hu.2.2 ψ hψ]

lemma isBiotSavart_sub_aniso {d m : ℝ} (hm : 2 < m)
    {f₁ f₂ : ℝ × ℝ → ℂ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure d m))
    (hf₂ : MemLp f₂ 2 (B0579.cellMeasure d m))
    (hu₁ : IsBiotSavart d f₁ u₁) (hu₂ : IsBiotSavart d f₂ u₂) :
    IsBiotSavart d (f₁ - f₂) (fun x j => u₁ x j - u₂ x j) := by
  refine ⟨fun j => (hu₁.1 j).sub (hu₂.1 j), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have i1 : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) +
        u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell d) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (hu₁.1 0)).add
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (hu₁.1 1))
    have i2 : IntegrableOn (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ) +
        u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell d) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (hu₂.1 0)).add
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (hu₂.1 1))
    have hpt : (fun x => (u₁ x 0 - u₂ x 0) * (B0579.pd 0 ψ x : ℂ) +
        (u₁ x 1 - u₂ x 1) * (B0579.pd 1 ψ x : ℂ)) =
        fun x => (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) -
          (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x; ring
    rw [hpt, integral_sub i1 i2, hu₁.2.1 ψ hψ, hu₂.2.1 ψ hψ, sub_self]
  · have iw1 := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
      (memLp_vol_of_cellMeasure (by linarith) hf₁)
    have iw2 := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
      (memLp_vol_of_cellMeasure (by linarith) hf₂)
    have iu1 : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ) -
        u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell d) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (hu₁.1 0)).sub
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (hu₁.1 1))
    have iu2 : IntegrableOn (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ) -
        u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell d) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (hu₂.1 0)).sub
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (hu₂.1 1))
    have hptL : (fun x => (f₁ - f₂) x * (ψ x : ℂ)) =
        fun x => f₁ x * (ψ x : ℂ) - f₂ x * (ψ x : ℂ) := by funext x; simp [sub_mul]
    have hptR : (fun x => (u₁ x 0 - u₂ x 0) * (B0579.pd 1 ψ x : ℂ) -
        (u₁ x 1 - u₂ x 1) * (B0579.pd 0 ψ x : ℂ)) =
        fun x => (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) -
          (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      funext x; ring
    rw [hptL, hptR, integral_sub iw1 iw2, integral_sub iu1 iu2, hu₁.2.2 ψ hψ, hu₂.2.2 ψ hψ]

lemma eLpNorm_u_cell_eq_rescaled {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (α : ℂ)
    (hα : α ≠ 0) {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ j : Fin 2, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c)))
    (j : Fin 2) :
    (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c))).toReal =
      ‖α‖ * a ^ (-1 : ℝ) *
        (eLpNorm (fun y => α⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) 2
          (volume.restrict (B0579.cell (cellLen c a)))).toReal := by
  let U_Z : ℝ × ℝ → ℂ := fun y => α⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
    u (Real.sqrt a * y.1, Real.sqrt a * y.2) j
  have hUZ_mem : MemLp U_Z 2 (volume.restrict (B0579.cell (cellLen c a))) := by
    have hsmul : MemLp (fun y : ℝ × ℝ => u (Real.sqrt a • y) j) 2
        (volume.restrict (B0579.cell (cellLen c a))) := by
      refine ⟨(hu j).1.comp_quasiMeasurePreserving (qmp_cell_smul ha), ?_⟩
      rw [T06.eLpNorm_two_eq_lintegral]
      have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
      have hgc : ⇑(MeasurableEquiv.smul₀ (Real.sqrt a)⁻¹ (inv_ne_zero hs) :
          (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)) = fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z := rfl
      have h1 := lintegral_map_equiv
        (f := fun y : ℝ × ℝ => ‖u (Real.sqrt a • y) j‖ₑ ^ 2)
        (μ := volume.restrict (B0579.cell c))
        (MeasurableEquiv.smul₀ (Real.sqrt a)⁻¹ (inv_ne_zero hs) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ))
      rw [hgc, E0.RsDil.map_dilate_restrict ha, lintegral_smul_measure] at h1
      have h1' : ENNReal.ofReal a *
          ∫⁻ y in B0579.cell (cellLen c a), ‖u (Real.sqrt a • y) j‖ₑ ^ 2 =
          ∫⁻ x in B0579.cell c, ‖u x j‖ₑ ^ 2 := by
        refine h1.trans (lintegral_congr_ae (Eventually.of_forall fun x => ?_))
        simp [smul_inv_smul₀ hs]
      have ha_ne0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
      have hfin_c : (∫⁻ x in B0579.cell c, ‖u x j‖ₑ ^ 2) < ⊤ := by
        have hlt := (hu j).2
        rw [T06.eLpNorm_two_eq_lintegral] at hlt
        exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 hlt
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      have h1_lt : (∫⁻ y in B0579.cell (cellLen c a), ‖u (Real.sqrt a • y) j‖ₑ ^ 2) < ⊤ := by
        by_contra htop2
        rw [not_lt, top_le_iff] at htop2
        rw [htop2, ENNReal.mul_top ha_ne0] at h1'
        exact hfin_c.ne h1'.symm
      exact htop.not_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) h1_lt.ne)
    exact hsmul.const_mul (α⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ))
  have _ := hc
  rw [eLpNorm_two_sq_eq_integral_norm_sq (hu j), eLpNorm_two_sq_eq_integral_norm_sq hUZ_mem]
  have hcv := cv_cell (c := c) ha (fun x => ((‖u x j‖ ^ (2 : ℝ) : ℝ) : ℂ))
  rw [Complex.real_smul, integral_complex_ofReal, integral_complex_ofReal,
    ← Complex.ofReal_mul] at hcv
  have hcv_re : a * ∫ y in B0579.cell (cellLen c a),
      ‖u (Real.sqrt a * y.1, Real.sqrt a * y.2) j‖ ^ (2 : ℝ) =
      ∫ x in B0579.cell c, ‖u x j‖ ^ (2 : ℝ) := Complex.ofReal_injective hcv
  have hpt_UZ : ∀ y : ℝ × ℝ,
      ‖u (Real.sqrt a * y.1, Real.sqrt a * y.2) j‖ ^ (2 : ℝ) =
        (‖α‖ ^ 2 * a ^ (-3 : ℝ)) * ‖U_Z y‖ ^ (2 : ℝ) := by
    intro y
    have heq_u : u (Real.sqrt a * y.1, Real.sqrt a * y.2) j =
        α * ((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * U_Z y := by
      dsimp only [U_Z]
      have ha32 : ((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add ha]; norm_num
      calc u (Real.sqrt a * y.1, Real.sqrt a * y.2) j
          = (α * α⁻¹) * (((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ)) *
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) j := by
            rw [mul_inv_cancel₀ hα, ha32, one_mul, one_mul]
        _ = α * ((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
              (α⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
                u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := by ring
    rw [heq_u, Real.rpow_two, Real.rpow_two, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ha.le _), mul_pow, mul_pow,
      ← Real.rpow_natCast (a ^ (-3 / 2 : ℝ)) 2, ← Real.rpow_mul ha.le]
    norm_num
  rw [← hcv_re]
  simp_rw [hpt_UZ]
  rw [integral_const_mul]
  have ha_mul : a * (‖α‖ ^ 2 * a ^ (-3 : ℝ) * ∫ y in B0579.cell (cellLen c a), ‖U_Z y‖ ^ (2 : ℝ)) =
      (‖α‖ * a ^ (-1 : ℝ)) ^ (2 : ℝ) *
        ∫ y in B0579.cell (cellLen c a), ‖U_Z y‖ ^ (2 : ℝ) := by
    have ha13 : a * a ^ (-3 : ℝ) = (a ^ (-1 : ℝ)) ^ 2 := by
      calc a * a ^ (-3 : ℝ)
          = a ^ (1 : ℝ) * a ^ (-3 : ℝ) := by rw [Real.rpow_one]
        _ = a ^ ((1 : ℝ) + -3) := (Real.rpow_add ha 1 (-3)).symm
        _ = (a ^ (-1 : ℝ)) ^ 2 := by
            rw [← Real.rpow_natCast (a ^ (-1 : ℝ)) 2, ← Real.rpow_mul ha.le]; norm_num
    rw [Real.rpow_two, mul_pow]
    calc a * (‖α‖ ^ 2 * a ^ (-3 : ℝ) * ∫ y in B0579.cell (cellLen c a), ‖U_Z y‖ ^ (2 : ℝ))
        = ‖α‖ ^ 2 * (a * a ^ (-3 : ℝ)) *
            ∫ y in B0579.cell (cellLen c a), ‖U_Z y‖ ^ (2 : ℝ) := by ring
      _ = ‖α‖ ^ 2 * (a ^ (-1 : ℝ)) ^ 2 *
            ∫ y in B0579.cell (cellLen c a), ‖U_Z y‖ ^ (2 : ℝ) := by rw [ha13]
  rw [ha_mul, Real.mul_rpow (by positivity)
    (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (by positivity)]
  norm_num

lemma datum_cell_l2_and_tail :
    ∃ (C_dat2 C_datT : ℝ), 0 < C_dat2 ∧ 0 < C_datT ∧
      ∀ {d : ℝ}, 1 ≤ d →
        (∀ i : Fin 2, MemLp (fun y => UnforcedLeray.Train.datum d y i) 2
            (volume.restrict (B0579.cell d)) ∧
          (eLpNorm (fun y => UnforcedLeray.Train.datum d y i) 2
            (volume.restrict (B0579.cell d))).toReal ≤ C_dat2) ∧
        (∀ y ∈ B0579.cell d, ∀ i : Fin 2,
          |UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i| ≤
            C_datT / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by
  obtain ⟨A_v0, hAv0, hbv0⟩ := EulerErrorTail.v0_gauss
  have hG8_int : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
    EulerErrorTail.integrable_gauss (by norm_num)
  set I_g8 : ℝ := ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
  have hIg8_nn : 0 ≤ I_g8 := integral_nonneg fun _ => (Real.exp_pos _).le
  set M_dat : ℝ := A_v0 + 256 * A_v0 * EulerErrorTail.sZ + 1
  have hMdat_pos : 0 < M_dat := by have := EulerErrorTail.sZ_nonneg; positivity
  set C_dat2 : ℝ := M_dat * Real.sqrt (I_g8 + 1)
  have hCdat2_pos : 0 < C_dat2 := mul_pos hMdat_pos (Real.sqrt_pos.2 (by positivity))
  set C_datT : ℝ := 256 * A_v0 * EulerErrorTail.sZ + 1
  have hCdatT_pos : 0 < C_datT := by have := EulerErrorTail.sZ_nonneg; positivity
  refine ⟨C_dat2, C_datT, hCdat2_pos, hCdatT_pos, fun {d} hd => ?_⟩
  have hd_ne : d ≠ 0 := by linarith
  have htail : ∀ y ∈ B0579.cell d,
      ‖UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y‖ ≤
        (256 * A_v0 * EulerErrorTail.sZ) / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro y hy
    rw [UnforcedLeray.Train.datum_apply]
    exact EulerErrorTail.tail_gauss' hAv0 hbv0 hd (EulerErrorTail.abs_fst_le_of_mem_cell hy)
  have htail_coord : ∀ y ∈ B0579.cell d, ∀ i : Fin 2,
      |UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i| ≤
        C_datT / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro y hy i
    have h1 : |UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i| ≤
        ‖UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le (UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y) i
    refine (h1.trans (htail y hy)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg d)
    dsimp [C_datT]; linarith
  refine ⟨fun i => ?_, htail_coord⟩
  have hcont_i : Continuous (fun y : ℝ × ℝ => UnforcedLeray.Train.datum d y i) :=
    (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
      (UnforcedLeray.Train.datum_contDiff hd_ne).continuous
  have hpt_bd : ∀ y ∈ B0579.cell d,
      |UnforcedLeray.Train.datum d y i| ≤ M_dat * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro y hy
    have hd2_ge1 : 1 ≤ d ^ 2 := by nlinarith
    have hsub := htail y hy
    have hv0_i : |UnforcedLeray.Train.v0 y i| ≤
        A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
      have h0 : |UnforcedLeray.Train.v0 y i| ≤ ‖UnforcedLeray.Train.v0 y‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (UnforcedLeray.Train.v0 y) i
      exact (h0.trans (hbv0 y)).trans
        (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 y) hAv0)
    have hdiff_i : |UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i| ≤
        (256 * A_v0 * EulerErrorTail.sZ) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
      have h0 : |UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i| ≤
          ‖UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y‖ := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le (UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y) i
      refine (h0.trans hsub).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact div_le_self (by have := EulerErrorTail.sZ_nonneg; positivity) hd2_ge1
    have htri : |UnforcedLeray.Train.datum d y i| ≤
        |UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i| +
          |UnforcedLeray.Train.v0 y i| := by
      have := abs_add_le (UnforcedLeray.Train.datum d y i - UnforcedLeray.Train.v0 y i)
        (UnforcedLeray.Train.v0 y i)
      simpa using this
    calc |UnforcedLeray.Train.datum d y i|
        ≤ (256 * A_v0 * EulerErrorTail.sZ) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
            A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := htri.trans (add_le_add hdiff_i hv0_i)
      _ ≤ M_dat * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
          dsimp [M_dat]; nlinarith [(Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 16)).le]
  have hsq_int : IntegrableOn (fun y => |UnforcedLeray.Train.datum d y i| ^ 2) (B0579.cell d) := by
    refine Integrable.mono' ((hG8_int.const_mul (M_dat ^ 2)).restrict)
      ((continuous_abs.comp hcont_i).pow 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ico.prod MeasurableSet.univ)] with y hy
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb := pow_le_pow_left₀ (abs_nonneg _) (hpt_bd y hy) 2
    refine hb.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hmem : MemLp (fun y => UnforcedLeray.Train.datum d y i) 2
      (volume.restrict (B0579.cell d)) :=
    (memLp_two_iff_integrable_sq_norm hcont_i.aestronglyMeasurable).2
      (hsq_int.congr_fun_ae (Eventually.of_forall fun y => by simp [Real.norm_eq_abs]))
  refine ⟨hmem, ?_⟩
  rw [eLpNorm_two_sq_eq_integral_norm_sq hmem]
  have hint_le : (∫ y in B0579.cell d, ‖UnforcedLeray.Train.datum d y i‖ ^ (2 : ℝ)) ≤
      M_dat ^ 2 * (I_g8 + 1) := by
    have h1 : (∫ y in B0579.cell d, ‖UnforcedLeray.Train.datum d y i‖ ^ (2 : ℝ)) ≤
        ∫ y in B0579.cell d, M_dat ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
        (hG8_int.const_mul (M_dat ^ 2)).restrict ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ico.prod MeasurableSet.univ)] with y hy
      rw [Real.rpow_two, Real.norm_eq_abs]
      refine (pow_le_pow_left₀ (abs_nonneg _) (hpt_bd y hy) 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have h2 : (∫ y in B0579.cell d, M_dat ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) ≤
        ∫ y : ℝ × ℝ, M_dat ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
      setIntegral_le_integral (hG8_int.const_mul (M_dat ^ 2))
        (Eventually.of_forall fun _ => by positivity)
    have h12 := h1.trans h2
    rw [integral_const_mul] at h12
    nlinarith [h12, hMdat_pos]
  calc (∫ y in B0579.cell d, ‖UnforcedLeray.Train.datum d y i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (M_dat ^ 2 * (I_g8 + 1)) ^ (1 / (2 : ℝ)) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
          hint_le (by positivity)
    _ = C_dat2 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hMdat_pos.le]

/-- Pointwise-to-cell comparison of `∫_{cell d} defectPairIntegrand Train.v0 (kerVelCx d V_d)`
against `0 = ∫_{ℝ²} defectPairIntegrand Train.v0 (kerVelPlanarCx (planarMode f))`, yielding an
`O(M₈ / d²)` bound for `1 ≤ d`. -/
lemma cylinder_vs_planar_v0_defect (m : ℝ) (hm : 8 < m) :
    ∃ C_cp : ℝ, 0 < C_cp ∧
      ∀ {d M₈ : ℝ}, 1 ≤ d → 0 < M₈ →
        ∀ {f : Profile}, MemXG f → ContDiffOn ℝ ∞ f (Ioi 0) →
          ∀ {u : UnforcedLeray.B0010.XG},
            f =ᵐ[UnforcedLeray.B0010.xGMeasure] (u : ℝ → ℂ) →
            ∀ (hu : u ∈ (UnforcedLeray.B0121.fracPow 8).domain),
              Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨u, hu⟩) ≤ M₈ →
              IntegrableOn (defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i)
                  (kerVelCx d (periodizeC d (planarMode f)))) (B0579.cell d) ∧
                ‖∫ y in B0579.cell d,
                  defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i)
                    (kerVelCx d (periodizeC d (planarMode f))) y‖ ≤ C_cp * M₈ / d ^ 2 := by
  obtain ⟨C_gj, _, hC_gj, _, hGJ⟩ := T22Sub.canonicalGaussAndJetBound_proof m hm
  obtain ⟨K_vc, hK_vc, hvc⟩ := EulerErrorTail.vel_compare
  obtain ⟨A_v0, hAv0, hbv0⟩ := EulerErrorTail.v0_gauss
  have hG16_int : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) :=
    EulerErrorTail.integrable_gauss (by norm_num)
  set I16 : ℝ := ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)
  have hI16_nn : 0 ≤ I16 := integral_nonneg fun _ => (Real.exp_pos _).le
  set C_kball : ℝ :=
    (∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 0 t‖) +
      (∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 1 t‖)
  have hCkball_nn : 0 ≤ C_kball :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  set c_syn : ℝ := synthZeroConst
  have hcsyn_pos : 0 < c_syn := synthZeroConst_pos
  set c_tail : ℝ := 256 * c_syn * EulerErrorTail.sZ
  have hctail_nn : 0 ≤ c_tail := by have := EulerErrorTail.sZ_nonneg; positivity
  set c_bs : ℝ := c_syn * (C_kball + (2 * Real.pi)⁻¹ * I16)
  have hcbs_nn : 0 ≤ c_bs := by positivity
  set K_near : ℝ := 64 * A_v0 * K_vc * (c_tail + c_syn)
  set K_farC : ℝ := 16384 * A_v0 * C_gj
  set K_farP : ℝ := 16384 * A_v0 * c_bs
  set C_cp : ℝ := (K_near + K_farC + K_farP) * I16 + 1
  have hCcp_pos : 0 < C_cp := by dsimp [C_cp, K_near, K_farC, K_farP]; positivity
  refine ⟨C_cp, hCcp_pos, fun {d M₈} hd hM₈ {f} hf_xg hfc {u} hfu hu hG₈ => ?_⟩
  set e : ℝ × ℝ → ℂ := planarMode f
  set W : ℝ × ℝ → ℂ := periodizeC d e
  obtain ⟨he_cont, he_bd, hW_cont, hWe_tail⟩ :=
    planarMode_and_periodizeC_gauss hfc hfu hu hM₈.le hG₈ hd
  have hGJ_inst := hGJ d hd f hf_xg hfc u hfu hu
  have hkerW_bd : ∀ (k : Fin 2), ∀ y ∈ B0579.cell d, ‖kerVelCx d W y k‖ ≤ C_gj * M₈ := by
    intro k y hy
    exact (hGJ_inst.2.2.2.2 k y hy).2.trans (mul_le_mul_of_nonneg_left hG₈ hC_gj.le)
  -- Measurability of `kerVelCx d W · k` via `EulerErrorSub.stronglyMeasurable_kerVelCx`
  have hkerW_meas : ∀ k : Fin 2, StronglyMeasurable (fun y => kerVelCx d W y k) :=
    fun k => EulerErrorSub.stronglyMeasurable_kerVelCx d hW_cont.stronglyMeasurable k
  -- Planar velocity uniform bound and measurability
  set g : ℂ → ℂ := fun z => e (UnforcedLeray.B0009.toPlane z)
  have hgc : Continuous g := he_cont.comp (Complex.continuous_re.prodMk Complex.continuous_im)
  have he_int : Integrable e :=
    Integrable.mono' (hG16_int.const_mul (c_syn * M₈)) he_cont.aestronglyMeasurable
      (Eventually.of_forall fun z => (he_bd z).trans
        (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 z) (by positivity)))
  have hgi : Integrable g := EulerErrorTail.integrable_toPlane he_int
  have hgK : ∀ z : ℂ, ‖g z‖ ≤ c_syn * M₈ := fun z =>
    (he_bd _).trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.2 (by
        nlinarith [sq_nonneg (UnforcedLeray.B0009.toPlane z).1,
          sq_nonneg (UnforcedLeray.B0009.toPlane z).2])))
  have hg_l1 : ∫ t : ℂ, ‖g t‖ ≤ (c_syn * M₈) * I16 := by
    have hto : ∫ t : ℂ, ‖g t‖ = ∫ x : ℝ × ℝ, ‖e x‖ := by
      apply Complex.ofReal_injective
      rw [← integral_complex_ofReal, ← integral_complex_ofReal,
        ← EulerErrorTail.integral_planeToC (fun t : ℂ => ((‖g t‖ : ℝ) : ℂ))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have htp : UnforcedLeray.B0009.toPlane (planeToC x) = x := by
        ext <;> simp [UnforcedLeray.B0009.toPlane, planeToC]
      dsimp only [g]; rw [htp]
    rw [hto, ← integral_const_mul]
    exact integral_mono he_int.norm (hG16_int.const_mul (c_syn * M₈)) fun z =>
      (he_bd z).trans (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 z) (by positivity))
  have hkerP_bd : ∀ (k : Fin 2) (y : ℝ × ℝ), ‖kerVelPlanarCx e y k‖ ≤ c_bs * M₈ := by
    intro k y
    have hb := EulerErrorTail.norm_biotSavart_le hgc hgK hgi k (planeToC y)
    have hk_le : (∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel k t‖) ≤ C_kball := by
      dsimp [C_kball]
      have i0 : 0 ≤ ∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 0 t‖ :=
        integral_nonneg fun _ => norm_nonneg _
      have i1 : 0 ≤ ∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 1 t‖ :=
        integral_nonneg fun _ => norm_nonneg _
      fin_cases k
      · change (∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 0 t‖) ≤ _
        linarith
      · change (∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 1 t‖) ≤ _
        linarith
    calc ‖kerVelPlanarCx e y k‖
        = ‖UnforcedLeray.B0009.biotSavart g k (planeToC y)‖ := rfl
      _ ≤ (c_syn * M₈) * C_kball + (2 * Real.pi)⁻¹ * ((c_syn * M₈) * I16) :=
          hb.trans (add_le_add (mul_le_mul_of_nonneg_left hk_le (by positivity))
            (mul_le_mul_of_nonneg_left hg_l1 (by positivity)))
      _ = c_bs * M₈ := by dsimp [c_bs]; ring
  have hkerP_meas : ∀ k : Fin 2, StronglyMeasurable (fun y => kerVelPlanarCx e y k) := fun k => by
    have hbs_m : StronglyMeasurable (UnforcedLeray.B0009.biotSavart g k) := by
      have hfun : UnforcedLeray.B0009.biotSavart g k =
          fun w : ℂ => ∫ z : ℂ, UnforcedLeray.B0009.kernel k (w - z) * g z :=
        funext (UnforcedLeray.B0009.biotSavart_apply g k)
      rw [hfun]
      exact StronglyMeasurable.integral_prod_right'
        (((UnforcedLeray.B0009.measurable_kernel k).comp
          (measurable_fst.sub measurable_snd)).mul (hgc.measurable.comp measurable_snd)
          |>.stronglyMeasurable)
    exact hbs_m.comp_measurable EulerErrorTail.continuous_planeToC.measurable
  -- Integrability of `F_cyl` on `B0579.cell d` and `F_plan` on `ℝ × ℝ`
  set F_cyl : ℝ × ℝ → ℂ := defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d W)
  set F_plan : ℝ × ℝ → ℂ := defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelPlanarCx e)
  have hFcyl_int : IntegrableOn F_cyl (B0579.cell d) := by
    have hi : ∀ i j : Fin 2, IntegrableOn
        (fun y => ((UnforcedLeray.Train.v0 y i : ℝ) : ℂ) * kerVelCx d W y j) (B0579.cell d) := by
      intro i j
      have hv_m : AEStronglyMeasurable
          (fun y => ((UnforcedLeray.Train.v0 y i : ℝ) : ℂ)) (volume.restrict (B0579.cell d)) :=
        (Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
            (UnforcedLeray.Train.contDiff_v0 (n := 1)).continuous)).aestronglyMeasurable
      refine Integrable.mono' ((hG16_int.const_mul (A_v0 * (C_gj * M₈))).restrict)
        (hv_m.mul (hkerW_meas j).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ico.prod MeasurableSet.univ)] with y hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hv0_i : |UnforcedLeray.Train.v0 y i| ≤
          A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
        have hp : |UnforcedLeray.Train.v0 y i| ≤ ‖UnforcedLeray.Train.v0 y‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (UnforcedLeray.Train.v0 y) i
        exact (hp.trans (hbv0 y)).trans
          (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 y) hAv0)
      calc |UnforcedLeray.Train.v0 y i| * ‖kerVelCx d W y j‖
          ≤ (A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) * (C_gj * M₈) :=
            mul_le_mul hv0_i (hkerW_bd j y hy) (norm_nonneg _) (by positivity)
        _ = (A_v0 * (C_gj * M₈)) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
    exact (integrableOn_and_integral_defectPairIntegrand hi).1
  have hFplan_int : Integrable F_plan := by
    have hmeas : AEStronglyMeasurable F_plan volume := by
      have hrew : F_plan = fun y =>
          (2 : ℂ) * (((UnforcedLeray.Train.v0 y 0 : ℝ) : ℂ) * kerVelPlanarCx e y 0) +
          (-4 : ℂ) * (((UnforcedLeray.Train.v0 y 1 : ℝ) : ℂ) * kerVelPlanarCx e y 1) +
          (3 * Complex.I) * (((UnforcedLeray.Train.v0 y 0 : ℝ) : ℂ) * kerVelPlanarCx e y 1) +
          (3 * Complex.I) * (((UnforcedLeray.Train.v0 y 1 : ℝ) : ℂ) * kerVelPlanarCx e y 0) :=
        funext (defectPairIntegrand_eq_four_terms (fun z i => UnforcedLeray.Train.v0 z i) (kerVelPlanarCx e))
      rw [hrew]
      have hv_m : ∀ i : Fin 2, AEStronglyMeasurable
          (fun y => ((UnforcedLeray.Train.v0 y i : ℝ) : ℂ)) volume := fun i =>
        (Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
            (UnforcedLeray.Train.contDiff_v0 (n := 1)).continuous)).aestronglyMeasurable
      exact (((((hv_m 0).mul (hkerP_meas 0).aestronglyMeasurable).const_mul _).add
        (((hv_m 1).mul (hkerP_meas 1).aestronglyMeasurable).const_mul _)).add
        (((hv_m 0).mul (hkerP_meas 1).aestronglyMeasurable).const_mul _)).add
        (((hv_m 1).mul (hkerP_meas 0).aestronglyMeasurable).const_mul _)
    refine Integrable.mono' (hG16_int.const_mul (16 * A_v0 * (c_bs * M₈))) hmeas
      (Eventually.of_forall fun y => ?_)
    have hv0_0 : |UnforcedLeray.Train.v0 y 0| ≤ A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
      have hp : |UnforcedLeray.Train.v0 y 0| ≤ ‖UnforcedLeray.Train.v0 y‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (UnforcedLeray.Train.v0 y) 0
      exact (hp.trans (hbv0 y)).trans
        (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 y) hAv0)
    have hv0_1 : |UnforcedLeray.Train.v0 y 1| ≤ A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
      have hp : |UnforcedLeray.Train.v0 y 1| ≤ ‖UnforcedLeray.Train.v0 y‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (UnforcedLeray.Train.v0 y) 1
      exact (hp.trans (hbv0 y)).trans
        (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 y) hAv0)
    have hu0 := hkerP_bd 0 y
    have hu1 := hkerP_bd 1 y
    have hd_pt := norm_defectPairIntegrand_le (fun z i => UnforcedLeray.Train.v0 z i) (kerVelPlanarCx e) y
    calc ‖F_plan y‖
        ≤ 4 * (|UnforcedLeray.Train.v0 y 0| + |UnforcedLeray.Train.v0 y 1|) *
            (‖kerVelPlanarCx e y 0‖ + ‖kerVelPlanarCx e y 1‖) := hd_pt
      _ ≤ 4 * (2 * (A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16))) *
            (2 * (c_bs * M₈)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
            (by linarith) (by positivity) (by positivity)
      _ = (16 * A_v0 * (c_bs * M₈)) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  -- Split at `B_near := {y | ‖planeToC y‖ ≤ d / 8} ⊆ B0579.cell d`
  set B_near : Set (ℝ × ℝ) := {y : ℝ × ℝ | ‖planeToC y‖ ≤ d / 8}
  have hBn_meas : MeasurableSet B_near :=
    isClosed_le (continuous_norm.comp EulerErrorTail.continuous_planeToC) continuous_const
      |>.measurableSet
  have hBn_sub : B_near ⊆ B0579.cell d := by
    intro y hy
    change ‖planeToC y‖ ≤ d / 8 at hy
    have h1 : |y.1| ≤ ‖planeToC y‖ := by
      simpa [planeToC] using Complex.abs_re_le_norm (planeToC y)
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
    exact ⟨by linarith [neg_abs_le y.1], by linarith [le_abs_self y.1]⟩
  have hplan_zero : ∫ y : ℝ × ℝ, F_plan y = 0 :=
    planar_stressDefect_integral_eq_zero he_cont (mul_nonneg hcsyn_pos.le hM₈.le) he_bd
  have hsplit_cyl : ∫ y in B0579.cell d, F_cyl y =
      (∫ y in B_near, F_cyl y) + ∫ y in B0579.cell d \ B_near, F_cyl y := by
    have hinter : B0579.cell d ∩ B_near = B_near := inter_eq_self_of_subset_right hBn_sub
    have h := (integral_add_compl (μ := volume.restrict (B0579.cell d)) hBn_meas hFcyl_int).symm
    rwa [Measure.restrict_restrict hBn_meas, inter_comm, hinter,
      Measure.restrict_restrict hBn_meas.compl, inter_comm _ (B0579.cell d), ← Set.sdiff_eq] at h
  have hsplit_plan : (∫ y in B_near, F_plan y) + ∫ y in B_nearᶜ, F_plan y = 0 := by
    rw [integral_add_compl hBn_meas hFplan_int, hplan_zero]
  have htel : ∫ y in B0579.cell d, F_cyl y =
      (∫ y in B_near, (F_cyl y - F_plan y)) +
        (∫ y in B0579.cell d \ B_near, F_cyl y) -
        (∫ y in B_nearᶜ, F_plan y) := by
    rw [integral_sub (hFcyl_int.mono_set hBn_sub) hFplan_int.integrableOn, hsplit_cyl]
    linear_combination hsplit_plan
  -- Bound the three pieces
  have hv0_8 : ∀ (y : ℝ × ℝ) (i : Fin 2),
      |UnforcedLeray.Train.v0 y i| ≤ A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := fun y i => by
    have hp : |UnforcedLeray.Train.v0 y i| ≤ ‖UnforcedLeray.Train.v0 y‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (UnforcedLeray.Train.v0 y) i
    exact hp.trans (hbv0 y)
  have hexp_far : ∀ y : ℝ × ℝ, y ∉ B_near →
      Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
        (1024 / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro y hy
    change ¬ ‖planeToC y‖ ≤ d / 8 at hy; rw [not_le] at hy
    rw [EulerErrorTail.norm_planeToC_sq' y]
    have hsq : (d / 8) ^ 2 ≤ ‖planeToC y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy.le 2
    have h1 := EulerErrorTail.exp_split hsq
    have h2 : Real.exp (-((d / 8) ^ 2) / 16) ≤ 1024 / d ^ 2 := by
      have hinv := EulerErrorTail.exp_neg_le_inv (x := d ^ 2 / 1024) (by positivity)
      calc Real.exp (-((d / 8) ^ 2) / 16) = Real.exp (-(d ^ 2 / 1024)) := by ring_nf
        _ ≤ 1 / (d ^ 2 / 1024) := hinv
        _ = 1024 / d ^ 2 := by field_simp
    calc Real.exp (-(‖planeToC y‖ ^ 2) / 8)
        ≤ Real.exp (-(‖planeToC y‖ ^ 2) / 16) * Real.exp (-((d / 8) ^ 2) / 16) := h1
      _ ≤ Real.exp (-(‖planeToC y‖ ^ 2) / 16) * (1024 / d ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (1024 / d ^ 2) * Real.exp (-(‖planeToC y‖ ^ 2) / 16) := mul_comm _ _
  have hb_near : ‖∫ y in B_near, (F_cyl y - F_plan y)‖ ≤ (K_near * M₈ / d ^ 2) * I16 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hG16_int.const_mul (K_near * M₈ / d ^ 2)).restrict ?_).trans ?_
    · filter_upwards [ae_restrict_mem hBn_meas] with y hy
      have hsub_eq : F_cyl y - F_plan y =
          defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i)
            (fun z k => kerVelCx d W z k - kerVelPlanarCx e z k) y :=
        defectPairIntegrand_sub_right _ _ _ y
      rw [hsub_eq]
      have hd_pt := norm_defectPairIntegrand_le (fun z i => UnforcedLeray.Train.v0 z i)
        (fun z k => kerVelCx d W z k - kerVelPlanarCx e z k) y
      have hvc_0 : ‖kerVelCx d W y 0 - kerVelPlanarCx e y 0‖ ≤
          K_vc * ((c_tail + c_syn) * M₈) * (1 + ‖planeToC y‖) / d ^ 2 := by
        have h := hvc hd (mul_nonneg hcsyn_pos.le hM₈.le) (mul_nonneg hctail_nn hM₈.le)
          he_cont hW_cont he_bd (fun z hz => by
            simpa [c_tail, c_syn, mul_assoc, mul_left_comm, mul_comm] using hWe_tail z hz)
          y 0 hy
        refine h.trans (le_of_eq ?_); ring
      have hvc_1 : ‖kerVelCx d W y 1 - kerVelPlanarCx e y 1‖ ≤
          K_vc * ((c_tail + c_syn) * M₈) * (1 + ‖planeToC y‖) / d ^ 2 := by
        have h := hvc hd (mul_nonneg hcsyn_pos.le hM₈.le) (mul_nonneg hctail_nn hM₈.le)
          he_cont hW_cont he_bd (fun z hz => by
            simpa [c_tail, c_syn, mul_assoc, mul_left_comm, mul_comm] using hWe_tail z hz)
          y 1 hy
        refine h.trans (le_of_eq ?_); ring
      have hexp_1 : (1 + ‖planeToC y‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
          4 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
        have hsp : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) =
            Real.exp (-(‖planeToC y‖ ^ 2) / 16) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
          rw [EulerErrorTail.norm_planeToC_sq' y, ← Real.exp_add]; congr 1; ring
        rw [hsp, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (EulerErrorTail.one_add_mul_exp_le (norm_nonneg _))
          (Real.exp_pos _).le
      calc ‖defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i)
              (fun z k => kerVelCx d W z k - kerVelPlanarCx e z k) y‖
          ≤ 4 * (2 * (A_v0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))) *
              (2 * (K_vc * ((c_tail + c_syn) * M₈) * (1 + ‖planeToC y‖) / d ^ 2)) :=
            hd_pt.trans (mul_le_mul
              (mul_le_mul_of_nonneg_left (add_le_add (hv0_8 y 0) (hv0_8 y 1) |>.trans_eq (by ring))
                (by norm_num))
              (add_le_add hvc_0 hvc_1 |>.trans_eq (by ring))
              (by positivity) (by positivity))
        _ = (16 * A_v0 * K_vc * (c_tail + c_syn) * M₈ / d ^ 2) *
              ((1 + ‖planeToC y‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by ring
        _ ≤ (16 * A_v0 * K_vc * (c_tail + c_syn) * M₈ / d ^ 2) *
              (4 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
            mul_le_mul_of_nonneg_left hexp_1 (by positivity)
        _ = (K_near * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
            dsimp [K_near]; ring
    · calc (∫ y in B_near, (K_near * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16))
          ≤ ∫ y : ℝ × ℝ, (K_near * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
            setIntegral_le_integral (hG16_int.const_mul _)
              (Eventually.of_forall fun _ => by positivity)
        _ = (K_near * M₈ / d ^ 2) * I16 := integral_const_mul _ _
  have hb_farC : ‖∫ y in B0579.cell d \ B_near, F_cyl y‖ ≤ (K_farC * M₈ / d ^ 2) * I16 := by
    have hm_diff : MeasurableSet (B0579.cell d \ B_near) :=
      (measurableSet_Ico.prod MeasurableSet.univ).diff hBn_meas
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hG16_int.const_mul (K_farC * M₈ / d ^ 2)).restrict ?_).trans ?_
    · filter_upwards [ae_restrict_mem hm_diff] with y ⟨hy_cell, hy_far⟩
      have hd_pt := norm_defectPairIntegrand_le (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d W) y
      have hf_exp := hexp_far y hy_far
      have hv0_far : ∀ i : Fin 2, |UnforcedLeray.Train.v0 y i| ≤
          A_v0 * ((1024 / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := fun i =>
        (hv0_8 y i).trans (mul_le_mul_of_nonneg_left hf_exp hAv0)
      calc ‖F_cyl y‖
          ≤ 4 * (2 * (A_v0 * ((1024 / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)))) *
              (2 * (C_gj * M₈)) :=
            hd_pt.trans (mul_le_mul
              (mul_le_mul_of_nonneg_left
                (add_le_add (hv0_far 0) (hv0_far 1) |>.trans_eq (by ring)) (by norm_num))
              (add_le_add (hkerW_bd 0 y hy_cell) (hkerW_bd 1 y hy_cell) |>.trans_eq (by ring))
              (by positivity) (by positivity))
        _ = (K_farC * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
            dsimp [K_farC]; ring
    · calc (∫ y in B0579.cell d \ B_near,
              (K_farC * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16))
          ≤ ∫ y : ℝ × ℝ, (K_farC * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
            setIntegral_le_integral (hG16_int.const_mul _)
              (Eventually.of_forall fun _ => by positivity)
        _ = (K_farC * M₈ / d ^ 2) * I16 := integral_const_mul _ _
  have hb_farP : ‖∫ y in B_nearᶜ, F_plan y‖ ≤ (K_farP * M₈ / d ^ 2) * I16 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hG16_int.const_mul (K_farP * M₈ / d ^ 2)).restrict ?_).trans ?_
    · filter_upwards [ae_restrict_mem hBn_meas.compl] with y hy_far
      have hd_pt := norm_defectPairIntegrand_le (fun z i => UnforcedLeray.Train.v0 z i) (kerVelPlanarCx e) y
      have hf_exp := hexp_far y hy_far
      have hv0_far : ∀ i : Fin 2, |UnforcedLeray.Train.v0 y i| ≤
          A_v0 * ((1024 / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := fun i =>
        (hv0_8 y i).trans (mul_le_mul_of_nonneg_left hf_exp hAv0)
      calc ‖F_plan y‖
          ≤ 4 * (2 * (A_v0 * ((1024 / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)))) *
              (2 * (c_bs * M₈)) :=
            hd_pt.trans (mul_le_mul
              (mul_le_mul_of_nonneg_left
                (add_le_add (hv0_far 0) (hv0_far 1) |>.trans_eq (by ring)) (by norm_num))
              (add_le_add (hkerP_bd 0 y) (hkerP_bd 1 y) |>.trans_eq (by ring))
              (by positivity) (by positivity))
        _ = (K_farP * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
            dsimp [K_farP]; ring
    · calc (∫ y in B_nearᶜ,
              (K_farP * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16))
          ≤ ∫ y : ℝ × ℝ, (K_farP * M₈ / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
            setIntegral_le_integral (hG16_int.const_mul _)
              (Eventually.of_forall fun _ => by positivity)
        _ = (K_farP * M₈ / d ^ 2) * I16 := integral_const_mul _ _
  refine ⟨hFcyl_int, ?_⟩
  rw [htel]
  have htri1 := norm_sub_le
    ((∫ y in B_near, (F_cyl y - F_plan y)) + ∫ y in B0579.cell d \ B_near, F_cyl y)
    (∫ y in B_nearᶜ, F_plan y)
  have htri2 := norm_add_le
    (∫ y in B_near, (F_cyl y - F_plan y))
    (∫ y in B0579.cell d \ B_near, F_cyl y)
  calc ‖(∫ y in B_near, (F_cyl y - F_plan y)) +
          (∫ y in B0579.cell d \ B_near, F_cyl y) -
          (∫ y in B_nearᶜ, F_plan y)‖
      ≤ (K_near * M₈ / d ^ 2) * I16 + (K_farC * M₈ / d ^ 2) * I16 +
          (K_farP * M₈ / d ^ 2) * I16 := by linarith
    _ = ((K_near + K_farC + K_farP) * I16) * M₈ / d ^ 2 := by ring
    _ ≤ C_cp * M₈ / d ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (sq_nonneg d)
        dsimp [C_cp]; nlinarith

lemma integral_Ioc_nu_sq_clockTheta_sq {ν B r : ℝ} (hν : 0 < ν)
    (hr_pos : 0 < r) (hrB : r ≤ B) (hB_inv : B ≤ ν⁻¹) :
    IntegrableOn (fun s => ν ^ 2 * (clockTheta ν s) ^ 2) (Ioc (clockAge ν B) (clockAge ν r)) ∧
      (∫ s in Ioc (clockAge ν B) (clockAge ν r), ν ^ 2 * (clockTheta ν s) ^ 2) = B - r := by
  have hB_pos : 0 < B := lt_of_lt_of_le hr_pos hrB
  set s_B : ℝ := clockAge ν B
  set s_r : ℝ := clockAge ν r
  have hsB_nn : 0 ≤ s_B := T22Sub.clockAge_nonneg hν hB_pos hB_inv
  have hsB_le_sr : s_B ≤ s_r := by
    unfold s_B s_r clockAge
    have h1 : (ν ^ 2 * B)⁻¹ ≤ (ν ^ 2 * r)⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hrB (by positivity))
    have hrew : ∀ θ : ℝ, θ ≠ 0 → (1 - ν * θ) / (ν ^ 2 * θ) = (ν ^ 2 * θ)⁻¹ - ν⁻¹ := fun θ hθ => by
      have := hν.ne'; field_simp
    rw [hrew B hB_pos.ne', hrew r hr_pos.ne']
    linarith
  have hderiv : ∀ s ∈ uIcc s_B s_r,
      HasDerivAt (fun t : ℝ => -clockTheta ν t) (ν ^ 2 * (clockTheta ν s) ^ 2) s := by
    intro s hs
    rw [uIcc_of_le hsB_le_sr] at hs
    have hs_nn : 0 ≤ s := hsB_nn.trans hs.1
    have hden_pos : 0 < ν + ν ^ 2 * s := by positivity
    have hfn : (fun t : ℝ => -clockTheta ν t) = fun t => -(ν + ν ^ 2 * t)⁻¹ := by
      funext t; unfold clockTheta clockA; ring_nf
    rw [hfn]
    have hlin : HasDerivAt (fun t : ℝ => ν + ν ^ 2 * t) (ν ^ 2) s :=
      (((hasDerivAt_id' s).const_mul (ν ^ 2)).const_add ν).congr_deriv (by ring)
    have hinv := (hlin.inv hden_pos.ne').neg
    refine hinv.congr_deriv ?_
    unfold clockTheta clockA
    have := hden_pos.ne'
    field_simp
  have hcont : ContinuousOn (fun s => ν ^ 2 * (clockTheta ν s) ^ 2) (Icc s_B s_r) := by
    refine continuousOn_const.mul ((ContinuousOn.inv₀ ?_ ?_).pow 2)
    · unfold clockA
      exact continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    · intro s hs
      have hs_nn : 0 ≤ s := hsB_nn.trans hs.1
      unfold clockA; positivity
  have hintOn : IntegrableOn (fun s => ν ^ 2 * (clockTheta ν s) ^ 2) (Ioc s_B s_r) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiiv : IntervalIntegrable (fun s => ν ^ 2 * (clockTheta ν s) ^ 2) volume s_B s_r :=
    (uIcc_of_le hsB_le_sr ▸ hcont).intervalIntegrable
  refine ⟨hintOn, ?_⟩
  rw [← intervalIntegral.integral_of_le hsB_le_sr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hiiv,
    T22Sub.clockTheta_clockAge hν hr_pos, T22Sub.clockTheta_clockAge hν hB_pos]
  ring

/-- Compact clock-window stress defect bound (`s ∈ (s_B, s_r]`, `0 < r < B`, `1 ≤ B`). -/
lemma stressDefect_compact_window
    (P : PlanarData) (hP : IsPlanarReference P) (m : ℝ) (hm : 8 < m)
    (K : Set ℂ) (hK : IsAdmissibleK K)
    {B r : ℝ} (hB1 : 1 ≤ B) (hr_pos : 0 < r) (hrB : r < B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          (∀ s : ℝ, IsCentrallyEven (w s)) →
          ∀ μ ∈ K,
            ‖∫ s in Ioc (clockAge ν B) (clockAge ν r),
                ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
                  3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                    ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ ε * scaleA P ν μ := by
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos hB1
  -- Gather ν-independent constants
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hBranch := T22Sub.ctCanonicalBranchProps P hP m hm
  obtain ⟨C_V, hC_V, hVd_xnorm⟩ := hBranch.2.2.2 B hB_pos
  obtain ⟨V_rep, hVsol, hVae⟩ := T22Sub.hasCanonicalSolutionRep_proof P hP
  obtain ⟨_, b₀_rep, _, hRep_all⟩ :=
    T22Sub.ResidualBoundAux.canonicalSolutionRep_smooth_and_bounds P hP V_rep hVsol hVae
  set B_rep : ℝ := max B b₀_rep
  obtain ⟨_, M₈_r, _, hM₈_r, _, hRep_G8⟩ :=
    (hRep_all B_rep (le_max_right _ _)).2 r hr_pos (hrB.le.trans (le_max_left _ _))
  obtain ⟨C_gj, _, hC_gj, _, hGJ⟩ := T22Sub.canonicalGaussAndJetBound_proof m hm
  obtain ⟨C_dat2, C_datT, hC_dat2, hC_datT, hDat⟩ := datum_cell_l2_and_tail
  obtain ⟨C_cp, hC_cp, hCylPlan⟩ := cylinder_vs_planar_v0_defect m hm
  obtain ⟨C_tc, b_tc, ν_tc, hC_tc, hb_tc, hν_tc, hTC⟩ :=
    T22Sub.trainComparison_unconditional 2 (by norm_num) 0
  obtain ⟨C_L2, ν_L2, hC_L2, hν_L2, hL2_unif⟩ := train_cellL2_uniform_aniso
  obtain ⟨b₀_comp, hComp_all⟩ := ctCompactComparison P hP m hm
  set B_comp : ℝ := max B b₀_comp
  -- Choose `ε_comp ≤ 1` so `12 * C_dat2 * ε_comp ≤ δ_target / 4`
  set δ_target : ℝ := ε / (4 * B ^ 3 + 1)
  have hδ_pos : 0 < δ_target := by positivity
  set ε_comp : ℝ := min 1 (δ_target / (48 * C_dat2 + 1))
  have hε_comp_pos : 0 < ε_comp := lt_min one_pos (by positivity)
  have hε_comp_le1 : ε_comp ≤ 1 := min_le_left _ _
  have hComp_ev := hComp_all B_comp (le_max_right _ _) r hr_pos
    (hrB.le.trans (le_max_left _ _)) ε_comp hε_comp_pos
  -- Choose small-ν numerical thresholds so the remaining three error pieces are each ≤ δ_target / 4
  set B_UZ : ℝ := 1 + C_emb * C_V
  have hB_UZ_pos : 0 < B_UZ := by positivity
  have hlim_tc : Tendsto (fun ν : ℝ => (12 * C_tc * B_UZ * B) * Real.exp (-(b_tc * r / ν ^ 3)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun ν : ℝ => ν ^ 3) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by
        simpa using ((continuous_pow 3).continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ν hν
      exact pow_pos (mem_Ioi.1 hν) 3
    have h2 : Tendsto (fun x : ℝ => (b_tc * r) * x⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
    have h3 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h4 := (h3.comp (h2.comp h1)).const_mul (12 * C_tc * B_UZ * B)
    rw [mul_zero] at h4
    exact h4.congr fun ν => by dsimp [Function.comp]; ring_nf
  have hlim_d2 : Tendsto
      (fun ν : ℝ => (1024 * C_datT * (C_gj * M₈_r) + C_cp * M₈_r) * (ν ^ 3 / r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun ν : ℝ => ν ^ 3 / r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun ν : ℝ => ν ^ 3 / r) := (continuous_pow 3).div_const r
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa using h0.const_mul (1024 * C_datT * (C_gj * M₈_r) + C_cp * M₈_r)
  have hev_pos : ∀ᶠ ν : ℝ in 𝓝[>] (0 : ℝ),
      ν ∈ Ioc 0 (min ν_tc (min ν_L2 (min (1 / 4) ((2 * B)⁻¹)))) ∧ ν ^ 3 ≤ r := by
    have hν_max : 0 < min ν_tc (min ν_L2 (min (1 / 4) ((2 * B)⁻¹))) :=
      lt_min hν_tc (lt_min hν_L2 (lt_min (by norm_num) (inv_pos.2 (by positivity))))
    have hev1 : Ioc 0 (min ν_tc (min ν_L2 (min (1 / 4) ((2 * B)⁻¹)))) ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT hν_max
    have hev2 : ∀ᶠ ν : ℝ in 𝓝[>] (0 : ℝ), ν ^ 3 ≤ r := by
      have h0 : Tendsto (fun ν : ℝ => ν ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using ((continuous_pow 3).continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds
      filter_upwards [(Metric.tendsto_nhds.1 h0) r hr_pos, self_mem_nhdsWithin] with ν hν_r hν_p
      rw [dist_zero_right, Real.norm_of_nonneg (pow_nonneg (mem_Ioi.1 hν_p).le 3)] at hν_r
      exact hν_r.le
    filter_upwards [hev1, hev2] with ν h1 h2 using ⟨h1, h2⟩
  filter_upwards [hComp_ev, hev_pos,
    (Metric.tendsto_nhds.1 hlim_tc) (δ_target / 4) (by positivity),
    (Metric.tendsto_nhds.1 hlim_d2) (2 * (δ_target / 4)) (by positivity)]
    with ν hComp_ν ⟨hν_in, hν3_r⟩ htc_small hd2_small
  intro tr htr w u hw hw_ev μ hμ
  have hν_pos : 0 < ν := hν_in.1
  have hν_tc_le : ν ≤ ν_tc := hν_in.2.trans (min_le_left _ _)
  have hν_L2_le : ν ≤ ν_L2 := hν_in.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_qtr : ν ≤ 1 / 4 :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_2B : ν ≤ (2 * B)⁻¹ :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  have hνB_half : ν * B ≤ 1 / 2 := by
    calc ν * B ≤ (2 * B)⁻¹ * B := mul_le_mul_of_nonneg_right hν_2B hB_pos.le
      _ = 1 / 2 := by field_simp [hB_pos.ne']
  have hB_lt_inv : B < ν⁻¹ := by
    rw [lt_inv_comm₀ hB_pos hν_pos]
    calc ν ≤ (2 * B)⁻¹ := hν_2B
      _ = B⁻¹ / 2 := by ring
      _ < B⁻¹ := half_lt_self (inv_pos.2 hB_pos)
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  have hc1 : 1 ≤ c := by
    have hle : ((1 / 4 : ℝ) ^ (-2 : ℝ)) ≤ c :=
      Real.rpow_le_rpow_of_nonpos hν_pos hν_qtr (by norm_num)
    have hev : ((1 / 4 : ℝ) ^ (-2 : ℝ)) = 16 := by norm_num
    linarith
  obtain ⟨_, hprep_zc, _⟩ := hBranch.1 ν ⟨hν_pos, hν1⟩
  obtain ⟨hσ_pos, hσ_lt⟩ := hK.2 μ hμ
  set σ : ℝ := μ.re
  have hscaleA_nn : 0 ≤ scaleA P ν μ := by unfold scaleA; positivity
  rw [dist_zero_right, Real.norm_of_nonneg (by positivity)] at htc_small hd2_small
  -- Set up the window `Ioc s_B s_r`
  set s_B : ℝ := clockAge ν B
  set s_r : ℝ := clockAge ν r
  have hsB_pos : 0 < s_B := by
    unfold s_B clockAge
    exact div_pos (by linarith) (by positivity)
  obtain ⟨hint_θsq, hval_θsq⟩ :=
    integral_Ioc_nu_sq_clockTheta_sq hν_pos hr_pos hrB.le hB_lt_inv.le
  -- Measurability of the defect integrand on `Ioc s_B s_r`
  set F_def : ℝ → ℂ := fun s =>
    ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
      3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
        ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)
  have hrc_pair : ∀ i j : Fin 2, ∀ s₀ : ℝ, 0 < s₀ →
      ContinuousWithinAt
        (fun s => ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s x j) (Ici s₀) s₀ :=
    fun i j s₀ hs₀ => rightContinuous_train_vel_pairing hm hc1 hC_L2 tr
      (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr) hprep_zc hw hw_ev i j hs₀.le
  have hrc_F : ∀ s₀ : ℝ, 0 < s₀ → ContinuousWithinAt F_def (Ici s₀) s₀ := by
    intro s₀ hs₀
    have hfun : EqOn F_def (fun s =>
        (((c⁻¹ : ℝ) : ℂ) * (s : ℂ) ^ (-μ) *
          ((2 : ℂ) * (∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * u s x 0) +
            (-4 : ℂ) * (∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * u s x 1) +
            (3 * Complex.I) * (∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * u s x 1) +
            (3 * Complex.I) * (∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * u s x 0))) *
          ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ici s₀) := by
      intro s hs
      have hs0 : 0 ≤ s := hs₀.le.trans hs
      have hv_fin : UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤ :=
        lt_of_le_of_lt (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr s hs0) ENNReal.ofReal_lt_top
      have hv_m : ∀ i, MemLp (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) :=
        fun i => (memLp_train_coord_of_cellL2 hs0 tr hv_fin i).1
      have hij : ∀ i j, IntegrableOn (fun x => ((tr.v s x i : ℝ) : ℂ) * u s x j)
          (B0579.cell c) := fun i j => (hv_m i).ofReal.integrable_mul ((hw.biotSavart s hs0).1 j)
      dsimp only [F_def]
      rw [pairs_defect_eq_defectPairIntegrand hν_pos tr μ hs0 hv_fin (hw.biotSavart s hs0)]
      congr 2
      exact (integrableOn_and_integral_defectPairIntegrand
        (V := fun z i => tr.v s z i) (U := u s) hij).2
    refine ContinuousWithinAt.congr ?_ (fun s hs => hfun hs) (hfun (mem_Ici.2 le_rfl))
    have hcpow : ContinuousWithinAt (fun s : ℝ => (s : ℂ) ^ (-μ)) (Ici s₀) s₀ := by
      have harg : ((s₀ : ℂ) ∈ Complex.slitPlane) :=
        Complex.ofReal_mem_slitPlane.2 hs₀
      exact ((continuousAt_cpow_const harg).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hrpow : ContinuousWithinAt (fun s : ℝ => ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ici s₀) s₀ :=
      (Complex.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_rpow_const s₀ (-3 / 2 : ℝ) (Or.inl hs₀.ne'))).continuousWithinAt
    exact (((continuousWithinAt_const.mul hcpow).mul
      (((((hrc_pair 0 0 s₀ hs₀).const_mul _).add ((hrc_pair 1 1 s₀ hs₀).const_mul _)).add
        ((hrc_pair 0 1 s₀ hs₀).const_mul _)).add ((hrc_pair 1 0 s₀ hs₀).const_mul _))).mul hrpow)
  have hF_aesm : AEStronglyMeasurable F_def (volume.restrict (Ioc s_B s_r)) :=
    aestronglyMeasurable_on_subset_Ioi_of_rightContinuous
      (fun s hs => hsB_pos.trans hs.1) measurableSet_Ioc hrc_F
  -- Pointwise slice bound on `s ∈ Ioc s_B s_r`
  have hslice_bd : ∀ s ∈ Ioc s_B s_r,
      ‖F_def s‖ ≤ (4 * B ^ 2 * scaleA P ν μ * δ_target) * (ν ^ 2 * (clockTheta ν s) ^ 2) := by
    intro s hs
    have hs_pos : 0 < s := hsB_pos.trans hs.1
    have hs0 : 0 ≤ s := hs_pos.le
    have ha_pos : 0 < clockA ν s := by unfold clockA; positivity
    set a : ℝ := clockA ν s
    set θ : ℝ := clockTheta ν s
    have hθ_pos : 0 < θ := by unfold θ clockTheta; positivity
    have hθ_ge_r : r ≤ θ := by
      have ha_le : clockA ν s ≤ clockA ν s_r := by
        unfold clockA; nlinarith [hs.2]
      rw [T22Sub.clockA_clockAge hν_pos hr_pos] at ha_le
      have hinv : θ⁻¹ ≤ r⁻¹ := by
        unfold θ clockTheta; rw [inv_inv]
        calc ν * clockA ν s ≤ ν * (ν * r)⁻¹ := mul_le_mul_of_nonneg_left ha_le hν_pos.le
          _ = r⁻¹ := by field_simp [hν_pos.ne']
      exact (inv_le_inv₀ hθ_pos hr_pos).1 hinv
    have hθ_le_B : θ ≤ B := by
      have ha_ge : clockA ν s_B ≤ clockA ν s := by
        unfold clockA; nlinarith [hs.1.le]
      rw [T22Sub.clockA_clockAge hν_pos hB_pos] at ha_ge
      have hinv : B⁻¹ ≤ θ⁻¹ := by
        unfold θ clockTheta; rw [inv_inv]
        calc B⁻¹ = ν * (ν * B)⁻¹ := by field_simp [hν_pos.ne']
          _ ≤ ν * clockA ν s := mul_le_mul_of_nonneg_left ha_ge hν_pos.le
      exact (inv_le_inv₀ hB_pos hθ_pos).1 hinv
    have hs_eq : clockAge ν θ = s := T22Sub.clockAge_clockTheta hν_pos ha_pos
    have ha_eq : a = (ν * θ)⁻¹ := by
      change clockA ν s = (ν * θ)⁻¹
      rw [← hs_eq, T22Sub.clockA_clockAge hν_pos hθ_pos]
    set d : ℝ := dOfTheta ν θ
    have hd_cell : d = cellLen c a := T22Sub.dOfTheta_eq_cellLen hν_pos ha_pos
    have hd1 : 1 ≤ d := T22Sub.one_le_dOfTheta hν_pos (hν3_r.trans hθ_ge_r)
    have hd0 : 0 < d := lt_of_lt_of_le one_pos hd1
    -- Compact comparison at `θ ∈ Icc r B`
    have hComp_θ := (hComp_ν tr htr w u hw θ ⟨hθ_ge_r, hθ_le_B.trans (le_max_left _ _)⟩).1
    set Z_θ : ℝ × ℝ → ℂ := heatColumn P ν w θ
    set V_d : ℝ × ℝ → ℂ := canonicalPeriodized P ν θ
    -- Biot-Savart velocities `U_Z` for `Z_θ` and `U_Vd` for `V_d` on `B0579.cell d`
    have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν_pos
    set U_Z : ℝ × ℝ → Fin 2 → ℂ := fun y j =>
      (P.gaugeFactor ν)⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        u s (Real.sqrt a * y.1, Real.sqrt a * y.2) j
    have hUZ_bs : IsBiotSavart d Z_θ U_Z := by
      have hbs_j := UnforcedLeray.Short.PartIIIb.Concrete.isBiotSavart_jscaleInv
        c a hc_pos ha_pos (w s) (u s) (hw.biotSavart s hs0)
      rw [← hd_cell] at hbs_j
      have hZ_eq : Z_θ = fun y => (P.gaugeFactor ν)⁻¹ * JscaleInv a (w s) y := by
        funext y; dsimp only [Z_θ, heatColumn]; rw [hs_eq, ← ha_eq]
      have hU_eq : U_Z = fun y j => (P.gaugeFactor ν)⁻¹ *
          (((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u s (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := by
        funext y j; dsimp only [U_Z]; ring
      have hint_j : IntegrableOn (JscaleInv a (w s)) (B0579.cell d) := by
        have hm_j := ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.memLp_JscaleInv_pos
          (c := c) (by linarith : (0 : ℝ) ≤ m) ha_pos (hw.memX s hs0)
        rw [← hd_cell] at hm_j
        exact integrableOn_cell_of_memX (by linarith) hm_j
      rw [hZ_eq, hU_eq]
      exact isBiotSavart_smul_aniso (P.gaugeFactor ν)⁻¹ hint_j hbs_j
    have hZ_mem : MemLp Z_θ 2 (B0579.cellMeasure d m) := by
      have hm_j := ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.memLp_JscaleInv_pos
        (c := c) (by linarith : (0 : ℝ) ≤ m) ha_pos (hw.memX s hs0)
      rw [← hd_cell] at hm_j
      have hZ_eq : Z_θ = fun y => (P.gaugeFactor ν)⁻¹ * JscaleInv a (w s) y := by
        funext y; dsimp only [Z_θ, heatColumn]; rw [hs_eq, ← ha_eq]
      rw [hZ_eq]
      exact hm_j.const_mul (P.gaugeFactor ν)⁻¹
    obtain ⟨hVd_mem, hVd_zc, hVd_ev, _⟩ := hBranch.2.1 ν θ hν_pos hθ_pos hd1
    obtain ⟨U_Vd, hUVd_bs⟩ := exists_isBiotSavart_of_memX hm hd1 V_d hVd_mem hVd_zc hVd_ev
    have hUVd_ae := ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.kerVelCx_ae_eq_of_isBiotSavart_pos
      hd0 hm hVd_mem hVd_zc hUVd_bs
    have hdiff_bs : IsBiotSavart d (Z_θ - V_d) (fun y j => U_Z y j - U_Vd y j) :=
      isBiotSavart_sub_aniso (by linarith) hZ_mem hVd_mem hUZ_bs hUVd_bs
    have hvel_diff_le : ∀ j : Fin 2,
        (eLpNorm (fun y => U_Z y j - U_Vd y j) 2 (volume.restrict (B0579.cell d))).toReal ≤
          ε_comp := by
      intro j
      have h1 : eLpNorm (fun y => U_Z y j - U_Vd y j) 2 (volume.restrict (B0579.cell d)) ≤
          ENNReal.ofReal ε_comp :=
        (eLpNorm_coord_le_velNorm (fun y k => U_Z y k - U_Vd y k) j).trans
          ((kinNorm_eq_velNorm_aniso hd0 hdiff_bs).symm.le.trans hComp_θ)
      exact ENNReal.toReal_le_of_le_ofReal hε_comp_pos.le h1
    have hUVd_le : ∀ j : Fin 2,
        (eLpNorm (fun y => U_Vd y j) 2 (volume.restrict (B0579.cell d))).toReal ≤
          C_emb * C_V := by
      intro j
      have hemb_Vd : velNorm d U_Vd ≤ ENNReal.ofReal (C_emb * C_V) := by
        calc velNorm d U_Vd
            ≤ ENNReal.ofReal C_emb0 * xNorm d m V_d :=
              le_add_self.trans (hEmb0 d hd1 V_d hVd_mem hVd_zc hVd_ev U_Vd hUVd_bs)
          _ ≤ ENNReal.ofReal C_emb * ENNReal.ofReal C_V :=
              mul_le_mul (ENNReal.ofReal_le_ofReal (le_max_left _ _))
                (hVd_xnorm ν ⟨hν_pos, hν1⟩ θ ⟨hθ_pos, hθ_le_B⟩ hd1) bot_le bot_le
          _ = ENNReal.ofReal (C_emb * C_V) := (ENNReal.ofReal_mul hC_emb.le).symm
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        ((eLpNorm_coord_le_velNorm U_Vd j).trans hemb_Vd)
    have hUZ_le : ∀ j : Fin 2,
        (eLpNorm (fun y => U_Z y j) 2 (volume.restrict (B0579.cell d))).toReal ≤ B_UZ := by
      intro j
      have heq_j : (fun y => U_Z y j) =
          (fun y => U_Z y j - U_Vd y j) + (fun y => U_Vd y j) := by funext y; simp
      have htri := eLpNorm_add_le (hdiff_bs.1 j).1 (hUVd_bs.1 j).1 one_le_two
      rw [← heq_j] at htri
      have htr := ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨(hdiff_bs.1 j).2.ne, (hUVd_bs.1 j).2.ne⟩) htri
      rw [ENNReal.toReal_add (hdiff_bs.1 j).2.ne (hUVd_bs.1 j).2.ne] at htr
      have b1 := hvel_diff_le j
      have b2 := hUVd_le j
      dsimp [B_UZ]; linarith
    -- Step 1: `tr.v s` vs `Train.Vc ν c s` on `B0579.cell c`
    have ha_le_c2 : UnforcedLeray.Train.width ν s ≤ c ^ 2 := by
      have hw_eq : UnforcedLeray.Train.width ν s = a := rfl
      rw [hw_eq]
      have hdiv : 1 ≤ c ^ 2 / a := by
        have hd_sq : d ^ 2 = c ^ 2 / a := by
          rw [hd_cell]; unfold cellLen
          rw [div_pow, Real.sq_sqrt ha_pos.le]
        rw [← hd_sq]; nlinarith
      exact (one_le_div ha_pos).1 hdiv
    have htc_s := (hTC ν hν_pos hν_tc_le tr htr s hs0 ha_le_c2).1
    dsimp only [UnforcedLeray.Short.PartI.trainPeriod] at htc_s
    rw [UnforcedLeray.Short.PartI.cellL2_jet_zero] at htc_s
    have hca_eq : (ν ^ (-2 : ℝ)) ^ 2 / UnforcedLeray.Train.width ν s = θ / ν ^ 3 := by
      have hw_eq : UnforcedLeray.Train.width ν s = a := rfl
      rw [hw_eq, ha_eq]
      have hc2 : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
        rw [Real.rpow_neg hν_pos.le, Real.rpow_two, inv_pow]; ring
      rw [hc2]
      have := hν_pos.ne'; have := hθ_pos.ne'
      field_simp
    have ha_inv2 : (UnforcedLeray.Train.width ν s) ^ (-(2 + (0 : ℕ) / (2 : ℝ))) =
        ν ^ 2 * θ ^ 2 := by
      have hw_eq : UnforcedLeray.Train.width ν s = a := rfl
      rw [hw_eq, ha_eq, Nat.cast_zero, zero_div, add_zero, Real.inv_rpow (by positivity),
        Real.rpow_neg (by positivity), inv_inv, Real.rpow_two]
      ring
    rw [mul_div_assoc b_tc, hca_eq, ha_inv2] at htc_s
    set E_tc : ℝ := C_tc * ν * θ ^ 2 * Real.exp (-(b_tc * (θ / ν ^ 3)))
    have hEtc_nn : 0 ≤ E_tc := by dsimp [E_tc]; positivity
    have htc_s' : UnforcedLeray.Train.cellL2 c
        (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z) ≤ ENNReal.ofReal E_tc := by
      refine htc_s.trans (le_of_eq ?_)
      congr 1; dsimp [E_tc]; have := hν_pos.ne'; field_simp
    have hv_diff_mem : ∀ i : Fin 2,
        MemLp (fun x => tr.v s x i - UnforcedLeray.Train.Vc ν c s x i) 2
          (volume.restrict (B0579.cell c)) ∧
        (eLpNorm (fun x => tr.v s x i - UnforcedLeray.Train.Vc ν c s x i) 2
          (volume.restrict (B0579.cell c))).toReal ≤ E_tc := by
      intro i
      have hcont_v : Continuous (fun x => tr.v s x i) :=
        ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
          tr.isTrain.smooth_v.continuousOn).comp_continuous
          (continuous_const.prodMk continuous_id) (fun _ => ⟨hs0, trivial⟩)
      have hcont_Vc : Continuous (fun x => UnforcedLeray.Train.Vc ν c s x i) := by
        have hVc_eq : (fun x : ℝ × ℝ => UnforcedLeray.Train.Vc ν c s x i) =
            fun x => a ^ (-3 / 2 : ℝ) *
              UnforcedLeray.Train.datum d ((Real.sqrt a)⁻¹ * x.1, (Real.sqrt a)⁻¹ * x.2) i := by
          funext x
          have hsq_ne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha_pos).ne'
          have hm := EulerErrorSub.movingTrainV_Vc_eq_datum (c := c) hν_pos hs0
            ((Real.sqrt a)⁻¹ * x.1, (Real.sqrt a)⁻¹ * x.2) i
          rw [mul_inv_cancel_left₀ hsq_ne, mul_inv_cancel_left₀ hsq_ne, ← hd_cell] at hm
          have ha32 : a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ) = 1 := by
            rw [← Real.rpow_add ha_pos]; norm_num
          calc UnforcedLeray.Train.Vc ν c s x i
              = (a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) * UnforcedLeray.Train.Vc ν c s x i := by
                rw [ha32, one_mul]
            _ = a ^ (-3 / 2 : ℝ) * UnforcedLeray.Train.datum d
                  ((Real.sqrt a)⁻¹ * x.1, (Real.sqrt a)⁻¹ * x.2) i := by
                rw [mul_assoc, hm]
        rw [hVc_eq]
        exact continuous_const.mul
          (((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
            (UnforcedLeray.Train.datum_contDiff hd0.ne').continuous).comp
            ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)))
      have hle_i : eLpNorm (fun x => tr.v s x i - UnforcedLeray.Train.Vc ν c s x i) 2
          (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal E_tc := by
        refine (?_ : _ ≤ UnforcedLeray.Train.cellL2 c
          (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z)).trans htc_s'
        unfold UnforcedLeray.Train.cellL2
        rw [cyl_cellμ_eq_restrict_aniso]
        exact eLpNorm_mono fun x =>
          PiLp.norm_apply_le (tr.v s x - UnforcedLeray.Train.Vc ν c s x) i
      exact ⟨⟨(hcont_v.sub hcont_Vc).aestronglyMeasurable,
        lt_of_le_of_lt hle_i ENNReal.ofReal_lt_top⟩,
        ENNReal.toReal_le_of_le_ofReal hEtc_nn hle_i⟩
    have hu_c_le : ∀ j : Fin 2,
        (eLpNorm (fun x => u s x j) 2 (volume.restrict (B0579.cell c))).toReal ≤
          ‖P.gaugeFactor ν‖ * (ν * θ) * B_UZ := by
      intro j
      have heq_u := eLpNorm_u_cell_eq_rescaled hc_pos ha_pos (P.gaugeFactor ν) hgf_ne
        (hw.biotSavart s hs0).1 j
      rw [← hd_cell] at heq_u
      have ha1 : a ^ (-1 : ℝ) = ν * θ := by
        rw [ha_eq, Real.rpow_neg_one, inv_inv]
      rw [heq_u, ha1]
      exact mul_le_mul_of_nonneg_left (hUZ_le j) (by positivity)
    obtain ⟨hInt_vdiff, hBd_step1⟩ := integrable_and_norm_defectPairIntegrand_cell
      hEtc_nn (by positivity)
      (fun i => (hv_diff_mem i).1) (hw.biotSavart s hs0).1
      (fun i => (hv_diff_mem i).2) hu_c_le
    -- Step 2: Rescaling `∫_{cell c} defectPairIntegrand (Vc) (u s)` to `B0579.cell d`
    have hv_s_fin : UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤ :=
      lt_of_le_of_lt (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr s hs0) ENNReal.ofReal_lt_top
    have hv_s_mem : ∀ i : Fin 2, MemLp (fun x => tr.v s x i) 2
        (volume.restrict (B0579.cell c)) :=
      fun i => (memLp_train_coord_of_cellL2 hs0 tr hv_s_fin i).1
    have hVc_mem : ∀ i : Fin 2, MemLp (fun x => UnforcedLeray.Train.Vc ν c s x i) 2
        (volume.restrict (B0579.cell c)) := fun i => by
      have heq : (fun x => UnforcedLeray.Train.Vc ν c s x i) =
          (fun x => tr.v s x i) - (fun x => tr.v s x i - UnforcedLeray.Train.Vc ν c s x i) := by
        funext x; simp
      rw [heq]; exact (hv_s_mem i).sub (hv_diff_mem i).1
    have hInt_v : IntegrableOn (defectPairIntegrand (fun z i => tr.v s z i) (u s)) (B0579.cell c) :=
      (integrableOn_and_integral_defectPairIntegrand
        (fun i j => (hv_s_mem i).ofReal.integrable_mul ((hw.biotSavart s hs0).1 j))).1
    have hInt_Vc : IntegrableOn (defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s))
        (B0579.cell c) := by
      have heq : defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) =
          defectPairIntegrand (fun z i => tr.v s z i) (u s) -
            defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i)
              (u s) := by
        funext x; dsimp only [Pi.sub_apply]; rw [← defectPairIntegrand_sub_left]; ring
      rw [heq]; exact hInt_v.sub hInt_vdiff
    have hVc_rescale : ∫ x in B0579.cell c,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) x =
        P.gaugeFactor ν * ((ν ^ 2 * θ ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d, defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z y := by
      rw [← cv_cell (c := c) ha_pos (defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s)),
        ← hd_cell, Complex.real_smul]
      have hpt : ∀ y : ℝ × ℝ,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s)
              (Real.sqrt a * y.1, Real.sqrt a * y.2) =
            P.gaugeFactor ν * ((a ^ (-3 : ℝ) : ℝ) : ℂ) *
              defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z y := by
        intro y
        have hm0 := EulerErrorSub.movingTrainV_Vc_eq_datum (c := c) hν_pos hs0 y 0
        have hm1 := EulerErrorSub.movingTrainV_Vc_eq_datum (c := c) hν_pos hs0 y 1
        rw [← hd_cell] at hm0 hm1
        have ha32 : a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ) = 1 := by
          rw [← Real.rpow_add ha_pos]; norm_num
        have hv0_y : UnforcedLeray.Train.Vc ν c s (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 =
            a ^ (-3 / 2 : ℝ) * UnforcedLeray.Train.datum d y 0 := by
          calc UnforcedLeray.Train.Vc ν c s (Real.sqrt a * y.1, Real.sqrt a * y.2) 0
              = (a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) *
                  UnforcedLeray.Train.Vc ν c s (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 := by
                rw [ha32, one_mul]
            _ = a ^ (-3 / 2 : ℝ) * UnforcedLeray.Train.datum d y 0 := by rw [mul_assoc, hm0]
        have hv1_y : UnforcedLeray.Train.Vc ν c s (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 =
            a ^ (-3 / 2 : ℝ) * UnforcedLeray.Train.datum d y 1 := by
          calc UnforcedLeray.Train.Vc ν c s (Real.sqrt a * y.1, Real.sqrt a * y.2) 1
              = (a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) *
                  UnforcedLeray.Train.Vc ν c s (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 := by
                rw [ha32, one_mul]
            _ = a ^ (-3 / 2 : ℝ) * UnforcedLeray.Train.datum d y 1 := by rw [mul_assoc, hm1]
        have hu_y : ∀ j : Fin 2, u s (Real.sqrt a * y.1, Real.sqrt a * y.2) j =
            P.gaugeFactor ν * ((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * U_Z y j := fun j => by
          dsimp only [U_Z]
          have hc32 : ((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
            rw [← Complex.ofReal_mul, ha32, Complex.ofReal_one]
          calc u s (Real.sqrt a * y.1, Real.sqrt a * y.2) j
              = (P.gaugeFactor ν * (P.gaugeFactor ν)⁻¹) *
                  (((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ)) *
                  u s (Real.sqrt a * y.1, Real.sqrt a * y.2) j := by
                rw [mul_inv_cancel₀ hgf_ne, hc32, one_mul, one_mul]
            _ = P.gaugeFactor ν * ((a ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
                  ((P.gaugeFactor ν)⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
                    u s (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := by ring
        have ha3_eq : a ^ (-3 : ℝ) = a ^ (-3 / 2 : ℝ) * a ^ (-3 / 2 : ℝ) := by
          rw [← Real.rpow_add ha_pos]; norm_num
        unfold defectPairIntegrand
        dsimp only
        rw [hv0_y, hv1_y, hu_y 0, hu_y 1, ha3_eq]
        push_cast; ring
      simp_rw [hpt, integral_const_mul]
      have ha_comb : (a : ℂ) * (P.gaugeFactor ν * ((a ^ (-3 : ℝ) : ℝ) : ℂ)) =
          P.gaugeFactor ν * ((ν ^ 2 * θ ^ 2 : ℝ) : ℂ) := by
        have h1 : a * a ^ (-3 : ℝ) = ν ^ 2 * θ ^ 2 := by
          have ha13 : a * a ^ (-3 : ℝ) = a ^ (-2 : ℝ) := by
            calc a * a ^ (-3 : ℝ)
                = a ^ (1 : ℝ) * a ^ (-3 : ℝ) := by rw [Real.rpow_one]
              _ = a ^ ((1 : ℝ) + -3) := (Real.rpow_add ha_pos 1 (-3)).symm
              _ = a ^ (-2 : ℝ) := by norm_num
          rw [ha13, ha_eq,
            Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv, Real.rpow_two]
          ring
        calc (a : ℂ) * (P.gaugeFactor ν * ((a ^ (-3 : ℝ) : ℝ) : ℂ))
            = P.gaugeFactor ν * (((a * a ^ (-3 : ℝ) : ℝ)) : ℂ) := by push_cast; ring
          _ = P.gaugeFactor ν * ((ν ^ 2 * θ ^ 2 : ℝ) : ℂ) := by rw [h1]
      rw [← mul_assoc, ha_comb]
    -- Step 3: On `B0579.cell d`, telescope `(datum d, U_Z) → (datum d, kerVelCx d V_d) → (v0, kerVelCx d V_d) → 0`
    obtain ⟨hdat_l2, hdat_tail⟩ := hDat hd1
    obtain ⟨hInt_UZ_diff, hBd_UZ_diff⟩ := integrable_and_norm_defectPairIntegrand_cell
      hC_dat2.le hε_comp_pos.le
      (fun i => (hdat_l2 i).1) (hdiff_bs.1)
      (fun i => (hdat_l2 i).2) hvel_diff_le
    obtain ⟨hInt_UVd, _⟩ := integrable_and_norm_defectPairIntegrand_cell
      hC_dat2.le (by positivity)
      (fun i => (hdat_l2 i).1) (hUVd_bs.1)
      (fun i => (hdat_l2 i).2) hUVd_le
    have hInt_UZ : IntegrableOn (defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z)
        (B0579.cell d) := by
      have heq : defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z =
          defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (fun y j => U_Z y j - U_Vd y j) +
            defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Vd := by
        funext y; dsimp only [Pi.add_apply]; rw [← defectPairIntegrand_sub_right]; ring
      rw [heq]; exact hInt_UZ_diff.add hInt_UVd
    have hUVd_eq_ker : ∫ y in B0579.cell d,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Vd y =
        ∫ y in B0579.cell d,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (kerVelCx d V_d) y := by
      refine integral_congr_ae (hUVd_ae.mono fun y hy => ?_)
      unfold defectPairIntegrand
      rw [hy 0, hy 1]
    have hInt_dat_ker : IntegrableOn
        (defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (kerVelCx d V_d)) (B0579.cell d) :=
      hInt_UVd.congr_fun_ae (hUVd_ae.mono fun y hy => by
        unfold defectPairIntegrand; rw [hy 0, hy 1])
    -- Canonical regularity at `θ ∈ Icc r B`
    obtain ⟨hj_θ, hG8_θ⟩ := hRep_G8 θ ⟨hθ_ge_r, hθ_le_B.trans (le_max_left _ _)⟩
    have hfc_θ : ContDiffOn ℝ ∞ (P.canonical θ) (Ioi 0) :=
      hP.canonical.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun z hz => ⟨hθ_pos, hz⟩)
    obtain ⟨hInt_v0_ker, hBd_cylPlan⟩ :=
      hCylPlan hd1 hM₈_r (hP.canonical.memXG θ hθ_pos) hfc_θ (hVae θ hθ_pos) hj_θ hG8_θ
    change IntegrableOn
        (defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d))
        (B0579.cell d) at hInt_v0_ker
    change ‖∫ y in B0579.cell d,
        defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y‖ ≤
        C_cp * M₈_r / d ^ 2 at hBd_cylPlan
    have hGJ_θ := hGJ d hd1 (P.canonical θ) (hP.canonical.memXG θ hθ_pos) hfc_θ
      (V_rep θ) (hVae θ hθ_pos) hj_θ
    have hkerVd_bd : ∀ (k : Fin 2), ∀ y ∈ B0579.cell d, ‖kerVelCx d V_d y k‖ ≤ C_gj * M₈_r :=
      fun k y hy => (hGJ_θ.2.2.2.2 k y hy).2.trans (mul_le_mul_of_nonneg_left hG8_θ hC_gj.le)
    -- Bound `(datum d - v0, kerVelCx d V_d)` on `B0579.cell d`
    have hG16_int : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) :=
      EulerErrorTail.integrable_gauss (by norm_num)
    -- Direct Gaussian integral `∫ exp(-|y|^2/16) = 16 * π ≤ 64`!
    have hI16_le : (∫ y : ℝ × ℝ, Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) ≤ 64 := by
      have h1d : (∫ t : ℝ, Real.exp (-(1 / 16 : ℝ) * t ^ 2)) = Real.sqrt (Real.pi / (1 / 16)) :=
        integral_gaussian (1 / 16)
      have hprod : (∫ y : ℝ × ℝ, Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) =
          (∫ t : ℝ, Real.exp (-(1 / 16 : ℝ) * t ^ 2)) *
            (∫ t : ℝ, Real.exp (-(1 / 16 : ℝ) * t ^ 2)) := by
        have hcongr : (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) =
            fun y => Real.exp (-(1 / 16 : ℝ) * y.1 ^ 2) * Real.exp (-(1 / 16 : ℝ) * y.2 ^ 2) := by
          funext y; rw [← Real.exp_add]; congr 1; ring
        rw [hcongr]
        exact integral_prod_mul (fun t => Real.exp (-(1 / 16 : ℝ) * t ^ 2))
          (fun t => Real.exp (-(1 / 16 : ℝ) * t ^ 2))
      rw [hprod, h1d, ← sq, Real.sq_sqrt (by positivity)]
      have hpi4 := Real.pi_lt_four
      linarith
    have hBd_dat_v0 : ‖∫ y in B0579.cell d,
        (defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (kerVelCx d V_d) y -
          defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y)‖ ≤
        (1024 * C_datT * (C_gj * M₈_r)) / d ^ 2 := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hG16_int.const_mul ((16 * C_datT * (C_gj * M₈_r)) / d ^ 2)).restrict ?_).trans ?_
      · filter_upwards [ae_restrict_mem (measurableSet_Ico.prod MeasurableSet.univ)] with y hy
        rw [defectPairIntegrand_sub_left]
        have hd_pt := norm_defectPairIntegrand_le
          (fun z i => UnforcedLeray.Train.datum d z i - UnforcedLeray.Train.v0 z i)
          (kerVelCx d V_d) y
        calc ‖defectPairIntegrand
                (fun z i => UnforcedLeray.Train.datum d z i - UnforcedLeray.Train.v0 z i)
                (kerVelCx d V_d) y‖
            ≤ 4 * (2 * (C_datT / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16))) *
                (2 * (C_gj * M₈_r)) :=
              hd_pt.trans (mul_le_mul
                (mul_le_mul_of_nonneg_left
                  (add_le_add (hdat_tail y hy 0) (hdat_tail y hy 1) |>.trans_eq (by ring))
                  (by norm_num))
                (add_le_add (hkerVd_bd 0 y hy) (hkerVd_bd 1 y hy) |>.trans_eq (by ring))
                (by positivity) (by positivity))
          _ = ((16 * C_datT * (C_gj * M₈_r)) / d ^ 2) *
                Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
      · calc (∫ y in B0579.cell d,
                ((16 * C_datT * (C_gj * M₈_r)) / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16))
            ≤ ∫ y : ℝ × ℝ,
                ((16 * C_datT * (C_gj * M₈_r)) / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
              setIntegral_le_integral (hG16_int.const_mul _)
                (Eventually.of_forall fun _ => by positivity)
          _ = ((16 * C_datT * (C_gj * M₈_r)) / d ^ 2) *
                (∫ y : ℝ × ℝ, Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
              integral_const_mul _ _
          _ ≤ ((16 * C_datT * (C_gj * M₈_r)) / d ^ 2) * 64 :=
              mul_le_mul_of_nonneg_left hI16_le (by positivity)
          _ = (1024 * C_datT * (C_gj * M₈_r)) / d ^ 2 := by ring
    -- Wait: make sure `hd2_small` uses `1024` or bound `(1024 * C_datT * ...) / d^2`!
    -- Notice `d ^ 2 = θ / ν ^ 3 ≥ r / ν ^ 3`! Let's check below.
    have hd_sq_ge : r / ν ^ 3 ≤ d ^ 2 := by
      dsimp [d]; unfold dOfTheta
      rw [Real.sq_sqrt (by positivity)]
      exact div_le_div_of_nonneg_right hθ_ge_r (by positivity)
    have hinv_d2 : 1 / d ^ 2 ≤ ν ^ 3 / r := by
      have hr_ν3_pos : 0 < r / ν ^ 3 := by positivity
      calc 1 / d ^ 2 ≤ 1 / (r / ν ^ 3) := one_div_le_one_div_of_le hr_ν3_pos hd_sq_ge
        _ = ν ^ 3 / r := one_div_div _ _
    -- Combine on `B0579.cell d`:
    have hcell_d_tel : (∫ y in B0579.cell d, defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z y) =
        (∫ y in B0579.cell d,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (fun z j => U_Z z j - U_Vd z j) y) +
        (∫ y in B0579.cell d,
          (defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (kerVelCx d V_d) y -
            defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y)) +
        (∫ y in B0579.cell d,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y) := by
      have h1 : (∫ y in B0579.cell d, defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z y) -
          (∫ y in B0579.cell d, defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Vd y) =
          ∫ y in B0579.cell d,
            defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (fun z j => U_Z z j - U_Vd z j) y := by
        rw [← integral_sub hInt_UZ hInt_UVd]
        exact integral_congr_ae (Eventually.of_forall fun y =>
          defectPairIntegrand_sub_right _ _ _ y)
      rw [hUVd_eq_ker] at h1
      have h2 := integral_sub hInt_dat_ker hInt_v0_ker
      linear_combination h1 - h2
    -- Wait: `1024 * C_datT` vs `12 * C_datT` in `hlim_d2`: let's fix `hlim_d2` constant to `1024`!
    -- Combine on `B0579.cell c` and multiply by `c⁻¹ * s^(-μ) * s^(-3/2)`
    have hcell_c_tel : (∫ x in B0579.cell c, defectPairIntegrand (fun z i => tr.v s z i) (u s) x) =
        (∫ x in B0579.cell c,
          defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i) (u s) x) +
        (∫ x in B0579.cell c, defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) x) := by
      have h1 := integral_sub hInt_v hInt_Vc
      have h2 : (∫ x in B0579.cell c,
            (defectPairIntegrand (fun z i => tr.v s z i) (u s) x -
              defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) x)) =
          ∫ x in B0579.cell c,
            defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i)
              (u s) x :=
        integral_congr_ae (Eventually.of_forall fun x => defectPairIntegrand_sub_left _ _ _ x)
      linear_combination -h1 + h2
    -- Pre-factor bound `c⁻¹ * s^(-σ) * s^(-3/2) * ‖P.gaugeFactor ν‖ ≤ 4 * B^2 * scaleA P ν μ`
    have hs_lower : (2 * ν ^ 2 * θ)⁻¹ ≤ s := by
      rw [← hs_eq]; unfold clockAge
      have hνθ_half : ν * θ ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left hθ_le_B hν_pos.le).trans hνB_half
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hνθ_half, mul_pos (sq_pos_of_pos hν_pos) hθ_pos]
    have hsinv_le : s⁻¹ ≤ 2 * ν ^ 2 * θ := by
      have h := inv_anti₀ (by positivity : 0 < (2 * ν ^ 2 * θ)⁻¹) hs_lower
      rwa [inv_inv] at h
    have hpow_le : c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) * ‖P.gaugeFactor ν‖ ≤
        4 * B ^ 2 * scaleA P ν μ := by
      have hs_comb : s ^ (-σ) * s ^ (-3 / 2 : ℝ) = (s⁻¹) ^ (σ + 3 / 2) := by
        rw [← Real.rpow_add hs_pos, Real.inv_rpow hs_pos.le, ← Real.rpow_neg hs_pos.le]
        congr 1; ring
      have hθ_pow : θ ^ (σ + 3 / 2) ≤ B ^ (2 : ℝ) := by
        by_cases hθ1 : θ ≤ 1
        · calc θ ^ (σ + 3 / 2) ≤ 1 := Real.rpow_le_one hθ_pos.le hθ1 (by linarith)
            _ ≤ B ^ (2 : ℝ) := Real.one_le_rpow hB1 (by norm_num)
        · push Not at hθ1
          calc θ ^ (σ + 3 / 2) ≤ θ ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hθ1.le (by linarith)
            _ ≤ B ^ (2 : ℝ) := Real.rpow_le_rpow hθ_pos.le hθ_le_B (by norm_num)
      have hs_rpow : (s⁻¹) ^ (σ + 3 / 2) ≤ 4 * ν ^ (3 + 2 * σ) * B ^ 2 := by
        calc (s⁻¹) ^ (σ + 3 / 2)
            ≤ (2 * ν ^ 2 * θ) ^ (σ + 3 / 2) :=
              Real.rpow_le_rpow (inv_nonneg.2 hs0) hsinv_le (by linarith)
          _ = 2 ^ (σ + 3 / 2) * (ν ^ 2) ^ (σ + 3 / 2) * θ ^ (σ + 3 / 2) := by
              rw [Real.mul_rpow (by positivity) hθ_pos.le,
                Real.mul_rpow (by norm_num) (sq_nonneg ν)]
          _ ≤ 4 * (ν ^ 2) ^ (σ + 3 / 2) * B ^ (2 : ℝ) := by
              have h2 : (2 : ℝ) ^ (σ + 3 / 2) ≤ 4 := by
                calc (2 : ℝ) ^ (σ + 3 / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                  _ = 4 := by norm_num
              exact mul_le_mul (mul_le_mul_of_nonneg_right h2 (by positivity)) hθ_pow
                (by positivity) (by positivity)
          _ = 4 * ν ^ (3 + 2 * σ) * B ^ 2 := by
              rw [← Real.rpow_natCast ν 2, ← Real.rpow_mul hν_pos.le, Real.rpow_two]
              congr 2; push_cast; ring
      rw [mul_assoc c⁻¹, hs_comb]
      calc c⁻¹ * (s⁻¹) ^ (σ + 3 / 2) * ‖P.gaugeFactor ν‖
          ≤ c⁻¹ * (4 * ν ^ (3 + 2 * σ) * B ^ 2) * ‖P.gaugeFactor ν‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs_rpow (inv_nonneg.2 hc_pos.le)) (norm_nonneg _)
        _ = 4 * B ^ 2 * scaleA P ν μ := by
            unfold scaleA; dsimp [c]; ring
    -- Norm of `F_def s`
    have hnorm_F : ‖F_def s‖ =
        c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) *
          ‖∫ x in B0579.cell c, defectPairIntegrand (fun z i => tr.v s z i) (u s) x‖ := by
      dsimp only [F_def]
      rw [pairs_defect_eq_defectPairIntegrand hν_pos tr μ hs0 hv_s_fin (hw.biotSavart s hs0),
        norm_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hc_pos.le),
        Complex.norm_cpow_eq_rpow_re_of_pos hs_pos (-μ), Complex.neg_re,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs0 _)]
      ring
    -- Bound `‖∫_{cell c} defectPairIntegrand (fun z i => tr.v s z i) (u s)‖`
    have hstep1_le : ‖∫ x in B0579.cell c,
          defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i)
            (u s) x‖ ≤
        ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * (δ_target / 4) := by
      have hexp_mono : Real.exp (-(b_tc * (θ / ν ^ 3))) ≤ Real.exp (-(b_tc * r / ν ^ 3)) := by
        apply Real.exp_le_exp.2
        have : b_tc * r / ν ^ 3 ≤ b_tc * (θ / ν ^ 3) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hθ_ge_r (by positivity)) hb_tc.le
        linarith
      calc ‖∫ x in B0579.cell c,
              defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i)
                (u s) x‖
          ≤ 12 * E_tc * (‖P.gaugeFactor ν‖ * (ν * θ) * B_UZ) := hBd_step1
        _ = ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) *
              ((12 * C_tc * B_UZ * θ) * Real.exp (-(b_tc * (θ / ν ^ 3)))) := by
            dsimp [E_tc]; ring
        _ ≤ ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) *
              ((12 * C_tc * B_UZ * B) * Real.exp (-(b_tc * r / ν ^ 3))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left hθ_le_B (by positivity))
              hexp_mono (Real.exp_pos _).le (by positivity)
        _ ≤ ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * (δ_target / 4) :=
            mul_le_mul_of_nonneg_left htc_small.le (by positivity)
    have hstep234_le : ‖∫ y in B0579.cell d,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) U_Z y‖ ≤
        3 * (δ_target / 4) := by
      rw [hcell_d_tel]
      have t12 := norm_add_le
        ((∫ y in B0579.cell d,
            defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (fun z j => U_Z z j - U_Vd z j) y) +
          ∫ y in B0579.cell d,
            (defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (kerVelCx d V_d) y -
              defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y))
        (∫ y in B0579.cell d, defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y)
      have t1 := norm_add_le
        (∫ y in B0579.cell d,
          defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (fun z j => U_Z z j - U_Vd z j) y)
        (∫ y in B0579.cell d,
          (defectPairIntegrand (fun z i => UnforcedLeray.Train.datum d z i) (kerVelCx d V_d) y -
            defectPairIntegrand (fun z i => UnforcedLeray.Train.v0 z i) (kerVelCx d V_d) y))
      have hb_comp : 12 * C_dat2 * ε_comp ≤ δ_target / 4 := by
        have hle : ε_comp ≤ δ_target / (48 * C_dat2 + 1) := min_le_right _ _
        calc 12 * C_dat2 * ε_comp
            ≤ 12 * C_dat2 * (δ_target / (48 * C_dat2 + 1)) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ ≤ δ_target / 4 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith only [hδ_pos, hC_dat2]
      have hb_tail_sum : (1024 * C_datT * (C_gj * M₈_r)) / d ^ 2 + C_cp * M₈_r / d ^ 2 ≤
          2 * (δ_target / 4) := by
        calc (1024 * C_datT * (C_gj * M₈_r)) / d ^ 2 + C_cp * M₈_r / d ^ 2
            = (1024 * C_datT * (C_gj * M₈_r) + C_cp * M₈_r) * (1 / d ^ 2) := by ring
          _ ≤ (1024 * C_datT * (C_gj * M₈_r) + C_cp * M₈_r) * (ν ^ 3 / r) :=
              mul_le_mul_of_nonneg_left hinv_d2 (by positivity)
          _ ≤ 2 * (δ_target / 4) := hd2_small.le
      linarith only [t12, t1, hBd_UZ_diff, hBd_dat_v0, hBd_cylPlan, hb_comp, hb_tail_sum]
    have hVc_le :
        ‖∫ x in B0579.cell c, defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) x‖ ≤
          ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * (3 * (δ_target / 4)) := by
      rw [hVc_rescale, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ ν ^ 2 * θ ^ 2)]
      exact mul_le_mul_of_nonneg_left hstep234_le (by positivity)
    have hcell_c_le : ‖∫ x in B0579.cell c, defectPairIntegrand (fun z i => tr.v s z i) (u s) x‖ ≤
        ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * δ_target := by
      rw [hcell_c_tel]
      calc ‖(∫ x in B0579.cell c,
              defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i)
                (u s) x) +
            ∫ x in B0579.cell c, defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) x‖
          ≤ ‖∫ x in B0579.cell c,
              defectPairIntegrand (fun z i => tr.v s z i - UnforcedLeray.Train.Vc ν c s z i)
                (u s) x‖ +
            ‖∫ x in B0579.cell c,
              defectPairIntegrand (fun z i => UnforcedLeray.Train.Vc ν c s z i) (u s) x‖ := norm_add_le _ _
        _ ≤ ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * (δ_target / 4) +
            ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * (3 * (δ_target / 4)) :=
            add_le_add hstep1_le hVc_le
        _ = ‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * δ_target := by ring
    rw [hnorm_F]
    calc c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) *
            ‖∫ x in B0579.cell c, defectPairIntegrand (fun z i => tr.v s z i) (u s) x‖
        ≤ c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) *
            (‖P.gaugeFactor ν‖ * (ν ^ 2 * θ ^ 2) * δ_target) :=
          mul_le_mul_of_nonneg_left hcell_c_le (by positivity)
      _ = (c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) * ‖P.gaugeFactor ν‖) *
            (δ_target * (ν ^ 2 * θ ^ 2)) := by ring
      _ ≤ (4 * B ^ 2 * scaleA P ν μ) * (δ_target * (ν ^ 2 * θ ^ 2)) :=
          mul_le_mul_of_nonneg_right hpow_le (by positivity)
      _ = (4 * B ^ 2 * scaleA P ν μ * δ_target) * (ν ^ 2 * θ ^ 2) := by ring
  -- Integrate `‖F_def s‖` over `Ioc s_B s_r`
  have hdom_int : IntegrableOn
      (fun s => (4 * B ^ 2 * scaleA P ν μ * δ_target) * (ν ^ 2 * (clockTheta ν s) ^ 2))
      (Ioc s_B s_r) := hint_θsq.const_mul _
  calc ‖∫ s in Ioc s_B s_r, F_def s‖
      ≤ ∫ s in Ioc s_B s_r, ‖F_def s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc s_B s_r,
          (4 * B ^ 2 * scaleA P ν μ * δ_target) * (ν ^ 2 * (clockTheta ν s) ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hdom_int
          (ae_restrict_mem measurableSet_Ioc |>.mono hslice_bd)
    _ = (4 * B ^ 2 * scaleA P ν μ * δ_target) * (B - r) := by
        rw [integral_const_mul, hval_θsq]
    _ ≤ (4 * B ^ 2 * scaleA P ν μ * δ_target) * B :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (4 * B ^ 3 * δ_target) * scaleA P ν μ := by ring
    _ ≤ ε * scaleA P ν μ := by
        refine mul_le_mul_of_nonneg_right ?_ hscaleA_nn
        dsimp [δ_target]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith only [hε, pow_pos hB_pos 3]



end UnforcedLeray.Short.IIIa.AnisoSynthAux

end
