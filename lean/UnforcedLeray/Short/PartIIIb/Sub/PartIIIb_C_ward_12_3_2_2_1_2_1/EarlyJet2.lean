import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets.Calc
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Sub.PartI_T21.TransverseTail
import UnforcedLeray.Short.PartI.Sub.PartI_T21_2.InteriorStripBounds

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1/1`: `ResProfileEarlyJet2` (early-age chart jet bound)

Source of record:
`the November 2 reference manuscript`,
lines 1255-1258, 1294-1304, 2542-2551: at bounded ages `0 < s ≤ 1`, the five polynomial residual
coefficients `A₁, A₂, B₁, B₂, B₃` of `resChartProfile p` belong to `EarlyBdd 2`
(`FarDecaySub.earlyBdd_coeffA1/A2/B1/B2/B3` in `PartIII-b_C_ward_12_3_2_2_1_1.lean`), so their
mixed profile derivatives `∂_s^ℓ ∂_η^a ∂_q^b` up to order `2` have rapid transverse decay in `η`,
giving `(1 + |η|)⁴ ‖D^l (resChartProfile p)(m)‖ ≤ C` for `0 < m.1 ≤ 1` and `l ≤ 2`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.IIb (trainStream trainPressure rawResidualC
  isExactPlanarTrain_params_rpow)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace EarlyJet2Sub

open FarDecaySub

/-- `chartSwap (s, (ξ, η)) = (ξ, (η, s))` as a linear isometry equivalence. -/
def chartSwapLIE : (ℝ × (ℝ × ℝ)) ≃ₗᵢ[ℝ] ProfilePoint where
  toFun m := (m.2.1, (m.2.2, m.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl
  map_add' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => rfl
  map_smul' := fun _ ⟨_, _, _⟩ => rfl
  norm_map' := fun ⟨s, ξ, η⟩ => by
    show max ‖ξ‖ (max ‖η‖ ‖s‖) = max ‖s‖ (max ‖ξ‖ ‖η‖)
    rw [max_comm ‖s‖, max_assoc]

@[simp]
theorem chartSwapLIE_apply (m : ℝ × (ℝ × ℝ)) : chartSwapLIE m = chartSwap m := rfl

theorem norm_iteratedFDeriv_comp_chartSwap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ProfilePoint → E) (m : ℝ × (ℝ × ℝ)) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun w => f (chartSwap w)) m‖ =
      ‖iteratedFDeriv ℝ l f (chartSwap m)‖ :=
  chartSwapLIE.norm_iteratedFDeriv_comp_right f m l

theorem LL_zero_eq : AgeDeriv.LL 0 = eqDir := rfl
theorem LL_one_eq : AgeDeriv.LL 1 = eηDir := rfl
theorem LL_two_eq : AgeDeriv.LL 2 = esDir := rfl

/-- Every coordinate word of length `1` on `ProfilePoint` is one of `partialQ`, `partialEta`,
`partialAge`. -/
theorem abs_dW_len1_le {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain)
    {x : ProfilePoint} (hx : x ∈ ageDomain) {W B : ℝ}
    (hpart : ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      W * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x| ≤ B)
    (r : Fin 1 → Fin 3) :
    W * |iteratedFDeriv ℝ 1 f x (fun k => AgeDeriv.LL (r k))| ≤ B := by
  rw [← AgeDeriv.dW_ofFn_eq FarDecaySub.isOpen_ageDomain hf 1 (fun k => AgeDeriv.LL (r k)) x hx]
  have hof : List.ofFn (fun k : Fin 1 => AgeDeriv.LL (r k)) = [AgeDeriv.LL (r 0)] :=
    List.ofFn_succ' _
  rw [hof]
  generalize r 0 = i0
  fin_cases i0
  · exact hpart 0 (by omega) 0 (by omega) 1 (by omega)
  · exact hpart 0 (by omega) 1 (by omega) 0 (by omega)
  · exact hpart 1 (by omega) 0 (by omega) 0 (by omega)

/-- Every coordinate word of length `2` on `ProfilePoint` reduces by `AgeDeriv.dW_swap` to
`partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))` with `ℓ + a + b = 2`. -/
theorem abs_dW_len2_le {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain)
    {x : ProfilePoint} (hx : x ∈ ageDomain) {W B : ℝ}
    (hpart : ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      W * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x| ≤ B)
    (r : Fin 2 → Fin 3) :
    W * |iteratedFDeriv ℝ 2 f x (fun k => AgeDeriv.LL (r k))| ≤ B := by
  rw [← AgeDeriv.dW_ofFn_eq FarDecaySub.isOpen_ageDomain hf 2 (fun k => AgeDeriv.LL (r k)) x hx]
  have hof : List.ofFn (fun k : Fin 2 => AgeDeriv.LL (r k)) =
      [AgeDeriv.LL (r 0), AgeDeriv.LL (r 1)] := by
    simp [List.ofFn_succ]
  rw [hof]
  generalize r 0 = i0
  generalize r 1 = i1
  fin_cases i0 <;> fin_cases i1
  · exact hpart 0 (by omega) 0 (by omega) 2 (by omega)
  · rw [AgeDeriv.dW_swap FarDecaySub.isOpen_ageDomain hf [] _ _ hx]
    exact hpart 0 (by omega) 1 (by omega) 1 (by omega)
  · rw [AgeDeriv.dW_swap FarDecaySub.isOpen_ageDomain hf [] _ _ hx]
    exact hpart 1 (by omega) 0 (by omega) 1 (by omega)
  · exact hpart 0 (by omega) 1 (by omega) 1 (by omega)
  · exact hpart 0 (by omega) 2 (by omega) 0 (by omega)
  · rw [AgeDeriv.dW_swap FarDecaySub.isOpen_ageDomain hf [] _ _ hx]
    exact hpart 1 (by omega) 1 (by omega) 0 (by omega)
  · exact hpart 1 (by omega) 0 (by omega) 1 (by omega)
  · exact hpart 1 (by omega) 1 (by omega) 0 (by omega)
  · exact hpart 2 (by omega) 0 (by omega) 0 (by omega)

/-- Weighted order-`≤ 2` Fréchet derivative bound on `ProfilePoint` from bounds on the mixed
directional partials `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))` for `ℓ, a, b ≤ 2`. -/
theorem wtd_norm_iteratedFDeriv_le_of_partials {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain) {x : ProfilePoint} (hx : x ∈ ageDomain)
    {W B : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hpart : ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
      W * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x| ≤ B)
    {l : ℕ} (hl : l ≤ 2) :
    W * ‖iteratedFDeriv ℝ l f x‖ ≤ 9 * B := by
  interval_cases l
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have h0 := hpart 0 (by omega) 0 (by omega) 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at h0
    linarith
  · have hsum := mul_le_mul_of_nonneg_left (AgeDeriv.norm_iteratedFDeriv_le_sum3 f 1 x) hW
    rw [Finset.mul_sum] at hsum
    have hle : ∑ r : Fin 1 → Fin 3, W * |iteratedFDeriv ℝ 1 f x (fun k => AgeDeriv.LL (r k))| ≤
        ∑ _r : Fin 1 → Fin 3, B :=
      Finset.sum_le_sum fun r _ => abs_dW_len1_le hf hx hpart r
    have hcard : (∑ _r : Fin 1 → Fin 3, B) = 3 * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      ring
    linarith
  · have hsum := mul_le_mul_of_nonneg_left (AgeDeriv.norm_iteratedFDeriv_le_sum3 f 2 x) hW
    rw [Finset.mul_sum] at hsum
    have hle : ∑ r : Fin 2 → Fin 3, W * |iteratedFDeriv ℝ 2 f x (fun k => AgeDeriv.LL (r k))| ≤
        ∑ _r : Fin 2 → Fin 3, B :=
      Finset.sum_le_sum fun r _ => abs_dW_len2_le hf hx hpart r
    have hcard : (∑ _r : Fin 2 → Fin 3, B) = 9 * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      ring
    linarith

/-- For any `t : ℝ`, `(1 + |t|)⁴ ≤ 4 (1 + t²)²`. -/
theorem pow_four_one_add_abs_le (t : ℝ) :
    (1 + |t|) ^ 4 ≤ 4 * (1 + t ^ 2) ^ 2 := by
  have h1 := sq_one_add_abs_le_two_mul_one_add_sq t
  have h0 : 0 ≤ (1 + |t|) ^ 2 := by positivity
  have hsq := pow_le_pow_left₀ h0 h1 2
  linarith [show ((1 + |t|) ^ 2) ^ 2 = (1 + |t|) ^ 4 by ring,
    show (2 * (1 + t ^ 2)) ^ 2 = 4 * (1 + t ^ 2) ^ 2 by ring]

/-- From `EarlyBdd 2 X`, for every `ℓ, a, b : ℕ` there is `ν₀ > 0` such that at fixed parameters
`p`, `(1 + x.2.1 ^ 2) ^ 2 * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] (X p.ν ψ pr)))) x|`
is bounded on `0 < x.2.2 ≤ 1`. -/
theorem earlyBdd_two_fixed_jet {X : ProfFam} (hX : EarlyBdd 2 X) (ℓ a b : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
        (1 + x.2.1 ^ 2) ^ 2 *
          |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (X p.ν (trainStream p) (trainPressure p))))) x| ≤ B := by
  obtain ⟨ν₀, C, d, hν₀, H⟩ := hX.2 2 a b ℓ
  refine ⟨ν₀, hν₀, fun p htr hν hc => ?_⟩
  have hex : IsExactPlanarTrain p.ν (p.ν ^ (-(2 : ℝ))) (trainStream p) (trainPressure p) :=
    isExactPlanarTrain_params_rpow p htr hc
  set B : ℝ := max (polyConst C d p.ν (p.ν ^ (-(2 : ℝ)))) 0
  refine ⟨B, le_max_right _ _, fun x hx0 hx1 => ?_⟩
  exact (H p.ν ⟨p.ν_pos, hν⟩ (trainStream p) (trainPressure p) hex x hx0 hx1).trans
    (le_max_left _ _)

/-- From `EarlyBdd 2 X`, there is `ν₀ > 0` such that for `p.ν < ν₀`, `X p.ν ψ pr` is smooth on
`ageDomain` and satisfies `(1 + x.2.1 ^ 2) ^ 2 * ‖iteratedFDeriv ℝ l (X p.ν ψ pr) x‖ ≤ C` on
`0 < x.2.2 ≤ 1` for all `l ≤ 2`. -/
theorem earlyBdd_two_iteratedFDeriv_le {X : ProfFam} (hX : EarlyBdd 2 X) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ →
        ContDiffOn ℝ ∞ (X p.ν (trainStream p) (trainPressure p)) ageDomain ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → ∀ l ≤ 2,
          (1 + x.2.1 ^ 2) ^ 2 *
            ‖iteratedFDeriv ℝ l (X p.ν (trainStream p) (trainPressure p)) x‖ ≤ C := by
  choose ν_f hν_f H_f using fun q : Fin 3 × Fin 3 × Fin 3 =>
    earlyBdd_two_fixed_jet hX q.1.val q.2.1.val q.2.2.val
  have hpos : ∀ q : Fin 3 × Fin 3 × Fin 3, 0 < ν_f q := hν_f
  obtain ⟨ν₀, hν₀, hle⟩ : ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ q : Fin 3 × Fin 3 × Fin 3, ν₀ ≤ ν_f q := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty ν_f, ?_, fun q =>
      Finset.inf'_le ν_f (Finset.mem_univ q)⟩
    rw [Finset.lt_inf'_iff]
    intro q _
    exact hν_f q
  refine ⟨ν₀, hν₀, fun p htr hν hc => ?_⟩
  have hex : IsExactPlanarTrain p.ν (p.ν ^ (-(2 : ℝ))) (trainStream p) (trainPressure p) :=
    isExactPlanarTrain_params_rpow p htr hc
  have hsm : ContDiffOn ℝ ∞ (X p.ν (trainStream p) (trainPressure p)) ageDomain :=
    hX.1 p.ν p.ν_pos (trainStream p) (trainPressure p) hex
  refine ⟨hsm, ?_⟩
  choose B_f hB0 hB using fun q : Fin 3 × Fin 3 × Fin 3 =>
    H_f q p htr (lt_of_lt_of_le hν (hle q)) hc
  set Bsum : ℝ := ∑ q : Fin 3 × Fin 3 × Fin 3, B_f q
  have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun q _ => hB0 q
  refine ⟨9 * Bsum, mul_nonneg (by norm_num) hBsum0, fun x hx0 hx1 l hl => ?_⟩
  have hW : 0 ≤ (1 + x.2.1 ^ 2) ^ 2 := by positivity
  refine wtd_norm_iteratedFDeriv_le_of_partials hsm hx0 hW hBsum0 ?_ hl
  intro ℓ hℓ a ha b hb
  let q : Fin 3 × Fin 3 × Fin 3 := (⟨ℓ, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
  exact (hB q x hx0 hx1).trans
    (Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_univ q))

/-- The polynomial meridional profile on `ProfilePoint` matching `resChartProfile p` after
`chartSwap`. -/
def resPolyMerid (R ν : ℝ) (ψ pr : ProfilePoint → ℝ) (x : ProfilePoint) : Axi.Merid :=
  (ringEps R * coeffA₁ ν ψ pr x + ringEps R ^ 2 * coeffB₁ ν ψ x) •
      (!₂[(1 : ℝ), 0] : Axi.Merid) +
    (ringEps R * coeffA₂ ν ψ x + ringEps R ^ 2 * coeffB₂ ν ψ x +
        ringEps R ^ 3 * coeffB₃ ν ψ x) •
      (!₂[(0 : ℝ), 1] : Axi.Merid)

theorem resChartProfile_eq_resPolyMerid (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    {m : ℝ × (ℝ × ℝ)} (hm : 0 < m.1) :
    resChartProfile p m =
      resPolyMerid p.R p.ν (trainStream p) (trainPressure p) (chartSwap m) := by
  obtain ⟨h0, h1⟩ := resChartProfile_eq_poly p htr hm
  ext i
  fin_cases i
  · simp [resPolyMerid, h0]
  · simp [resPolyMerid, h1]

theorem norm_merid_e0 : ‖(!₂[(1 : ℝ), 0] : Axi.Merid)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

theorem norm_merid_e1 : ‖(!₂[(0 : ℝ), 1] : Axi.Merid)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

theorem norm_iteratedFDeriv_smul_merid_le {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ ∞ f x) (v : Axi.Merid) (hv : ‖v‖ ≤ 1) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun y => f y • v) x‖ ≤ ‖iteratedFDeriv ℝ l f x‖ := by
  let L : ℝ →L[ℝ] Axi.Merid := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hfun : (fun y => f y • v) = L ∘ f := rfl
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
    simp only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, one_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) hv
  rw [hfun]
  exact (L.norm_iteratedFDeriv_comp_left hf (by exact_mod_cast le_top)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hL)

theorem norm_iteratedFDeriv_const_mul_le {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ ∞ f x) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun y => c * f y) x‖ ≤ ‖iteratedFDeriv ℝ l f x‖ := by
  have h1 : ContDiffAt ℝ l f x := hf.of_le (by exact_mod_cast le_top)
  have heq : (fun y => c * f y) = fun y => c • f y := rfl
  rw [heq, iteratedFDeriv_const_smul_apply' h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  exact mul_le_of_le_one_left (norm_nonneg _) hc1

/-- Pointwise bound on `‖iteratedFDeriv ℝ l (resPolyMerid R ν ψ pr) x‖` from the five coefficient
jet norms when `2 ≤ R`. -/
theorem norm_iteratedFDeriv_resPolyMerid_le {R ν : ℝ} (hR : 2 ≤ R)
    {ψ pr : ProfilePoint → ℝ} {x : ProfilePoint} (hx : x ∈ ageDomain)
    (hA1 : ContDiffOn ℝ ∞ (coeffA₁ ν ψ pr) ageDomain)
    (hB1 : ContDiffOn ℝ ∞ (coeffB₁ ν ψ) ageDomain)
    (hA2 : ContDiffOn ℝ ∞ (coeffA₂ ν ψ) ageDomain)
    (hB2 : ContDiffOn ℝ ∞ (coeffB₂ ν ψ) ageDomain)
    (hB3 : ContDiffOn ℝ ∞ (coeffB₃ ν ψ) ageDomain) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (resPolyMerid R ν ψ pr) x‖ ≤
      ‖iteratedFDeriv ℝ l (coeffA₁ ν ψ pr) x‖ +
        ‖iteratedFDeriv ℝ l (coeffB₁ ν ψ) x‖ +
        ‖iteratedFDeriv ℝ l (coeffA₂ ν ψ) x‖ +
        ‖iteratedFDeriv ℝ l (coeffB₂ ν ψ) x‖ +
        ‖iteratedFDeriv ℝ l (coeffB₃ ν ψ) x‖ := by
  obtain ⟨hε0, hε1⟩ := ringEps_nonneg_and_le_one hR
  have hε20 : 0 ≤ ringEps R ^ 2 := sq_nonneg _
  have hε21 : ringEps R ^ 2 ≤ 1 := by nlinarith
  have hε30 : 0 ≤ ringEps R ^ 3 := pow_nonneg hε0 3
  have hε31 : ringEps R ^ 3 ≤ 1 := by
    calc ringEps R ^ 3 = ringEps R ^ 2 * ringEps R := by ring
      _ ≤ 1 * 1 := mul_le_mul hε21 hε1 hε0 zero_le_one
      _ = 1 := mul_one 1
  have hnhds : ageDomain ∈ 𝓝 x := FarDecaySub.isOpen_ageDomain.mem_nhds hx
  have cA1 : ContDiffAt ℝ ∞ (coeffA₁ ν ψ pr) x := hA1.contDiffAt hnhds
  have cB1 : ContDiffAt ℝ ∞ (coeffB₁ ν ψ) x := hB1.contDiffAt hnhds
  have cA2 : ContDiffAt ℝ ∞ (coeffA₂ ν ψ) x := hA2.contDiffAt hnhds
  have cB2 : ContDiffAt ℝ ∞ (coeffB₂ ν ψ) x := hB2.contDiffAt hnhds
  have cB3 : ContDiffAt ℝ ∞ (coeffB₃ ν ψ) x := hB3.contDiffAt hnhds
  let f1 : ProfilePoint → ℝ := fun y => ringEps R * coeffA₁ ν ψ pr y
  let f2 : ProfilePoint → ℝ := fun y => ringEps R ^ 2 * coeffB₁ ν ψ y
  let g1 : ProfilePoint → ℝ := fun y => ringEps R * coeffA₂ ν ψ y
  let g2 : ProfilePoint → ℝ := fun y => ringEps R ^ 2 * coeffB₂ ν ψ y
  let g3 : ProfilePoint → ℝ := fun y => ringEps R ^ 3 * coeffB₃ ν ψ y
  have cf1 : ContDiffAt ℝ ∞ f1 x := contDiffAt_const.mul cA1
  have cf2 : ContDiffAt ℝ ∞ f2 x := contDiffAt_const.mul cB1
  have cg1 : ContDiffAt ℝ ∞ g1 x := contDiffAt_const.mul cA2
  have cg2 : ContDiffAt ℝ ∞ g2 x := contDiffAt_const.mul cB2
  have cg3 : ContDiffAt ℝ ∞ g3 x := contDiffAt_const.mul cB3
  let F0 : ProfilePoint → Axi.Merid := fun y => (f1 y + f2 y) • (!₂[(1 : ℝ), 0] : Axi.Merid)
  let F1 : ProfilePoint → Axi.Merid :=
    fun y => (g1 y + g2 y + g3 y) • (!₂[(0 : ℝ), 1] : Axi.Merid)
  have cF0 : ContDiffAt ℝ l F0 x :=
    ((cf1.add cf2).smul contDiffAt_const).of_le (by exact_mod_cast le_top)
  have cF1 : ContDiffAt ℝ l F1 x :=
    (((cg1.add cg2).add cg3).smul contDiffAt_const).of_le (by exact_mod_cast le_top)
  have hsumF : iteratedFDeriv ℝ l (resPolyMerid R ν ψ pr) x =
      iteratedFDeriv ℝ l F0 x + iteratedFDeriv ℝ l F1 x :=
    iteratedFDeriv_add_apply cF0 cF1
  have hF0 : ‖iteratedFDeriv ℝ l F0 x‖ ≤
      ‖iteratedFDeriv ℝ l (coeffA₁ ν ψ pr) x‖ + ‖iteratedFDeriv ℝ l (coeffB₁ ν ψ) x‖ := by
    have hsm : ‖iteratedFDeriv ℝ l F0 x‖ ≤ ‖iteratedFDeriv ℝ l (fun y => f1 y + f2 y) x‖ :=
      norm_iteratedFDeriv_smul_merid_le (cf1.add cf2) _ norm_merid_e0.le l
    have hadd : iteratedFDeriv ℝ l (fun y => f1 y + f2 y) x =
        iteratedFDeriv ℝ l f1 x + iteratedFDeriv ℝ l f2 x :=
      iteratedFDeriv_add_apply (cf1.of_le (by exact_mod_cast le_top))
        (cf2.of_le (by exact_mod_cast le_top))
    calc ‖iteratedFDeriv ℝ l F0 x‖
        ≤ ‖iteratedFDeriv ℝ l f1 x + iteratedFDeriv ℝ l f2 x‖ := by rw [← hadd]; exact hsm
      _ ≤ ‖iteratedFDeriv ℝ l f1 x‖ + ‖iteratedFDeriv ℝ l f2 x‖ := norm_add_le _ _
      _ ≤ ‖iteratedFDeriv ℝ l (coeffA₁ ν ψ pr) x‖ + ‖iteratedFDeriv ℝ l (coeffB₁ ν ψ) x‖ :=
          add_le_add (norm_iteratedFDeriv_const_mul_le cA1 hε0 hε1 l)
            (norm_iteratedFDeriv_const_mul_le cB1 hε20 hε21 l)
  have hF1 : ‖iteratedFDeriv ℝ l F1 x‖ ≤
      ‖iteratedFDeriv ℝ l (coeffA₂ ν ψ) x‖ + ‖iteratedFDeriv ℝ l (coeffB₂ ν ψ) x‖ +
        ‖iteratedFDeriv ℝ l (coeffB₃ ν ψ) x‖ := by
    have hsm : ‖iteratedFDeriv ℝ l F1 x‖ ≤
        ‖iteratedFDeriv ℝ l (fun y => g1 y + g2 y + g3 y) x‖ :=
      norm_iteratedFDeriv_smul_merid_le ((cg1.add cg2).add cg3) _ norm_merid_e1.le l
    have hadd1 : iteratedFDeriv ℝ l (fun y => g1 y + g2 y + g3 y) x =
        iteratedFDeriv ℝ l (fun y => g1 y + g2 y) x + iteratedFDeriv ℝ l g3 x :=
      iteratedFDeriv_add_apply ((cg1.add cg2).of_le (by exact_mod_cast le_top))
        (cg3.of_le (by exact_mod_cast le_top))
    have hadd2 : iteratedFDeriv ℝ l (fun y => g1 y + g2 y) x =
        iteratedFDeriv ℝ l g1 x + iteratedFDeriv ℝ l g2 x :=
      iteratedFDeriv_add_apply (cg1.of_le (by exact_mod_cast le_top))
        (cg2.of_le (by exact_mod_cast le_top))
    calc ‖iteratedFDeriv ℝ l F1 x‖
        ≤ ‖iteratedFDeriv ℝ l g1 x + iteratedFDeriv ℝ l g2 x + iteratedFDeriv ℝ l g3 x‖ := by
          rw [← hadd2, ← hadd1]; exact hsm
      _ ≤ ‖iteratedFDeriv ℝ l g1 x + iteratedFDeriv ℝ l g2 x‖ + ‖iteratedFDeriv ℝ l g3 x‖ :=
          norm_add_le _ _
      _ ≤ ‖iteratedFDeriv ℝ l g1 x‖ + ‖iteratedFDeriv ℝ l g2 x‖ + ‖iteratedFDeriv ℝ l g3 x‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖iteratedFDeriv ℝ l (coeffA₂ ν ψ) x‖ + ‖iteratedFDeriv ℝ l (coeffB₂ ν ψ) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₃ ν ψ) x‖ :=
          add_le_add
            (add_le_add (norm_iteratedFDeriv_const_mul_le cA2 hε0 hε1 l)
              (norm_iteratedFDeriv_const_mul_le cB2 hε20 hε21 l))
            (norm_iteratedFDeriv_const_mul_le cB3 hε30 hε31 l)
  calc ‖iteratedFDeriv ℝ l (resPolyMerid R ν ψ pr) x‖
      ≤ ‖iteratedFDeriv ℝ l F0 x‖ + ‖iteratedFDeriv ℝ l F1 x‖ := by
        rw [hsumF]; exact norm_add_le _ _
    _ ≤ _ := by linarith

end EarlyJet2Sub

open FarDecaySub EarlyJet2Sub

/-- **`ResProfileEarlyJet2` from `EarlyStreamProfile` and `EarlyPressureProfile`**
(`the November 2 reference manuscript`, lines 1294-1304, 2542-2551). -/
theorem resProfileEarlyJet2_of (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile) :
    ResProfileEarlyJet2 := by
  have hρ : (1 : ℝ) / 2 < 2 := by norm_num
  obtain ⟨ν1, hν1, H1⟩ := earlyBdd_two_iteratedFDeriv_le (earlyBdd_coeffA1 hψ hp hρ)
  obtain ⟨ν2, hν2, H2⟩ := earlyBdd_two_iteratedFDeriv_le (earlyBdd_coeffB1 hψ hρ)
  obtain ⟨ν3, hν3, H3⟩ := earlyBdd_two_iteratedFDeriv_le (earlyBdd_coeffA2 hψ hρ)
  obtain ⟨ν4, hν4, H4⟩ := earlyBdd_two_iteratedFDeriv_le (earlyBdd_coeffB2 hψ hρ)
  obtain ⟨ν5, hν5, H5⟩ := earlyBdd_two_iteratedFDeriv_le (earlyBdd_coeffB3 hψ hρ)
  refine ⟨min (min (min (min ν1 ν2) ν3) ν4) ν5,
    lt_min (lt_min (lt_min (lt_min hν1 hν2) hν3) hν4) hν5,
    fun p htr hν hc hR _ => ?_⟩
  obtain ⟨hsm1, C1, _, hC1⟩ := H1 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm2, C2, _, hC2⟩ := H2 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm3, C3, _, hC3⟩ := H3 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm4, C4, _, hC4⟩ := H4 p htr (lt_of_lt_of_le hν (by simp)) hc
  obtain ⟨hsm5, C5, _, hC5⟩ := H5 p htr (lt_of_lt_of_le hν (by simp)) hc
  refine ⟨4 * (C1 + C2 + C3 + C4 + C5), fun m hm0 hm1 l hl => ?_⟩
  have hU : IsOpen {w : ℝ × (ℝ × ℝ) | 0 < w.1} := isOpen_lt continuous_const continuous_fst
  have hev : resChartProfile p =ᶠ[𝓝 m]
      fun w => resPolyMerid p.R p.ν (trainStream p) (trainPressure p) (chartSwap w) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hm0)
      (fun w hw => resChartProfile_eq_resPolyMerid p htr hw)
  have hnorm_eq : ‖iteratedFDeriv ℝ l (resChartProfile p) m‖ =
      ‖iteratedFDeriv ℝ l
        (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) (chartSwap m)‖ := by
    rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds,
      norm_iteratedFDeriv_comp_chartSwap
        (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) m l]
  rw [hnorm_eq]
  set x : ProfilePoint := chartSwap m
  have hx0 : 0 < x.2.2 := hm0
  have hx1 : x.2.2 ≤ 1 := hm1
  have hpoly := norm_iteratedFDeriv_resPolyMerid_le hR hx0 hsm1 hsm2 hsm3 hsm4 hsm5 l
  have hW : (1 + |m.2.2|) ^ 4 ≤ 4 * (1 + x.2.1 ^ 2) ^ 2 :=
    pow_four_one_add_abs_le m.2.2
  have hW2_pos : 0 ≤ (1 + x.2.1 ^ 2) ^ 2 := by positivity
  have hb1 := hC1 x hx0 hx1 l hl
  have hb2 := hC2 x hx0 hx1 l hl
  have hb3 := hC3 x hx0 hx1 l hl
  have hb4 := hC4 x hx0 hx1 l hl
  have hb5 := hC5 x hx0 hx1 l hl
  calc (1 + |m.2.2|) ^ 4 *
        ‖iteratedFDeriv ℝ l (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) x‖
      ≤ (4 * (1 + x.2.1 ^ 2) ^ 2) *
          ‖iteratedFDeriv ℝ l (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) x‖ :=
        mul_le_mul_of_nonneg_right hW (norm_nonneg _)
    _ = 4 * ((1 + x.2.1 ^ 2) ^ 2 *
          ‖iteratedFDeriv ℝ l (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) x‖) := by
        ring
    _ ≤ 4 * ((1 + x.2.1 ^ 2) ^ 2 *
          (‖iteratedFDeriv ℝ l (coeffA₁ p.ν (trainStream p) (trainPressure p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₁ p.ν (trainStream p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffA₂ p.ν (trainStream p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₂ p.ν (trainStream p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₃ p.ν (trainStream p)) x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly hW2_pos) (by norm_num)
    _ ≤ 4 * (C1 + C2 + C3 + C4 + C5) := by linarith

/-- **`ResProfileEarlyJet2` from `PartI.TrainFluctuationDecay` and `PartI.TrainMeanExpansion`**. -/
theorem resProfileEarlyJet2_of_partI
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) :
    ResProfileEarlyJet2 := by
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  exact resProfileEarlyJet2_of (earlyStreamProfile_of hF hM hS) (earlyPressureProfile_of hF hS)

/-- **`ResProfileFarJet` from `ResProfileEarlyJet2`** (with `s0 = 1`). -/
theorem resProfileFarJet_of_earlyJet2 (h : ResProfileEarlyJet2) : ResProfileFarJet := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP => ?_⟩
  obtain ⟨C, hC⟩ := H p htr hν hc hR hP
  refine ⟨C, 1, one_pos, fun m hm0 hm1 l hl => ?_⟩
  have h1 : 0 < 1 + |m.2.2| := by positivity
  have hrpow : (1 + |m.2.2|) ^ (-4 : ℝ) = ((1 + |m.2.2|) ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1.le, Real.rpow_natCast]
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀' (pow_pos h1 4)]
  exact hC m hm0 hm1 l hl

namespace EarlyJet2Sub

/-- Unconditional proof of `EarlyStreamProfile` from the Part I interior-strip and transverse-tail
weighted jet bounds (`PartI_T21.wSupNorm_stream_vel_pressure_of_interior_and_tail`) on `0 < s ≤ 1`. -/
theorem earlyStreamProfile : EarlyStreamProfile := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD hMP
  have hOv := UnforcedLeray.Short.PartI.trainOverlap_proof hFD hMD
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTail := UnforcedLeray.Short.PartI.trainStreamVelocityPressureTransverseTail_proof hOv hVort
  have hInt := UnforcedLeray.Short.PartI.trainInteriorStripJetBounds_proof hOv hVort hTail
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  intro ρ m a b ℓ hρ
  obtain ⟨C, N, ν₀, hC0, hν₀, H⟩ :=
    PartI_T21.wSupNorm_stream_vel_pressure_of_interior_and_tail hTail hInt ρ hρ (2 * m) ℓ (a + b)
  refine ⟨ν₀, 2 ^ N * C, N, hν₀, ?_⟩
  intro ν hν ψ p hψ x hx0 hx1
  obtain ⟨T, hT, rfl, rfl⟩ := hψ
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hsm : ContDiffOn ℝ ∞ (trainProfile T.ψ) {y : ProfilePoint | 0 < y.2.2} :=
    (hS ν (ν ^ (-ρ)) hν0 hc T hT).1
  have hψ_sup := (H ν hν0 hν.2.le T hT x.2.2 hx0).1
  have hB : 0 ≤ polyPS C N ν (ν ^ (-ρ)) x.2.2 := by
    unfold polyPS
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
    have : 0 ≤ 1 + x.2.2 := by linarith
    positivity
  have h2 := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm hB hψ_sup (x.1, x.2.1)
  rw [UnforcedLeray.Short.PartIIa.sqrt_jap_even] at h2
  have hcomm := profileIterComm (trainProfile T.ψ) hsm 0 a b ℓ x hx0
  simp only [Function.iterate_zero, id_eq, zero_add] at hcomm
  rw [hcomm]
  have h1 := profileJetBound_of profileDict (sliceJetBound_of profileDict) T.ψ hsm a b ℓ x hx0
  have h1s : (1 + x.2.2) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
  have hbase : 0 ≤ C * (1 + ν ^ (-ρ) + ν⁻¹) ^ N := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
    positivity
  calc (1 + x.2.1 ^ 2) ^ m *
        |(partialEta^[a] (partialQ^[b] (partialAge^[ℓ] (trainProfile T.ψ)))) x|
      ≤ (1 + x.2.1 ^ 2) ^ m * ‖UnforcedLeray.Short.PartI.ageJet ℓ (a + b) T.ψ x.2.2 (x.1, x.2.1)‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ polyPS C N ν (ν ^ (-ρ)) x.2.2 := h2
    _ = C * (1 + ν ^ (-ρ) + ν⁻¹) ^ N * (1 + x.2.2) ^ N := by
        unfold polyPS; rw [mul_pow]; ring
    _ ≤ C * (1 + ν ^ (-ρ) + ν⁻¹) ^ N * 2 ^ N :=
        mul_le_mul_of_nonneg_left h1s hbase
    _ = polyConst (2 ^ N * C) N ν (ν ^ (-ρ)) := by
        unfold polyConst; ring

/-- Unconditional proof of `EarlyPressureProfile` from the Part I interior-strip and transverse-tail
weighted jet bounds (`PartI_T21.wSupNorm_stream_vel_pressure_of_interior_and_tail`) on `0 < s ≤ 1`. -/
theorem earlyPressureProfile : EarlyPressureProfile := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD hMP
  have hOv := UnforcedLeray.Short.PartI.trainOverlap_proof hFD hMD
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTail := UnforcedLeray.Short.PartI.trainStreamVelocityPressureTransverseTail_proof hOv hVort
  have hInt := UnforcedLeray.Short.PartI.trainInteriorStripJetBounds_proof hOv hVort hTail
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  intro ρ m a b ℓ hρ
  obtain ⟨C, N, ν₀, hC0, hν₀, H⟩ :=
    PartI_T21.wSupNorm_stream_vel_pressure_of_interior_and_tail hTail hInt ρ hρ (2 * m) ℓ (a + b)
  refine ⟨ν₀, 2 ^ N * C, N, hν₀, ?_⟩
  intro ν hν ψ p hψ x hx0 hx1
  obtain ⟨T, hT, rfl, rfl⟩ := hψ
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hsm : ContDiffOn ℝ ∞ (trainProfile T.p) {y : ProfilePoint | 0 < y.2.2} :=
    (hS ν (ν ^ (-ρ)) hν0 hc T hT).2
  have hp_sup := (H ν hν0 hν.2.le T hT x.2.2 hx0).2.2
  have hB : 0 ≤ polyPS C N ν (ν ^ (-ρ)) x.2.2 := by
    unfold polyPS
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
    have : 0 ≤ 1 + x.2.2 := by linarith
    positivity
  have h2 := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm hB hp_sup (x.1, x.2.1)
  rw [UnforcedLeray.Short.PartIIa.sqrt_jap_even] at h2
  have hcomm := profileIterComm (trainProfile T.p) hsm 0 a b ℓ x hx0
  simp only [Function.iterate_zero, id_eq, zero_add] at hcomm
  rw [hcomm]
  have h1 := profileJetBound_of profileDict (sliceJetBound_of profileDict) T.p hsm a b ℓ x hx0
  have h1s : (1 + x.2.2) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
  have hbase : 0 ≤ C * (1 + ν ^ (-ρ) + ν⁻¹) ^ N := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
    positivity
  calc (1 + x.2.1 ^ 2) ^ m *
        |(partialEta^[a] (partialQ^[b] (partialAge^[ℓ] (trainProfile T.p)))) x|
      ≤ (1 + x.2.1 ^ 2) ^ m * ‖UnforcedLeray.Short.PartI.ageJet ℓ (a + b) T.p x.2.2 (x.1, x.2.1)‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ polyPS C N ν (ν ^ (-ρ)) x.2.2 := h2
    _ = C * (1 + ν ^ (-ρ) + ν⁻¹) ^ N * (1 + x.2.2) ^ N := by
        unfold polyPS; rw [mul_pow]; ring
    _ ≤ C * (1 + ν ^ (-ρ) + ν⁻¹) ^ N * 2 ^ N :=
        mul_le_mul_of_nonneg_left h1s hbase
    _ = polyConst (2 ^ N * C) N ν (ν ^ (-ρ)) := by
        unfold polyConst; ring

end EarlyJet2Sub

/-- **Early-age (`0 < s ≤ 1`) weighted second-jet bound of the chart residual profile**
(`PartIII-b:C/ward/12/3/2/2/1/2/1/1`, `the November 2 reference manuscript`, lines 1294-1304, 2542-2551). -/
theorem resProfileEarlyJet2 : ResProfileEarlyJet2 :=
  resProfileEarlyJet2_of EarlyJet2Sub.earlyStreamProfile EarlyJet2Sub.earlyPressureProfile

end UnforcedLeray.Short.PartIIIb.Concrete
