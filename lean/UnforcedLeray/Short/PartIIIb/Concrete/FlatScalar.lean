import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat

/-!
# Conditional scalar estimate for the flat return (source 4628-4632, proof 4662-4690)

Draft proof of `FlatScalarEstimateC` (from `YoungFlat.lean`): the old/early split of the
`I_T` integral, the class amplitude `a_ν,+ ↦ a_0` replacement, and the algebra
`ε³/(8(μ+3/2)) · (3π/(2c))(μ+3/2) ν^{3+2μ} = (3π/16) ε³ ν^{5+2μ}` with `c = ν⁻²`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory Real

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

/-- Pointwise split of the `I_T` integrand at the old time `u = u_o`. -/
lemma flat_ITdens_split (S : FlatSetting) (u : ℝ) (M : ℝ → ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : ℝ) :
    S.ITdens M s = S.ITdens (fun s => if u ≤ s then M s else fun _ => 0) s
      + S.ITdens (fun s => if s < u then M s else fun _ => 0) s := by
  by_cases h : u ≤ s
  · have h2 : ¬ s < u := not_lt.mpr h
    simp [FlatSetting.ITdens, cellInt, h, h2]
  · have h2 : s < u := lt_of_not_ge h
    simp [FlatSetting.ITdens, cellInt, h, h2]

/-- Splitting of `I_T` into its old and early parts (integrability as input). -/
lemma flat_IT_split (S : FlatSetting) (u : ℝ) (M : ℝ → ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (h1 : Integrable (fun s => S.ITdens (fun s => if u ≤ s then M s else fun _ => 0) s)
      (volume.restrict (Ioi (0 : ℝ))))
    (h2 : Integrable (fun s => S.ITdens (fun s => if s < u then M s else fun _ => 0) s)
      (volume.restrict (Ioi (0 : ℝ)))) :
    S.IT M = S.IT (fun s => if u ≤ s then M s else fun _ => 0)
      + S.IT (fun s => if s < u then M s else fun _ => 0) := by
  simp only [FlatSetting.IT_eq]
  rw [← integral_add h1 h2]
  congr 1
  funext s
  exact flat_ITdens_split S u M s

lemma abs_add_three3 (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le (a + b) c
  have h2 := abs_add_le a b
  linarith

/-- Pure real algebra behind the scalar estimate. `Ige`, `Ilt` are the old and early parts of
`I_T`, `X` and `Y0`, `Y` are the imaginary and real parts of the complex amplitude expressions. -/
lemma flat_core (ε μ ν ω C1 C2 C3 P nN J0 bN Ige Ilt X Y0 Y p q c : ℝ)
    (hε : 0 < ε) (hμ : 0 < μ) (hν : 0 < ν) (hP : 0 ≤ P) (hnN : 0 ≤ nN) (hJ : 0 ≤ J0)
    (hb : 0 ≤ bN) (hc : c = ν⁻¹ ^ 2) (hp : 0 ≤ p) (hq : q = p * ν ^ 2)
    (hY : Y = -X)
    (hO : |Ige - 3 * π / (2 * c) * (μ + 3 / 2) * p * X| ≤ C2 * ((nN * p / c) * (ν + ω)) * bN)
    (hE : |Ilt| ≤ C3 * (nN * p / c) * P * bN)
    (hW : |Y0 - Y| ≤ C1 * ν * bN * nN * J0) :
    |ε * (Ige + Ilt) / (8 * (μ + 3 / 2)) + 3 * π / 16 * (ε * q) * Y0|
      ≤ (|C2| + |C3| + 3 * π / 16 * |C1| * J0) * (ε * nN * q) * (|ω| + ν + P) * bN := by
  subst hq
  have hν0 : ν ≠ 0 := hν.ne'
  have hν2 : 1 / c = ν ^ 2 := by rw [hc, one_div, inv_pow, inv_inv]
  have hA : nN * p / c = nN * (p * ν ^ 2) := by
    rw [div_eq_mul_one_div, hν2]; ring
  rw [hA] at hO hE
  have hD : (1 : ℝ) ≤ 8 * (μ + 3 / 2) := by linarith
  have hK : ε / (8 * (μ + 3 / 2)) ≤ ε := div_le_self hε.le hD
  have hK0 : 0 ≤ ε / (8 * (μ + 3 / 2)) := div_nonneg hε.le (by linarith)
  have hR : ε / (8 * (μ + 3 / 2)) * (3 * π / (2 * c) * (μ + 3 / 2) * p * X)
      = 3 * π / 16 * (ε * (p * ν ^ 2)) * X := by
    rw [hc]
    have hμ' : μ + 3 / 2 ≠ 0 := by linarith
    field_simp
    ring
  have hid : ε * (Ige + Ilt) / (8 * (μ + 3 / 2)) + 3 * π / 16 * (ε * (p * ν ^ 2)) * Y0
      = ε / (8 * (μ + 3 / 2)) * (Ige - 3 * π / (2 * c) * (μ + 3 / 2) * p * X)
        + ε / (8 * (μ + 3 / 2)) * Ilt + 3 * π / 16 * (ε * (p * ν ^ 2)) * (Y0 - Y) := by
    linear_combination hR + (3 * π / 16 * (ε * (p * ν ^ 2))) * hY
  rw [hid]
  have hωb : |ν + ω| ≤ ν + |ω| := by
    calc |ν + ω| ≤ |ν| + |ω| := abs_add_le _ _
      _ = ν + |ω| := by rw [abs_of_pos hν]
  have hAn : 0 ≤ nN * (p * ν ^ 2) := mul_nonneg hnN (mul_nonneg hp (sq_nonneg ν))
  have key1 : C2 * ((nN * (p * ν ^ 2)) * (ν + ω)) ≤ |C2| * ((nN * (p * ν ^ 2)) * (ν + |ω|)) := by
    calc C2 * ((nN * (p * ν ^ 2)) * (ν + ω))
        ≤ |C2 * ((nN * (p * ν ^ 2)) * (ν + ω))| := le_abs_self _
      _ = |C2| * |(nN * (p * ν ^ 2)) * (ν + ω)| := abs_mul _ _
      _ = |C2| * ((nN * (p * ν ^ 2)) * |ν + ω|) := by rw [abs_mul, abs_of_nonneg hAn]
      _ ≤ |C2| * ((nN * (p * ν ^ 2)) * (ν + |ω|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hωb hAn) (abs_nonneg _)
  have hbound1 : |Ige - 3 * π / (2 * c) * (μ + 3 / 2) * p * X|
      ≤ |C2| * ((nN * (p * ν ^ 2)) * (ν + |ω|)) * bN :=
    hO.trans (mul_le_mul_of_nonneg_right key1 hb)
  have t1 : |ε / (8 * (μ + 3 / 2)) * (Ige - 3 * π / (2 * c) * (μ + 3 / 2) * p * X)|
      ≤ ε * (|C2| * ((nN * (p * ν ^ 2)) * (ν + |ω|)) * bN) := by
    rw [abs_mul, abs_of_nonneg hK0]
    exact (mul_le_mul_of_nonneg_right hK (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hbound1 hε.le)
  have hAP : 0 ≤ (nN * (p * ν ^ 2)) * P := mul_nonneg hAn hP
  have hE' : |Ilt| ≤ |C3| * ((nN * (p * ν ^ 2)) * P) * bN := by
    refine hE.trans ?_
    have h0 : C3 * (nN * (p * ν ^ 2)) * P = C3 * ((nN * (p * ν ^ 2)) * P) := by ring
    rw [h0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C3) hAP) hb
  have t2 : |ε / (8 * (μ + 3 / 2)) * Ilt| ≤ ε * (|C3| * ((nN * (p * ν ^ 2)) * P) * bN) := by
    rw [abs_mul, abs_of_nonneg hK0]
    exact (mul_le_mul_of_nonneg_right hK (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hE' hε.le)
  have hCq0 : 0 ≤ 3 * π / 16 * (ε * (p * ν ^ 2)) :=
    mul_nonneg (by positivity) (mul_nonneg hε.le (mul_nonneg hp (sq_nonneg ν)))
  have hW' : |Y0 - Y| ≤ |C1| * ν * bN * nN * J0 := by
    refine hW.trans ?_
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hν.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb
    have h3 := mul_le_mul_of_nonneg_right h2 hnN
    exact mul_le_mul_of_nonneg_right h3 hJ
  have t3 : |3 * π / 16 * (ε * (p * ν ^ 2)) * (Y0 - Y)|
      ≤ 3 * π / 16 * (ε * (p * ν ^ 2)) * (|C1| * ν * bN * nN * J0) := by
    rw [abs_mul, abs_of_nonneg hCq0]
    exact mul_le_mul_of_nonneg_left hW' hCq0
  have hk3 : 0 ≤ 3 * π / 16 * |C1| * J0 := by positivity
  have hs : 0 ≤ |ω| + ν + P := by
    have := abs_nonneg ω
    linarith
  have hsum : |C2| * (ν + |ω|) + |C3| * P + 3 * π / 16 * |C1| * J0 * ν
      ≤ (|C2| + |C3| + 3 * π / 16 * |C1| * J0) * (|ω| + ν + P) := by
    have a1 : |C2| * (ν + |ω|) ≤ |C2| * (|ω| + ν + P) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have a2 : |C3| * P ≤ |C3| * (|ω| + ν + P) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg ω]) (abs_nonneg _)
    have a3 : 3 * π / 16 * |C1| * J0 * ν ≤ 3 * π / 16 * |C1| * J0 * (|ω| + ν + P) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg ω]) hk3
    have e : (|C2| + |C3| + 3 * π / 16 * |C1| * J0) * (|ω| + ν + P)
        = |C2| * (|ω| + ν + P) + |C3| * (|ω| + ν + P) + 3 * π / 16 * |C1| * J0 * (|ω| + ν + P) := by
      ring
    linarith
  have hZ : 0 ≤ ε * (nN * (p * ν ^ 2)) * bN := mul_nonneg (mul_nonneg hε.le hAn) hb
  have hfin : ε * (|C2| * ((nN * (p * ν ^ 2)) * (ν + |ω|)) * bN)
      + ε * (|C3| * ((nN * (p * ν ^ 2)) * P) * bN)
      + 3 * π / 16 * (ε * (p * ν ^ 2)) * (|C1| * ν * bN * nN * J0)
      ≤ (|C2| + |C3| + 3 * π / 16 * |C1| * J0) * (ε * nN * (p * ν ^ 2)) * (|ω| + ν + P) * bN := by
    have e2 : ε * (|C2| * ((nN * (p * ν ^ 2)) * (ν + |ω|)) * bN)
        + ε * (|C3| * ((nN * (p * ν ^ 2)) * P) * bN)
        + 3 * π / 16 * (ε * (p * ν ^ 2)) * (|C1| * ν * bN * nN * J0)
        = (ε * (nN * (p * ν ^ 2)) * bN) * (|C2| * (ν + |ω|) + |C3| * P + 3 * π / 16 * |C1| * J0 * ν) := by
      ring
    rw [e2]
    calc (ε * (nN * (p * ν ^ 2)) * bN) * (|C2| * (ν + |ω|) + |C3| * P + 3 * π / 16 * |C1| * J0 * ν)
        ≤ (ε * (nN * (p * ν ^ 2)) * bN) * ((|C2| + |C3| + 3 * π / 16 * |C1| * J0) * (|ω| + ν + P)) :=
          mul_le_mul_of_nonneg_left hsum hZ
      _ = (|C2| + |C3| + 3 * π / 16 * |C1| * J0) * (ε * nN * (p * ν ^ 2)) * (|ω| + ν + P) * bN := by
          ring
  refine (abs_add_three3 _ _ _).trans ?_
  linarith [t1, t2, t3, hfin]

/-- `flatScalarEstimateC` (source 4628-4632, proof 4662-4690): the conditional scalar estimate
for the concrete flat packages, from the class amplitude, the old anisotropy law, the early
old bound and the integrability of the `I_T` pieces. -/
theorem flatScalarEstimateC (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (μ a : ℝ) : FlatScalarEstimateC S ν lam κ ell J μ a := by
  unfold FlatScalarEstimateC
  intro hyp hAmp hOld hEarly hInt
  unfold FlatScalarEstimate
  intro γ' hγ0 hγl
  obtain ⟨C1, N1, hA⟩ := hAmp
  obtain ⟨ω, C2, N2, hωT, hO⟩ := hOld
  obtain ⟨C3, k, N3, hE⟩ := hEarly γ' hγ0 hγl
  refine ⟨fun n => |ω n|, |C2| + |C3| + 3 * Real.pi / 16 * |C1| * ‖J (μ : ℂ)‖, k,
    max (max N1 N2) N3, ?_, ?_⟩
  · have h := (continuous_abs.tendsto (0 : ℝ)).comp hωT
    simpa [Function.comp_def] using h
  intro n hn B hB
  have h1 : N1 ≤ n := le_trans (le_trans (le_max_left N1 N2) (le_max_left _ N3)) hn
  have h2 : N2 ≤ n := le_trans (le_trans (le_max_right N1 N2) (le_max_left _ N3)) hn
  have h3 : N3 ≤ n := le_trans (le_max_right _ N3) hn
  have hνpos : 0 < ν n := hyp.young.1 n
  have hεpos : 0 < (S n).eps3 := hyp.eps3_pos n
  have hcn : (S n).c = (ν n)⁻¹ ^ 2 := hyp.c_eq n
  have hμ : 0 < μ := hyp.mu_pos
  have hA' : ‖(S n).aNuC lam κ (μ : ℂ) (ν n) B - aZero lam ell (μ : ℂ) B‖
      ≤ C1 * ν n * bNorm a B := hA n h1 B hB
  have hO' : |(S n).IT (fun s => if ν n ^ (-(3 / 2 : ℝ)) ≤ s then
        (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0)
      - 3 * Real.pi / (2 * (S n).c) * (μ + 3 / 2) * ν n ^ (3 + 2 * μ)
        * (((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)).im|
      ≤ C2 * ((‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ) / (S n).c) * (ν n + ω n)) * bNorm a B :=
    hO n h2 B hB
  have hE' : |(S n).IT (fun s => if s < ν n ^ (-(3 / 2 : ℝ)) then
        (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0)|
      ≤ C3 * (‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ) / (S n).c)
        * ((ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B :=
    hE n h3 B hB
  have hint := hInt n B hB
  have hsplit := flat_IT_split (S n) (ν n ^ (-(3 / 2 : ℝ)))
    (fun s => (S n).Mcell s ((S n).xi (μ : ℂ) B s)) hint.1 hint.2
  -- the Y-part: real parts of the amplitude expressions
  have hYX : (Complex.I * ((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)).re
      = -(((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)).im := by
    rw [show Complex.I * ((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)
        = Complex.I * (((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)) by ring]
    simp [Complex.mul_re]
  have hWeq : (Complex.I * aZero lam ell (μ : ℂ) B * Nnu lam κ (ν n) * J (μ : ℂ)).re
      - (Complex.I * ((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)).re
      = (Complex.I * (aZero lam ell (μ : ℂ) B - ((S n).aNuC lam κ (μ : ℂ) (ν n) B))
          * Nnu lam κ (ν n) * J (μ : ℂ)).re := by
    rw [show Complex.I * (aZero lam ell (μ : ℂ) B - ((S n).aNuC lam κ (μ : ℂ) (ν n) B))
        * Nnu lam κ (ν n) * J (μ : ℂ)
        = Complex.I * aZero lam ell (μ : ℂ) B * Nnu lam κ (ν n) * J (μ : ℂ)
          - Complex.I * ((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ) by ring]
    rw [Complex.sub_re]
  have hWn : |(Complex.I * (aZero lam ell (μ : ℂ) B - ((S n).aNuC lam κ (μ : ℂ) (ν n) B))
        * Nnu lam κ (ν n) * J (μ : ℂ)).re|
      ≤ ‖aZero lam ell (μ : ℂ) B - ((S n).aNuC lam κ (μ : ℂ) (ν n) B)‖
        * ‖Nnu lam κ (ν n)‖ * ‖J (μ : ℂ)‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    simp
  have hWb : |(Complex.I * aZero lam ell (μ : ℂ) B * Nnu lam κ (ν n) * J (μ : ℂ)).re
      - (Complex.I * ((S n).aNuC lam κ (μ : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)).re|
      ≤ C1 * ν n * bNorm a B * ‖Nnu lam κ (ν n)‖ * ‖J (μ : ℂ)‖ := by
    rw [hWeq]
    refine hWn.trans ?_
    have hd : ‖aZero lam ell (μ : ℂ) B - ((S n).aNuC lam κ (μ : ℂ) (ν n) B)‖
        ≤ C1 * ν n * bNorm a B := by
      rw [norm_sub_rev]; exact hA'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) (norm_nonneg _)
  have hP : 0 ≤ (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n)) :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hνpos.le) k) (Real.exp_pos _).le
  have hp : 0 ≤ ν n ^ (3 + 2 * μ) := Real.rpow_nonneg hνpos.le _
  have hq : ν n ^ (5 + 2 * μ) = ν n ^ (3 + 2 * μ) * ν n ^ 2 := by
    rw [show (5 + 2 * μ) = (3 + 2 * μ) + 2 by ring, Real.rpow_add hνpos, Real.rpow_two]
  have hb : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hcore := flat_core (S n).eps3 μ (ν n) (ω n) C1 C2 C3
    ((ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) ‖Nnu lam κ (ν n)‖ ‖J (μ : ℂ)‖
    (bNorm a B) _ _ _ _ _ (ν n ^ (3 + 2 * μ)) (ν n ^ (5 + 2 * μ)) (S n).c
    hεpos hμ hνpos hP (norm_nonneg _) (norm_nonneg _) hb hcn hp hq hYX hO' hE' hWb
  dsimp only [FlatSetting.toPkg, FlatSetting.ellMuC]
  rw [hsplit]
  exact hcore

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
