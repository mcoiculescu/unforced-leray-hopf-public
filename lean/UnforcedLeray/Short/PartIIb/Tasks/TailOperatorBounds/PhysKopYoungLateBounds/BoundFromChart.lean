import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail
import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound.BoxJet
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.RawProfileLate

/-!
# Conditional Young & Late Physical Interaction Bounds (`PartII-b:G2/2` from `KOutChartAe`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2434–2437 (late physical tail) and 2443–2445 (young physical tail), together with
2007–2012 (chart representation of `K_ε`) and 2412–2431 (`StrongLateCoeff` / `RawProfileLate`).

Proves `physKopYoungLateBounds_of_chartAe : KOutChartAe → PhysKopYoungLateBounds`:
* `kOutChart_norm_le_lateProfileQuantity`: pointwise control of `‖kOutChart p b Qb Eb x‖` by
  `lateProfileQuantity p.ε (rawProf p) x` against `‖sqrtS Qb x‖`, `‖sqrtS Eb x‖`, and `‖b x‖`;
* `rawProf_young_chartJet`: uniform polynomial bound `chartJet (rawProf p) x ≤ C_y * (p.ν ^ k_y)⁻¹`
  for `0 < x.1 ≤ 1` across all `(q, η) ∈ ℝ²`, combining `rawBoxJet_proof` on `|η| ≤ Γ` with
  `RawCoeffTail.tailsUniform` + `tailAbsorb` (`K = 0`, `S = 1`, `D = 2`) on `|η| > Γ`;
* `physKopYoungLateBounds_of_chartAe`: combines `KOutChartAe`, `rawProf_young_chartJet`,
  `rawProfileLate`, and the `GraphBound` hypothesis at `(bgp, μ = 0)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.PhysKopYLHelp

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartI UnforcedLeray.Short.IIIa

/-! ## 1. Pointwise `kOutChart` bound via `lateProfileQuantity` -/

/-- `gradProfileQuantity ε u x` equals `x.1 * (‖Axi.dEta u x‖ + ‖qEps ε u x‖ + ε * |u x 0|)`. -/
private theorem gradProfileQuantity_eq_qEps (ε : ℝ) (u : Coord → Axi.Merid) (x : Coord) :
    gradProfileQuantity ε u x =
      x.1 * (‖Axi.dEta u x‖ + ‖qEps ε u x‖ + ε * |u x 0|) := by
  rfl

/-- Pointwise bound on `kOutChart` from `lateProfileQuantity p.ε (rawProf p) x ≤ L` (`s > 0`,
`0 ≤ ε`, SP 2007–2012, 2434–2437). -/
theorem kOutChart_norm_le_lateProfileQuantity (p : Params) (b Qb Eb : CProf) {x : Coord}
    (hx : 0 < x.1) (hε0 : 0 ≤ p.ε) {L : ℝ}
    (hL : lateProfileQuantity p.ε (rawProf p) x ≤ L) :
    ‖kOutChart p b Qb Eb x‖ ≤ L * ‖sqrtS Qb x‖ + L * ‖sqrtS Eb x‖ + (2 * L) * ‖b x‖ := by
  set u : Coord → Axi.Merid := rawProf p
  have hgrad_nn : 0 ≤ gradProfileQuantity p.ε u x := by
    rw [gradProfileQuantity_eq_qEps]
    positivity
  have hsu_nn : 0 ≤ Real.sqrt x.1 * ‖u x‖ := by positivity
  have hsu : Real.sqrt x.1 * ‖u x‖ ≤ L := by
    unfold lateProfileQuantity at hL
    linarith
  have hgrad : x.1 * (‖Axi.dEta u x‖ + ‖qEps p.ε u x‖ + p.ε * |u x 0|) ≤ L := by
    unfold lateProfileQuantity at hL
    rw [gradProfileQuantity_eq_qEps] at hL
    linarith
  have hL0 : 0 ≤ L := hsu_nn.trans hsu
  have hqe : x.1 * (‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) ≤ L := by
    have h1 : ‖qEps p.ε u x‖ + ‖Axi.dEta u x‖ ≤
        ‖Axi.dEta u x‖ + ‖qEps p.ε u x‖ + p.ε * |u x 0| := by
      have : 0 ≤ p.ε * |u x 0| := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hx.le).trans hgrad
  have hdiv : x.1 * |chartDivR p.ε u x| ≤ L := by
    have h1 : |qEps p.ε u x 0| ≤ ‖qEps p.ε u x‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    have h2 : |Axi.dEta u x 1| ≤ ‖Axi.dEta u x‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    have h3 : |p.ε * u x 0| = p.ε * |u x 0| := by
      rw [abs_mul, abs_of_nonneg hε0]
    have hcd : |chartDivR p.ε u x| ≤
        ‖Axi.dEta u x‖ + ‖qEps p.ε u x‖ + p.ε * |u x 0| := by
      unfold chartDivR
      calc |qEps p.ε u x 0 + p.ε * u x 0 + Axi.dEta u x 1|
          ≤ |qEps p.ε u x 0| + |p.ε * u x 0| + |Axi.dEta u x 1| := abs_add_three _ _ _
        _ ≤ ‖Axi.dEta u x‖ + ‖qEps p.ε u x‖ + p.ε * |u x 0| := by linarith
    exact (mul_le_mul_of_nonneg_left hcd hx.le).trans hgrad
  have hsq : x.1 = Real.sqrt x.1 * Real.sqrt x.1 := (Real.mul_self_sqrt hx.le).symm
  have hnQ : ‖sqrtS Qb x‖ = Real.sqrt x.1 * ‖Qb x‖ := norm_sqrtS_of_nonneg Qb hx.le
  have hnE : ‖sqrtS Eb x‖ = Real.sqrt x.1 * ‖Eb x‖ := norm_sqrtS_of_nonneg Eb hx.le
  have hcp : ∀ F : Coord → Axi.Merid, ‖cplx F x‖ = ‖F x‖ := fun F => liftM_norm (F x)
  have hr0 : ‖(((u x 0 : ℝ) : ℂ))‖ ≤ ‖u x‖ := by
    rw [Complex.norm_real]; exact PiLp.norm_apply_le _ _
  have hr1 : ‖(((u x 1 : ℝ) : ℂ))‖ ≤ ‖u x‖ := by
    rw [Complex.norm_real]; exact PiLp.norm_apply_le _ _
  have hb0 : ‖b x 0‖ ≤ ‖b x‖ := PiLp.norm_apply_le _ _
  have hb1 : ‖b x 1‖ ≤ ‖b x‖ := PiLp.norm_apply_le _ _
  have hA : ‖((u x 0 : ℝ) : ℂ) • Qb x + ((u x 1 : ℝ) : ℂ) • Eb x‖ ≤
      ‖u x‖ * ‖Qb x‖ + ‖u x‖ * ‖Eb x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    gcongr
  have hB : ‖b x 0 • cplx (qEps p.ε u) x + b x 1 • cplx (Axi.dEta u) x‖ ≤
      (‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) * ‖b x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, hcp, hcp]
    calc ‖b x 0‖ * ‖qEps p.ε u x‖ + ‖b x 1‖ * ‖Axi.dEta u x‖
        ≤ ‖b x‖ * ‖qEps p.ε u x‖ + ‖b x‖ * ‖Axi.dEta u x‖ := by gcongr
      _ = (‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) * ‖b x‖ := by ring
  have hC : ‖((chartDivR p.ε u x : ℝ) : ℂ) • b x‖ ≤ |chartDivR p.ε u x| * ‖b x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hmain : ‖kOutChart p b Qb Eb x‖ ≤
      x.1 * ((‖u x‖ * ‖Qb x‖ + ‖u x‖ * ‖Eb x‖) +
        (‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) * ‖b x‖ + |chartDivR p.ε u x| * ‖b x‖) := by
    unfold kOutChart
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hx.le]
    refine mul_le_mul_of_nonneg_left ?_ hx.le
    refine (norm_add_le _ _).trans ?_
    exact add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC
  refine hmain.trans ?_
  have hQe : x.1 * (‖u x‖ * ‖Qb x‖) ≤ L * ‖sqrtS Qb x‖ := by
    rw [hnQ]
    calc x.1 * (‖u x‖ * ‖Qb x‖) = (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Qb x‖) := by
          rw [show (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Qb x‖) =
            (Real.sqrt x.1 * Real.sqrt x.1) * (‖u x‖ * ‖Qb x‖) by ring, ← hsq]
      _ ≤ L * (Real.sqrt x.1 * ‖Qb x‖) :=
          mul_le_mul_of_nonneg_right hsu (by positivity)
  have hEe : x.1 * (‖u x‖ * ‖Eb x‖) ≤ L * ‖sqrtS Eb x‖ := by
    rw [hnE]
    calc x.1 * (‖u x‖ * ‖Eb x‖) = (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Eb x‖) := by
          rw [show (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Eb x‖) =
            (Real.sqrt x.1 * Real.sqrt x.1) * (‖u x‖ * ‖Eb x‖) by ring, ← hsq]
      _ ≤ L * (Real.sqrt x.1 * ‖Eb x‖) :=
          mul_le_mul_of_nonneg_right hsu (by positivity)
  have hB' : x.1 * ((‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) * ‖b x‖) ≤ L * ‖b x‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hqe (norm_nonneg _)
  have hC' : x.1 * (|chartDivR p.ε u x| * ‖b x‖) ≤ L * ‖b x‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
  calc x.1 * ((‖u x‖ * ‖Qb x‖ + ‖u x‖ * ‖Eb x‖) +
          (‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) * ‖b x‖ + |chartDivR p.ε u x| * ‖b x‖)
      = x.1 * (‖u x‖ * ‖Qb x‖) + x.1 * (‖u x‖ * ‖Eb x‖) +
          (x.1 * ((‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) * ‖b x‖) +
            x.1 * (|chartDivR p.ε u x| * ‖b x‖)) := by ring
    _ ≤ L * ‖sqrtS Qb x‖ + L * ‖sqrtS Eb x‖ + (L * ‖b x‖ + L * ‖b x‖) := by gcongr
    _ = L * ‖sqrtS Qb x‖ + L * ‖sqrtS Eb x‖ + (2 * L) * ‖b x‖ := by ring

/-- On the young age region `0 < x.1 ≤ σ ≤ 1` (`0 ≤ ε ≤ 1`), `lateProfileQuantity ε u x` is at
most `3 * chartJet u x * √σ` (SP 2443–2445). -/
theorem lateProfileQuantity_le_young {ε σ : ℝ} (u : Coord → Axi.Merid) {x : Coord}
    (hx0 : 0 ≤ x.1) (hxσ : x.1 ≤ σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    lateProfileQuantity ε u x ≤ 3 * chartJet u x * Real.sqrt σ := by
  set J : ℝ := chartJet u x with hJ_def
  have hu0 : ‖u x‖ ≤ J := by
    simp only [hJ_def, chartJet]
    have := norm_nonneg (Axi.dQ u x)
    have := norm_nonneg (Axi.dEta u x)
    have := norm_nonneg (kAge u x)
    linarith
  have hJ0 : 0 ≤ J := (norm_nonneg _).trans hu0
  have hqe : ‖Axi.dEta u x‖ + ‖qEps ε u x‖ + ε * |u x 0| ≤ 2 * J := by
    have h1 : ‖qEps ε u x‖ ≤ ‖Axi.dQ u x‖ + (‖kAge u x‖ + ‖u x‖) := by
      unfold qEps
      calc ‖Axi.dQ u x - ε • (kAge u x + u x)‖
          ≤ ‖Axi.dQ u x‖ + ‖ε • (kAge u x + u x)‖ := norm_sub_le _ _
        _ ≤ ‖Axi.dQ u x‖ + (‖kAge u x‖ + ‖u x‖) := by
          gcongr
          rw [norm_smul, Real.norm_of_nonneg hε0]
          calc ε * ‖kAge u x + u x‖ ≤ 1 * ‖kAge u x + u x‖ :=
                mul_le_mul_of_nonneg_right hε1 (norm_nonneg _)
            _ = ‖kAge u x + u x‖ := one_mul _
            _ ≤ ‖kAge u x‖ + ‖u x‖ := norm_add_le _ _
    have h2 : ε * |u x 0| ≤ ‖u x‖ := by
      have ha : |u x 0| ≤ ‖u x‖ := by
        rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
      calc ε * |u x 0| ≤ 1 * |u x 0| := mul_le_mul_of_nonneg_right hε1 (abs_nonneg _)
        _ = |u x 0| := one_mul _
        _ ≤ ‖u x‖ := ha
    have := norm_nonneg (Axi.dQ u x)
    have := norm_nonneg (Axi.dEta u x)
    have := norm_nonneg (kAge u x)
    simp only [hJ_def, chartJet]
    linarith
  have hsqrt_le : Real.sqrt x.1 ≤ Real.sqrt σ := Real.sqrt_le_sqrt hxσ
  have hs_le : x.1 ≤ Real.sqrt σ := (young_age_weight_le hx0 hxσ hσ1).2
  unfold lateProfileQuantity
  rw [gradProfileQuantity_eq_qEps]
  have hA : Real.sqrt x.1 * ‖u x‖ ≤ Real.sqrt σ * J :=
    mul_le_mul hsqrt_le hu0 (norm_nonneg _) (Real.sqrt_nonneg _)
  have hB : x.1 * (‖Axi.dEta u x‖ + ‖qEps ε u x‖ + ε * |u x 0|) ≤ Real.sqrt σ * (2 * J) :=
    mul_le_mul hs_le hqe (by positivity) (Real.sqrt_nonneg _)
  calc Real.sqrt x.1 * ‖u x‖ + x.1 * (‖Axi.dEta u x‖ + ‖qEps ε u x‖ + ε * |u x 0|)
      ≤ Real.sqrt σ * J + Real.sqrt σ * (2 * J) := add_le_add hA hB
    _ = 3 * J * Real.sqrt σ := by ring

/-! ## 2. Uniform young `chartJet` bound on `0 < x.1 ≤ 1` -/

/-- Transverse jet tail on `0 < x.1 ≤ 1` (`S = 1`, `K = 0`, `D = 2`). -/
private theorem youngJetTail (ℓ j : ℕ) :
    ∃ C_D₀ ν₀ : ℝ, 1 ≤ C_D₀ ∧ 0 < ν₀ ∧
      ∀ C_D : ℝ, C_D₀ ≤ C_D →
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ 1 →
          C_D * ((p.ν ^ 2)⁻¹ / p.ν + 2) < |x.2.2| →
          (1 + (1 : ℝ)) ^ 3 * (1 + x.2.2 ^ 2) * ‖ageJet ℓ j p.train.ψ x.1 x.2‖ ≤
              Real.exp (-2 / p.ν) / 2 ∧
            (1 + (1 : ℝ)) ^ 3 * (1 + x.2.2 ^ 2) * ‖ageJet ℓ j p.train.v x.1 x.2‖ ≤
              Real.exp (-2 / p.ν) / 2 := by
  obtain ⟨b₀, C₀, C', C, N, ν₁, hb₀, hC₀, _hC', _hC, hν₁, hT'⟩ :=
    RawCoeffTail.tailsUniform 2 (by norm_num) ℓ j
  obtain ⟨Cp, ν₂, _hCp, hν₂, hK'⟩ :=
    tailAbsorb b₀ C₀ C' C 0 2 N 3 1 hb₀ hC₀ (by norm_num) le_rfl
  refine ⟨max Cp 1, min ν₁ ν₂, le_max_right Cp 1, lt_min hν₁ hν₂, ?_⟩
  intro C_D hCD p d dm dp hd hν x hx0 hx1 hη
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hpc : p.c = trainPeriod 2 p.ν := by
    rw [hd.c_eq]
    unfold trainPeriod
    rw [Real.rpow_neg p.ν_pos.le, Real.rpow_two]
  have hSK : (1 : ℝ) ≤ Real.exp (0 / p.ν) := by simp
  have hCp_le : Cp ≤ C_D := (le_max_left Cp 1).trans hCD
  have hthr : Cp * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt 1 + 1) < |x.2.2| := by
    have hbr : (p.ν ^ 2)⁻¹ / p.ν + Real.sqrt 1 + 1 = (p.ν ^ 2)⁻¹ / p.ν + 2 := by
      rw [Real.sqrt_one]; ring
    rw [hbr]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCp_le (by positivity)) hη
  obtain ⟨hl, hmain⟩ := hK' p.ν hνpos hν2 1 le_rfl hSK x.2.2 hthr
  have hlpos : 0 ≤ |x.2.2| - C' / p.ν - 2 := by linarith
  have hT2 := hT' p.ν hνpos hν1 p.c hpc p.train hd.train_buc 1 (by norm_num)
    (|x.2.2| - C' / p.ν - 2) hlpos x.1 hx0 hx1 x.2
    (by show C' / p.ν + 2 + (|x.2.2| - C' / p.ν - 2) ≤ |x.2.2|; linarith)
  dsimp only at hT2
  obtain ⟨hψ, hv, _, _⟩ := hT2
  rw [T23RS.K_eq C N p.ν p.c 1 b₀ (|x.2.2| - C' / p.ν - 2) C₀ hd.c_eq] at hψ hv
  rw [pow_one] at hmain
  have hWpos : 0 ≤ (1 + (1 : ℝ)) ^ 3 * (1 + x.2.2 ^ 2) := by positivity
  exact ⟨(mul_le_mul_of_nonneg_left hψ hWpos).trans hmain,
    (mul_le_mul_of_nonneg_left hv hWpos).trans hmain⟩

open RawProfJetHelp in
/-- Exterior half (`|η| > CD * ((ν ^ 2)⁻¹ / ν + 2)`) of the young `chartJet` bound: on `0 < x.1 ≤ 1`
the six `youngJetTail` bounds give `chartJet (rawProf p) x ≤ 1`. -/
private theorem rawProf_young_chartJet_ext :
    ∃ (CD ν_ext : ℝ), 1 ≤ CD ∧ 0 < ν_ext ∧ ν_ext ≤ 1 ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν_ext →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ 1 →
          CD * ((p.ν ^ 2)⁻¹ / p.ν + 2) < |x.2.2| →
          chartJet (rawProf p) x ≤ 1 := by
  obtain ⟨C0, n0, hC0, hn0, H0⟩ := youngJetTail 0 0
  obtain ⟨C1, n1, _hC1, hn1, H1⟩ := youngJetTail 1 0
  obtain ⟨C2, n2, _hC2, hn2, H2⟩ := youngJetTail 0 1
  obtain ⟨C3, n3, _hC3, hn3, H3⟩ := youngJetTail 2 0
  obtain ⟨C4, n4, _hC4, hn4, H4⟩ := youngJetTail 1 1
  obtain ⟨C5, n5, _hC5, hn5, H5⟩ := youngJetTail 0 2
  have hBridge : TrainChartBridge := trainChartBridge_of trainVelSmooth_proof
  set CD : ℝ := max C0 (max C1 (max C2 (max C3 (max C4 C5))))
  have hCD1 : 1 ≤ CD := hC0.trans (le_max_left _ _)
  set n_tail : ℝ := min (min n0 (min n1 (min n2 (min n3 (min n4 n5))))) (1 / 180)
  have hn_tail : 0 < n_tail :=
    lt_min (lt_min hn0 (lt_min hn1 (lt_min hn2 (lt_min hn3 (lt_min hn4 hn5))))) (by norm_num)
  have hn_le1 : n_tail ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨CD, n_tail, hCD1, hn_tail, hn_le1, ?_⟩
  intro p d dm dp hreg hν_t' x hx0 hx1 hthr
  have hνpos : 0 < p.ν := p.ν_pos
  have hn180 : p.ν ≤ 1 / 180 := hν_t'.trans (min_le_right _ _)
  obtain ⟨hTd, hRd⟩ := trainDiff p d dm dp hreg x hx0
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hreg
  have hsplit : chartJet (rawProf p) x ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x := by
    rw [rawProf_eq]
    exact chartJet_add_smul hε0 hε1 x hTd hRd
  have hCi : C0 ≤ CD ∧ C1 ≤ CD ∧ C2 ≤ CD ∧ C3 ≤ CD ∧ C4 ≤ CD ∧ C5 ≤ CD := by
    refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
  have hm := min_le_left (min n0 (min n1 (min n2 (min n3 (min n4 n5))))) (1 / 180)
  have hνi : p.ν ≤ n0 ∧ p.ν ≤ n1 ∧ p.ν ≤ n2 ∧ p.ν ≤ n3 ∧ p.ν ≤ n4 ∧ p.ν ≤ n5 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hν_t'.trans (hm.trans (min_le_left _ _))
    · exact hν_t'.trans (hm.trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact hν_t'.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
    · exact hν_t'.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
    · exact hν_t'.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    · exact hν_t'.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  obtain ⟨hC0', hC1', hC2', hC3', hC4', hC5'⟩ := hCi
  obtain ⟨hn0', hn1', hn2', hn3', hn4', hn5'⟩ := hνi
  obtain ⟨j00ψ, j00v⟩ := H0 CD hC0' p d dm dp hreg hn0' x hx0 hx1 hthr
  obtain ⟨j10ψ, j10v⟩ := H1 CD hC1' p d dm dp hreg hn1' x hx0 hx1 hthr
  obtain ⟨j01ψ, j01v⟩ := H2 CD hC2' p d dm dp hreg hn2' x hx0 hx1 hthr
  obtain ⟨j20ψ, -⟩ := H3 CD hC3' p d dm dp hreg hn3' x hx0 hx1 hthr
  obtain ⟨j11ψ, -⟩ := H4 CD hC4' p d dm dp hreg hn4' x hx0 hx1 hthr
  obtain ⟨j02ψ, -⟩ := H5 CD hC5' p d dm dp hreg hn5' x hx0 hx1 hthr
  set W : ℝ := (1 + (1 : ℝ)) ^ 3 * (1 + x.2.2 ^ 2) with hW
  set e' : ℝ := Real.exp (-2 / p.ν)
  have hJr : chartJet (raisedMerid p) x =
      |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x| +
        |kAge (raisedProf p) x| := chartJet_smul_m1 x hRd
  have hRB := raisedChartBridge_proof p d dm dp hreg x hx0
  obtain ⟨hb_v, hb_s, hb_q, hb_η⟩ := hBridge p d dm dp hreg x hx0
  have hkv : ‖kAge (trainProf p) x‖ ≤
      2 * x.1 * ‖Axi.dS (trainProf p) x‖ + |x.2.2| * ‖Axi.dEta (trainProf p) x‖ := by
    unfold kAge
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_eq_abs]
  have hJt : chartJet (trainProf p) x ≤
      ‖ageJet 0 0 p.train.v x.1 x.2‖ + (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖ +
        2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖ := by
    unfold chartJet
    have h1 : 2 * x.1 * ‖Axi.dS (trainProf p) x‖ ≤ 2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖ :=
      mul_le_mul_of_nonneg_left hb_s (by linarith)
    have h2 : |x.2.2| * ‖Axi.dEta (trainProf p) x‖ ≤ |x.2.2| * ‖ageJet 0 1 p.train.v x.1 x.2‖ :=
      mul_le_mul_of_nonneg_left hb_η (abs_nonneg _)
    linarith [h1, h2, hkv, hb_v, hb_q, hb_η]
  obtain ⟨w1, w2, w3, w4⟩ := RawCoeffTail.weights hx0.le hx1 (abs_nonneg x.2.2)
  have hsq : x.2.2 ^ 2 = |x.2.2| ^ 2 := (sq_abs _).symm
  rw [← hsq] at w1 w2 w3 w4
  set Spsi : ℝ := ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
    ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
    ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖ with hSpsi
  have hWS : W * Spsi ≤ 6 * (e' / 2) := by
    rw [hSpsi]
    calc W * (‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖)
        = W * ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + W * ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          W * ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + W * ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
          W * ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + W * ‖ageJet 0 2 p.train.ψ x.1 x.2‖ := by ring
      _ ≤ e' / 2 + e' / 2 + e' / 2 + e' / 2 + e' / 2 + e' / 2 := by gcongr
      _ = 6 * (e' / 2) := by ring
  have hSpsi0 : 0 ≤ Spsi := by rw [hSpsi]; positivity
  have hA0 : 0 ≤ 1 + x.1 := by linarith
  have hmain : (1 + x.1) * chartJet (rawProf p) x ≤ 123 * e' := by
    have hJ : chartJet (rawProf p) x ≤
        (‖ageJet 0 0 p.train.v x.1 x.2‖ + (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖ +
          2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) + 20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi := by
      rw [hJr] at hsplit
      linarith
    have e1 : (1 + x.1) * ‖ageJet 0 0 p.train.v x.1 x.2‖ ≤ e' / 2 :=
      (mul_le_mul_of_nonneg_right w1 (norm_nonneg _)).trans j00v
    have e2 : (1 + x.1) * ((2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖) ≤ 3 * (e' / 2) := by
      rw [← mul_assoc]
      calc (1 + x.1) * (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖
          ≤ 3 * W * ‖ageJet 0 1 p.train.v x.1 x.2‖ :=
            mul_le_mul_of_nonneg_right (by rw [hW]; linarith) (norm_nonneg _)
        _ = 3 * (W * ‖ageJet 0 1 p.train.v x.1 x.2‖) := by ring
        _ ≤ 3 * (e' / 2) := by linarith
    have e3 : (1 + x.1) * (2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) ≤ 2 * (e' / 2) := by
      calc (1 + x.1) * (2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖)
          = (1 + x.1) * (2 * x.1) * ‖ageJet 1 0 p.train.v x.1 x.2‖ := by ring
        _ ≤ 2 * W * ‖ageJet 1 0 p.train.v x.1 x.2‖ :=
            mul_le_mul_of_nonneg_right (by rw [hW]; linarith) (norm_nonneg _)
        _ = 2 * (W * ‖ageJet 1 0 p.train.v x.1 x.2‖) := by ring
        _ ≤ 2 * (e' / 2) := by linarith
    have e4 : (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi) ≤ 40 * (6 * (e' / 2)) := by
      calc (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi)
          = (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2) * Spsi := by ring
        _ ≤ 40 * W * Spsi := mul_le_mul_of_nonneg_right (by rw [hW]; linarith) hSpsi0
        _ = 40 * (W * Spsi) := by ring
        _ ≤ 40 * (6 * (e' / 2)) := by linarith
    calc (1 + x.1) * chartJet (rawProf p) x
        ≤ (1 + x.1) * ((‖ageJet 0 0 p.train.v x.1 x.2‖ +
            (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖ +
            2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) +
            20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi) := mul_le_mul_of_nonneg_left hJ hA0
      _ = (1 + x.1) * ‖ageJet 0 0 p.train.v x.1 x.2‖ +
            (1 + x.1) * ((2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖) +
            (1 + x.1) * (2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) +
            (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi) := by ring
      _ ≤ e' / 2 + 3 * (e' / 2) + 2 * (e' / 2) + 40 * (6 * (e' / 2)) := by linarith
      _ = 123 * e' := by ring
  have hexp1 : 123 * e' ≤ 1 := by
    have hbig : (360 : ℝ) ≤ 2 / p.ν := by
      rw [le_div_iff₀ hνpos]
      linarith
    have h1 : 2 / p.ν + 1 ≤ Real.exp (2 / p.ν) := Real.add_one_le_exp _
    have h2 : e' = (Real.exp (2 / p.ν))⁻¹ := by
      show Real.exp (-2 / p.ν) = _
      rw [neg_div, Real.exp_neg]
    rw [h2, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  have hJ0 : 0 ≤ chartJet (rawProf p) x := by
    unfold chartJet
    positivity
  exact (le_mul_of_one_le_left hJ0 (by linarith : 1 ≤ 1 + x.1)).trans (hmain.trans hexp1)

open RawProfJetHelp in
/-- Uniform polynomial bound on `chartJet (rawProf p) x` over `0 < x.1 ≤ 1` and all `(q, η) ∈ ℝ²`
(SP 2419–2423, 2443–2445). -/
theorem rawProf_young_chartJet :
    ∃ (C_y : ℝ) (k_y : ℕ) (ν_y : ℝ), 0 < C_y ∧ 0 < ν_y ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν_y →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ 1 →
          chartJet (rawProf p) x ≤ C_y * (p.ν ^ k_y)⁻¹ := by
  obtain ⟨k_b, C_b, ν_b, hC_b, hν_b, hBox⟩ := rawBoxJet_proof
  obtain ⟨CD, ν_ext, hCD1, hν_ext, hν_ext1, hExt⟩ := rawProf_young_chartJet_ext
  set ν_y : ℝ := min ν_b ν_ext
  have hν_y : 0 < ν_y := lt_min hν_b hν_ext
  set C_y : ℝ := max (C_b * (3 * CD) ^ k_b) 1
  have hC_y : 0 < C_y := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C_y, 3 * k_b, ν_y, hC_y, hν_y, ?_⟩
  intro p d dm dp hreg hν x hx0 hx1
  have hνpos : 0 < p.ν := p.ν_pos
  have hν_b' : p.ν ≤ ν_b := hν.trans (min_le_left _ _)
  have hν_t' : p.ν ≤ ν_ext := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := hν_t'.trans hν_ext1
  obtain ⟨hTd, hRd⟩ := trainDiff p d dm dp hreg x hx0
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hreg
  have hsplit : chartJet (rawProf p) x ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x := by
    rw [rawProf_eq]
    exact chartJet_add_smul hε0 hε1 x hTd hRd
  set Γ : ℝ := (3 * CD) * (p.ν ^ 3)⁻¹
  have hν_inv1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).mpr hν1
  have hν3_le : p.ν ^ 3 ≤ p.ν := by
    calc p.ν ^ 3 = p.ν * p.ν ^ 2 := by ring
      _ ≤ p.ν * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hνpos.le hν1) hνpos.le
      _ = p.ν := mul_one _
  have hν3_inv_ge_inv : p.ν⁻¹ ≤ (p.ν ^ 3)⁻¹ := inv_anti₀ (pow_pos hνpos 3) hν3_le
  have hν3_inv1 : 1 ≤ (p.ν ^ 3)⁻¹ := hν_inv1.trans hν3_inv_ge_inv
  have hΓ1 : 1 ≤ Γ := by
    dsimp [Γ]
    calc (1 : ℝ) ≤ (3 * 1) * 1 := by norm_num
      _ ≤ (3 * CD) * (p.ν ^ 3)⁻¹ :=
          mul_le_mul (by linarith) hν3_inv1 zero_le_one (by positivity)
  have hΓ_inv : p.ν⁻¹ ≤ Γ := by
    dsimp [Γ]
    calc p.ν⁻¹ = 1 * p.ν⁻¹ := (one_mul _).symm
      _ ≤ (3 * CD) * (p.ν ^ 3)⁻¹ :=
          mul_le_mul (by linarith) hν3_inv_ge_inv (inv_nonneg.mpr hνpos.le) (by positivity)
  by_cases hη : |x.2.2| ≤ Γ
  · -- Box region `|η| ≤ Γ`: apply `rawBoxJet_proof`
    have hB := hBox p d dm dp hreg hν_b' Γ hΓ1 hΓ_inv x hx0 (hx1.trans hΓ1) hη
    have hpow : Γ ^ k_b = (3 * CD) ^ k_b * (p.ν ^ (3 * k_b))⁻¹ := by
      dsimp [Γ]
      rw [mul_pow, inv_pow, ← pow_mul]
    calc chartJet (rawProf p) x
        ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x := hsplit
      _ ≤ C_b * Γ ^ k_b := hB
      _ = (C_b * (3 * CD) ^ k_b) * (p.ν ^ (3 * k_b))⁻¹ := by rw [hpow]; ring
      _ ≤ C_y * (p.ν ^ (3 * k_b))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (pow_nonneg hνpos.le _))
  · -- Exterior region `|η| > Γ`: apply `rawProf_young_chartJet_ext`
    have hη' : Γ < |x.2.2| := lt_of_not_ge hη
    have hthr : CD * ((p.ν ^ 2)⁻¹ / p.ν + 2) < |x.2.2| := by
      have hbr : (p.ν ^ 2)⁻¹ / p.ν + 2 ≤ 3 * (p.ν ^ 3)⁻¹ := by
        have heq : (p.ν ^ 2)⁻¹ / p.ν = (p.ν ^ 3)⁻¹ := by
          rw [div_eq_mul_inv, ← mul_inv, show p.ν ^ 2 * p.ν = p.ν ^ 3 by ring]
        rw [heq]
        linarith
      calc CD * ((p.ν ^ 2)⁻¹ / p.ν + 2)
          ≤ CD * (3 * (p.ν ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hbr (by linarith)
        _ = Γ := by dsimp [Γ]; ring
        _ < |x.2.2| := hη'
    have h1_le : chartJet (rawProf p) x ≤ 1 := hExt p d dm dp hreg hν_t' x hx0 hx1 hthr
    have hinv_ge1 : 1 ≤ (p.ν ^ (3 * k_b))⁻¹ :=
      (one_le_inv₀ (pow_pos hνpos _)).mpr (pow_le_one₀ hνpos.le hν1)
    calc chartJet (rawProf p) x ≤ 1 := h1_le
      _ = 1 * 1 := (mul_one _).symm
      _ ≤ C_y * (p.ν ^ (3 * k_b))⁻¹ :=
          mul_le_mul (le_max_right _ _) hinv_ge1 zero_le_one hC_y.le

/-! ## 3. Restricted `hpIndNorm` helper from `lateProfileQuantity` and `GraphBound` -/

/-- General indicator norm bound on a measurable region `E ⊆ Coord` where
`lateProfileQuantity p.ε (rawProf p) x ≤ L` for `0 < x.1` (`p.ν ≤ 1`, `C_phys > 0`). -/
private theorem hpIndNorm_le_of_lateProfileQuantity (hId : KOutChartAe)
    {p : Params} {d dm dp C_phys L : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hC_phys : 0 < C_phys) (hL0 : 0 ≤ L)
    (hPhys : ∀ F : CProf, InHr p.c bgp F →
      (∃ b, InHr p.c bgp b ∧ IsResponse p.ν p.c p.ε 0 bgp F b) ∧
      ∀ b, IsResponse p.ν p.c p.ε 0 bgp F b → GraphBound p.ν p.c bgp p.ε C_phys F b)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hKe : IsKop p Ke) (f : HpR p.c)
    (E : Set Coord) (hE : MeasurableSet E)
    (hptL : ∀ x ∈ E, 0 < x.1 → lateProfileQuantity p.ε (rawProf p) x ≤ L) :
    hpIndNorm p.c E (Ke f) ≤ (3 * C_phys) * (p.ν ^ 1)⁻¹ * L * ‖f‖ := by
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hε_pos : 0 < p.ε := p.ε_pos
  obtain ⟨bε, hb_in, hb_resp, hKout⟩ := hKe f
  have hF_in : InHr p.c bgp (toProf p.c f) := inHr_toProf hc_pos f
  obtain ⟨_Sb, Qb, Eb, _hSb, hQb, hEb, hnorm⟩ := (hPhys (toProf p.c f) hF_in).2 bε hb_resp
  have hg_in : InHr p.c bgp (toProf p.c (Ke f)) := inHr_toProf hc_pos (Ke f)
  have hae : toProf p.c (Ke f) =ᵐ[hMeas p.c bgp] kOutChart p bε Qb Eb :=
    hMeas_ae_of_strip hc_pos (hId p d dm dp hreg bε _ Qb Eb hb_in hg_in hQb hEb hKout)
  have hpt : ∀ x ∈ E, 0 < x.1 →
      ‖kOutChart p bε Qb Eb x‖ ≤
        L * ‖sqrtS Qb x‖ + L * ‖sqrtS Eb x‖ + (2 * L) * ‖bε x‖ :=
    fun x hxE hx0 => kOutChart_norm_le_lateProfileQuantity p bε Qb Eb hx0 hε_pos.le (hptL x hxE hx0)
  have hsq_cont : Continuous fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)
  have hQm : AEStronglyMeasurable (sqrtS Qb) (hMeas p.c bgp) :=
    hsq_cont.aestronglyMeasurable.smul (HasWeakVec.aestronglyMeasurable_hMeas hQb)
  have hEm : AEStronglyMeasurable (sqrtS Eb) (hMeas p.c bgp) :=
    hsq_cont.aestronglyMeasurable.smul (HasWeakVec.aestronglyMeasurable_hMeas hEb)
  have hRes := eLpNorm_restrict_le_graph hc_pos (kOutChart p bε Qb Eb) bε Qb Eb hb_in.meas
    hQm hEm E hE hL0 (by positivity) hpt
  have hF_norm : hNorm p.c bgp (toProf p.c f) = ENNReal.ofReal ‖f‖ := by
    rw [hNorm_toProf hc_pos f, (ofReal_norm f).symm]
  have hν_le_sqrt : p.ν ≤ Real.sqrt p.ν := by
    calc p.ν = Real.sqrt p.ν * Real.sqrt p.ν := (Real.mul_self_sqrt hν_pos.le).symm
      _ ≤ 1 * Real.sqrt p.ν :=
          mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt hν1) (Real.sqrt_nonneg _)
      _ = Real.sqrt p.ν := one_mul _
  have hν_inv_ge_one : 1 ≤ (p.ν ^ 1)⁻¹ := by
    rw [pow_one]
    exact (one_le_inv₀ hν_pos).mpr hν1
  have hb_norm_le : hNorm p.c bgp bε ≤ ENNReal.ofReal (C_phys * (p.ν ^ 1)⁻¹ * ‖f‖) := by
    have h1 : hNorm p.c bgp bε ≤ ENNReal.ofReal C_phys * hNorm p.c bgp (toProf p.c f) :=
      (le_self_add.trans le_self_add).trans hnorm
    rw [hF_norm, ← ENNReal.ofReal_mul hC_phys.le] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    calc C_phys * ‖f‖ = C_phys * 1 * ‖f‖ := by ring
      _ ≤ C_phys * (p.ν ^ 1)⁻¹ * ‖f‖ := by gcongr
  have hgrad_norm_le :
      hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb) ≤
        ENNReal.ofReal (C_phys * (p.ν ^ 1)⁻¹ * ‖f‖) := by
    have h1 : ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) ≤
        ENNReal.ofReal C_phys * ENNReal.ofReal ‖f‖ := by
      rw [← hF_norm]
      calc ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))
          ≤ ENNReal.ofReal (Real.sqrt p.ν) *
              (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := by gcongr
        _ ≤ hNorm p.c bgp bε + hNorm p.c bgp _Sb +
              ENNReal.ofReal (Real.sqrt p.ν) *
                (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := le_add_self
        _ ≤ ENNReal.ofReal C_phys * hNorm p.c bgp (toProf p.c f) := hnorm
    have h_inv_mul : ENNReal.ofReal p.ν⁻¹ * ENNReal.ofReal p.ν = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le), inv_mul_cancel₀ hν_pos.ne',
        ENNReal.ofReal_one]
    calc hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)
        = 1 * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := (one_mul _).symm
      _ = ENNReal.ofReal p.ν⁻¹ *
            (ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))) := by
          rw [← mul_assoc, h_inv_mul]
      _ ≤ ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal C_phys * ENNReal.ofReal ‖f‖) := by gcongr
      _ = ENNReal.ofReal (C_phys * (p.ν ^ 1)⁻¹ * ‖f‖) := by
          rw [pow_one, ← ENNReal.ofReal_mul hC_phys.le,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le)]
          congr 1; ring
  have hRes_toProf :
      eLpNorm (toProf p.c (Ke f)) (ENNReal.ofReal bgp) ((hMeas p.c bgp).restrict E) ≤
        ENNReal.ofReal ((3 * C_phys) * (p.ν ^ 1)⁻¹ * L * ‖f‖) := by
    rw [eLpNorm_congr_ae (ae_restrict_of_ae hae)]
    calc eLpNorm (kOutChart p bε Qb Eb) (ENNReal.ofReal bgp) ((hMeas p.c bgp).restrict E)
        ≤ ENNReal.ofReal L * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) +
            ENNReal.ofReal (2 * L) * hNorm p.c bgp bε := hRes
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (C_phys * (p.ν ^ 1)⁻¹ * ‖f‖) +
            ENNReal.ofReal (2 * L) * ENNReal.ofReal (C_phys * (p.ν ^ 1)⁻¹ * ‖f‖) := by gcongr
      _ = ENNReal.ofReal ((3 * C_phys) * (p.ν ^ 1)⁻¹ * L * ‖f‖) := by
          rw [← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  exact hpIndNorm_le_of_restrict_toProf hc_pos (by positivity) E hE (Ke f) hRes_toProf

/-! ## 4. Conditional assembly of `PhysKopYoungLateBounds` -/

/-- **`PhysKopYoungLateBounds` from `KOutChartAe`** (SP 2434–2437, 2443–2445). -/
theorem physKopYoungLateBounds_of_chartAe (hId : KOutChartAe) : PhysKopYoungLateBounds := by
  intro dm dp hdm _C_late _k_late C_phys _hC_late hC_phys
  obtain ⟨C_y, k_y, ν_y, hC_y, hν_y, hYoung⟩ := rawProf_young_chartJet
  obtain ⟨C_rl, k_rl, ν_rl, hC_rl, hν_rl, hLateProf⟩ := rawProfileLate dm dp hdm
  set C_ke : ℝ := max (9 * C_phys * C_y) (3 * C_phys * C_rl)
  set k_ke : ℕ := max k_y k_rl + 1
  set ν₀ : ℝ := min (min ν_y ν_rl) 1
  have hC_ke : 0 < C_ke := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_y hν_rl) one_pos
  refine ⟨C_ke, k_ke, ν₀, hC_ke, hν₀, ?_⟩
  intro p d hreg hν hε1 _hper _hLate hPhys Ke hKe
  have hν_pos : 0 < p.ν := p.ν_pos
  have hε_pos : 0 < p.ε := p.ε_pos
  have hν_y' : p.ν ≤ ν_y := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_rl' : p.ν ≤ ν_rl := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  constructor
  · -- Young tail: `0 < σ ≤ 1`
    intro σ hσ0 hσ1 f
    set L_y : ℝ := 3 * (C_y * (p.ν ^ k_y)⁻¹) * Real.sqrt σ
    have hLy_nn : 0 ≤ L_y := by positivity
    have hpt_y : ∀ x ∈ youngAgeSet σ, 0 < x.1 →
        lateProfileQuantity p.ε (rawProf p) x ≤ L_y := by
      intro x hxσ hx0
      have hxσ_le : x.1 ≤ σ := le_of_lt hxσ
      have hJ := hYoung p d dm dp hreg hν_y' x hx0 (hxσ_le.trans hσ1)
      calc lateProfileQuantity p.ε (rawProf p) x
          ≤ 3 * chartJet (rawProf p) x * Real.sqrt σ :=
            lateProfileQuantity_le_young (rawProf p) hx0.le hxσ_le hσ1 hε_pos.le hε1
        _ ≤ 3 * (C_y * (p.ν ^ k_y)⁻¹) * Real.sqrt σ := by gcongr
    have hbd := hpIndNorm_le_of_lateProfileQuantity hId hreg hν1 hC_phys hLy_nn hPhys hKe f
      (youngAgeSet σ) (measurableSet_youngAgeSet σ) hpt_y
    have hpow_le : (p.ν ^ (k_y + 1))⁻¹ ≤ (p.ν ^ k_ke)⁻¹ := by
      apply inv_anti₀ (pow_pos hν_pos k_ke)
      exact pow_le_pow_of_le_one hν_pos.le hν1 (Nat.add_le_add_right (le_max_left k_y k_rl) 1)
    have hC_le : 9 * C_phys * C_y ≤ C_ke := le_max_left _ _
    calc hpIndNorm p.c (youngAgeSet σ) (Ke f)
        ≤ (3 * C_phys) * (p.ν ^ 1)⁻¹ * L_y * ‖f‖ := hbd
      _ = (9 * C_phys * C_y) * (p.ν ^ (k_y + 1))⁻¹ * Real.sqrt σ * ‖f‖ := by
          dsimp [L_y]
          rw [pow_add, pow_one, mul_inv]
          ring
      _ ≤ C_ke * (p.ν ^ k_ke)⁻¹ * Real.sqrt σ * ‖f‖ := by gcongr
  · -- Late tail: `1 ≤ S`
    intro S hS1 f
    set L_l : ℝ := C_rl * (p.ν ^ k_rl)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)
    have hS0 : 0 < S := lt_of_lt_of_le one_pos hS1
    have hLl_nn : 0 ≤ L_l := by
      have : 0 ≤ S ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hS0.le _
      positivity
    have hpt_l : ∀ x ∈ lateAgeSet S, 0 < x.1 →
        lateProfileQuantity p.ε (rawProf p) x ≤ L_l := by
      intro x hxS _hx0
      exact (hLateProf p d hreg hν_rl' S hS1 x hxS).2
    have hbd := hpIndNorm_le_of_lateProfileQuantity hId hreg hν1 hC_phys hLl_nn hPhys hKe f
      (lateAgeSet S) (measurableSet_lateAgeSet S) hpt_l
    have hpow_le : (p.ν ^ (k_rl + 1))⁻¹ ≤ (p.ν ^ k_ke)⁻¹ := by
      apply inv_anti₀ (pow_pos hν_pos k_ke)
      exact pow_le_pow_of_le_one hν_pos.le hν1 (Nat.add_le_add_right (le_max_right k_y k_rl) 1)
    have hC_le : 3 * C_phys * C_rl ≤ C_ke := le_max_right _ _
    calc hpIndNorm p.c (lateAgeSet S) (Ke f)
        ≤ (3 * C_phys) * (p.ν ^ 1)⁻¹ * L_l * ‖f‖ := hbd
      _ = (3 * C_phys * C_rl) * (p.ν ^ (k_rl + 1))⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) * ‖f‖ := by
          dsimp [L_l]
          rw [pow_add, pow_one, mul_inv]
          ring
      _ ≤ C_ke * (p.ν ^ k_ke)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) * ‖f‖ := by gcongr

end UnforcedLeray.Short.IIb.PhysKopYLHelp

end
