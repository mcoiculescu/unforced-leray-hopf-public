import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Tasks.HardyMean
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphFlat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Part II-b, task `PartII-b:F9`: Global flat reconstruction (`FlatReconstruction`, SP 2313–2341)

Source of record: `the November 2 reference manuscript` (SP), lines 2313–2341,
display `short-bg:flat-reconstruction` at line 2326:
  `b_0 + z = Eα + T_0 f,   f = F - s B_v(b_0 + z) - s(∂_s - νΔ)Eα`.

## Proved here (zero `sorry`)

1. `tail_sMeas_neg_nine_eighths`: exact evaluation of the tail integral
   `∫⁻ s in Ioi T, 1 ∂sMeas (-9 / 8) = ENNReal.ofReal (8 * T ^ (-1 / 8 : ℝ))` for `T > 0`
   (SP 2319: `∫_T^∞ s^{-9/8} ds = 8 T^{-1/8}`);
2. `tail_sMeas_lp_le_of_sup`: `L^p((T, ∞), s^{-9/8} ds)` tail bound
   `(∫⁻ s in Ioi T, u s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤ ENNReal.ofReal (8 ^ (4 / 11 : ℝ) * T ^ (-1 / 22 : ℝ) * M)`
   for any `u ≤ M` on `(T, ∞)` (SP 2318–2320);
3. `early_sMeas_lp_le_of_hardyMean`: early-age `L^p((0, T], s^{-9/8} ds)` mean Hardy bound
   `(∫⁻ s in Ioc 0 T, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤ 22 * sLpNorm (13 / 8) T g`
   from `hardyMean_proof` (`PartII-b:T03`, SP 2316–2318);
4. `exp_rate_le_of_le_cLate` and `poly_nu_mono`: monotonicity of the polynomial and exponential
   growth factors in `(C, k, C_late)` for `0 < ν ≤ 1`;
5. `flatReconstruction_of_leaves`: conditional assembly of `FlatReconstruction` from the three
   leaf steps `FlatFreeInteractionStep` (`PartII-b:F9/1`), `FlatColumnHpStep` (`PartII-b:F9/2`),
   `FlatReconstructionIdentityStep` (`PartII-b:F9/3`), together with `TailSourceAndGlobalEnergy`
   (`F7`), `LocalSmoothing` (`F8`), and `profileGraphFlat_proof` (`T14`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Tail integral `∫_T^∞ s^{-9/8} ds = 8 T^{-1/8}` and `L^p(s^{-9/8} ds)` bounds (SP 2316–2320) -/

/-- Exact evaluation of `∫_T^∞ s^{-9/8} ds = 8 T^{-1/8}` against `sMeas (-9 / 8)` for `T > 0`
(SP 2319). -/
theorem tail_sMeas_neg_nine_eighths {T : ℝ} (hT : 0 < T) :
    ∫⁻ _s in Ioi T, (1 : ℝ≥0∞) ∂sMeas (-9 / 8) = ENNReal.ofReal (8 * T ^ (-1 / 8 : ℝ)) := by
  have hφ : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-9 / 8 : ℝ))) := by fun_prop
  unfold sMeas
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hT.le, lintegral_withDensity_eq_lintegral_mul _ hφ measurable_const]
  simp only [Pi.mul_apply, mul_one]
  have hr : (-9 / 8 : ℝ) < -1 := by norm_num
  have hint : IntegrableOn (fun s : ℝ => s ^ (-9 / 8 : ℝ)) (Ioi T) :=
    integrableOn_Ioi_rpow_of_lt hr hT
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi T)] fun s : ℝ => s ^ (-9 / 8 : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      Real.rpow_nonneg (hT.trans hs).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Ioi_rpow_of_lt hr hT]
  congr 1
  have hexp : (-9 / 8 : ℝ) + 1 = -1 / 8 := by norm_num
  rw [hexp]
  ring

/-- Tail `L^p(s^{-9/8} ds)` bound on `(T, ∞)` (`p = bgp = 11/4`, `1/p = 4/11`): if `u(s) ≤ M` on
`s > T > 0`, then
`(∫_T^∞ u(s)^p s^{-9/8} ds)^{4/11} ≤ 8^{4/11} T^{-1/22} M` (SP 2318–2320). -/
theorem tail_sMeas_lp_le_of_sup {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    {u : ℝ → ℝ≥0∞} (hu : ∀ s ∈ Ioi T, u s ≤ ENNReal.ofReal M) :
    (∫⁻ s in Ioi T, u s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
      ENNReal.ofReal (8 ^ (4 / 11 : ℝ) * T ^ (-1 / 22 : ℝ) * M) := by
  have hbgp_pos : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h411_pos : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hmono : ∫⁻ s in Ioi T, u s ^ bgp ∂sMeas (-9 / 8) ≤
      ∫⁻ s in Ioi T, (ENNReal.ofReal M) ^ bgp ∂sMeas (-9 / 8) := by
    refine setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun s hs => ?_)
    exact ENNReal.rpow_le_rpow (hu s hs) hbgp_pos
  have hconst : ∫⁻ s in Ioi T, (ENNReal.ofReal M) ^ bgp ∂sMeas (-9 / 8) =
      (ENNReal.ofReal M) ^ bgp * ∫⁻ s in Ioi T, (1 : ℝ≥0∞) ∂sMeas (-9 / 8) := by
    simp [lintegral_const]
  rw [hconst, tail_sMeas_neg_nine_eighths hT] at hmono
  have hrpow := ENNReal.rpow_le_rpow hmono h411_pos
  rw [ENNReal.mul_rpow_of_nonneg _ _ h411_pos, ← ENNReal.rpow_mul,
    show bgp * (4 / 11 : ℝ) = 1 by norm_num [bgp], ENNReal.rpow_one] at hrpow
  refine hrpow.trans ?_
  have hT_nonneg : 0 ≤ 8 * T ^ (-1 / 8 : ℝ) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hT_nonneg h411_pos,
    ← ENNReal.ofReal_mul hM]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT.le _),
    ← Real.rpow_mul hT.le, show (-1 / 8 : ℝ) * (4 / 11 : ℝ) = -1 / 22 by norm_num]
  ring_nf
  exact le_rfl

/-- Early-age mean Hardy bound on `(0, T]` (`PartII-b:T03`, SP 2316–2318): for any measurable
`g : ℝ → ℝ≥0∞`,
`(∫_0^T (∫_0^s g(t) dt)^p s^{-9/8} ds)^{4/11} ≤ 22 ‖g‖_{L^p((0, T], s^{13/8} ds)}`. -/
theorem early_sMeas_lp_le_of_hardyMean (T : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ s in Ioc 0 T, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
      22 * sLpNorm (13 / 8) T g := by
  set gT : ℝ → ℝ≥0∞ := (Ioc 0 T).indicator g
  have hgT : Measurable gT := hg.indicator measurableSet_Ioc
  have hHM := hardyMean_proof gT hgT
  have h411_pos : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hL : ∫⁻ s in Ioc 0 T, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8) ≤
      ∫⁻ s, (∫⁻ t in Ioc 0 s, gT t) ^ bgp ∂sMeas (-9 / 8) := by
    calc ∫⁻ s in Ioc 0 T, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8)
        = ∫⁻ s in Ioc 0 T, (∫⁻ t in Ioc 0 s, gT t) ^ bgp ∂sMeas (-9 / 8) := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
          congr 1
          refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          have htT : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans hs.2⟩
          exact (Set.indicator_of_mem htT g).symm
      _ ≤ ∫⁻ s, (∫⁻ t in Ioc 0 s, gT t) ^ bgp ∂sMeas (-9 / 8) :=
          setLIntegral_le_lintegral _ _
  have hR : ∫⁻ s, gT s ^ bgp ∂sMeas (13 / 8) =
      ∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8) := by
    have hptw : (fun s => gT s ^ bgp) = (Ioc 0 T).indicator (fun s => g s ^ bgp) := by
      ext s
      by_cases hs : s ∈ Ioc 0 T
      · simp [gT, hs]
      · simp [gT, hs, ENNReal.zero_rpow_of_pos (show (0 : ℝ) < bgp by norm_num [bgp])]
    rw [hptw, lintegral_indicator measurableSet_Ioc]
  calc (∫⁻ s in Ioc 0 T, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ)
      ≤ (∫⁻ s, (∫⁻ t in Ioc 0 s, gT t) ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) :=
        ENNReal.rpow_le_rpow hL h411_pos
    _ ≤ 22 * (∫⁻ s, gT s ^ bgp ∂sMeas (13 / 8)) ^ (4 / 11 : ℝ) := hHM
    _ = 22 * sLpNorm (13 / 8) T g := by
        unfold sLpNorm
        rw [hR]

/-- Monotonicity of the exponential growth factor in `C_late` when `0 < Sig` and `0 < ν`. -/
theorem exp_rate_le_of_le_cLate {a' Sig C₁ C₂ ν : ℝ}
    (hSig : 0 < Sig) (hν : 0 < ν) (hC : C₁ ≤ C₂) :
    Real.exp ((a' * Sig + C₁ / (1 + Sig)) / ν + C₁ * ν ^ 3) ≤
      Real.exp ((a' * Sig + C₂ / (1 + Sig)) / ν + C₂ * ν ^ 3) := by
  apply Real.exp_le_exp.mpr
  have h1Sig : 0 < 1 + Sig := by linarith
  have hdiv1 : C₁ / (1 + Sig) ≤ C₂ / (1 + Sig) := div_le_div_of_nonneg_right hC h1Sig.le
  have hdiv2 : (a' * Sig + C₁ / (1 + Sig)) / ν ≤ (a' * Sig + C₂ / (1 + Sig)) / ν :=
    div_le_div_of_nonneg_right (by linarith) hν.le
  have hmul : C₁ * ν ^ 3 ≤ C₂ * ν ^ 3 := mul_le_mul_of_nonneg_right hC (by positivity)
  linarith

/-- Monotonicity of `C * (ν ^ k)⁻¹` in `(C, k)` when `0 < ν ≤ 1`. -/
theorem poly_nu_mono {C₁ C₂ ν : ℝ} {k₁ k₂ : ℕ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hk : k₁ ≤ k₂) :
    C₁ * (ν ^ k₁)⁻¹ ≤ C₂ * (ν ^ k₂)⁻¹ := by
  have hpow : ν ^ k₂ ≤ ν ^ k₁ := pow_le_pow_of_le_one hν0.le hν1 hk
  have hinv : (ν ^ k₁)⁻¹ ≤ (ν ^ k₂)⁻¹ := inv_anti₀ (pow_pos hν0 k₂) hpow
  exact mul_le_mul hC hinv (by positivity) (hC₁.trans hC)

/-! ## 2. Leaf propositions for `PartII-b:F9` (`FlatReconstruction`, SP 2313–2341) -/

/-- **Leaf `PartII-b:F9/1` (`FlatFreeInteractionStep`, SP 2329–2334)**:
for `F ∈ H_p` and `b_0 = T_0 F` (`InFlatClass p.c bgp b0`, `IsFlatResponse p.ν 0 F b0`), the free
convective interaction `s B_v b_0 = flatK p.train b0 b0q b0η` lies in `H_p` and satisfies:
* on `(0, p.H]` (`p.H = Σ / ν`):
  `‖s B_v b_0‖_{H_p(0, H)} ≤ C ν^{-k} (ν^{-1/2} H^{1/2} + H) ‖F‖_{H_p}`;
* on `(p.H, ∞)`:
  `‖s B_v b_0‖_{H_p(H, ∞)} ≤ C ν^{-k} H^{-1/2} (ν^{-1/2} + 1) ‖F‖_{H_p}`. -/
def FlatFreeInteractionStep : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
          ∃ b0q b0η : CProf,
            HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
            InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
            eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
              ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
                hNorm p.c bgp F ∧
            eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
              ENNReal.ofReal
                  (C * (p.ν ^ k)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
                hNorm p.c bgp F

/-- **Leaf `PartII-b:F9/2` (`FlatColumnHpStep`, SP 2328, 2370–2385)**:
each flat inlet column `flatColumn p i = s[(∂_s - νΔ)e_0 + B_v e_0]` lies in `H_p` with polynomial
`ν⁻¹` norm bound `hNorm p.c bgp (flatColumn p i) ≤ C ν^{-k}`. -/
def FlatColumnHpStep : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ i : Fin 2,
          InHr p.c bgp (flatColumn p i) ∧
          hNorm p.c bgp (flatColumn p i) ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹)

/-- **Leaf `PartII-b:F9/3` (`FlatReconstructionIdentityStep`, SP 2316–2328, display 2326)**:
given the free graph bound `ProfileGraphFlat` (`T14`), the `LocalSmoothing` (`F8`) operators and
estimates, the free interaction bound (`F9/1`), and the flat column bound (`F9/2`), construct the
continuous linear reconstruction map `R0 : HpR p.c →L[ℝ] RowSpace p.c` (`F ↦ (f, α)`) satisfying
`‖R0‖ ≤ C ν^{-k} exp((a'Σ + C_late/(1+Σ))/ν + C_late ν³)`, `z - Eα ∈ H_p`, and the exact global
flat response identity `b_0 + z = Eα + T_0 f` with
`f = F - s B_v(b_0 + z) - s(∂_s - νΔ)Eα`. -/
def FlatReconstructionIdentityStep : Prop :=
  ∀ C_late : ℝ, 0 < C_late →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_ge : ℝ) (_k_ge : ℕ) (C_ls : ℝ) (k_ls : ℕ) (C_fl : ℝ)
    (C_fi : ℝ) (k_fi : ℕ) (C_col : ℝ) (k_col : ℕ),
    0 < C_ge → 0 < C_ls → 0 < C_fl → 0 < C_fi → 0 < C_col →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        (∀ F : CProf, InHr p.c bgp F →
          ∃ b, InFlatClass p.c bgp b ∧ IsFlatResponse p.ν 0 F b ∧
            GraphBound p.ν p.c bgp 0 C_fl F b ∧
            ∀ b', InFlatClass p.c bgp b' → IsFlatResponse p.ν 0 F b' → b' =ᵐ[hMeas p.c bgp] b) →
        (∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
          ∃ b0q b0η : CProf,
            HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
            InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
            eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
              ENNReal.ofReal (C_fi * (p.ν ^ k_fi)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
                hNorm p.c bgp F ∧
            eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
              ENNReal.ofReal
                  (C_fi * (p.ν ^ k_fi)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
                hNorm p.c bgp F) →
        (∀ i : Fin 2,
          InHr p.c bgp (flatColumn p i) ∧
          hNorm p.c bgp (flatColumn p i) ≤ ENNReal.ofReal (C_col * (p.ν ^ k_col)⁻¹)) →
        (∃ (αMap : HpR p.c →L[ℝ] E2)
          (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf)
          (D2zOf : Fin 2 → Fin 2 → HpR p.c →ₗ[ℝ] CProf),
          (∀ F : HpR p.c,
            let M_z := C_ls * (p.ν ^ k_ls)⁻¹ *
              Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖
            let gH1_tail :=
              (∫⁻ s in Ioi (max 1 (p.H - 1)),
                sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ)
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
            HasWeakVec vQ0 dZero (zqOf F) (D2zOf 0 0 F) ∧
            HasWeakVec vEta dZero (zqOf F) (D2zOf 0 1 F) ∧
            HasWeakVec vQ0 dZero (zηOf F) (D2zOf 1 0 F) ∧
            HasWeakVec vEta dZero (zηOf F) (D2zOf 1 1 F) ∧
            Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
            Measurable (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ∧
            (∀ s : ℝ, 0 < s →
              sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                ENNReal.ofReal M_z) ∧
            sLpNorm (13 / 8) p.H
                (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ≤
              ENNReal.ofReal M_z ∧
            (∫⁻ s in Ioi p.H,
                sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F) s ^ bgp
                  ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
              ENNReal.ofReal (C_ls * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z) + gH1_tail) ∧
            InHr p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ∧
            hNorm p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ≤
              ENNReal.ofReal M_z)) →
        ∃ R0 : HpR p.c →L[ℝ] RowSpace p.c,
          ‖R0‖ ≤ C * (p.ν ^ k)⁻¹ *
            Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) ∧
          ∀ F : HpR p.c,
            let f : HpR p.c := (WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F)
            let α : E2 := (WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)
            ∃ b0 b0q b0η z zq zη : CProf,
              InFlatClass p.c bgp b0 ∧
              IsFlatResponse p.ν 0 (toProf p.c F) b0 ∧
              HasWeakVec vQ0 dZero b0 b0q ∧
              HasWeakVec vEta dZero b0 b0η ∧
              HasWeakVec vQ0 dZero z zq ∧
              HasWeakVec vEta dZero z zη ∧
              InHr p.c bgp (fun x => z x - inletProf p α x) ∧
              InFlatClass p.c bgp (fun x => b0 x + z x - inletProf p α x) ∧
              IsFlatResponse p.ν 0 (toProf p.c f) (fun x => b0 x + z x - inletProf p α x) ∧
              toProf p.c f =ᵐ[hMeas p.c bgp] fun x =>
                toProf p.c F x -
                  flatK p.train (fun y => b0 y + z y - inletProf p α y)
                    (fun y => b0q y + zq y - inletProfQ p α y)
                    (fun y => b0η y + zη y - inletProfEta p α y) x -
                  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x

/-! ## 3. Conditional assembly of `FlatReconstruction` (`PartII-b:F9`) -/

/-- **Conditional assembly of `FlatReconstruction` (`PartII-b:F9`)** from
`FlatFreeInteractionStep` (`F9/1`), `FlatColumnHpStep` (`F9/2`),
`FlatReconstructionIdentityStep` (`F9/3`), `TailSourceAndGlobalEnergy` (`F7`),
`LocalSmoothing` (`F8`), and the proved `profileGraphFlat_proof` (`T14`). -/
theorem flatReconstruction_of_leaves
    (hFI : FlatFreeInteractionStep)
    (hCol : FlatColumnHpStep)
    (hId : FlatReconstructionIdentityStep)
    (hGE : UnforcedLeray.Short.IIb.TailSourceAndGlobalEnergy)
    (hLS : UnforcedLeray.Short.IIb.LocalSmoothing) :
    UnforcedLeray.Short.IIb.FlatReconstruction := by
  obtain ⟨_hTS, C_late₁, hCl₁, hGE_main⟩ := hGE
  obtain ⟨C_late₂, hCl₂, hLS_main⟩ := hLS
  set C_late : ℝ := max C_late₁ C_late₂
  have hC_late : 0 < C_late := lt_max_of_lt_left hCl₁
  refine ⟨C_late, hC_late, ?_⟩
  intro Sig lam q hSig hEig a' ha'0 ha'lam dm dp hdm
  obtain ⟨C_ge, k_ge, ν_ge, hC_ge, hν_ge, _hGE_p⟩ :=
    hGE_main Sig lam q hSig hEig a' ha'0 ha'lam dm dp hdm
  obtain ⟨C_ls, k_ls, ν_ls, hC_ls, hν_ls, hLS_p⟩ :=
    hLS_main Sig lam q hSig hEig a' ha'0 ha'lam dm dp hdm
  obtain ⟨C_fi, k_fi, ν_fi, hC_fi, hν_fi, hFI_p⟩ :=
    hFI Sig lam q hSig hEig dm dp hdm
  obtain ⟨C_col, k_col, ν_col, hC_col, hν_col, hCol_p⟩ :=
    hCol Sig lam q hSig hEig dm dp hdm
  have hbgp1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hbgp3 : bgp < (3 : ℝ) := by norm_num [bgp]
  have hgap0 : (0 : ℝ) < (0 : ℂ).re + (3 / bgp - 1) / 2 := by norm_num [bgp]
  obtain ⟨C_fl, hC_fl, hFl_p⟩ := profileGraphFlat_proof bgp hbgp1 hbgp3 0 hgap0
  obtain ⟨C_id, k_id, ν_id, hC_id, hν_id, hId_p⟩ :=
    hId C_late hC_late Sig lam q hSig hEig a' ha'0 ha'lam dm dp hdm
      C_ge k_ge C_ls k_ls C_fl C_fi k_fi C_col k_col hC_ge hC_ls hC_fl hC_fi hC_col
  set C : ℝ := max C_id (max C_fi C_col)
  set k : ℕ := max k_id (max k_fi k_col)
  set ν₀ : ℝ := min 1 (min ν_id (min ν_fi (min ν_col (min ν_ge ν_ls))))
  have hC : 0 < C := lt_max_of_lt_left hC_id
  have hν₀ : 0 < ν₀ :=
    lt_min zero_lt_one (lt_min hν_id (lt_min hν_fi (lt_min hν_col (lt_min hν_ge hν_ls))))
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν hSig_p hmode_p
  have hν0 : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have hν_id' : p.ν ≤ ν_id := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_fi' : p.ν ≤ ν_fi :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_col' : p.ν ≤ ν_col :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hν_ls' : p.ν ≤ ν_ls :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hH_pos : 0 < p.H := div_pos (hSig_p.symm ▸ hSig) hν0
  have hFI_inst := hFI_p p d hreg hν_fi' hSig_p hmode_p
  have hCol_inst := hCol_p p d hreg hν_col' hSig_p hmode_p
  have hC_fi_le : C_fi * (p.ν ^ k_fi)⁻¹ ≤ C * (p.ν ^ k)⁻¹ :=
    poly_nu_mono hC_fi.le ((le_max_left _ _).trans (le_max_right _ _)) hν0 hν1
      ((le_max_left _ _).trans (le_max_right _ _))
  have hC_col_le : C_col * (p.ν ^ k_col)⁻¹ ≤ C * (p.ν ^ k)⁻¹ :=
    poly_nu_mono hC_col.le ((le_max_right _ _).trans (le_max_right _ _)) hν0 hν1
      ((le_max_right _ _).trans (le_max_right _ _))
  have hC_id_le : C_id * (p.ν ^ k_id)⁻¹ ≤ C * (p.ν ^ k)⁻¹ :=
    poly_nu_mono hC_id.le (le_max_left _ _) hν0 hν1 (le_max_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro F b0 hF hb0 hResp
    obtain ⟨b0q, b0η, hq, hη, hIn, hEarly, hLate⟩ := hFI_inst F b0 hF hb0 hResp
    refine ⟨b0q, b0η, hq, hη, hIn, hEarly.trans ?_, hLate.trans ?_⟩
    · gcongr
    · gcongr
  · intro i
    obtain ⟨hIn, hNorm_i⟩ := hCol_inst i
    exact ⟨hIn, hNorm_i.trans (ENNReal.ofReal_le_ofReal hC_col_le)⟩
  · have hLS_ext :
        ∃ (αMap : HpR p.c →L[ℝ] E2)
          (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf)
          (D2zOf : Fin 2 → Fin 2 → HpR p.c →ₗ[ℝ] CProf),
          ∀ F : HpR p.c,
            let M_z := C_ls * (p.ν ^ k_ls)⁻¹ *
              Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖
            let gH1_tail :=
              (∫⁻ s in Ioi (max 1 (p.H - 1)),
                sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ)
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
            HasWeakVec vQ0 dZero (zqOf F) (D2zOf 0 0 F) ∧
            HasWeakVec vEta dZero (zqOf F) (D2zOf 0 1 F) ∧
            HasWeakVec vQ0 dZero (zηOf F) (D2zOf 1 0 F) ∧
            HasWeakVec vEta dZero (zηOf F) (D2zOf 1 1 F) ∧
            Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
            Measurable (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ∧
            (∀ s : ℝ, 0 < s →
              sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                ENNReal.ofReal M_z) ∧
            sLpNorm (13 / 8) p.H
                (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ≤
              ENNReal.ofReal M_z ∧
            (∫⁻ s in Ioi p.H,
                sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F) s ^ bgp
                  ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
              ENNReal.ofReal (C_ls * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z) + gH1_tail) ∧
            InHr p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ∧
            hNorm p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ≤
              ENNReal.ofReal M_z := by
      obtain ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, D2zOf, hF⟩ :=
        hLS_p p d hreg hν_ls' hSig_p hmode_p
      refine ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, D2zOf, fun F => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        hz_sup, hz_early, hz_late, hK_in, hK_norm⟩ := hF F
      have hExp_le :
          Real.exp ((a' * Sig + C_late₂ / (1 + Sig)) / p.ν + C_late₂ * p.ν ^ 3) ≤
            Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) :=
        exp_rate_le_of_le_cLate hSig hν0 (le_max_right C_late₁ C_late₂)
      have hMz_le :
          C_ls * (p.ν ^ k_ls)⁻¹ *
            Real.exp ((a' * Sig + C_late₂ / (1 + Sig)) / p.ν + C_late₂ * p.ν ^ 3) * ‖F‖ ≤
          C_ls * (p.ν ^ k_ls)⁻¹ *
            Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖ := by
        gcongr
      have hMz_enn :
          ENNReal.ofReal (C_ls * (p.ν ^ k_ls)⁻¹ *
            Real.exp ((a' * Sig + C_late₂ / (1 + Sig)) / p.ν + C_late₂ * p.ν ^ 3) * ‖F‖) ≤
          ENNReal.ofReal (C_ls * (p.ν ^ k_ls)⁻¹ *
            Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖) :=
        ENNReal.ofReal_le_ofReal hMz_le
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        fun s hs => (hz_sup s hs).trans hMz_enn,
        hz_early.trans hMz_enn,
        hz_late.trans ?_,
        hK_in,
        hK_norm.trans hMz_enn⟩
      gcongr
    obtain ⟨R0, hR0_norm, hR0_spec⟩ :=
      hId_p p d hreg hν_id' hSig_p hmode_p
        (hFl_p p.ν p.c p.ν_pos p.c_pos) hFI_inst hCol_inst hLS_ext
    refine ⟨R0, hR0_norm.trans ?_, hR0_spec⟩
    gcongr

end UnforcedLeray.Short.IIb

end
