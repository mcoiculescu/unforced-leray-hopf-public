import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Dom

/-!
# `PartIII-b:C/cont/WY/2`: `WardYTransSubDom`, pointwise `μ`-Lipschitz domination of `transField`

Source of record: `the November 2 reference manuscript`
(73 pages), lines 3684-3712, 4181-4214, 5701-5704.

The `μ`-difference analogue of `wardYTransDomG_proved` (`Sub/PartIII-b_C_ward_9_3/S1.lean`) and
`transDomW` (`Sub/PartIII-b_C_ward_9_3/S1/Dom.lean`). On the transition annulus `streamAnn ν R`,
`tcLeibniz` gives `sepComm ν m R χy T = tcComm ν R χy (sepX0 ν m T)` for both `m = μ` and `m = μ'`,
where `tcComm` and `streamCorr` are `μ`-independent linear expressions in the field, its spatial
derivative, and its outward primitive `outPrim`. Applying `SepWSubDom` (at orders `0` and `1`) to
`(μ, μ')` and `(μ + 1, μ' + 1)` bounds the differences by `|μ - μ'|` times `transMajA (2(-1/8)+2)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Order-`0` `μ`-Lipschitz domination without the finiteness hypothesis (`C0 + 1 > 0`). -/
private theorem sepWSubDom_zero (hSub : SepWSubDom) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν μ μ' rOut rIn P : ℝ),
      0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T →
      ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
        ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
            iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y‖ₑ ≤
          ENNReal.ofReal (C0 * |μ - μ'|) *
            IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y := by
  obtain ⟨C0, hC0, hSub0⟩ := hSub 0
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy
  by_cases hmu : μ = μ'
  · subst hmu; simp
  by_cases hfin : IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤
  · refine (hSub0 ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy hfin).trans ?_
    gcongr
    linarith
  · have hpos : 0 < (C0 + 1) * |μ - μ'| := mul_pos (by linarith) (abs_pos.2 (sub_ne_zero.2 hmu))
    rw [not_lt_top_iff.1 hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top

private theorem norm_iteratedFDeriv_zero_sub' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} (y : E) :
    ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 g y‖ = ‖f y - g y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply, ← map_sub]
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.norm_map _

/-- Pointwise `μ`-Lipschitz domination of `outPrim (sepWre ν μ T - sepWre ν μ' T)` and
`outPrim (sepX0 ν μ T - sepX0 ν μ' T)` by `outMaj (2(-1/8)+2)`. -/
private theorem outPrimSubPointwise (hSub : SepWSubDom) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (ν μ μ' rOut rIn P : ℝ), 0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 ≤ rOut → rOut < rIn → 0 < P →
        ∀ T, IIIa.IsSepSource P rOut T → ∀ (τ r z : ℝ), rIn ≤ r →
          ENNReal.ofReal |outPrim (fun t y' => sepWre ν μ T t y' - sepWre ν μ' T t y') τ r z| ≤
              ENNReal.ofReal (C0 * |μ - μ'|) *
                outMaj (2 * (-1 / 8 : ℝ) + 2) (rIn - rOut) (IIIa.srcNorm T) τ r z ∧
          ENNReal.ofReal |outPrim (fun t y' => sepX0 ν μ T t y' - sepX0 ν μ' T t y') τ r z| ≤
              ENNReal.ofReal (C0 * |μ - μ'|) *
                (2 * outMaj (2 * (-1 / 8 : ℝ) + 2) (rIn - rOut) (IIIa.srcNorm T) τ r z) := by
  obtain ⟨C0, hC0, hdom⟩ := sepWSubDom_zero hSub
  refine ⟨C0, hC0, ?_⟩
  intro ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ r z hr
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  have hcomp : ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' → ∀ ρ : ℝ, rIn ≤ ρ →
      ‖(sepWre ν m T τ !₂[ρ, 0, z] - sepWre ν m' T τ !₂[ρ, 0, z]) 2‖ₑ ≤
        ENNReal.ofReal (C0 * |m - m'|) *
          IIIa.sepDom a0 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z] := by
    intro m m' hm hm' ρ hρ
    have hy : rIn ≤ Real.sqrt ((!₂[ρ, 0, z] : Space) 0 ^ 2 + (!₂[ρ, 0, z] : Space) 1 ^ 2) := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show ρ ^ 2 + (0 : ℝ) ^ 2 = ρ ^ 2 by ring, Real.sqrt_sq (by linarith)]
      exact hρ
    have h1 := hdom ν m m' rOut rIn P hν hm hm' hrO hrr hP T hT τ _ hy
    refine le_trans ?_ h1
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero_sub']
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : ‖(sepWre ν m T τ !₂[ρ, 0, z] - sepWre ν m' T τ !₂[ρ, 0, z]) 2‖ ≤
        ‖(IIIa.sepW ν (m : ℂ) T !₂[ρ, 0, z] τ - IIIa.sepW ν (m' : ℂ) T !₂[ρ, 0, z] τ) 2‖ := by
      simp only [sepWre, PiLp.sub_apply, Pi.sub_apply, ← Complex.sub_re,
        Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    exact h2.trans (norm_le_pi_norm
      (IIIa.sepW ν (m : ℂ) T !₂[ρ, 0, z] τ - IIIa.sepW ν (m' : ℂ) T !₂[ρ, 0, z] τ) 2)
  have hint : ∀ (Z : ℝ → Space → Space) (B : ℝ → ℝ≥0∞),
      (∀ ρ, rIn ≤ ρ → ‖Z τ !₂[ρ, 0, z] 2‖ₑ ≤ B ρ) →
      ENNReal.ofReal |outPrim Z τ r z| ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * B ρ := by
    intro Z B hB
    refine (outPrimAbsLe Z τ r z (by linarith)).trans ?_
    refine setLIntegral_mono' measurableSet_Ioi (fun ρ hρ => ?_)
    exact mul_le_mul' le_rfl (hB ρ (hr.trans (le_of_lt hρ)))
  constructor
  · refine (hint _ (fun ρ => ENNReal.ofReal (C0 * |μ - μ'|) *
      IIIa.sepDom a0 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z])
      (fun ρ hρ => hcomp μ μ' hμ hμ' ρ hρ)).trans ?_
    unfold outMaj
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_of_eq (lintegral_congr fun ρ => ?_)
    ring
  · have hB : ∀ ρ, rIn ≤ ρ →
        ‖(sepX0 ν μ T τ !₂[ρ, 0, z] - sepX0 ν μ' T τ !₂[ρ, 0, z]) 2‖ₑ ≤
          ENNReal.ofReal (C0 * |μ - μ'|) *
            (2 * IIIa.sepDom a0 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z]) := by
      intro ρ hρ
      have e : (sepX0 ν μ T τ !₂[ρ, 0, z] - sepX0 ν μ' T τ !₂[ρ, 0, z]) 2 =
          (sepWre ν μ T τ !₂[ρ, 0, z] - sepWre ν μ' T τ !₂[ρ, 0, z]) 2 -
            (sepWre ν (μ + 1) T τ !₂[ρ, 0, z] - sepWre ν (μ' + 1) T τ !₂[ρ, 0, z]) 2 := by
        rw [sepX0_eq_sub, sepX0_eq_sub]
        simp only [PiLp.sub_apply]
        ring
      rw [e]
      refine enorm_sub_le.trans ?_
      have h1 := hcomp μ μ' hμ hμ' ρ hρ
      have h2 := hcomp (μ + 1) (μ' + 1) (by linarith) (by linarith) ρ hρ
      rw [show (μ + 1) - (μ' + 1) = μ - μ' by ring] at h2
      calc _ ≤ ENNReal.ofReal (C0 * |μ - μ'|) *
              IIIa.sepDom a0 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z] +
            ENNReal.ofReal (C0 * |μ - μ'|) *
              IIIa.sepDom a0 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z] :=
            add_le_add h1 h2
        _ = _ := by rw [← mul_add, ← two_mul]
    refine (hint _ _ hB).trans ?_
    unfold outMaj
    rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by simp),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_of_eq (lintegral_congr fun ρ => ?_)
    ring

/-- Pointwise `μ`-Lipschitz domination of `sepX0` and `fderiv (sepX0)` by `sepDom (2(-1/8)+2)`. -/
private theorem sepX0SubDom (hSub : SepWSubDom) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ μ' rOut rIn P : ℝ), 0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T → ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
        ‖sepX0 ν μ T τ y - sepX0 ν μ' T τ y‖ₑ ≤
            ENNReal.ofReal (C * |μ - μ'|) *
              IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y ∧
          ‖fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y‖ₑ ≤
            ENNReal.ofReal (C * |μ - μ'|) *
              (IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y +
                IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 1 (rIn - rOut) (IIIa.srcNorm T) τ y) := by
  classical
  obtain ⟨A0, hA0, hW0⟩ := hSub 0
  obtain ⟨A1, hA1, hW1⟩ := hSub 1
  have hCpos : 0 < ‖reL‖ * (2 * A0 + 2 * A1) + 1 := by
    have := mul_nonneg (norm_nonneg reL) (by linarith : (0 : ℝ) ≤ 2 * A0 + 2 * A1)
    linarith
  refine ⟨‖reL‖ * (2 * A0 + 2 * A1) + 1, hCpos.le, ?_⟩
  intro ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT hM τ y hry
  by_cases hmu : μ = μ'
  · subst hmu
    exact ⟨by rw [← ofReal_norm]; simp, by rw [← ofReal_norm]; simp⟩
  have hri : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hry
  have hy : y ∈ {y : Space | rOut < ϱ y} := lt_of_lt_of_le hrr hry
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hcdW : ∀ m : ℝ, 0 ≤ m →
      ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (m : ℂ) T z τ) {y : Space | rOut < ϱ y} := by
    intro m hm
    have hmre : -(1 / 4) < ((m : ℂ)).re := by simp only [Complex.ofReal_re]; linarith
    exact contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (m : ℂ) rOut P T hν
      hmre hrO hP hT hM τ i)
  have hWa := hcdW μ hμ
  have hWa' := hcdW μ' hμ'
  have hWb := hcdW (μ + 1) (by linarith)
  have hWb' := hcdW (μ' + 1) (by linarith)
  set f : Space → Fin 3 → ℂ :=
    fun z => IIIa.sepW ν (μ : ℂ) T z τ - IIIa.sepW ν (μ' : ℂ) T z τ
  set g : Space → Fin 3 → ℂ :=
    fun z => IIIa.sepW ν ((μ + 1 : ℝ) : ℂ) T z τ - IIIa.sepW ν ((μ' + 1 : ℝ) : ℂ) T z τ
  have hf : ContDiffOn ℝ 2 f {y : Space | rOut < ϱ y} := hWa.sub hWa'
  have hg : ContDiffOn ℝ 2 g {y : Space | rOut < ϱ y} := hWb.sub hWb'
  have hXsub : (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) =
      fun z => reL (f z - g z) := by
    funext z
    rw [sepX0_eq_reL, sepX0_eq_reL, ← map_sub]
    congr 1
    simp only [f, g]
    push_cast
    abel
  have hder : ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y‖ₑ ≤
        ENNReal.ofReal ‖reL‖ *
          (‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
              iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y‖ₑ +
            ‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν ((μ + 1 : ℝ) : ℂ) T y' τ) y -
              iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν ((μ' + 1 : ℝ) : ℂ) T y' τ) y‖ₑ) := by
    intro j hj
    have h1 := iteratedFDeriv_reL_le hU hf hg hj hy
    rw [← hXsub] at h1
    have hfa : ContDiffAt ℝ j (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y :=
      (hWa.of_le (by exact_mod_cast hj)).contDiffAt (hU.mem_nhds hy)
    have hfa' : ContDiffAt ℝ j (fun z => IIIa.sepW ν (μ' : ℂ) T z τ) y :=
      (hWa'.of_le (by exact_mod_cast hj)).contDiffAt (hU.mem_nhds hy)
    have hgb : ContDiffAt ℝ j (fun z => IIIa.sepW ν ((μ + 1 : ℝ) : ℂ) T z τ) y :=
      (hWb.of_le (by exact_mod_cast hj)).contDiffAt (hU.mem_nhds hy)
    have hgb' : ContDiffAt ℝ j (fun z => IIIa.sepW ν ((μ' + 1 : ℝ) : ℂ) T z τ) y :=
      (hWb'.of_le (by exact_mod_cast hj)).contDiffAt (hU.mem_nhds hy)
    have ef : iteratedFDeriv ℝ j f y =
        iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
          iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y :=
      iteratedFDeriv_sub_apply hfa hfa'
    have eg : iteratedFDeriv ℝ j g y =
        iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν ((μ + 1 : ℝ) : ℂ) T y' τ) y -
          iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν ((μ' + 1 : ℝ) : ℂ) T y' τ) y :=
      iteratedFDeriv_sub_apply hgb hgb'
    rwa [ef, eg] at h1
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  set S0 : ℝ≥0∞ := IIIa.sepDom a0 0 (rIn - rOut) (IIIa.srcNorm T) τ y
  set S1 : ℝ≥0∞ := IIIa.sepDom a0 1 (rIn - rOut) (IIIa.srcNorm T) τ y
  set C : ℝ := ‖reL‖ * (2 * A0 + 2 * A1) + 1 with hC
  have hCne : ENNReal.ofReal (C * |μ - μ'|) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hCpos (abs_pos.2 (sub_ne_zero.2 hmu))
  by_cases hfin : S0 = ⊤
  · constructor
    · rw [hfin, ENNReal.mul_top hCne]
      exact le_top
    · rw [hfin, top_add, ENNReal.mul_top hCne]
      exact le_top
  have hS0lt : S0 < ⊤ := lt_top_iff_ne_top.2 hfin
  have wa0 := hW0 ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hri hS0lt
  have wb0 := hW0 ν (μ + 1) (μ' + 1) rOut rIn P hν (by linarith) (by linarith) hrO hrr hP T hT
    τ y hri hS0lt
  have wa1 := hW1 ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hri hS0lt
  have wb1 := hW1 ν (μ + 1) (μ' + 1) rOut rIn P hν (by linarith) (by linarith) hrO hrr hP T hT
    τ y hri hS0lt
  rw [show (μ + 1) - (μ' + 1) = μ - μ' by ring] at wb0 wb1
  have hA0c : ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A0 * |μ - μ'|) +
        ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A0 * |μ - μ'|) ≤
      ENNReal.ofReal (C * |μ - μ'|) := by
    have h0a : 0 ≤ A0 * |μ - μ'| := mul_nonneg hA0 (abs_nonneg _)
    rw [← ENNReal.ofReal_mul (norm_nonneg reL),
      ← ENNReal.ofReal_add (mul_nonneg (norm_nonneg reL) h0a) (mul_nonneg (norm_nonneg reL) h0a)]
    apply ENNReal.ofReal_le_ofReal
    have := mul_nonneg (mul_nonneg (norm_nonneg reL) hA1) (abs_nonneg (μ - μ'))
    rw [hC]
    nlinarith [abs_nonneg (μ - μ')]
  have hA1c : ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A1 * |μ - μ'|) +
        ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A1 * |μ - μ'|) ≤
      ENNReal.ofReal (C * |μ - μ'|) := by
    have h1a : 0 ≤ A1 * |μ - μ'| := mul_nonneg hA1 (abs_nonneg _)
    rw [← ENNReal.ofReal_mul (norm_nonneg reL),
      ← ENNReal.ofReal_add (mul_nonneg (norm_nonneg reL) h1a) (mul_nonneg (norm_nonneg reL) h1a)]
    apply ENNReal.ofReal_le_ofReal
    have := mul_nonneg (mul_nonneg (norm_nonneg reL) hA0) (abs_nonneg (μ - μ'))
    rw [hC]
    nlinarith [abs_nonneg (μ - μ')]
  have e0 : ‖sepX0 ν μ T τ y - sepX0 ν μ' T τ y‖ₑ =
      ‖iteratedFDeriv ℝ 0 (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
  have e1 : ‖fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y‖ₑ =
      ‖iteratedFDeriv ℝ 1 (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y‖ₑ := by
    have hd1 : DifferentiableAt ℝ (sepX0 ν μ T τ) y :=
      (tcd_X0_cd hν (by linarith) hrO hP hT hM τ hy).differentiableAt (by norm_num)
    have hd2 : DifferentiableAt ℝ (sepX0 ν μ' T τ) y :=
      (tcd_X0_cd hν (by linarith) hrO hP hT hM τ hy).differentiableAt (by norm_num)
    have hfd : fderiv ℝ (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y =
        fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y :=
      fderiv_sub hd1 hd2
    rw [← hfd, ← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_one]
  constructor
  · rw [e0]
    calc ‖iteratedFDeriv ℝ 0 (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y‖ₑ
        ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal (A0 * |μ - μ'|) * S0 +
            ENNReal.ofReal (A0 * |μ - μ'|) * S0) :=
          (hder 0 (by norm_num)).trans (mul_le_mul' le_rfl (add_le_add wa0 wb0))
      _ = (ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A0 * |μ - μ'|) +
            ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A0 * |μ - μ'|)) * S0 := by ring
      _ ≤ ENNReal.ofReal (C * |μ - μ'|) * S0 := mul_le_mul' hA0c le_rfl
  · rw [e1]
    have h1le : ‖iteratedFDeriv ℝ 1 (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y‖ₑ ≤
        ENNReal.ofReal (C * |μ - μ'|) * S1 := by
      calc ‖iteratedFDeriv ℝ 1 (fun z => sepX0 ν μ T τ z - sepX0 ν μ' T τ z) y‖ₑ
          ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal (A1 * |μ - μ'|) * S1 +
              ENNReal.ofReal (A1 * |μ - μ'|) * S1) :=
            (hder 1 (by norm_num)).trans (mul_le_mul' le_rfl (add_le_add wa1 wb1))
        _ = (ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A1 * |μ - μ'|) +
              ENNReal.ofReal ‖reL‖ * ENNReal.ofReal (A1 * |μ - μ'|)) * S1 := by ring
        _ ≤ ENNReal.ofReal (C * |μ - μ'|) * S1 := mul_le_mul' hA1c le_rfl
    exact h1le.trans (mul_le_mul' le_rfl le_add_self)

/-- Integrability of `ρ ↦ ρ * sepWre ν μ T τ (ρ, 0, z)_z` on `(r, ∞)` for `r > rOut`. -/
private theorem sepWre_outPrim_integrable {ν μ rOut P : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ z : ℝ) {r : ℝ} (hrr : rOut < r) :
    IntegrableOn (fun ρ : ℝ => ρ * sepWre ν μ T τ (!₂[ρ, 0, z] : Space) 2) (Ioi r) := by
  obtain ⟨C, hC0, hb⟩ := tcd_X0_bound hν hμ hr0 hP hT hM
  have hD1 : 0 < r - rOut := by linarith
  set κ : ℝ := r / (r - rOut)
  have hrpos : 0 < r := lt_of_le_of_lt hr0 hrr
  have hκ0 : 0 ≤ κ := by positivity
  have hint : IntegrableOn (fun ρ : ℝ => κ * C * (ρ - rOut) ^ (-(3 / 2 : ℝ))) (Ioi r) :=
    (tcd_int_shift rOut r hD1).const_mul _
  have hW := tcd_Wre_cd hν hμ hr0 hP hT hM τ
  have hsub : Ioi r ⊆ Ioi rOut := Ioi_subset_Ioi hrr.le
  have hcont : ContinuousOn (fun ρ : ℝ => ρ * sepWre ν μ T τ (!₂[ρ, 0, z] : Space) 2) (Ioi r) :=
    continuousOn_id.mul ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn
      ((tcd_cont_val hr0 hW z).mono hsub))
  refine Integrable.mono' hint (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
  have hρr : r ≤ ρ := le_of_lt hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le hrpos hρr
  set p : Space := (!₂[ρ, 0, z] : Space)
  have hϱ : ϱ p = ρ := tcd_varrho hρ0.le
  have hy : rOut < ϱ p := by rw [hϱ]; linarith
  set D : ℝ := ρ - rOut
  have hDp : 0 < D := by show 0 < ρ - rOut; linarith
  set w : ℝ := D⁻¹
  have hwp : 0 < w := inv_pos.2 hDp
  have hDw : D * w = 1 := mul_inv_cancel₀ hDp.ne'
  have hρκ : ρ ≤ κ * D := by
    show ρ ≤ r / (r - rOut) * (ρ - rOut)
    rw [div_mul_eq_mul_div, le_div_iff₀ hD1]
    nlinarith
  set u : ℝ := D ^ (-(3 / 2 : ℝ))
  have hu0 : 0 ≤ u := Real.rpow_nonneg hDp.le _
  have hWbd := (hb τ p hy).2
  rw [hϱ] at hWbd
  have sp0 := tcd_rpow_split D hDp 0
  simp only [Nat.cast_zero, sub_zero] at sp0
  have a3 : ‖IIIa.sepW ν (μ : ℂ) T p τ‖ ≤ C * (u * w ^ 1) := by
    simpa [u, w, D, sp0] using hWbd
  have hcomp : |sepWre ν μ T τ p 2| ≤ ‖IIIa.sepW ν (μ : ℂ) T p τ‖ := by
    have h1 : |sepWre ν μ T τ p 2| ≤ ‖IIIa.sepW ν (μ : ℂ) T p τ 2‖ := by
      simpa [sepWre] using Complex.abs_re_le_norm (IIIa.sepW ν (μ : ℂ) T p τ 2)
    exact h1.trans (norm_le_pi_norm (IIIa.sepW ν (μ : ℂ) T p τ) 2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
  calc ρ * |sepWre ν μ T τ p 2| ≤ ρ * (C * (u * w ^ 1)) :=
        mul_le_mul_of_nonneg_left (hcomp.trans a3) hρ0.le
    _ ≤ κ * C * u * w ^ 0 := tcd_alg1 hDw hρκ hC0 hu0 hwp.le 0
    _ = κ * C * u := by ring

private theorem outPrim_sub_eq {Z₁ Z₂ : ℝ → Space → Space} {τ r z : ℝ}
    (h1 : IntegrableOn (fun ρ : ℝ => ρ * Z₁ τ (!₂[ρ, 0, z] : Space) 2) (Ioi r))
    (h2 : IntegrableOn (fun ρ : ℝ => ρ * Z₂ τ (!₂[ρ, 0, z] : Space) 2) (Ioi r)) :
    outPrim Z₁ τ r z - outPrim Z₂ τ r z =
      outPrim (fun t y' => Z₁ t y' - Z₂ t y') τ r z := by
  unfold outPrim
  have e : (fun ρ : ℝ => ρ * (Z₁ τ (!₂[ρ, 0, z] : Space) - Z₂ τ (!₂[ρ, 0, z] : Space)) 2) =
      fun ρ => ρ * Z₁ τ (!₂[ρ, 0, z] : Space) 2 - ρ * Z₂ τ (!₂[ρ, 0, z] : Space) 2 := by
    funext ρ
    simp only [PiLp.sub_apply]
    ring
  rw [e, integral_sub h1 h2]
  ring

/-- `sepComm` `μ`-difference bound on the transition annulus `streamAnn ν R`. -/
private theorem sepCommSubBoundW (ν R : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' P : ℝ), -(1 / 4) < μ → -(1 / 4) < μ' → 0 < P →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), y ∈ streamAnn ν R →
          ‖sepComm ν μ R χy T τ y - sepComm ν μ' R χy T τ y‖ₑ ≤ ENNReal.ofReal C *
            (‖sepX0 ν μ T τ y - sepX0 ν μ' T τ y‖ₑ +
              ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
                ‖fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y‖ₑ +
              ENNReal.ofReal (((R * Real.sqrt ν)⁻¹) ^ 2) *
                ENNReal.ofReal |outPrim (fun t y' => sepX0 ν μ T t y' - sepX0 ν μ' T t y')
                  τ (ϱ y) (y 2)|) := by
  obtain ⟨M, _, hB⟩ := tcCoeffW χy hχ
  have hL0 : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  set W : ℝ := ν * ((R * Real.sqrt ν)⁻¹) ^ 2 with hWdef
  have hW0 : 0 ≤ W := by positivity
  set C0 : ℝ := 100 * M * (1 + W + ν) with hC0def
  have hC0 : 0 ≤ C0 := by positivity
  refine ⟨2 * C0, by positivity, ?_⟩
  intro μ μ' P hμ hμ' hP T hT hM hA τ y hy
  have hctx : TCCtxW μ μ ν μ R P T y :=
    ⟨hμ, hν, trivial, hR, hP, ⟨le_rfl, le_rfl⟩, hT, hM, hA, hy⟩
  have hctx' : TCCtxW μ' μ' ν μ' R P T y :=
    ⟨hμ', hν, trivial, hR, hP, ⟨le_rfl, le_rfl⟩, hT, hM, hA, hy⟩
  have hϱ0 : 0 < ϱ y := lt_of_lt_of_le hL0 hy.1
  obtain ⟨r1, r2, r3, r4⟩ := tcRegW μ μ ν μ R P T τ y hctx
  obtain ⟨i1, i2, i3, i4⟩ := tcIntW μ μ ν μ R P T τ y hctx
  obtain ⟨r1', r2', r3', r4'⟩ := tcRegW μ' μ' ν μ' R P T τ y hctx'
  obtain ⟨i1', i2', i3', i4'⟩ := tcIntW μ' μ' ν μ' R P T τ y hctx'
  have key1 : sepComm ν μ R χy T τ y = tcComm ν R χy (sepX0 ν μ T) τ y :=
    tcLeibniz ν μ R χy hχ hν hR (sepX0 ν μ T) τ y hϱ0 r1 r2 r3 r4 i1 i2 i3 i4
      (tcTimeW μ μ ν μ R P T τ y hctx)
      (tcGrad_of_partsW tcGradX0StructW tcGradX0DecayW μ μ ν μ R P T τ y hctx)
      (tcLapW μ μ ν μ R P T τ y hctx) (tcRadW μ μ ν μ R P T τ y hctx) (μ + 1)
  have key2 : sepComm ν μ' R χy T τ y = tcComm ν R χy (sepX0 ν μ' T) τ y :=
    tcLeibniz ν μ' R χy hχ hν hR (sepX0 ν μ' T) τ y hϱ0 r1' r2' r3' r4' i1' i2' i3' i4'
      (tcTimeW μ' μ' ν μ' R P T τ y hctx')
      (tcGrad_of_partsW tcGradX0StructW tcGradX0DecayW μ' μ' ν μ' R P T τ y hctx')
      (tcLapW μ' μ' ν μ' R P T τ y hctx') (tcRadW μ' μ' ν μ' R P T τ y hctx') (μ' + 1)
  set Z : ℝ → Space → Space := fun t y' => sepX0 ν μ T t y' - sepX0 ν μ' T t y'
  have hfd : fderiv ℝ (Z τ) y = fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y :=
    fderiv_sub (r1.differentiableAt (by norm_num)) (r1'.differentiableAt (by norm_num))
  have hop : outPrim (sepX0 ν μ T) τ (ϱ y) (y 2) - outPrim (sepX0 ν μ' T) τ (ϱ y) (y 2) =
      outPrim Z τ (ϱ y) (y 2) :=
    outPrim_sub_eq i1 i1'
  have htc : tcComm ν R χy (sepX0 ν μ T) τ y - tcComm ν R χy (sepX0 ν μ' T) τ y =
      tcComm ν R χy Z τ y := by
    unfold tcComm
    rw [hfd, ← hop]
    simp only [Z, sub_apply, PiLp.sub_apply, smul_sub]
    have hsm : (tcB1 ν R χy (ϱ y) *
          (outPrim (sepX0 ν μ T) τ (ϱ y) (y 2) - outPrim (sepX0 ν μ' T) τ (ϱ y) (y 2)) +
        tcB2 ν R χy (ϱ y) * (sepX0 ν μ T τ y 2 - sepX0 ν μ' T τ y 2)) •
          (coordinateVector 2 : Space) =
        (tcB1 ν R χy (ϱ y) * outPrim (sepX0 ν μ T) τ (ϱ y) (y 2) +
          tcB2 ν R χy (ϱ y) * sepX0 ν μ T τ y 2) • (coordinateVector 2 : Space) -
        (tcB1 ν R χy (ϱ y) * outPrim (sepX0 ν μ' T) τ (ϱ y) (y 2) +
          tcB2 ν R χy (ϱ y) * sepX0 ν μ' T τ y 2) • (coordinateVector 2 : Space) := by
      rw [← sub_smul]
      congr 1
      ring
    rw [hsm]
    abel
  rw [key1, key2, htc]
  unfold tcComm
  obtain ⟨b1, b2, b3, b4⟩ := hB ν R hν hR (ϱ y) hy.1 hy.2
  have hLi : 0 ≤ (R * Real.sqrt ν)⁻¹ := inv_nonneg.2 hL0.le
  have c1 : |tcA1 ν R χy (ϱ y)| ≤ C0 := by
    refine b1.trans ?_
    rw [hC0def]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M) hν.le]
  have c2 : |tcA2 ν R χy (ϱ y)| ≤ C0 * (R * Real.sqrt ν)⁻¹ := by
    refine b2.trans ?_
    rw [hC0def]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) (by linarith : (0 : ℝ) ≤ 1 + W)) hLi,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) hW0) hLi]
  have c3 : |tcB1 ν R χy (ϱ y)| ≤ C0 * ((R * Real.sqrt ν)⁻¹) ^ 2 := by
    refine b3.trans ?_
    rw [hC0def]
    have h2 : 0 ≤ ((R * Real.sqrt ν)⁻¹) ^ 2 := sq_nonneg _
    have : 0 ≤ M * ν * ((R * Real.sqrt ν)⁻¹) ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) hν.le) h2
    nlinarith
  have c4 : |tcB2 ν R χy (ϱ y)| ≤ C0 := by
    refine b4.trans ?_
    rw [hC0def]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M) hν.le]
  have hG' : ‖fderiv ℝ (Z τ) y (radialUnit y)‖ₑ ≤
      ‖fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y‖ₑ := by
    rw [← hfd, ← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖fderiv ℝ (Z τ) y (radialUnit y)‖
        ≤ ‖fderiv ℝ (Z τ) y‖ * ‖radialUnit y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (Z τ) y‖ * 1 :=
          mul_le_mul_of_nonneg_left (tc_radialUnit_norm hϱ0) (norm_nonneg _)
      _ = _ := mul_one _
  exact tc_expr_bound (L := R * Real.sqrt ν) hC0 c1 c2 c3 c4 (Z τ y)
    (fderiv ℝ (Z τ) y (radialUnit y))
    ‖fderiv ℝ (sepX0 ν μ T τ) y - fderiv ℝ (sepX0 ν μ' T τ) y‖ₑ hG'
    (ψ := outPrim Z τ (ϱ y) (y 2))

/-- Pointwise `μ`-Lipschitz domination of `sepTrans ν μ R χy T - sepTrans ν μ' R χy T`. -/
private theorem transSubDomW (hSub : SepWSubDom) (ν R : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR0 : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' P : ℝ), 0 ≤ μ → 0 ≤ μ' → 0 < P →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
          ‖sepTrans ν μ R χy T τ y - sepTrans ν μ' R χy T τ y‖ₑ ≤
            ENNReal.ofReal (C * |μ - μ'|) *
              transMajA (2 * (-1 / 8 : ℝ) + 2) ν R (IIIa.srcNorm T) τ y := by
  classical
  obtain ⟨Cc, hCc0, hCut⟩ := transCutPoint χy hχ
  obtain ⟨Cx, hCx0, hX0⟩ := sepX0SubDom hSub
  obtain ⟨C0, hC00, hOut⟩ := outPrimSubPointwise hSub
  obtain ⟨Cm, hCm0, hComm⟩ := sepCommSubBoundW ν R χy hχ hν hR0
  have hL0 : 0 < transLen ν R := mul_pos hR0 (Real.sqrt_pos.2 hν)
  set p : ℝ := max 1 (transLen ν R)⁻¹
  have hp1 : (1 : ℝ) ≤ p := le_max_left _ _
  have hrp : (transLen ν R)⁻¹ ≤ p := le_max_right _ _
  have hr0 : 0 ≤ (transLen ν R)⁻¹ := inv_nonneg.2 hL0.le
  refine ⟨(Cc * C0 + Cm * (2 * Cx + 2 * C0)) * p ^ (0 + 1),
    mul_nonneg (add_nonneg (mul_nonneg hCc0 hC00) (mul_nonneg hCm0 (by linarith)))
      (pow_nonneg (by linarith) _), ?_⟩
  intro μ μ' P hμ hμ' hP T hT hM hA τ y hy
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  by_cases hann : y ∈ streamAnn ν R
  · have hann' : R * Real.sqrt ν ≤ ϱ y ∧ ϱ y ≤ R * Real.sqrt (5 * ν / 4) := hann
    have hin : R * Real.sqrt ν ≤ ϱ y := hann'.1
    have hrO : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg hR0.le (Real.sqrt_nonneg _)
    have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by linarith) (by linarith)) hR0
    obtain ⟨hXd0, hXd1⟩ :=
      hX0 ν μ μ' (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hμ' hrO hrr hP T hT hM
        τ y hin
    obtain ⟨hOW, hOX⟩ :=
      hOut ν μ μ' (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hμ' hrO hrr hP T
        hT τ (ϱ y) (y 2) hin
    have hIntW1 := sepWre_outPrim_integrable (μ := μ) hν (by linarith) hrO hP hT hM τ (y 2)
      (lt_of_lt_of_le hrr hin)
    have hIntW2 := sepWre_outPrim_integrable (μ := μ') hν (by linarith) hrO hP hT hM τ (y 2)
      (lt_of_lt_of_le hrr hin)
    have hscSub : streamCorr ν R χy (sepWre ν μ T) τ y - streamCorr ν R χy (sepWre ν μ' T) τ y =
        streamCorr ν R χy (fun t y' => sepWre ν μ T t y' - sepWre ν μ' T t y') τ y := by
      unfold streamCorr
      rw [← sub_smul, ← outPrim_sub_eq hIntW1 hIntW2]
      congr 1
      ring
    have hcut := hCut ν R hν hR0 (fun t y' => sepWre ν μ T t y' - sepWre ν μ' T t y') τ y hy
    simp only [Set.indicator_of_mem hann] at hcut
    rw [← hscSub] at hcut
    have hEc : ‖streamCorr ν R χy (sepWre ν μ T) τ y -
          streamCorr ν R χy (sepWre ν μ' T) τ y‖ₑ ≤
        ENNReal.ofReal (Cc * (transLen ν R)⁻¹ ^ 2) *
          (ENNReal.ofReal (C0 * |μ - μ'|) *
            outMaj a0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) :=
      le_trans hcut (tsd_mulL hOW _)
    have hEs : ‖sepComm ν μ R χy T τ y - sepComm ν μ' R χy T τ y‖ₑ ≤
        ENNReal.ofReal (Cm * p ^ 0) *
          (ENNReal.ofReal (Cx * |μ - μ'|) *
              IIIa.sepDom a0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
            ENNReal.ofReal (transLen ν R)⁻¹ *
              (ENNReal.ofReal (Cx * |μ - μ'|) *
                (IIIa.sepDom a0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
                  IIIa.sepDom a0 1 (transGap ν R) (IIIa.srcNorm T) τ y)) +
            ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
              (ENNReal.ofReal (C0 * |μ - μ'|) *
                (2 * outMaj a0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)))) := by
      rw [pow_zero, mul_one]
      refine le_trans (hComm μ μ' P (by linarith) (by linarith) hP T hT hM hA τ y hann) ?_
      exact tsd_mulL
        (add_le_add (add_le_add hXd0 (tsd_mulL hXd1 (ENNReal.ofReal (transLen ν R)⁻¹)))
          (tsd_mulL hOX (ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2)))) _
    have hTM : transMajA a0 ν R (IIIa.srcNorm T) τ y =
        IIIa.sepDom a0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal (transLen ν R)⁻¹ *
            IIIa.sepDom a0 1 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            outMaj a0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2) := by
      simp only [transMajA, Set.indicator_of_mem hann]
    have hST : sepTrans ν μ R χy T τ y - sepTrans ν μ' R χy T τ y =
        (streamCorr ν R χy (sepWre ν μ T) τ y - streamCorr ν R χy (sepWre ν μ' T) τ y) +
          (sepComm ν μ R χy T τ y - sepComm ν μ' R χy T τ y) := by
      change (streamCorr ν R χy (sepWre ν μ T) τ y + sepComm ν μ R χy T τ y) -
        (streamCorr ν R χy (sepWre ν μ' T) τ y + sepComm ν μ' R χy T τ y) = _
      abel
    rw [hST, hTM]
    refine (enorm_add_le _ _).trans ?_
    have hEqC : (Cc * C0 + Cm * (2 * Cx + 2 * C0)) * p ^ (0 + 1) * |μ - μ'| =
        (Cc * (C0 * |μ - μ'|) + Cm * (2 * (Cx * |μ - μ'|) + 2 * (C0 * |μ - μ'|))) * p ^ (0 + 1) := by
      ring
    rw [hEqC]
    exact tsd_abstract Cc (C0 * |μ - μ'|) (Cx * |μ - μ'|) Cm p (transLen ν R)⁻¹ 0 hCc0
      (mul_nonneg hC00 (abs_nonneg _)) (mul_nonneg hCx0 (abs_nonneg _)) hCm0 hp1 hr0 hrp
      _ _ _ _ _ hEc hEs
  · have hc := tsd_case_out ν R y hν hR0 hy hann
    rw [transVanishOff ν μ R χy hχ hν hR0 T τ y hy hc,
      transVanishOff ν μ' R χy hχ hν hR0 T τ y hy hc]
    simp

/-- **Leaf 2** (`PartIII-b:C/cont/WY/2`): `WardYTransSubDom` from `SepWSubDom`. -/
theorem wardYTransSubDom_proved (hSub : SepWSubDom) : WardYTransSubDom := by
  intro ν R c χy hχy hν hR hc
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨C, hC0, hdom⟩ := transSubDomW hSub ν R χy hχ hν hR
  refine ⟨C, hC0, ?_⟩
  intro μ μ' hμ hμ' g hg τ y hy
  have hgm := hg.measurable
  have hpull := chartOfNullPullback R c hR hc _ (ae_iff.1 hg.old)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (R * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by nlinarith
      have hs : ν * (NearInst.chartOf R c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (R ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hper : ∀ τ z, T (τ + 2 * c / R) z = T τ z := by
    intro τ z; unfold T oldCutSrc; rw [oldPhysPeriodic R c g τ z]
  have hsupp : ∀ τ z, R * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) → T τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ R * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold T oldCutSrc; simp only [hz', ite_false]
  have hS : IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6)) T :=
    ⟨oldCutMeasurable R c _ g hgm, hper, hsupp⟩
  have hAx : IsAxiSource T := by
    unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold T oldCutSrc; rw [rot_hRad co si hco z]; split_ifs with hz
      · exact oldPhysRotEquiv co si hco R c g τ z
      · simp
    · unfold T oldCutSrc; rw [refl_hRad z]; split_ifs with hz
      · exact oldPhysReflEquiv R c g τ z
      · simp
  have hresp : ∀ (m : ℂ) (y : Space) (τ : ℝ), IIIa.sepW ν m (oldPhys R c g) y τ = IIIa.sepW ν m T y τ :=
    fun m y τ => sepWCongrAE ν m _ _ hagree y τ
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set I : ℝ≥0∞ := ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) with hI
  have hG2 : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hgm.enorm.pow_const 2
  have hFm : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 :=
    ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG2
  have hAW : ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) = I :=
    ageWeightShift c hc _ hG2
  have hMain := chartPhaseLIntegral R c hR hc _ hFm
  rw [hAW] at hMain
  have hB0 : ∫⁻ τ in Ioc 0 (2 * c / R),
      (∫⁻ y, IIIa.srcNorm T τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) ≤
        ENNReal.ofReal (2 * c / R) * (ENNReal.ofReal (Real.pi * R ^ 2) * I) := by
    rw [← mul_assoc, ← hMain]
    refine lintegral_mono fun τ => ?_
    rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
    exact lintegral_mono fun z => oldCut_sq_le R c _ g τ z
  have hPne : ENNReal.ofReal (2 * c / R) ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  have hX : (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R),
      (∫⁻ y, IIIa.srcNorm T τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) ≤
        ENNReal.ofReal (Real.pi * R ^ 2) * I := by
    calc _ ≤ (ENNReal.ofReal (2 * c / R))⁻¹ * (ENNReal.ofReal (2 * c / R) *
          (ENNReal.ofReal (Real.pi * R ^ 2) * I)) := by gcongr
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hPne ENNReal.ofReal_ne_top, one_mul]
  have hB : IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T) ≤
      ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
    unfold IIIa.ltauLq
    calc ((ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R),
        (∫⁻ y, IIIa.srcNorm T τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (Real.pi * R ^ 2) * I) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
            congr 1
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
          · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
            simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hI]
  have hmom : SepMoment (2 * c / R) T :=
    lt_of_le_of_lt hB (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.memLp.eLpNorm_lt_top)
  have heq1 : transField ν μ R c χy g = sepTrans ν μ R χy T := by
    rw [transField_eq_sepTrans]
    exact sepTrans_congr hresp
  have heq2 : transField ν μ' R c χy g = sepTrans ν μ' R χy T := by
    rw [transField_eq_sepTrans]
    exact sepTrans_congr hresp
  rw [heq1, heq2]
  exact hdom μ μ' (2 * c / R) hμ hμ' hP0 T hS hmom hAx τ y hy

end UnforcedLeray.Short.PartIIIb.Concrete
