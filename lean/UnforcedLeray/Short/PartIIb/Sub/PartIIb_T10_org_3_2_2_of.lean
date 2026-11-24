import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_of
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.IBP
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.Units.B0005.Spaces
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `PartII-b:T10/org/3/2/2`: decomposition of `LerayTestComm`

Source `the November 2 reference manuscript`:
lines 1370-1376 (the inverse `ℛ_μ` of `μ + L` is the Laplace integral of the heat-dilation-phase
semigroup `S(t)f(τ - t)`), 1445-1455 (uniqueness of distributional `Y_r` solutions), 1456-1465
and 1472-1473 (the smooth periodic Schwartz class, core integration by parts), 1474-1475
("Leray commutes with heat, dilation and phase translation, so projection preserves all
identities"), 1364-1366 (projected inverse; the adjoint at `r = 2`).

`LerayTestComm` (`Sub/PartII-b_T10_org_3_2_of.lean`): if the Schwartz-type fields `Ψ, Ψ'`
represent `𝐏Φ` and `𝐏((μ̄ + L₀)Φ)`, then `Ψ' = (μ̄ + L₀)Ψ`.  For every phase test `g`
(`⟪·,·⟫` is the bilinear `Y_2` pairing, `L₀ᵗ` the transpose `L0T`):

  `⟪g, Ψ'⟫ = ⟪Ψ', g⟫`                 (symmetry of the pairing, `phasePair_swap_two`)
  `      = ⟪(μ̄ + L₀)Φ, 𝐏g⟫`           (definition of `Ψ'`)
  `      = ⟪Φ, 𝐏(μ̄ + L₀ᵗ)g⟫`          (`lerayOpTestComm_of`: Leray commutes with `L` on tests)
  `      = ⟪Ψ, (μ̄ + L₀ᵗ)g⟫`           (definition of `Ψ`)
  `      = ⟪(μ̄ + L₀ᵗ)g, Ψ⟫`           (symmetry)
  `      = ⟪g, (μ̄ + L₀)Ψ⟫`            (core integration by parts, `schwartzOpGraph`),

and two continuous `L²` slice fields with the same pairings against all phase tests coincide
(`phaseSliceUniqTwo`).  The commutation on tests comes from the resolvent: for `ν > 0`,
`ℛ₁ (1 + L)g = g` (uniqueness) and `𝐏 ℛ₁ = ℛ₁ 𝐏` (`PartIIa.lerayYResolventComm`: Leray commutes
with heat, dilation and phase translation), so `𝐏g = ℛ₁ 𝐏(1 + L)g` solves the equation with datum
`𝐏(1 + L)g` (the leaf `LerayResolventTestComm`).  Its value at `ν = 1, 2` separates the drift and
diffusion commutations, which give the identity for every real `ν, μ` (`lerayOpTestComm_of`).

Everything here is proved except the leaf `LerayResolventTestComm`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LTC

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-! ### Exponent bookkeeping: `conjExp 2 = 2` -/

theorem conjExp_two : conjExp (2 : ℝ≥0∞) = 2 := by
  rw [conjExp, ENNReal.one_sub_inv_two, inv_inv]

theorem isSliceTest_exp {P : ℝ} {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)] (h : r = s)
    {A : ℝ × Space → CVec3} (hA : IsSliceTest P r A) : IsSliceTest P s A := by
  subst h
  exact hA

theorem isPhaseSchwartz_exp {P : ℝ} {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)] (h : r = s)
    {A : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A) : IsPhaseSchwartz P s A := by
  subst h
  exact hA

/-! ### Slice tests -/

section Slice

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem sliceTest_sub {A B : ℝ × Space → CVec3} (hA : IsSliceTest P r A)
    (hB : IsSliceTest P r B) : IsSliceTest P r (A - B) := by
  rw [sub_eq_add_neg]
  exact hA.add hB.neg

theorem testElem_sub_ltc {A B : ℝ × Space → CVec3} (hA : IsSliceTest P r A)
    (hB : IsSliceTest P r B) : testElem P r (A - B) = testElem P r A - testElem P r B := by
  rw [sub_eq_add_neg, testElem_add hA hB.neg, testElem_neg hB, ← sub_eq_add_neg]

end Slice

/-! ### The pairing of two slice tests and its symmetry -/

section Swap

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `phasePair_eq_periodIntegral` for a slice test (the proof only uses the slice property). -/
theorem phasePair_eq_periodIntegral_slice {Φ : ℝ × Space → CVec3}
    (hs : IsSliceTest P (conjExp q) Φ) (f : Yq P q) :
    phasePair P q Φ f =
      P⁻¹ • ∫ t in Ioc (0 : ℝ) (0 + P),
        ∫ y, dotL (Φ (t, y)) ((f (t : AddCircle P) : Space → CVec3) y) := by
  rw [phasePair, phasePairing_apply, testElem_of hs]
  have h1 : (fun τ : AddCircle P => innerPair q
      ((ContinuousMap.toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space)) (conjExp q)
        AddCircle.haarAddCircle ℂ (circleSlice hs)) τ) (f τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => innerPair q (circleSlice hs τ) (f τ) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space))
      (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)] with τ hτ
    rw [hτ]
  rw [integral_congr_ae h1, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage (T := P) (0 : ℝ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [circleSlice_coe, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
  simp only [sliceMap]
  rw [hy]

/-- The pairing of two slice tests is the period average of `∫ A · B dy`. -/
theorem phasePair_slice_testElem {A B : ℝ × Space → CVec3} (hA : IsSliceTest P (conjExp q) A)
    (hB : IsSliceTest P q B) :
    phasePair P q A (testElem P q B) =
      (P⁻¹ : ℝ) • ∫ t in Ioc (0 : ℝ) P, ∫ y, dotL (A (t, y)) (B (t, y)) := by
  rw [phasePair_eq_periodIntegral_slice hA, zero_add]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [PartIIa.testElem_ae_slice hB] with t ht
  exact integral_congr_ae (by filter_upwards [ht] with y hy; rw [hy])

/-- **Symmetry of the bilinear `Y_2` pairing** on `L²` slice tests. -/
theorem phasePair_swap_two {A B : ℝ × Space → CVec3} (hA : IsSliceTest P 2 A)
    (hB : IsSliceTest P 2 B) :
    phasePair P 2 A (testElem P 2 B) = phasePair P 2 B (testElem P 2 A) := by
  rw [phasePair_slice_testElem (isSliceTest_exp conjExp_two.symm hA) hB,
    phasePair_slice_testElem (isSliceTest_exp conjExp_two.symm hB) hA]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [dotL_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Swap

/-! ### Uniqueness of continuous `L²` fields from their test pairings -/

/-- Two continuous `L²` slice fields with the same pairings against all phase tests are equal
(`B0411.eq_of_forall_phasePair`, then continuity of the slices). -/
theorem phaseSliceUniqTwo {P : ℝ} [Fact (0 < P)] {A B : ℝ × Space → CVec3} (hAc : Continuous A)
    (hBc : Continuous B) (hA : IsSliceTest P 2 A) (hB : IsSliceTest P 2 B)
    (h : ∀ g : ℝ × Space → CVec3, IsPhaseTest P g →
      phasePair P 2 g (testElem P 2 A) = phasePair P 2 g (testElem P 2 B)) : A = B := by
  have he : testElem P 2 A = testElem P 2 B := B0411.eq_of_forall_phasePair h
  rw [testElem_of hA, testElem_of hB] at he
  have h3 : circleSlice hA = circleSlice hB := ContinuousMap.toLp_injective _ he
  have h4 : ∀ τ : ℝ, sliceMap hA.2 τ = sliceMap hB.2 τ := fun τ => by
    rw [← circleSlice_coe hA, ← circleSlice_coe hB, h3]
  funext ⟨τ, y⟩
  have h5 := h4 τ
  unfold sliceMap at h5
  rw [MemLp.toLp_eq_toLp_iff] at h5
  have hAτ : Continuous fun y => A (τ, y) := hAc.comp (Continuous.prodMk_right τ)
  have hBτ : Continuous fun y => B (τ, y) := hBc.comp (Continuous.prodMk_right τ)
  have h6 : (fun y => A (τ, y)) = fun y => B (τ, y) :=
    (Continuous.ae_eq_iff_eq volume hAτ hBτ).1 h5
  exact congrFun h6 y

/-! ### The operator `μ̄ + L₀` on Schwartz-type fields -/

theorem isSliceTest_op {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (ν μ : ℝ)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseSchwartz P r Ψ) :
    IsSliceTest P r ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) := by
  rw [op_eq_driftT]
  have e : nuLapT ν Ψ = (ν : ℂ) • lapT Ψ := by
    funext p
    simp [nuLapT, Complex.coe_smul]
  rw [e]
  exact sliceTest_sub (sliceTest_sub (hΨ.sliceTest.const_smul _) hΨ.sliceTest_driftT)
    (hΨ.sliceTest_lapT.const_smul _)

/-! ### Pointwise forms of `c + L₀` and `c + L₀ᵗ` -/

theorem form_L0T (ν : ℝ) (c : ℂ) (Φ : ℝ × Space → CVec3) :
    c • Φ + L0T ν Φ = (c - 1 / 2) • Φ + driftT Φ - nuLapT ν Φ := by
  funext p
  simp only [L0T, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem form_L0 (ν : ℝ) (c : ℂ) (g : ℝ × Space → CVec3) :
    c • g + L0 ν g = (c - 1 / 2) • g + B0005.T0op g - nuLapT ν g := by
  funext p
  simp only [L0, T0, B0005.T0op, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem form_L0T' (ν : ℝ) (c : ℂ) (g : ℝ × Space → CVec3) :
    c • g + L0T ν g = (c + 1) • g - B0005.T0op g - nuLapT ν g := by
  funext p
  simp only [L0T, driftT, B0005.T0op, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem form_L0' (ν : ℝ) (c : ℂ) (Φ : ℝ × Space → CVec3) :
    c • Φ + L0 ν Φ = (c + 1) • Φ - driftT Φ - nuLapT ν Φ := by
  funext p
  simp only [L0, T0, driftT, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem contDiff_op (ν μ : ℝ) {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) := by
  rw [form_L0]
  have h1 : ContDiff ℝ ∞ (((starRingEnd ℂ) (μ : ℂ) - 1 / 2) • Ψ) :=
    hΨ.const_smul ((starRingEnd ℂ) (μ : ℂ) - 1 / 2 : ℂ)
  have h2 : ContDiff ℝ ∞ (B0005.T0op Ψ) := PartIIa.contDiff_T0op hΨ
  have h3 : ContDiff ℝ ∞ (nuLapT ν Ψ) := (contDiff_lapT hΨ).const_smul ν
  exact (h1.add h2).sub h3

/-! ### Integration by parts on Schwartz-type fields (core, lines 1456-1465, 1472-1473) -/

/-- **The classical `c + L₀` of a Schwartz-type field is its distributional one**: for
`IsPhaseSchwartz P q Ψ`, `⟪(c + L₀ᵗ)Φ, Ψ⟫ = ⟪Φ, (c + L₀)Ψ⟫` for every phase test `Φ`
(`PartIIa.schwartzGraphIBP`). -/
theorem schwartzOpGraph (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (ν : ℝ) (c : ℂ)
    (Ψ : ℝ × Space → CVec3) (hΨ : IsPhaseSchwartz P q Ψ) :
    HasPhaseOp (fun Φ => c • Φ + L0T ν Φ) (testElem P q Ψ) (testElem P q (c • Ψ + L0 ν Ψ)) := by
  obtain ⟨hlap, hdrift⟩ := PartIIa.schwartzGraphIBP P q ν Ψ hΨ
  have hS : IsSliceTest P q Ψ := hΨ.sliceTest
  have hT : IsSliceTest P q (B0005.T0op Ψ) := by
    have e : B0005.T0op Ψ = (3 / 2 : ℂ) • Ψ - driftT Ψ := by
      funext p
      simp only [B0005.T0op, driftT, Pi.sub_apply, Pi.smul_apply]
      module
    rw [e]
    exact sliceTest_sub (hS.const_smul _) hΨ.sliceTest_driftT
  have hN : IsSliceTest P q (nuLapT ν Ψ) := by
    have e : nuLapT ν Ψ = (ν : ℂ) • lapT Ψ := by
      funext p
      simp [nuLapT, Complex.coe_smul]
    rw [e]
    exact hΨ.sliceTest_lapT.const_smul _
  intro Φ hΦ
  show phasePair P q (c • Φ + L0T ν Φ) (testElem P q Ψ) =
    phasePair P q Φ (testElem P q (c • Ψ + L0 ν Ψ))
  rw [form_L0T, form_L0,
    phasePair_sub ((hΦ.const_smul (c - 1 / 2)).add hΦ.driftT) (isPhaseTest_nuLapT hΦ ν),
    phasePair_add (hΦ.const_smul (c - 1 / 2)) hΦ.driftT, phasePair_const_smul hΦ,
    testElem_sub_ltc ((hS.const_smul (c - 1 / 2)).add hT) hN,
    testElem_add (hS.const_smul (c - 1 / 2)) hT, testElem_const_smul hS, map_sub, map_add,
    map_smul, smul_eq_mul, hdrift Φ hΦ, hlap Φ hΦ]

/-! ### Leray commutes with `μ̄ + L₀` on tests -/

/-- `⟪Φ, 𝐏 g⟫`: the `Y_2` pairing of a test `Φ` with the Leray projection of a test `g`. -/
def lpair (P : ℝ) [Fact (0 < P)] (Φ g : ℝ × Space → CVec3) : ℂ :=
  phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 g))

section LPair

variable {P : ℝ} [Fact (0 < P)] {Φ Φ' g g' : ℝ × Space → CVec3}

theorem lpair_add_left (hΦ : IsPhaseTest P Φ) (hΦ' : IsPhaseTest P Φ') :
    lpair P (Φ + Φ') g = lpair P Φ g + lpair P Φ' g :=
  phasePair_add hΦ hΦ' _

theorem lpair_sub_left (hΦ : IsPhaseTest P Φ) (hΦ' : IsPhaseTest P Φ') :
    lpair P (Φ - Φ') g = lpair P Φ g - lpair P Φ' g :=
  phasePair_sub hΦ hΦ' _

theorem lpair_smul_left (hΦ : IsPhaseTest P Φ) (c : ℂ) :
    lpair P (c • Φ) g = c * lpair P Φ g :=
  phasePair_const_smul hΦ c _

theorem lpair_nuLapT_left (hΦ : IsPhaseTest P Φ) (ν : ℝ) :
    lpair P (nuLapT ν Φ) g = (ν : ℂ) * lpair P (lapT Φ) g :=
  phasePair_real_smul hΦ.lapT ν _

theorem lpair_add_right (hg : IsSliceTest P 2 g) (hg' : IsSliceTest P 2 g') :
    lpair P Φ (g + g') = lpair P Φ g + lpair P Φ g' := by
  simp only [lpair, testElem_add hg hg', map_add]

theorem lpair_sub_right (hg : IsSliceTest P 2 g) (hg' : IsSliceTest P 2 g') :
    lpair P Φ (g - g') = lpair P Φ g - lpair P Φ g' := by
  simp only [lpair, testElem_sub_ltc hg hg', map_sub]

theorem lpair_smul_right (hg : IsSliceTest P 2 g) (c : ℂ) :
    lpair P Φ (c • g) = c * lpair P Φ g := by
  simp only [lpair, testElem_const_smul hg c, map_smul, smul_eq_mul]

theorem lpair_nuLapT_right (hg : IsSliceTest P 2 (lapT g)) (ν : ℝ) :
    lpair P Φ (nuLapT ν g) = (ν : ℂ) * lpair P Φ (lapT g) := by
  simp only [lpair, nuLapT, testElem_real_smul hg ν, map_smul, smul_eq_mul]

theorem lpair_L0T_left (hΦ : IsPhaseTest P Φ) (ν : ℝ) (c : ℂ) :
    lpair P (c • Φ + L0T ν Φ) g =
      (c - 1 / 2) * lpair P Φ g + lpair P (driftT Φ) g - (ν : ℂ) * lpair P (lapT Φ) g := by
  rw [form_L0T,
    lpair_sub_left ((hΦ.const_smul (c - 1 / 2)).add hΦ.driftT) (isPhaseTest_nuLapT hΦ ν),
    lpair_add_left (hΦ.const_smul (c - 1 / 2)) hΦ.driftT, lpair_smul_left hΦ,
    lpair_nuLapT_left hΦ]

theorem lpair_L0_left (hΦ : IsPhaseTest P Φ) (ν : ℝ) (c : ℂ) :
    lpair P (c • Φ + L0 ν Φ) g =
      (c + 1) * lpair P Φ g - lpair P (driftT Φ) g - (ν : ℂ) * lpair P (lapT Φ) g := by
  rw [form_L0',
    lpair_sub_left ((hΦ.const_smul (c + 1)).sub hΦ.driftT) (isPhaseTest_nuLapT hΦ ν),
    lpair_sub_left (hΦ.const_smul (c + 1)) hΦ.driftT, lpair_smul_left hΦ,
    lpair_nuLapT_left hΦ]

theorem lpair_L0_right (hg : IsPhaseTest P g) (ν : ℝ) (c : ℂ) :
    lpair P Φ (c • g + L0 ν g) =
      (c - 1 / 2) * lpair P Φ g + lpair P Φ (B0005.T0op g) -
        (ν : ℂ) * lpair P Φ (lapT g) := by
  have hg2 : IsSliceTest P 2 g := hg.isSliceTest 2
  have hT : IsSliceTest P 2 (B0005.T0op g) := (B0005.IsPhaseTest.T0op hg).isSliceTest 2
  rw [form_L0,
    lpair_sub_right ((hg2.const_smul (c - 1 / 2)).add hT)
      ((isPhaseTest_nuLapT hg ν).isSliceTest 2),
    lpair_add_right (hg2.const_smul (c - 1 / 2)) hT, lpair_smul_right hg2,
    lpair_nuLapT_right (hg.lapT.isSliceTest 2)]

theorem lpair_L0T_right (hg : IsPhaseTest P g) (ν : ℝ) (c : ℂ) :
    lpair P Φ (c • g + L0T ν g) =
      (c + 1) * lpair P Φ g - lpair P Φ (B0005.T0op g) - (ν : ℂ) * lpair P Φ (lapT g) := by
  have hg2 : IsSliceTest P 2 g := hg.isSliceTest 2
  have hT : IsSliceTest P 2 (B0005.T0op g) := (B0005.IsPhaseTest.T0op hg).isSliceTest 2
  rw [form_L0T',
    lpair_sub_right (sliceTest_sub (hg2.const_smul (c + 1)) hT)
      ((isPhaseTest_nuLapT hg ν).isSliceTest 2),
    lpair_sub_right (hg2.const_smul (c + 1)) hT, lpair_smul_right hg2,
    lpair_nuLapT_right (hg.lapT.isSliceTest 2)]

end LPair

/-- **Leaf: Leray commutes with `1 + L` on tests** (lines 1370-1376, 1445-1455, 1474-1475): for
`ν > 0` and phase tests `Φ, g`, `⟪(1 + L₀ᵗ)Φ, 𝐏g⟫ = ⟪Φ, 𝐏(1 + L₀)g⟫`, i.e. `𝐏g` solves
`(1 + L)w = 𝐏(1 + L)g` in distributions.  Proof: the Laplace integral `ℛ₁` of the
heat-dilation-phase semigroup (`PartIIa.bodyResolvent_exists` at `r = 2`, `μ = 1`) solves the
equation (`PartIIa.bodyResolvent_solves`); by uniqueness (`PartIIa.bodyOp_uniqueness`) and core
integration by parts (`schwartzOpGraph`), `ℛ₁ (1 + L)g = g`; Leray commutes with `ℛ₁`
(`PartIIa.lerayYResolventComm`), so `𝐏g = ℛ₁ 𝐏(1 + L)g`. -/
def LerayResolventTestComm : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ Φ g : ℝ × Space → CVec3,
    IsPhaseTest P Φ → IsPhaseTest P g →
      phasePair P 2 ((1 : ℂ) • Φ + L0T ν Φ)
          (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 g)) =
        phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
          (testElem P 2 ((1 : ℂ) • g + L0 ν g)))

/-- **Leray commutes with `μ̄ + L₀` on tests**, for all real `ν, μ` (line 1474-1475):
`⟪Φ, 𝐏(μ̄ + L₀ᵗ)g⟫ = ⟪(μ̄ + L₀)Φ, 𝐏g⟫`. -/
def LerayOpTestComm : Prop :=
  ∀ (P ν μ : ℝ) [Fact (0 < P)] (Φ g : ℝ × Space → CVec3), IsPhaseTest P Φ → IsPhaseTest P g →
    phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
        (testElem P 2 ((starRingEnd ℂ) (μ : ℂ) • g + L0T ν g))) =
      phasePair P 2 ((starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 g))

/-- The resolvent identity at `ν = 1` and `ν = 2` separates the drift commutation
`⟪T₀ᵗΦ, 𝐏g⟫ = ⟪Φ, 𝐏T₀g⟫` from the diffusion commutation `⟪ΔΦ, 𝐏g⟫ = ⟪Φ, 𝐏Δg⟫`; together they
give the commutation with `μ̄ + L₀` for every real `ν, μ`. -/
theorem lerayOpTestComm_of (hD : LerayResolventTestComm) : LerayOpTestComm := by
  intro P ν μ _ Φ g hΦ hg
  have key : ∀ ν' : ℝ, 0 < ν' →
      lpair P (driftT Φ) g - lpair P Φ (B0005.T0op g) =
        (ν' : ℂ) * (lpair P (lapT Φ) g - lpair P Φ (lapT g)) := by
    intro ν' hν'
    have h : lpair P ((1 : ℂ) • Φ + L0T ν' Φ) g = lpair P Φ ((1 : ℂ) • g + L0 ν' g) :=
      hD P ν' hν' Φ g hΦ hg
    rw [lpair_L0T_left hΦ, lpair_L0_right hg] at h
    linear_combination h
  have hX := key 1 one_pos
  have hY := key 2 two_pos
  push_cast at hX hY
  have hlap : lpair P (lapT Φ) g = lpair P Φ (lapT g) := by linear_combination hX - hY
  have hdr : lpair P (driftT Φ) g = lpair P Φ (B0005.T0op g) := by
    linear_combination 2 * hX - hY
  show lpair P Φ ((starRingEnd ℂ) (μ : ℂ) • g + L0T ν g) =
    lpair P ((starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ) g
  rw [lpair_L0T_right hg, lpair_L0_left hΦ]
  linear_combination hdr + (ν : ℂ) * hlap

end UnforcedLeray.Short.IIb.LTC

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`LerayTestComm` from the leaf `LerayResolventTestComm`** (lines 1474-1475). -/
theorem lerayTestComm_of (hD : LTC.LerayResolventTestComm) : LerayTestComm := by
  intro P ν μ _ Φ Ψ Ψ' hΦ hΨ hΨ' h1 h2
  have hΨ2 : IsPhaseSchwartz P 2 Ψ := LTC.isPhaseSchwartz_exp LTC.conjExp_two hΨ
  have hΨ'2 : IsPhaseSchwartz P 2 Ψ' := LTC.isPhaseSchwartz_exp LTC.conjExp_two hΨ'
  have hE := LTC.lerayOpTestComm_of hD
  refine LTC.phaseSliceUniqTwo hΨ'.smooth.continuous (LTC.contDiff_op ν μ hΨ.smooth).continuous
    hΨ'2.sliceTest (LTC.isSliceTest_op ν μ hΨ2) fun g hg => ?_
  have hg2 : IsSliceTest P 2 g := hg.isSliceTest 2
  have hop : IsPhaseTest P ((starRingEnd ℂ) (μ : ℂ) • g + L0T ν g) :=
    (hg.const_smul _).add (isPhaseTest_L0T hg ν)
  calc phasePair P 2 g (testElem P 2 Ψ')
      = phasePair P 2 Ψ' (testElem P 2 g) := LTC.phasePair_swap_two hg2 hΨ'2.sliceTest
    _ = phasePair P 2 ((starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ)
          (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 g)) := (h2 _).symm
    _ = phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
          (testElem P 2 ((starRingEnd ℂ) (μ : ℂ) • g + L0T ν g))) := (hE P ν μ Φ g hΦ hg).symm
    _ = phasePair P 2 Ψ (testElem P 2 ((starRingEnd ℂ) (μ : ℂ) • g + L0T ν g)) := h1 _
    _ = phasePair P 2 ((starRingEnd ℂ) (μ : ℂ) • g + L0T ν g) (testElem P 2 Ψ) :=
          LTC.phasePair_swap_two hΨ2.sliceTest (hop.isSliceTest 2)
    _ = phasePair P 2 g (testElem P 2 ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ)) :=
          LTC.schwartzOpGraph P 2 ν _ Ψ hΨ2 g hg

end UnforcedLeray.Short.IIb
