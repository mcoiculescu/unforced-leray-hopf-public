import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_N
import UnforcedLeray.Units.B0656.Sobolev

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/a/1`: leaf D from the free transport limit

Source: `the November 2 reference manuscript` (SP) 2919, 2927, 2937-2945,
2962-2964 (cf. the frozen version SP 2104-2110).

`RelFreeTestLimitTo κ planarRelTransportRe` (SP 2962-2964, "compact smooth tests and Duhamel give
direct strong convergence to radial Euler transport in the successive limit"): for a compactly
supported smooth `Φ`, `F_rel τ σ Φ → e^{-γ(τ-σ)} T(τ-σ) Φ`, `γ = Re λ`.

The PDE content is isolated in `FreeMovingTransportLimit`: the *undamped* free cylinder flow of a
real compactly supported smooth test, read in moving variables and zero-extended off the moving
cell, converges in `L²_m` to the radial Euler transport `T(z_t - z_s)` (the moving-frame generator
is `θ⁻¹D + L_{ν,c}`, SP 2861-2863; `θ⁻¹D → 0` on `θ ≥ b`, and the rescaled train velocity is the
central vortex `Ω(|y|) = e^{-|y|²/4}` rotation up to the errors `δ_ν → 0`, SP 2954-2956,
`FmrVelGap`). It is not in Lean (its frozen analogue `IIb.FreeTransportComparison` is also an
open leaf).

`relFreeTestLimit_of` proves leaf D from it:
* `Φ = Φ₁ + iΦ₂` with real compactly supported smooth parts (both sides are `ℂ`-linear);
* for small `ν` the support lies in the entrance cell `d(s)` (`d(s) ≥ ν⁻¹`), the periodization
  `B0656.periodize` is a cylinder test of period `d(s)` and its zero extension is the datum;
* the pin of `IsPeriodizedRelFreeBlockEvol` (`RelFreeNormSub.freeBlock_testW_ae`) is
  `N⁻¹ I_t J_t⁻¹ ω₀(t)`, with `ω₀` the free cylinder flow (`IIb.free_cyl_exists_unique`);
* the normaliser `N = clockN` satisfies `e^{(γ-|Re κ|/b)Δz} ≤ N ≤ e^{(γ+|Re κ|/b)Δz}`
  (`exp_beta0_le_clockN`, `clockN_le_exp`), so `N⁻¹ → e^{-γ(τ-σ)}` uniformly on the block
  (real damping, SP 2919, 2927).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub
  OrgSplit OrgSplit3 OrgSplit3.StrongA RelExteriorSub RelBlockDiagonalSub VariationOfConstantsSub
  RelFreeNormSub

namespace RelFreeTestSub

/-- **Free transport limit on compact smooth tests** (SP 2962-2964; moving equation SP 2861-2863;
velocity errors SP 2954-2956; frozen analogue SP 2104-2110): for a real compactly supported smooth
`φ` in moving variables, in the successive limit `ν → 0` after `b → ∞`, uniformly in the BUC train
and in the ages `0 ≤ s ≤ t` with `θ(t) ≥ b` and `z(t) - z(s) ≤ B`: the free cylinder flow `ω₀`
from any cylinder test datum `f` with `J_s⁻¹ f = φ` on the moving cell `d(s)`, read in moving
variables at age `t` and zero-extended off the cell `d(t)`, is `ε`-close in `L²_m` to the radial
Euler transport `T(z(t) - z(s)) φ`. -/
def FreeMovingTransportLimit : Prop :=
  ∀ m : ℝ, 8 < m → ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
  ∀ Wφ : Planar.L2w m, (⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ)) →
  ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → b ≤ clockTheta ν t → movingZ ν t - movingZ ν s ≤ B →
    ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
      (∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
        JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) y = ((φ y : ℝ) : ℂ)) →
    ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω₀ →
    ∀ X : Planar.L2w m, (⇑X =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
          (JscaleInv (clockA ν t) (fun x => ((ω₀ t x : ℝ) : ℂ))) (cToPlane z)) →
      ‖X - Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ‖ ≤ ε

/-! ## 1. The normaliser on a block -/

/-- Upper bound `N ≤ e^{(γ + |Re κ|/b)Δz}` (companion of `exp_beta0_le_clockN`). -/
theorem clockN_le_exp (P : PlanarData) {ν u r b : ℝ}
    (hν : 0 < ν) (hu : 0 ≤ u) (hur : u ≤ r) (hb0 : 0 < b) (hbr : b ≤ clockTheta ν r) :
    clockN P ν u r ≤
      Real.exp ((P.eigenvalue.re + |P.kappa.re| / b) * (movingZ ν r - movingZ ν u)) := by
  have hr : 0 ≤ r := hu.trans hur
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hθ_le : clockTheta ν r ≤ clockTheta ν u := theta_anti hν hu hur
  have hz_eq : clockTheta ν u - clockTheta ν r = movingZ ν r - movingZ ν u :=
    FrameShortBlockSub.clockTheta_sub_eq_movingZ_sub hν hu hr
  have hz_nonneg : 0 ≤ movingZ ν r - movingZ ν u := by linarith
  set Δz := movingZ ν r - movingZ ν u
  set q := clockTheta ν u / clockTheta ν r
  have hq1 : 1 ≤ q := (one_le_div hθr).2 hθ_le
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hq_exp : q ≤ Real.exp (Δz / b) := by
    have hq_split : q = 1 + Δz / clockTheta ν r := by
      simp only [q, Δz, ← hz_eq]
      rw [one_add_div hθr.ne']
      ring
    have hdiv_le : Δz / clockTheta ν r ≤ Δz / b :=
      div_le_div_of_nonneg_left hz_nonneg hb0 hbr
    calc q = 1 + Δz / clockTheta ν r := hq_split
      _ ≤ 1 + Δz / b := by linarith
      _ ≤ Real.exp (Δz / b) := by linarith [Real.add_one_le_exp (Δz / b)]
  have hrpow : q ^ P.kappa.re ≤ Real.exp ((|P.kappa.re| / b) * Δz) := by
    calc q ^ P.kappa.re ≤ q ^ |P.kappa.re| :=
          Real.rpow_le_rpow_of_exponent_le hq1 (le_abs_self _)
      _ ≤ (Real.exp (Δz / b)) ^ |P.kappa.re| := Real.rpow_le_rpow hq0.le hq_exp (abs_nonneg _)
      _ = Real.exp ((|P.kappa.re| / b) * Δz) := by
          rw [← Real.exp_mul]
          congr 1
          ring
  unfold clockN
  rw [hz_eq]
  calc Real.exp (P.eigenvalue.re * Δz) * q ^ P.kappa.re
      ≤ Real.exp (P.eigenvalue.re * Δz) * Real.exp ((|P.kappa.re| / b) * Δz) :=
        mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le
    _ = Real.exp ((P.eigenvalue.re + |P.kappa.re| / b) * Δz) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- `|N⁻¹ - e^{-γΔ}| ≤ e^{-γΔ} (e^{kΔ} - 1)` and `N⁻¹ ≤ e^{-γΔ} e^{kΔ}`, `k = |Re κ|/b`. -/
theorem clockN_inv_bounds (P : PlanarData) {ν u r b : ℝ}
    (hν : 0 < ν) (hu : 0 ≤ u) (hur : u ≤ r) (hb0 : 0 < b) (hbr : b ≤ clockTheta ν r) :
    (clockN P ν u r)⁻¹ ≤ Real.exp (-P.eigenvalue.re * (movingZ ν r - movingZ ν u)) *
        Real.exp (|P.kappa.re| / b * (movingZ ν r - movingZ ν u)) ∧
      |(clockN P ν u r)⁻¹ - Real.exp (-P.eigenvalue.re * (movingZ ν r - movingZ ν u))| ≤
        Real.exp (-P.eigenvalue.re * (movingZ ν r - movingZ ν u)) *
          (Real.exp (|P.kappa.re| / b * (movingZ ν r - movingZ ν u)) - 1) := by
  have hlo := exp_beta0_le_clockN P hν hu hur hb0 hbr
  have hhi := clockN_le_exp P hν hu hur hb0 hbr
  have hr : 0 ≤ r := hu.trans hur
  have hz_nonneg : 0 ≤ movingZ ν r - movingZ ν u := by
    have := FrameShortBlockSub.clockTheta_sub_eq_movingZ_sub hν hu hr
    have := theta_anti hν hu hur
    linarith
  set Δ := movingZ ν r - movingZ ν u
  set N := clockN P ν u r
  set A := Real.exp (-P.eigenvalue.re * Δ)
  set x := |P.kappa.re| / b * Δ with hxdef
  have hx0 : 0 ≤ x := mul_nonneg (div_nonneg (abs_nonneg _) hb0.le) hz_nonneg
  have hA0 : 0 < A := Real.exp_pos _
  have h1 : N⁻¹ ≤ A * Real.exp x := by
    calc N⁻¹ ≤ (Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * Δ))⁻¹ :=
          inv_anti₀ (Real.exp_pos _) hlo
      _ = A * Real.exp x := by
          rw [← Real.exp_neg, ← Real.exp_add]
          congr 1
          rw [hxdef]
          ring
  have h2 : A * Real.exp (-x) ≤ N⁻¹ := by
    calc A * Real.exp (-x) = (Real.exp ((P.eigenvalue.re + |P.kappa.re| / b) * Δ))⁻¹ := by
          rw [← Real.exp_neg, ← Real.exp_add]
          congr 1
          rw [hxdef]
          ring
      _ ≤ N⁻¹ := inv_anti₀ (clockN_pos P hν hu hr) hhi
  have e1 : 1 - Real.exp (-x) ≤ Real.exp x - 1 := by
    have := Real.one_sub_le_exp_neg x
    have := Real.add_one_le_exp x
    linarith
  refine ⟨h1, abs_sub_le_iff.2 ⟨?_, ?_⟩⟩
  · nlinarith
  · have : A * (1 - Real.exp (-x)) ≤ A * (Real.exp x - 1) := mul_le_mul_of_nonneg_left e1 hA0.le
    nlinarith

/-! ## 2. Real compactly supported tests -/

theorem mem_cell_of_abs_le {d R : ℝ} (hd : 2 * R < d) {y : ℝ × ℝ} (hy : |y.1| ≤ R) :
    y ∈ B0579.cell d := by
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · linarith [neg_abs_le y.1]
  · linarith [le_abs_self y.1]

/-- **Leaf D for a real test**: in the successive limit,
`‖F_rel τ σ Wφ - e^{-γ(τ-σ)} T(τ-σ) Wφ‖ ≤ ε`. -/
theorem realTestLimit (hT : FreeMovingTransportLimit) (κ : PlanarFrameKernels) (P : PlanarData)
    {m : ℝ} (hm : 8 < m) (K : ℝ) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε : 0 < ε)
    {φ : ℝ × ℝ → ℝ} (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ)) :
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ Wφ - planarRelTransportRe P m τ σ Wφ‖ ≤ ε := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  set E := Real.exp (|P.eigenvalue.re| * B) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set ε' := ε / (4 * E) with hε'def
  have hε' : 0 < ε' := by positivity
  set η := min 1 (ε / (2 * E * (‖Wφ‖ + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (2 * E * (‖Wφ‖ + 1)) := min_le_right _ _
  have hlog : 0 < Real.log (1 + η) := Real.log_pos (by linarith)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport φ ⊆ Metric.closedBall 0 R :=
    hφc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨b₁, hb₁, H⟩ := hT m hm B hB ε' hε' φ hφs hφc Wφ hWφ
  refine ⟨max b₁ (|P.kappa.re| * B / Real.log (1 + η)), le_trans hb₁ (le_max_left _ _),
    fun b hb => ?_⟩
  have hb1 : b₁ ≤ b := le_trans (le_max_left _ _) hb
  have hbk : |P.kappa.re| * B / Real.log (1 + η) ≤ b := le_trans (le_max_right _ _) hb
  have hb1' : 1 ≤ b := hb₁.trans hb1
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1'
  obtain ⟨ν₁, hν₁, G⟩ := H b hb1
  refine ⟨min ν₁ (min 1 (1 / (2 * |R| + 1))), lt_min hν₁ (lt_min one_pos (by positivity)),
    fun ν hν _hPF tr htr t₁ t₂ ht₁ h12 hbt hBeq F_rel hF σ τ hσ hστ hτB => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hνν₁ : ν ≤ ν₁ := hν.2.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνR : ν ≤ 1 / (2 * |R| + 1) := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hsI := ageAt_mem_Icc hν0 ht₁ h12 hBeq ⟨hσ, hστ.trans hτB⟩
  have htI := ageAt_mem_Icc hν0 ht₁ h12 hBeq ⟨hσ.trans hστ, hτB⟩
  have hs : 0 ≤ ageAt ν t₁ σ := ht₁.trans hsI.1
  have ht : 0 ≤ ageAt ν t₁ τ := ht₁.trans htI.1
  have hst : ageAt ν t₁ σ ≤ ageAt ν t₁ τ := ageAt_mono_on_block hν0 ht₁ ht₂ hBeq hσ hστ hτB
  have hbt' : b ≤ clockTheta ν (ageAt ν t₁ τ) := hbt.trans (theta_anti hν0 ht htI.2)
  have hΔ : movingZ ν (ageAt ν t₁ τ) - movingZ ν (ageAt ν t₁ σ) = τ - σ := by
    have h1 := movingZ_ageAt_sub hν0 ht₂ hBeq hτB
    have h2 := movingZ_ageAt_sub hν0 ht₂ hBeq (hστ.trans hτB)
    linarith
  have hΔ0 : 0 ≤ τ - σ := sub_nonneg.2 hστ
  have hΔB : τ - σ ≤ B := by linarith
  -- the entrance cell contains the support of `φ`
  have hds2R : 2 * |R| < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := by
    have h1 := StrongA.inv_le_cellLen hν0 hν1 hs hsI.2 hb1' hbt
    have h3 : 2 * |R| + 1 ≤ ν⁻¹ := by
      rw [le_div_iff₀ (by positivity)] at hνR
      rw [← one_div, le_div_iff₀ hν0]
      linarith
    linarith
  have hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := cellLen_pos hν0 hs
  have hsupp : ∀ y : ℝ × ℝ, φ y ≠ 0 → |y.1| ≤ |R| := by
    intro y hy
    have hy' := hR (subset_tsupport φ hy)
    rw [Metric.mem_closedBall, dist_zero_right] at hy'
    exact (norm_fst_le y).trans (hy'.trans (le_abs_self R))
  have hsub : tsupport φ ⊆
      UnforcedLeray.B0656.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) := by
    intro y hy
    have hy' := hR hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy'
    have h1 : |y.1| ≤ |R| := (norm_fst_le y).trans (hy'.trans (le_abs_self R))
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · linarith [neg_abs_le y.1]
    · linarith [le_abs_self y.1]
  -- the periodized test of period `d(s)`
  have P1 := UnforcedLeray.B0656.isPeriodicTest_periodize hds hφs hφc hsub
  have hg : B0579.IsCylTest (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
      (UnforcedLeray.B0656.periodize hds φ) :=
    ⟨P1.smooth, fun x => P1.periodic x.1 x.2, P1.bounded⟩
  have hgφ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
      UnforcedLeray.B0656.periodize hds φ y = φ y := by
    intro y hy
    have h := (Set.mem_prod.1 hy).1
    have hmod : toIcoMod hds (-(cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) / 2)) y.1 =
        y.1 := (toIcoMod_eq_self hds).2 ⟨h.1, by linarith [h.2]⟩
    simp only [UnforcedLeray.B0656.periodize]
    rw [hmod]
  have hWeq : testW m hg = Wφ := by
    refine Lp.ext ?_
    filter_upwards [coeFn_testW m hg, (Planar.wMeasure_ac m).ae_le hWφ] with z hz1 hz2
    rw [hz1, hz2]
    by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
    · simp only [cellZeroExt, Set.indicator_of_mem hmem, hgφ _ hmem]
    · have h0 : φ (cToPlane z) = 0 := by
        by_contra hne
        exact hmem (mem_cell_of_abs_le hds2R (hsupp _ hne))
      simp only [cellZeroExt, Set.indicator_of_notMem hmem, h0, Complex.ofReal_zero]
  -- the free cylinder flow and the pin
  have ha : 0 < clockA ν (ageAt ν t₁ σ) := by unfold clockA; positivity
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hf : B0579.IsCylTest (ν ^ (-2 : ℝ))
      (rescaleTest (clockA ν (ageAt ν t₁ σ)) (UnforcedLeray.B0656.periodize hds φ)) :=
    isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha hg
  obtain ⟨⟨ω₀, hω₀⟩, -⟩ := UnforcedLeray.Short.IIb.free_cyl_exists_unique m ν (ν ^ (-2 : ℝ)) hm
    hν0 hc tr htr (ageAt ν t₁ σ) hs _ (hf.memLp m)
  have hae := freeBlock_testW_ae hF hν0 hσ hστ hτB hs ht hg hω₀
  have hVm : MemLp (JscaleInv (clockA ν (ageAt ν t₁ τ))
        (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ))) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m) :=
    ComplCouplingSub.memLp_JscaleInv hm0 (one_le_clockA hν0.le ht)
      (show MemLp (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) from (hω₀.memX _ hst).ofReal (K := ℂ))
  have hXm := memLp_cellZeroExt_cToPlane (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m hVm
  set X : Planar.L2w m := hXm.toLp _ with hXdef
  have hXae := (Planar.volume_ac m).ae_le hXm.coeFn_toLp
  -- the free transport limit
  have hagree : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
      JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((rescaleTest (clockA ν (ageAt ν t₁ σ))
        (UnforcedLeray.B0656.periodize hds φ) x : ℝ) : ℂ)) y = ((φ y : ℝ) : ℂ) := by
    intro y hy
    rw [← hgφ y hy]
    exact jscaleInv_rescale ha _ y
  have hPDE := G ν ⟨hν0, hνν₁⟩ tr htr (ageAt ν t₁ σ) (ageAt ν t₁ τ) hs hst hbt'
    (by rw [hΔ]; exact hΔB) _ hf hagree ω₀ hω₀ X hXae
  rw [hΔ] at hPDE
  -- `F_rel τ σ Wφ = N⁻¹ • X`
  have hN : 0 < clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) := clockN_pos P hν0 hs ht
  have hFW : F_rel τ σ Wφ = ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ)⁻¹) • X := by
    rw [← hWeq]
    refine Lp.ext ?_
    filter_upwards [(Planar.wMeasure_ac m).ae_le hae,
      Lp.coeFn_smul ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ)⁻¹) X,
      hXm.coeFn_toLp] with z hz1 hz2 hz3
    rw [hz1, hz2, Pi.smul_apply, hz3, smul_eq_mul]
  have hT0 : planarRelTransportRe P m τ σ Wφ =
      ((Real.exp (-P.eigenvalue.re * (τ - σ)) : ℝ) : ℂ) •
        Planar.transportGroupW m (τ - σ) Wφ := rfl
  rw [hFW, hT0]
  -- the normaliser bounds
  obtain ⟨hNle, hNabs⟩ := clockN_inv_bounds P hν0 hs hst hb0 hbt'
  rw [hΔ] at hNle hNabs
  set N := clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) with hNdef
  set A := Real.exp (-P.eigenvalue.re * (τ - σ)) with hAdef
  set TW := Planar.transportGroupW m (τ - σ) Wφ with hTWdef
  have hsplit : ((N : ℂ))⁻¹ • X - (A : ℂ) • TW =
      ((N⁻¹ : ℝ) : ℂ) • (X - TW) + ((N⁻¹ - A : ℝ) : ℂ) • TW := by
    rw [smul_sub, Complex.ofReal_sub, sub_smul, Complex.ofReal_inv]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 hN.le), Real.norm_eq_abs]
  have hTW : ‖TW‖ ≤ ‖Wφ‖ := by
    calc ‖TW‖ ≤ ‖Planar.transportGroupW m (τ - σ)‖ * ‖Wφ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖Wφ‖ :=
          mul_le_mul_of_nonneg_right (Planar.norm_transportGroupW_le _ _) (norm_nonneg _)
      _ = ‖Wφ‖ := one_mul _
  have hx : Real.exp (|P.kappa.re| / b * (τ - σ)) ≤ 1 + η := by
    have h1 : |P.kappa.re| / b * (τ - σ) ≤ Real.log (1 + η) := by
      have h2 : |P.kappa.re| / b * (τ - σ) ≤ |P.kappa.re| / b * B :=
        mul_le_mul_of_nonneg_left hΔB (div_nonneg (abs_nonneg _) hb0.le)
      have h3 : |P.kappa.re| / b * B ≤ Real.log (1 + η) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
        rw [div_le_iff₀ hlog] at hbk
        linarith [mul_comm (Real.log (1 + η)) b]
      linarith
    calc Real.exp (|P.kappa.re| / b * (τ - σ)) ≤ Real.exp (Real.log (1 + η)) :=
          Real.exp_le_exp.2 h1
      _ = 1 + η := Real.exp_log (by linarith)
  have hA : A ≤ E := by
    refine Real.exp_le_exp.2 ?_
    have h1 : -P.eigenvalue.re * (τ - σ) ≤ |P.eigenvalue.re| * (τ - σ) :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) hΔ0
    have h2 : |P.eigenvalue.re| * (τ - σ) ≤ |P.eigenvalue.re| * B :=
      mul_le_mul_of_nonneg_left hΔB (abs_nonneg _)
    linarith
  have hA0 : 0 < A := Real.exp_pos _
  have hNinv : N⁻¹ ≤ 2 * E := by
    calc N⁻¹ ≤ A * Real.exp (|P.kappa.re| / b * (τ - σ)) := hNle
      _ ≤ E * (1 + η) := mul_le_mul hA hx (Real.exp_pos _).le hE0.le
      _ ≤ E * 2 := mul_le_mul_of_nonneg_left (by linarith) hE0.le
      _ = 2 * E := mul_comm _ _
  have hx1 : 1 ≤ Real.exp (|P.kappa.re| / b * (τ - σ)) :=
    Real.one_le_exp (mul_nonneg (div_nonneg (abs_nonneg P.kappa.re) hb0.le) hΔ0)
  have habs : |N⁻¹ - A| ≤ E * η := by
    calc |N⁻¹ - A| ≤ A * (Real.exp (|P.kappa.re| / b * (τ - σ)) - 1) := hNabs
      _ ≤ E * η := mul_le_mul hA (by linarith) (by linarith) hE0.le
  have hXT : ‖X - TW‖ ≤ ε' := hPDE
  have e1 : N⁻¹ * ‖X - TW‖ ≤ ε / 2 := by
    calc N⁻¹ * ‖X - TW‖ ≤ (2 * E) * ε' :=
          mul_le_mul hNinv hXT (norm_nonneg _) (by positivity)
      _ = ε / 2 := by rw [hε'def]; field_simp; ring
  have e2 : |N⁻¹ - A| * ‖TW‖ ≤ ε / 2 := by
    have h1 : |N⁻¹ - A| * ‖TW‖ ≤ (E * η) * (‖Wφ‖ + 1) :=
      mul_le_mul habs (by linarith) (norm_nonneg _) (by positivity)
    have h2 : η * (2 * E * (‖Wφ‖ + 1)) ≤ ε := by
      rw [le_div_iff₀ (by positivity)] at hηε
      exact hηε
    nlinarith
  linarith

/-! ## 3. Leaf D -/

/-- **Leaf D from the free transport limit** (SP 2962-2964): `FreeMovingTransportLimit` implies
`RelFreeTestLimitTo κ planarRelTransportRe`. -/
theorem relFreeTestLimit_of (hT : FreeMovingTransportLimit) (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.StrongA.RelFreeTestLimitTo κ
      UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.StrongA.planarRelTransportRe := by
  intro _hκ P _hP m hm K B hB ε hε Φ hΦs hΦc W hW
  have : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  have hcs : ∀ g : ℂ → ℝ, g 0 = 0 → HasCompactSupport (fun y : ℝ × ℝ => g (Φ (planeToC y))) := by
    intro g hg0
    refine HasCompactSupport.intro (K := cToPlane '' tsupport Φ)
      (hΦc.isCompact.image continuous_cToPlane) fun y hy => ?_
    have : planeToC y ∉ tsupport Φ := fun h => hy ⟨planeToC y, h, cToPlane_planeToC y⟩
    simp only [image_eq_zero_of_notMem_tsupport this, hg0]
  have hs₁ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (Φ (planeToC y)).re) :=
    Complex.reCLM.contDiff.comp (hΦs.comp contDiff_planeToC)
  have hs₂ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (Φ (planeToC y)).im) :=
    Complex.imCLM.contDiff.comp (hΦs.comp contDiff_planeToC)
  have hc₁ : HasCompactSupport (fun y : ℝ × ℝ => (Φ (planeToC y)).re) :=
    hcs Complex.re Complex.zero_re
  have hc₂ : HasCompactSupport (fun y : ℝ × ℝ => (Φ (planeToC y)).im) :=
    hcs Complex.im Complex.zero_im
  have hm₁ : MemLp (fun z : ℂ => (((Φ z).re : ℝ) : ℂ)) 2 (Planar.wMeasure m) :=
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hΦs.continuous)).memLp_of_hasCompactSupport
      (hΦc.comp_left (g := fun w : ℂ => ((w.re : ℝ) : ℂ)) (by simp))
  have hm₂ : MemLp (fun z : ℂ => (((Φ z).im : ℝ) : ℂ)) 2 (Planar.wMeasure m) :=
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hΦs.continuous)).memLp_of_hasCompactSupport
      (hΦc.comp_left (g := fun w : ℂ => ((w.im : ℝ) : ℂ)) (by simp))
  set W₁ : Planar.L2w m := hm₁.toLp _ with hW₁def
  set W₂ : Planar.L2w m := hm₂.toLp _ with hW₂def
  have hW₁ : ⇑W₁ =ᵐ[volume] fun z => (((fun y : ℝ × ℝ => (Φ (planeToC y)).re) (cToPlane z) : ℝ) : ℂ) := by
    filter_upwards [(Planar.volume_ac m).ae_le hm₁.coeFn_toLp] with z hz
    rw [hz]
    simp
  have hW₂ : ⇑W₂ =ᵐ[volume] fun z => (((fun y : ℝ × ℝ => (Φ (planeToC y)).im) (cToPlane z) : ℝ) : ℂ) := by
    filter_upwards [(Planar.volume_ac m).ae_le hm₂.coeFn_toLp] with z hz
    rw [hz]
    simp
  have hWsplit : W = W₁ + Complex.I • W₂ := by
    refine Lp.ext ?_
    filter_upwards [(Planar.wMeasure_ac m).ae_le hW, Lp.coeFn_add W₁ (Complex.I • W₂),
      Lp.coeFn_smul Complex.I W₂, hm₁.coeFn_toLp, hm₂.coeFn_toLp] with z h0 h1 h2 h3 h4
    rw [h0, h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul, mul_comm]
    exact (Complex.re_add_im (Φ z)).symm
  have hε3 : 0 < ε / 3 := by positivity
  refine succBlock_mono (succBlock_and
    (realTestLimit hT κ P hm K hB hε3 hs₁ hc₁ W₁ hW₁)
    (realTestLimit hT κ P hm K hB hε3 hs₂ hc₂ W₂ hW₂)) ?_
  rintro ν tr t₁ t₂ ⟨H₁, H₂⟩ F_rel hF σ τ hσ hστ hτB
  have e₁ := H₁ F_rel hF σ τ hσ hστ hτB
  have e₂ := H₂ F_rel hF σ τ hσ hστ hτB
  rw [hWsplit, map_add, map_smul, map_add, map_smul]
  have hre : F_rel τ σ W₁ + Complex.I • F_rel τ σ W₂ -
      (planarRelTransportRe P m τ σ W₁ + Complex.I • planarRelTransportRe P m τ σ W₂) =
      (F_rel τ σ W₁ - planarRelTransportRe P m τ σ W₁) +
        Complex.I • (F_rel τ σ W₂ - planarRelTransportRe P m τ σ W₂) := by
    rw [smul_sub]
    abel
  rw [hre]
  calc ‖(F_rel τ σ W₁ - planarRelTransportRe P m τ σ W₁) +
        Complex.I • (F_rel τ σ W₂ - planarRelTransportRe P m τ σ W₂)‖
      ≤ ‖F_rel τ σ W₁ - planarRelTransportRe P m τ σ W₁‖ +
          ‖Complex.I • (F_rel τ σ W₂ - planarRelTransportRe P m τ σ W₂)‖ := norm_add_le _ _
    _ = ‖F_rel τ σ W₁ - planarRelTransportRe P m τ σ W₁‖ +
          ‖F_rel τ σ W₂ - planarRelTransportRe P m τ σ W₂‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ ε / 3 + ε / 3 := add_le_add e₁ e₂
    _ < ε := by linarith

end RelFreeTestSub

end UnforcedLeray.Short.IIIa
