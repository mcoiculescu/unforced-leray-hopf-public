import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16_2
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont

/-!
# Part II-b, task `PartII-b:T16/2/1`: `SubtractedChartTestedEq`

Source of record: `the November 2 reference manuscript`, lines 1955-1962, 1978-1981.

Proves `subtractedChartTestedEq_proof : SubtractedChartTestedEq`:
1. Establishes `L²(hMeas c 2)` pairing continuity, Cauchy-Schwarz, and `sqrtS`-weighted pairing
   identities on `hMeas c 2`.
2. Tests the physical response `IsResponse ν c ε μ 2 F bε` against `NvC ε⁻¹ (scteConj B)` for any
   `NiceProf c B`, rewrites the phase pairing as an `H_2` chart integral via `phaseAvgC_proof`,
   integrates `(S, Q_ε, ∂_η)` by parts on `hMeas c 2`, and bounds the projected `Y_2` source via
   `norm_lerayY_le` (with exact cancellation of `π (ε⁻¹)²`).
3. Lifts the flat response `IsFlatResponse ν μ F b0` (`InFlatClass c 2 b0`) via
   `flatLerayLiftOfSlice` + `duhamelFullEq` + `flat_unique` to `FullFlatEq ν μ G b0` with
   `‖G‖_{H_2} ≤ CL ‖F‖_{H_2}`, and unfolds against `scteConj B` via `coordPeriodicUnfold`.
4. Subtracts the flat identity from the physical identity at the Friedrichs mollifications
   `B_n = mollP n (χ² • w)` (`r = 2`), passes `n → ∞` in `H_2`, bounds the radial hoop discrepancy
   `-ν ε² Re ∫ s bε_0 conj(χ² w_0) dH_2` via Young's inequality and `flat_graph_poly_two_given`,
   and concludes `SubtractedChartTestedEq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-! ## Section 1: Conjugation on `CProf` and `L²(hMeas c 2)` pairing helpers -/

private def scteConjMap : CMerid →ₗᵢ[ℝ] CMerid where
  toFun v := WithLp.toLp 2 fun i => (starRingEnd ℂ) (v i)
  map_add' u v := by ext i; simp
  map_smul' r v := by ext i; simp [Complex.real_smul]
  norm_map' v := by
    simp [PiLp.norm_eq_of_L2]

private def scteConj (B : CProf) : CProf := fun x => scteConjMap (B x)

@[simp]
private lemma scteConj_apply (B : CProf) (x : Coord) (i : Fin 2) :
    scteConj B x i = (starRingEnd ℂ) (B x i) := rfl

private lemma scteConj_norm (B : CProf) (x : Coord) :
    ‖scteConj B x‖ = ‖B x‖ :=
  scteConjMap.norm_map (B x)

private lemma scteConj_hNorm (c r : ℝ) (B : CProf) :
    hNorm c r (scteConj B) = hNorm c r B := by
  unfold hNorm
  exact eLpNorm_congr_norm_ae (ae_of_all _ fun x => scteConj_norm B x)

private lemma scteConj_nice {c : ℝ} {B : CProf} (hB : NiceProf c B) :
    NiceProf c (scteConj B) := by
  obtain ⟨hs, hper, s₀, s₁, L, hs₀, hvan⟩ := hB
  refine ⟨scteConjMap.toContinuousLinearMap.contDiff.comp hs, fun x => ?_,
    s₀, s₁, L, hs₀, fun x hx => ?_⟩
  · change scteConjMap (B (qShift c x)) = scteConjMap (B x)
    rw [hper x]
  · change scteConjMap (B x) = 0
    rw [hvan x hx, map_zero]

private lemma scte_nice_inHr {c : ℝ} (hc : 0 < c) {g : CProf} (hg : NiceProf c g) :
    InHr c 2 g := by
  obtain ⟨hsm, hper, s₀, s₁, L, hs₀, hz⟩ := hg
  set W : Set Coord := Icc s₀ s₁ ×ˢ (univ ×ˢ Icc (-L) L)
  have hWm : MeasurableSet W :=
    measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)
  have hgW : g = W.indicator g := by
    funext x
    by_cases hx : x ∈ W
    · exact (indicator_of_mem hx g).symm
    · rw [indicator_of_notMem hx]
      apply hz x
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2, h3⟩ := hcon
      exact hx ⟨⟨h1, h2⟩, ⟨mem_univ _, abs_le.mp h3⟩⟩
  set K : Set Coord := Icc s₀ s₁ ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L)
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hsm.continuous.continuousOn
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ; infer_instance
  have hμW : hMeas c 2 W < ⊤ := by
    unfold hMeas Axi.ageμ
    rw [Measure.prod_prod, Cyl.avgμ_univ_prod hc, withDensity_apply _ measurableSet_Icc]
    refine ENNReal.mul_lt_top ?_ measure_Icc_lt_top
    have hcont : ContinuousOn (fun t : ℝ => t ^ ((2 : ℝ) / 2 - 5 / 2)) (Icc s₀ s₁) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hs₀ hx.1))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hle : ∫⁻ x in Icc s₀ s₁, ENNReal.ofReal (x ^ ((2 : ℝ) / 2 - 5 / 2))
          ∂(volume.restrict (Ioi (0 : ℝ))) ≤
        ∫⁻ x in Icc s₀ s₁, ENNReal.ofReal C ∂(volume.restrict (Ioi (0 : ℝ))) := by
      refine setLIntegral_mono' measurableSet_Icc fun x hx => ENNReal.ofReal_le_ofReal ?_
      have h := hC x hx
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    refine lt_of_le_of_lt hle ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (Measure.restrict_apply_le _ _) measure_Icc_lt_top)
  have hq_ae : ∀ᵐ x ∂(hMeas c 2), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
    rw [ae_iff]
    unfold hMeas Axi.ageμ
    have heq : {x : Coord | ¬ x.2.1 ∈ Ico (-c / 2) (c / 2)} =
        (univ : Set ℝ) ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) := by
      ext x; simp
    rw [heq, Measure.prod_prod]
    have h0 : Cyl.avgμ c ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Cyl.avgμ, Measure.smul_apply, Cyl.cellμ, Measure.restrict_apply
        (measurableSet_Ico.compl.prod MeasurableSet.univ)]
      have hInt : (Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ) ∩ Cyl.cell c = ∅ := by
        ext x; simp [Cyl.cell]
      simp [hInt]
    simp [h0]
  have hae : ∀ᵐ x ∂(hMeas c 2), ‖g x‖ ≤ max M 0 := by
    filter_upwards [hq_ae] with x hx
    by_cases hW' : x ∈ W
    · exact le_max_of_le_left (by simpa [Real.norm_eq_abs] using hM x ⟨hW'.1, ⟨Ico_subset_Icc_self hx, hW'.2.2⟩⟩)
    · have hg0 : g x = 0 := by
        have h := congrFun hgW x; rw [indicator_of_notMem hW'] at h; exact h
      simp [hg0]
  have : IsFiniteMeasure ((hMeas c 2).restrict W) := ⟨by rw [Measure.restrict_apply_univ]; exact hμW⟩
  have hmem : MemLp g (ENNReal.ofReal 2) ((hMeas c 2).restrict W) :=
    MemLp.of_bound hsm.continuous.aestronglyMeasurable (max M 0) (ae_restrict_of_ae hae)
  refine ⟨ae_of_all _ hper, hsm.continuous.aestronglyMeasurable, ?_⟩
  unfold hNorm
  have heq : eLpNorm g (ENNReal.ofReal 2) (hMeas c 2) =
      eLpNorm g (ENNReal.ofReal 2) ((hMeas c 2).restrict W) := by
    conv_lhs => rw [hgW]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hWm
  rw [heq]
  exact hmem.eLpNorm_lt_top

private lemma scteConj_fderiv {B : CProf} (hB : ContDiff ℝ ∞ B) (x v : Coord) (i : Fin 2) :
    fderiv ℝ (scteConj B) x v i = (starRingEnd ℂ) (fderiv ℝ B x v i) := by
  have hd : DifferentiableAt ℝ B x := (hB.differentiable (by simp)) x
  have hcomp : HasFDerivAt (scteConj B)
      (scteConjMap.toContinuousLinearMap.comp (fderiv ℝ B x)) x :=
    scteConjMap.toContinuousLinearMap.hasFDerivAt.comp x hd.hasFDerivAt
  rw [hcomp.fderiv]
  rfl

private lemma scteConj_classQ (ε : ℝ) {B : CProf} (hB : ContDiff ℝ ∞ B) (x : Coord) (i : Fin 2) :
    classQ ε (scteConj B) x i = (starRingEnd ℂ) (classQ ε B x i) := by
  unfold classQ
  simp only [PiLp.add_apply, PiLp.smul_apply, Fin.sum_univ_three, PiLp.add_apply,
    scteConj_fderiv hB, scteConj_apply, Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]

private lemma scteConj_classEta {B : CProf} (hB : ContDiff ℝ ∞ B) (x : Coord) (i : Fin 2) :
    classEta (scteConj B) x i = (starRingEnd ℂ) (classEta B x i) :=
  scteConj_fderiv hB x (cdir 2) i

private lemma scte_ofReal_two : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num

private lemma scte_memLp_comp {μ : Measure Coord} {f : CProf}
    (hm : AEStronglyMeasurable f μ) (hf : eLpNorm f (ENNReal.ofReal 2) μ < ⊤) (i : Fin 2) :
    MemLp (fun x => f x i) 2 μ ∧
      eLpNorm (fun x => f x i) 2 μ ≤ eLpNorm f (ENNReal.ofReal 2) μ := by
  have hproj : AEStronglyMeasurable (fun x => f x i) μ :=
    (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hm
  have hle : eLpNorm (fun x => f x i) 2 μ ≤ eLpNorm f (ENNReal.ofReal 2) μ := by
    rw [scte_ofReal_two]
    exact eLpNorm_mono fun x => PiLp.norm_apply_le (f x) i
  exact ⟨⟨hproj, lt_of_le_of_lt hle hf⟩, hle⟩

private lemma scte_pair_comp_int_bound {μ : Measure Coord} {f g : CProf}
    (mf : AEStronglyMeasurable f μ) (hf : eLpNorm f (ENNReal.ofReal 2) μ < ⊤)
    (mg : AEStronglyMeasurable g μ) (hg : eLpNorm g (ENNReal.ofReal 2) μ < ⊤) (i : Fin 2) :
    Integrable (fun x => f x i * (starRingEnd ℂ) (g x i)) μ ∧
      ‖∫ x, f x i * (starRingEnd ℂ) (g x i) ∂μ‖ ≤
        (eLpNorm f (ENNReal.ofReal 2) μ).toReal * (eLpNorm g (ENNReal.ofReal 2) μ).toReal := by
  obtain ⟨hMf, hlef⟩ := scte_memLp_comp mf hf i
  obtain ⟨hMg, hleg⟩ := scte_memLp_comp mg hg i
  have hMg_star : MemLp (fun x => (starRingEnd ℂ) (g x i)) 2 μ := by
    refine ⟨Complex.conjCLE.continuous.comp_aestronglyMeasurable hMg.1, ?_⟩
    have heq : eLpNorm (fun x => (starRingEnd ℂ) (g x i)) 2 μ = eLpNorm (fun x => g x i) 2 μ :=
      eLpNorm_congr_norm_ae (ae_of_all _ fun x => RCLike.norm_conj (g x i))
    rw [heq]
    exact hMg.2
  have hint : Integrable (fun x => f x i * (starRingEnd ℂ) (g x i)) μ :=
    hMf.integrable_mul hMg_star
  refine ⟨hint, ?_⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hlin := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hMf.1.enorm hMg.1.enorm
  have heq_lin : (∫⁻ x, ‖f x i * (starRingEnd ℂ) (g x i)‖ₑ ∂μ) =
      ∫⁻ x, ‖f x i‖ₑ * ‖g x i‖ₑ ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [enorm_mul, RCLike.enorm_conj]
  have heLp_eq : ∀ u : Coord → ℂ,
      (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = eLpNorm u 2 μ := by
    intro u
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp
  rw [heLp_eq, heLp_eq] at hlin
  have hbound_enn : ∫⁻ x, ‖f x i * (starRingEnd ℂ) (g x i)‖ₑ ∂μ ≤
      eLpNorm f (ENNReal.ofReal 2) μ * eLpNorm g (ENNReal.ofReal 2) μ := by
    rw [heq_lin]
    exact hlin.trans (mul_le_mul' hlef hleg)
  have htop : eLpNorm f (ENNReal.ofReal 2) μ * eLpNorm g (ENNReal.ofReal 2) μ ≠ ⊤ :=
    ENNReal.mul_ne_top hf.ne hg.ne
  calc ‖∫ x, f x i * (starRingEnd ℂ) (g x i) ∂μ‖
      ≤ (∫⁻ x, ‖f x i * (starRingEnd ℂ) (g x i)‖ₑ ∂μ).toReal := by
        have h1 := norm_integral_le_lintegral_norm (fun x => f x i * (starRingEnd ℂ) (g x i)) (μ := μ)
        simpa only [ofReal_norm] using h1
    _ ≤ (eLpNorm f (ENNReal.ofReal 2) μ * eLpNorm g (ENNReal.ofReal 2) μ).toReal :=
        ENNReal.toReal_mono htop hbound_enn
    _ = (eLpNorm f (ENNReal.ofReal 2) μ).toReal * (eLpNorm g (ENNReal.ofReal 2) μ).toReal :=
        ENNReal.toReal_mul

private lemma scte_h2_pair_bound {c : ℝ} {f g : CProf}
    (mf : AEStronglyMeasurable f (hMeas c 2)) (hf : hNorm c 2 f < ⊤)
    (mg : AEStronglyMeasurable g (hMeas c 2)) (hg : hNorm c 2 g < ⊤) :
    Integrable (fun x => ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i)) (hMeas c 2) ∧
      ‖∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i) ∂(hMeas c 2)‖ ≤
        2 * (hNorm c 2 f).toReal * (hNorm c 2 g).toReal := by
  obtain ⟨hi0, hb0⟩ := scte_pair_comp_int_bound mf hf mg hg 0
  obtain ⟨hi1, hb1⟩ := scte_pair_comp_int_bound mf hf mg hg 1
  have hsum_eq : (fun x => ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i)) =
      fun x => f x 0 * (starRingEnd ℂ) (g x 0) + f x 1 * (starRingEnd ℂ) (g x 1) := by
    funext x; exact Fin.sum_univ_two _
  rw [hsum_eq]
  refine ⟨hi0.add hi1, ?_⟩
  rw [integral_add hi0 hi1]
  calc ‖(∫ x, f x 0 * (starRingEnd ℂ) (g x 0) ∂(hMeas c 2)) +
          ∫ x, f x 1 * (starRingEnd ℂ) (g x 1) ∂(hMeas c 2)‖
      ≤ ‖∫ x, f x 0 * (starRingEnd ℂ) (g x 0) ∂(hMeas c 2)‖ +
          ‖∫ x, f x 1 * (starRingEnd ℂ) (g x 1) ∂(hMeas c 2)‖ := norm_add_le _ _
    _ ≤ (hNorm c 2 f).toReal * (hNorm c 2 g).toReal +
          (hNorm c 2 f).toReal * (hNorm c 2 g).toReal := add_le_add hb0 hb1
    _ = 2 * (hNorm c 2 f).toReal * (hNorm c 2 g).toReal := by ring

private lemma scte_hMeas_pos (c r : ℝ) : ∀ᵐ x ∂(hMeas c r), 0 < x.1 := by
  have h0 : hMeas c r {x : Coord | ¬ 0 < x.1} = 0 := by
    have hset : {x : Coord | ¬ 0 < x.1} = {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} := by
      ext x; simp
    rw [hset]
    exact prep_ageμ_nonpos c _
  exact ae_iff.2 h0

private lemma scte_weighted_pair_eq_sqrtS {c : ℝ} (f g : CProf) :
    ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i) ∂(hMeas c 2) =
      ∫ x, ∑ i : Fin 2, sqrtS f x i * (starRingEnd ℂ) (sqrtS g x i) ∂(hMeas c 2) := by
  refine integral_congr_ae ?_
  filter_upwards [scte_hMeas_pos c 2] with x hx
  have hsq : ((Real.sqrt x.1 : ℂ) * (Real.sqrt x.1 : ℂ)) = (x.1 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx.le]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  linear_combination ((f x 0 * (starRingEnd ℂ) (g x 0)) + (f x 1 * (starRingEnd ℂ) (g x 1))) * hsq.symm

private lemma scte_pair_tendsto {c : ℝ} {f g : CProf} {gn : ℕ → CProf}
    (mf : AEStronglyMeasurable f (hMeas c 2)) (hf : hNorm c 2 f < ⊤)
    (mg : AEStronglyMeasurable g (hMeas c 2)) (hg : hNorm c 2 g < ⊤)
    (mgn : ∀ n, AEStronglyMeasurable (gn n) (hMeas c 2)) (hgn : ∀ n, hNorm c 2 (gn n) < ⊤)
    (hlim : Tendsto (fun n => hNorm c 2 (fun x => gn n x - g x)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (gn n x i) ∂(hMeas c 2))
      atTop (𝓝 (∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i) ∂(hMeas c 2))) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hbound : ∀ n,
      ‖(∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (gn n x i) ∂(hMeas c 2)) -
          ∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i) ∂(hMeas c 2)‖ ≤
        2 * (hNorm c 2 f).toReal * (hNorm c 2 (fun x => gn n x - g x)).toReal := by
    intro n
    obtain ⟨h1, -⟩ := scte_h2_pair_bound mf hf (mgn n) (hgn n)
    obtain ⟨h2, -⟩ := scte_h2_pair_bound mf hf mg hg
    have hdiff_fin : hNorm c 2 (fun x => gn n x - g x) < ⊤ :=
      lt_of_le_of_lt (eLpNorm_sub_le (mgn n) mg hp1) (ENNReal.add_lt_top.2 ⟨hgn n, hg⟩)
    obtain ⟨-, hbd⟩ := scte_h2_pair_bound mf hf ((mgn n).sub mg) hdiff_fin
    rw [← integral_sub h1 h2]
    have heq : (fun x => (∑ i : Fin 2, f x i * (starRingEnd ℂ) (gn n x i)) -
          ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i)) =
        fun x => ∑ i : Fin 2, f x i * (starRingEnd ℂ) ((gn n x - g x) i) := by
      funext x
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [PiLp.sub_apply, map_sub]
      ring
    rw [heq]
    exact hbd
  have ht : Tendsto (fun n => (hNorm c 2 (fun x => gn n x - g x)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have hsq : Tendsto (fun n =>
      (∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (gn n x i) ∂(hMeas c 2)) -
        ∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i) ∂(hMeas c 2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    simpa using ht.const_mul (2 * (hNorm c 2 f).toReal)
  simpa using hsq.add_const (∫ x, ∑ i : Fin 2, f x i * (starRingEnd ℂ) (g x i) ∂(hMeas c 2))

/-! ## Section 2: Chart-lift pairing in `H_2` and `Y_2` Leray source bound -/

private lemma scte_dotL_NvC_pt (R : ℝ) (H u : CProf) (τ : ℝ) (y : Space) :
    dotL (NvC R H (τ, y)) (NvC R u (τ, y)) =
      let z := Axi.chart R τ y
      (z.1 : ℂ) * ∑ i : Fin 2, H z i * u z i := by
  dsimp only
  rw [dotL_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [ChartLift.nvC_comp_apply]
  have ha0 : 0 ≤ Axi.age R y := Axi.age_nonneg R y
  have hz1 : (Axi.chart R τ y).1 = Axi.age R y := rfl
  by_cases hϱ : Axi.ϱ y = 0
  · have hage0 : Axi.age R y = 0 := by simp [Axi.age, hϱ]
    rw [hz1, hage0]
    simp
  · have heR := ChartLift.eR_sq_sum y hϱ
    have heR2 : Axi.eR y 2 = 0 := Axi.eR_apply_two y
    have he3_0 : Axi.e3 0 = 0 := by simp [Axi.e3]
    have he3_1 : Axi.e3 1 = 0 := by simp [Axi.e3]
    have he3_2 : Axi.e3 2 = 1 := by simp [Axi.e3]
    rw [heR2, he3_0, he3_1, he3_2]
    have hsq : ((√(Axi.age R y) : ℝ) : ℂ) * ((√(Axi.age R y) : ℝ) : ℂ) =
        ((Axi.age R y : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha0]
    have heRc : ((Axi.eR y 0 : ℝ) : ℂ) ^ 2 + ((Axi.eR y 1 : ℝ) : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, heR,
        Complex.ofReal_one]
    rw [hz1]
    push_cast
    linear_combination
      (H (Axi.chart R τ y) 0 * u (Axi.chart R τ y) 0 *
          (((Axi.eR y 0 : ℝ) : ℂ) ^ 2 + ((Axi.eR y 1 : ℝ) : ℂ) ^ 2) +
        H (Axi.chart R τ y) 1 * u (Axi.chart R τ y) 1) * hsq +
      ((Axi.age R y : ℝ) : ℂ) * H (Axi.chart R τ y) 0 * u (Axi.chart R τ y) 0 * heRc

private lemma scte_ageμ_m52_mul_fst {c : ℝ} (hc : 0 < c) {G0 : Coord → ℂ}
    (hG0_meas : Measurable G0) (hG0_int : Integrable G0 (hMeas c 2)) :
    Integrable (fun x : Coord => (x.1 : ℂ) * G0 x) (Axi.ageμ c (-(5 / 2 : ℝ))) ∧
      ∫ x, (x.1 : ℂ) * G0 x ∂(Axi.ageμ c (-(5 / 2 : ℝ))) = ∫ x, G0 x ∂(hMeas c 2) := by
  have h2_eq : (2 : ℝ) / 2 - 5 / 2 = -(3 / 2 : ℝ) := by norm_num
  have hm_eq : hMeas c 2 = Axi.ageμ c (-(3 / 2 : ℝ)) := by
    unfold hMeas; rw [h2_eq]
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hw5 : Measurable fun p : Coord => ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).const_mul _)
  have hw3 : Measurable fun p : Coord => ENNReal.ofReal (c⁻¹ * p.1 ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).const_mul _)
  have hG1_meas : Measurable (fun x : Coord => (x.1 : ℂ) * G0 x) :=
    (Complex.measurable_ofReal.comp measurable_fst).mul hG0_meas
  have hlin_eq : (∫⁻ x, ‖(x.1 : ℂ) * G0 x‖ₑ ∂(Axi.ageμ c (-(5 / 2 : ℝ)))) =
      ∫⁻ x, ‖G0 x‖ₑ ∂(hMeas c 2) := by
    rw [hm_eq, Axi.lintegral_ageμ hc _ hG1_meas.enorm, Axi.lintegral_ageμ hc _ hG0_meas.enorm]
    refine setLIntegral_congr_fun hS fun x hx => ?_
    have hxpos : 0 < x.1 := hx.1
    have hc0 : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have hpow : x.1 ^ (-(5 / 2 : ℝ)) * x.1 = x.1 ^ (-(3 / 2 : ℝ)) := by
      calc x.1 ^ (-(5 / 2 : ℝ)) * x.1 = x.1 ^ (-(5 / 2 : ℝ)) * x.1 ^ (1 : ℝ) := by
            rw [Real.rpow_one]
        _ = x.1 ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    have hxnorm : ‖(x.1 : ℂ)‖ₑ = ENNReal.ofReal x.1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hxpos.le]
    rw [enorm_mul, hxnorm, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg hc0 (Real.rpow_nonneg hxpos.le _))]
    congr 2
    calc c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)) * x.1 = c⁻¹ * (x.1 ^ (-(5 / 2 : ℝ)) * x.1) := by ring
      _ = c⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) := by rw [hpow]
  have hint5 : Integrable (fun x : Coord => (x.1 : ℂ) * G0 x) (Axi.ageμ c (-(5 / 2 : ℝ))) :=
    ⟨hG1_meas.aestronglyMeasurable, by unfold HasFiniteIntegral; rw [hlin_eq]; exact hG0_int.2⟩
  refine ⟨hint5, ?_⟩
  rw [hm_eq, ph_ageμ_density hc (-(5 / 2 : ℝ)), ph_ageμ_density hc (-(3 / 2 : ℝ)),
    integral_withDensity_eq_integral_toReal_smul hw5 (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hw3 (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  have hxpos : 0 < x.1 := hx.1
  have hc0 : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  have hpow : x.1 ^ (-(5 / 2 : ℝ)) * x.1 = x.1 ^ (-(3 / 2 : ℝ)) := by
    calc x.1 ^ (-(5 / 2 : ℝ)) * x.1 = x.1 ^ (-(5 / 2 : ℝ)) * x.1 ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = x.1 ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
  rw [ENNReal.toReal_ofReal (mul_nonneg hc0 (Real.rpow_nonneg hxpos.le _)),
    ENNReal.toReal_ofReal (mul_nonneg hc0 (Real.rpow_nonneg hxpos.le _)),
    Complex.real_smul, Complex.real_smul]
  push_cast
  have hc_pow : ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (x.1 : ℂ) =
      ((x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hpow
  linear_combination (c⁻¹ : ℂ) * G0 x * hc_pow

private lemma scte_pairF_NvC {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    {H u : CProf} (hH : NiceProf c H) (hu : InHr c 2 u) :
    pairF (2 * ε * c) (NvC ε⁻¹ H) (NvC ε⁻¹ u) =
      ((Real.pi * (ε⁻¹) ^ 2 : ℝ) : ℂ) * ∫ x, ∑ i : Fin 2, H x i * u x i ∂(hMeas c 2) := by
  obtain ⟨u', M, hu'm, hu'per, hMm, hM0, huu', hNu', hpair_eq⟩ :=
    pairCont_rep hc hε (NvC ε⁻¹ H) u hu
  rw [hpair_eq]
  have hH_in : InHr c 2 H := scte_nice_inHr hc hH
  have hu'_in : InHr c 2 u' :=
    ⟨ae_of_all _ fun x => hu'per x.1 x.2.1 x.2.2, hu'm.aestronglyMeasurable,
      by rw [hNu']; exact hu.finite⟩
  set G0 : Coord → ℂ := fun x => ∑ i : Fin 2, H x i * u' x i
  have hconj_meas : AEStronglyMeasurable (scteConj u') (hMeas c 2) :=
    scteConjMap.toContinuousLinearMap.continuous.comp_aestronglyMeasurable hu'_in.meas
  have hconj_fin : hNorm c 2 (scteConj u') < ⊤ := by
    rw [scteConj_hNorm]; exact hu'_in.finite
  obtain ⟨hG0_int', -⟩ := scte_h2_pair_bound hH_in.meas hH_in.finite hconj_meas hconj_fin
  have hG0_eq : (fun x => ∑ i : Fin 2, H x i * (starRingEnd ℂ) (scteConj u' x i)) = G0 := by
    funext x
    simp only [G0, scteConj_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hG0_int : Integrable G0 (hMeas c 2) := hG0_eq ▸ hG0_int'
  have hG0_meas : Measurable G0 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.measurable.comp
      hH.1.continuous.measurable).mul
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.measurable.comp hu'm)
  obtain ⟨hG1_int, hG1_val⟩ := scte_ageμ_m52_mul_fst hc hG0_meas hG0_int
  have hG1_per : ∀ (s q η : ℝ), (((s, (q + c, η)) : Coord).1 : ℂ) * G0 (s, (q + c, η)) =
      (((s, (q, η)) : Coord).1 : ℂ) * G0 (s, (q, η)) := by
    intro s q η
    have hHq := hH.2.1 (s, (q, η))
    have huq := hu'per s q η
    change (s : ℂ) * ∑ i : Fin 2, H (qShift c (s, (q, η))) i * u' (s, (q + c, η)) i = _
    rw [hHq, huq]
  have hP_eq : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hpt : (fun p : ℝ × Space => dotL (NvC ε⁻¹ H p) (NvC ε⁻¹ u' p)) =
      fun p : ℝ × Space => (let z := Axi.chart ε⁻¹ p.1 p.2; (z.1 : ℂ) * G0 z) := by
    funext ⟨τ, y⟩
    exact scte_dotL_NvC_pt ε⁻¹ H u' τ y
  unfold pairF
  rw [hpt, hP_eq,
    phaseAvgC_proof ε⁻¹ c (fun x => (x.1 : ℂ) * G0 x) (inv_pos.2 hε) hc
      ((Complex.measurable_ofReal.comp measurable_fst).mul hG0_meas) hG1_per hG1_int,
    hG1_val]
  congr 1
  have hae : u' =ᵐ[hMeas c 2] u := by
    have hsub : {x : Coord | ¬ u' x = u x} ⊆ M ∪ {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} := by
      intro x hx
      by_cases h1 : x.1 ≤ 0
      · exact Or.inr h1
      · exact Or.inl (by by_contra hM; exact hx (huu' x (not_le.1 h1) hM).symm)
    exact ae_iff.2 (measure_mono_null hsub
      (measure_union_null (ageμ_null_of_volume_null hc hMm hM0) (prep_ageμ_nonpos c _)))
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp [G0, hx]

private lemma scte_dotL_norm_le_three (a b : CVec3) :
    ‖dotL a b‖ ≤ 3 * ‖a‖ * ‖b‖ := by
  rw [dotL_apply, Fin.sum_univ_three]
  have h0 : ‖a 0 * b 0‖ ≤ ‖a‖ * ‖b‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a 0) (PiLp.norm_apply_le b 0) (norm_nonneg _) (norm_nonneg _)
  have h1 : ‖a 1 * b 1‖ ≤ ‖a‖ * ‖b‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a 1) (PiLp.norm_apply_le b 1) (norm_nonneg _) (norm_nonneg _)
  have h2 : ‖a 2 * b 2‖ ≤ ‖a‖ * ‖b‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a 2) (PiLp.norm_apply_le b 2) (norm_nonneg _) (norm_nonneg _)
  calc ‖a 0 * b 0 + a 1 * b 1 + a 2 * b 2‖
      ≤ ‖a 0 * b 0 + a 1 * b 1‖ + ‖a 2 * b 2‖ := norm_add_le _ _
    _ ≤ ‖a 0 * b 0‖ + ‖a 1 * b 1‖ + ‖a 2 * b 2‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := add_le_add (add_le_add h0 h1) h2
    _ = 3 * ‖a‖ * ‖b‖ := by ring

private lemma scte_pairF_l2_bound {P : ℝ} (hP : 0 < P)
    {Φ u : ℝ × Space → CVec3} (hΦm : Measurable Φ) (hΦfin : phaseLpNorm P 2 Φ < ⊤)
    (hum : Measurable u) (hufin : phaseLpNorm P 2 u < ⊤) :
    ‖pairF P Φ u‖ ≤ 3 * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal := by
  have hpq : (Real.conjExponent 2) = 2 := by norm_num [Real.conjExponent]
  set g : ℝ × Space → ℝ≥0∞ := fun z => ENNReal.ofReal 3 * ‖Φ z‖ₑ
  have hg : Measurable g := measurable_const.mul hΦm.enorm
  have hw : ∀ᵐ z ∂(hSlab P), ‖dotL (Φ z) (u z)‖ₑ ≤ g z * ‖u z‖ₑ := by
    refine ae_of_all _ fun z => ?_
    have h := scte_dotL_norm_le_three (Φ z) (u z)
    calc ‖dotL (Φ z) (u z)‖ₑ = ENNReal.ofReal ‖dotL (Φ z) (u z)‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (3 * ‖Φ z‖ * ‖u z‖) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal 3 * ENNReal.ofReal ‖Φ z‖ * ENNReal.ofReal ‖u z‖ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
      _ = g z * ‖u z‖ₑ := by simp [g, ofReal_norm]
  have habs := holder_abstract P 2 hP one_lt_two g hg u hum _ hw
  rw [hpq] at habs
  have hg_norm : (∫⁻ z, g z ^ (2 : ℝ) ∂(hSlab P)) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal 3 * (ENNReal.ofReal P ^ (1 / (2 : ℝ)) * phaseLpNorm P 2 Φ) := by
    have hpt : ∀ z, g z ^ (2 : ℝ) = ENNReal.ofReal 3 ^ (2 : ℝ) * ‖Φ z‖ₑ ^ (2 : ℝ) := fun z =>
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    simp_rw [hpt]
    rw [lintegral_const_mul _ (hΦm.enorm.pow_const _), holder_Ur P 2 hP two_pos Φ hΦm,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  rw [hg_norm] at habs
  set B : ℝ≥0∞ :=
    (ENNReal.ofReal 3 * (ENNReal.ofReal P ^ (1 / (2 : ℝ)) * phaseLpNorm P 2 Φ)) *
      (ENNReal.ofReal P ^ (1 / (2 : ℝ)) * phaseLpNorm P 2 u)
  have hP_half : ENNReal.ofReal P ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  have hBtop : B ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hP_half hΦfin.ne))
      (ENNReal.mul_ne_top hP_half hufin.ne)
  obtain ⟨-, hnorm⟩ := holder_integral P hP _ (holder_measurable_dot Φ u hΦm hum) B hBtop habs
  have hP_sq : (P ^ (1 / (2 : ℝ))) * (P ^ (1 / (2 : ℝ))) = P := by
    rw [← Real.rpow_add hP]
    norm_num
  have hB_toReal : B.toReal = 3 * P * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal := by
    dsimp [B]
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hP.le,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3)]
    calc 3 * (P ^ (1 / (2 : ℝ)) * (phaseLpNorm P 2 Φ).toReal) *
          (P ^ (1 / (2 : ℝ)) * (phaseLpNorm P 2 u).toReal)
        = 3 * ((P ^ (1 / (2 : ℝ))) * (P ^ (1 / (2 : ℝ)))) *
            (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal := by ring
      _ = 3 * P * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal := by rw [hP_sq]
  calc ‖pairF P Φ u‖ ≤ P⁻¹ * B.toReal := hnorm
    _ = P⁻¹ * (3 * P * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal) := by rw [hB_toReal]
    _ = 3 * (P⁻¹ * P) * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal := by ring
    _ = 3 * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 u).toReal := by
        rw [inv_mul_cancel₀ hP.ne', mul_one]

/-! ## Section 3: Periodic weighted IBP on `hMeas c 2` and physical `NiceProf` tested equation -/

private lemma scte_nice_comp_props {c : ℝ} {B : CProf} (hB : NiceProf c B) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x => (B x i).re) ∧
      (∀ x, ((B (qShift c x) i).re) = (B x i).re) ∧
      ContDiff ℝ ∞ (fun x => (B x i).im) ∧
      (∀ x, ((B (qShift c x) i).im) = (B x i).im) ∧
      ∃ s₀ s₁ L : ℝ, 0 < s₀ ∧
        (∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → (B x i).re = 0) ∧
        (∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → (B x i).im = 0) := by
  obtain ⟨hs, hper, s₀, s₁, L, hs₀, hvan⟩ := hB
  have hci : ContDiff ℝ ∞ (fun x => B x i) :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hs
  refine ⟨Complex.reCLM.contDiff.comp hci, fun x => by rw [hper x],
    Complex.imCLM.contDiff.comp hci, fun x => by rw [hper x],
    s₀, s₁, L, hs₀, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hvan x hx]; simp
  · rw [hvan x hx]; simp

private lemma scte_fderiv_re_im {B : CProf} (hB : ContDiff ℝ ∞ B) (x : Coord) (j : Fin 3) (i : Fin 2) :
    fderiv ℝ B x (cdir j) i =
      ((cpd j (fun y => (B y i).re) x : ℝ) : ℂ) +
        Complex.I * ((cpd j (fun y => (B y i).im) x : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ B x := (hB.differentiable (by simp)) x
  have hproj : HasFDerivAt (fun y => B y i)
      (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ B x)) x :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp x hd.hasFDerivAt
  have hre : HasFDerivAt (fun y => (B y i).re)
      (Complex.reCLM.comp (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp
        (fderiv ℝ B x))) x :=
    Complex.reCLM.hasFDerivAt.comp x hproj
  have him : HasFDerivAt (fun y => (B y i).im)
      (Complex.imCLM.comp (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp
        (fderiv ℝ B x))) x :=
    Complex.imCLM.hasFDerivAt.comp x hproj
  unfold cpd
  rw [hre.fderiv, him.fderiv]
  change _ = ((((fderiv ℝ B x) (cdir j) i).re : ℝ) : ℂ) +
      Complex.I * ((((fderiv ℝ B x) (cdir j) i).im : ℝ) : ℂ)
  rw [mul_comm Complex.I]
  exact (Complex.re_add_im _).symm

private lemma scte_comp_unconj_int {c : ℝ} {u v : CProf}
    (mu : AEStronglyMeasurable u (hMeas c 2)) (hu : hNorm c 2 u < ⊤)
    (mv : AEStronglyMeasurable v (hMeas c 2)) (hv : hNorm c 2 v < ⊤) (i : Fin 2) :
    Integrable (fun x => u x i * v x i) (hMeas c 2) := by
  have mvc : AEStronglyMeasurable (scteConj v) (hMeas c 2) :=
    scteConjMap.toContinuousLinearMap.continuous.comp_aestronglyMeasurable mv
  have hvc : hNorm c 2 (scteConj v) < ⊤ := by rw [scteConj_hNorm]; exact hv
  obtain ⟨hint, -⟩ := scte_pair_comp_int_bound mu hu mvc hvc i
  have heq : (fun x => u x i * (starRingEnd ℂ) (scteConj v x i)) = fun x => u x i * v x i := by
    funext x
    simp only [scteConj_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
  exact heq ▸ hint

private lemma scte_periodic_ibp_S_nice {c : ℝ} (hc : 0 < c) {b Sb Ψ : CProf}
    (hb : InHr c 2 b) (hSb : InHr c 2 Sb) (hw : HasWeakVec vS dZero b Sb) (hΨ : NiceProf c Ψ) :
    ∫ x, ∑ i : Fin 2, Sb x i * Ψ x i ∂(hMeas c 2) =
      ∫ x, ∑ i : Fin 2, b x i *
        ((1 / 2 : ℂ) * Ψ x i - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) i) ∂(hMeas c 2) := by
  have hP := weakSPeriodicExtension c b Sb hc hb hSb hw
  have h2_eq : (2 : ℝ) / 2 - 5 / 2 = -(3 / 2 : ℝ) := by norm_num
  have hm_eq : hMeas c 2 = Axi.ageμ c (-(3 / 2 : ℝ)) := by unfold hMeas; rw [h2_eq]
  have hΨ_in : InHr c 2 Ψ := scte_nice_inHr hc hΨ
  set DΨ : CProf := fun x => (1 / 2 : ℂ) • Ψ x - x.1 • fderiv ℝ Ψ x (cdir 0)
  have hDΨ_nice : NiceProf c DΨ := by
    obtain ⟨hs, hp, s₀', s₁', L', hs₀', hv⟩ := hΨ
    have hfd : ContDiff ℝ ∞ (fun x => fderiv ℝ Ψ x (cdir 0)) :=
      (hs.fderiv_right (by simp)).clm_apply contDiff_const
    have hDΨ_cd : ContDiff ℝ ∞ DΨ := by
      have h1 : ContDiff ℝ ∞ (fun x : Coord => (1 / 2 : ℂ) • Ψ x) :=
        (contDiff_const (c := (1 / 2 : ℂ))).smul hs
      have h2 : ContDiff ℝ ∞ (fun x : Coord => x.1 • fderiv ℝ Ψ x (cdir 0)) :=
        contDiff_fst.smul hfd
      exact h1.sub h2
    refine ⟨hDΨ_cd, fun x => ?_, s₀', s₁', L', hs₀', fun x hx => ?_⟩
    · have hqy : ∀ y : Coord, y + (0, (c, 0)) = qShift c y := fun ⟨s, q, η⟩ => by simp [qShift]
      have hfsh : fderiv ℝ Ψ (qShift c x) = fderiv ℝ Ψ x := by
        have hcomp_eq : (fun y : Coord => Ψ (y + (0, (c, 0)))) = Ψ :=
          funext fun y => by rw [hqy y, hp y]
        have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Ψ) (x := x) (0, (c, 0))
        rw [hcomp_eq, hqy x] at h
        exact h.symm
      dsimp [DΨ]
      rw [hp x, hfsh]
    · have hev : Ψ =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.eventuallyEq_of_mem ((coef_isOpen s₀' s₁' L').mem_nhds hx) fun y hy => hv y hy
      dsimp [DΨ]
      rw [hv x hx, hev.fderiv_eq]
      simp
  have hDΨ_in : InHr c 2 DΨ := scte_nice_inHr hc hDΨ_nice
  have hcomp : ∀ i : Fin 2,
      ∫ x, Sb x i * Ψ x i ∂(hMeas c 2) =
        ∫ x, b x i * ((1 / 2 : ℂ) * Ψ x i - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) i) ∂(hMeas c 2) := by
    intro i
    obtain ⟨hre_s, hre_p, him_s, him_p, s₀, s₁, L, hs₀, hre_v, him_v⟩ := scte_nice_comp_props hΨ i
    have ere := hP _ hre_s hre_p ⟨s₀, s₁, L, hs₀, hre_v⟩ i
    have eim := hP _ him_s him_p ⟨s₀, s₁, L, hs₀, him_v⟩ i
    have iS_full : Integrable (fun x => Sb x i * Ψ x i) (hMeas c 2) :=
      scte_comp_unconj_int hSb.meas hSb.finite hΨ_in.meas hΨ_in.finite i
    have iB_full : Integrable (fun x => b x i * DΨ x i) (hMeas c 2) :=
      scte_comp_unconj_int hb.meas hb.finite hDΨ_in.meas hDΨ_in.finite i
    have iS1 : Integrable (fun x => Sb x i * (((Ψ x i).re : ℝ) : ℂ)) (hMeas c 2) := by
      have hle : ∀ x, ‖Sb x i * (((Ψ x i).re : ℝ) : ℂ)‖ ≤ ‖Sb x i * Ψ x i‖ := fun x => by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)
      exact iS_full.mono
        (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hSb.meas).mul
          (Complex.continuous_ofReal.comp hre_s.continuous).aestronglyMeasurable)
        (ae_of_all _ hle)
    have iS2 : Integrable (fun x => Sb x i * (((Ψ x i).im : ℝ) : ℂ)) (hMeas c 2) := by
      have hle : ∀ x, ‖Sb x i * (((Ψ x i).im : ℝ) : ℂ)‖ ≤ ‖Sb x i * Ψ x i‖ := fun x => by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)
      exact iS_full.mono
        (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hSb.meas).mul
          (Complex.continuous_ofReal.comp him_s.continuous).aestronglyMeasurable)
        (ae_of_all _ hle)
    set fB1 : Coord → ℂ := fun x => b x i *
      ((((1 + (-3 / 2 : ℝ)) * (Ψ x i).re + x.1 * cpd 0 (fun y => (Ψ y i).re) x : ℝ) : ℂ))
    set fB2 : Coord → ℂ := fun x => b x i *
      ((((1 + (-3 / 2 : ℝ)) * (Ψ x i).im + x.1 * cpd 0 (fun y => (Ψ y i).im) x : ℝ) : ℂ))
    have iB1 : Integrable fB1 (hMeas c 2) := by
      have hle : ∀ x, ‖fB1 x‖ ≤ ‖b x i * DΨ x i‖ := by
        intro x
        have hre_eq : -(((1 + (-3 / 2 : ℝ)) * (Ψ x i).re + x.1 * cpd 0 (fun y => (Ψ y i).re) x)) =
            (DΨ x i).re := by
          dsimp [DΨ]
          rw [scte_fderiv_re_im hΨ.1 x 0 i]
          simp [Complex.mul_re]
          ring
        dsimp [fB1]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have habs : |(1 + (-3 / 2 : ℝ)) * (Ψ x i).re + x.1 * cpd 0 (fun y => (Ψ y i).re) x| =
            |(DΨ x i).re| := by rw [← abs_neg, hre_eq]
        rw [habs]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)
      exact iB_full.mono
        (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb.meas).mul
          (Complex.continuous_ofReal.comp (((continuous_const.mul hre_s.continuous).add
            (continuous_fst.mul (coef_cpd_contDiff hre_s 0).continuous)))).aestronglyMeasurable)
        (ae_of_all _ hle)
    have iB2 : Integrable fB2 (hMeas c 2) := by
      have hle : ∀ x, ‖fB2 x‖ ≤ ‖b x i * DΨ x i‖ := by
        intro x
        have him_eq : -(((1 + (-3 / 2 : ℝ)) * (Ψ x i).im + x.1 * cpd 0 (fun y => (Ψ y i).im) x)) =
            (DΨ x i).im := by
          dsimp [DΨ]
          rw [scte_fderiv_re_im hΨ.1 x 0 i]
          simp [Complex.mul_im]
          ring
        dsimp [fB2]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have habs : |(1 + (-3 / 2 : ℝ)) * (Ψ x i).im + x.1 * cpd 0 (fun y => (Ψ y i).im) x| =
            |(DΨ x i).im| := by rw [← abs_neg, him_eq]
        rw [habs]
        exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)
      exact iB_full.mono
        (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb.meas).mul
          (Complex.continuous_ofReal.comp (((continuous_const.mul him_s.continuous).add
            (continuous_fst.mul (coef_cpd_contDiff him_s 0).continuous)))).aestronglyMeasurable)
        (ae_of_all _ hle)
    have hsplitL : (fun x => Sb x i * Ψ x i) =
        fun x => Sb x i * (((Ψ x i).re : ℝ) : ℂ) +
          Complex.I * (Sb x i * (((Ψ x i).im : ℝ) : ℂ)) := by
      funext x
      have h1 : (((Ψ x i).re : ℝ) : ℂ) + Complex.I * (((Ψ x i).im : ℝ) : ℂ) = Ψ x i := by
        rw [mul_comm]; exact Complex.re_add_im _
      linear_combination Sb x i * h1.symm
    have hsplitR : (fun x => b x i *
          ((1 / 2 : ℂ) * Ψ x i - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) i)) =
        fun x => (-1 : ℂ) * fB1 x + (-Complex.I) * fB2 x := by
      funext x
      have h1 : Ψ x i = (((Ψ x i).re : ℝ) : ℂ) + Complex.I * (((Ψ x i).im : ℝ) : ℂ) := by
        rw [mul_comm]; exact (Complex.re_add_im _).symm
      conv_lhs => rw [scte_fderiv_re_im hΨ.1 x 0 i, h1]
      dsimp [fB1, fB2]
      push_cast
      ring
    have hm_eq' : Axi.ageμ c (-3 / 2) = hMeas c 2 := by
      rw [hm_eq]; norm_num
    rw [hm_eq'] at ere eim
    change ∫ x, Sb x i * (((Ψ x i).re : ℝ) : ℂ) ∂(hMeas c 2) = - ∫ x, fB1 x ∂(hMeas c 2) at ere
    change ∫ x, Sb x i * (((Ψ x i).im : ℝ) : ℂ) ∂(hMeas c 2) = - ∫ x, fB2 x ∂(hMeas c 2) at eim
    rw [hsplitL, integral_add iS1 (iS2.const_mul Complex.I), integral_const_mul,
      ere, eim, hsplitR, integral_add (iB1.const_mul _) (iB2.const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  have hsumL : (fun x => ∑ i : Fin 2, Sb x i * Ψ x i) =
      fun x => Sb x 0 * Ψ x 0 + Sb x 1 * Ψ x 1 := funext fun _ => Fin.sum_univ_two _
  have hsumR : (fun x => ∑ i : Fin 2, b x i *
        ((1 / 2 : ℂ) * Ψ x i - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) i)) =
      fun x => b x 0 * ((1 / 2 : ℂ) * Ψ x 0 - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) 0) +
        b x 1 * ((1 / 2 : ℂ) * Ψ x 1 - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) 1) :=
    funext fun _ => Fin.sum_univ_two _
  have i0L := scte_comp_unconj_int hSb.meas hSb.finite hΨ_in.meas hΨ_in.finite 0
  have i1L := scte_comp_unconj_int hSb.meas hSb.finite hΨ_in.meas hΨ_in.finite 1
  have i0R := scte_comp_unconj_int hb.meas hb.finite hDΨ_in.meas hDΨ_in.finite 0
  have i1R := scte_comp_unconj_int hb.meas hb.finite hDΨ_in.meas hDΨ_in.finite 1
  have i0R' : Integrable (fun x => b x 0 *
      ((1 / 2 : ℂ) * Ψ x 0 - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) 0)) (hMeas c 2) := by
    simpa [DΨ, Complex.real_smul] using i0R
  have i1R' : Integrable (fun x => b x 1 *
      ((1 / 2 : ℂ) * Ψ x 1 - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) 1)) (hMeas c 2) := by
    simpa [DΨ, Complex.real_smul] using i1R
  rw [hsumL, hsumR, integral_add i0L i1L, integral_add i0R' i1R', hcomp 0, hcomp 1]

/-! ### Section 3b: Periodic unfolding helpers, `∂_η` / `Q_ε` periodic IBP, and physical tested Eq -/

private lemma scte_unfold_comp {c s₀ s₁ L : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {u : CProf} (hu : InHr c 2 u) (i : Fin 2)
    {h : ℝ → ℝ} {P : ℝ} (hh_cont : Continuous h) (hh_cs : HasCompactSupport h)
    (hh_sum : ∀ q : ℝ, HasSum (fun n : ℤ => h (q - n * c)) P)
    {α : Coord → ℝ} (hα_cont : Continuous α) (hα_per : ∀ x, α (qShift c x) = α x)
    (hα_van : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → α x = 0) :
    Integrable (fun x : Coord => (h x.2.1 : ℂ) * (u x i * (α x : ℂ))) volume ∧
      IntegrableOn (fun x : Coord => u x i * (α x : ℂ)) (univ ×ˢ Cyl.cell c) volume ∧
      ∫ x, (h x.2.1 : ℂ) * (u x i * (α x : ℂ)) =
        (P : ℂ) * ∫ x in univ ×ˢ Cyl.cell c, u x i * (α x : ℂ) := by
  have hper : ∀ᵐ x : Coord, u (qShift c x) i * (α (qShift c x) : ℂ) = u x i * (α x : ℂ) := by
    filter_upwards [QPerHalf.ae_imp hu.periodic] with x hx
    by_cases hx0 : 0 < x.1
    · rw [hx hx0, hα_per x]
    · have hxs : x.1 < s₀ := lt_of_le_of_lt (not_lt.1 hx0) hs₀
      rw [hα_van x (Or.inl hxs), hα_van (qShift c x) (Or.inl hxs)]
      simp
  have hvan : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → u x i * (α x : ℂ) = 0 := by
    intro x hx
    rw [hα_van x hx]
    simp
  have hbox : ∀ R : ℝ,
      IntegrableOn (fun x : Coord => u x i * (α x : ℂ))
        (Icc s₀ s₁ ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume := by
    intro R
    have hK : IsCompact (Icc s₀ s₁ ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    exact IntegrableOn.mul_continuousOn
      (hrBoxIntegrable c 2 u hc one_lt_two hu s₀ s₁ R L hs₀ i)
      (Complex.continuous_ofReal.comp hα_cont).continuousOn hK
  exact coordPeriodicUnfold c h P (fun x : Coord => u x i * (α x : ℂ)) s₀ s₁ L
    hc hh_cont hh_cs hh_sum hper hvan hbox

private lemma scte_cell_to_hMeas {c s₀ : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {f : Coord → ℂ} (hvan : ∀ x : Coord, x.1 < s₀ → f x = 0) :
    ∫ x in univ ×ˢ Cyl.cell c, ((c⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * f x =
      ∫ x, f x ∂(hMeas c 2) := by
  have h2_eq : (2 : ℝ) / 2 - 5 / 2 = -(3 / 2 : ℝ) := by norm_num
  have hm_eq : hMeas c 2 = Axi.ageμ c (-(3 / 2 : ℝ)) := by unfold hMeas; rw [h2_eq]
  have hw3 : Measurable fun p : Coord => ENNReal.ofReal (c⁻¹ * p.1 ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).const_mul _)
  rw [hm_eq, ph_ageμ_density hc (-(3 / 2 : ℝ)),
    integral_withDensity_eq_integral_toReal_smul hw3 (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    Axi.qCell_eq_cell,
    ← integral_indicator (MeasurableSet.univ.prod (Cyl.measurableSet_cell c)),
    ← integral_indicator (measurableSet_Ioi.prod (Cyl.measurableSet_cell c))]
  congr 1
  funext x
  by_cases hcell : x.2 ∈ Cyl.cell c
  · by_cases hx0 : 0 < x.1
    · have hm1 : x ∈ univ ×ˢ Cyl.cell c := ⟨trivial, hcell⟩
      have hm2 : x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c := ⟨hx0, hcell⟩
      rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2,
        ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hx0.le _)),
        Complex.real_smul]
    · have hm1 : x ∈ univ ×ˢ Cyl.cell c := ⟨trivial, hcell⟩
      have hm2 : x ∉ Ioi (0 : ℝ) ×ˢ Cyl.cell c := fun h => hx0 h.1
      rw [Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2,
        hvan x (lt_of_le_of_lt (not_lt.1 hx0) hs₀), mul_zero]
  · have hm1 : x ∉ univ ×ˢ Cyl.cell c := fun h => hcell h.2
    have hm2 : x ∉ Ioi (0 : ℝ) ×ˢ Cyl.cell c := fun h => hcell h.2
    rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]

private def scteW (a c : ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ :=
  c⁻¹ * (x.1 ^ a * φ x)

private lemma scteW_contDiff {a c s₀ : ℝ} {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ)
    (hs₀ : 0 < s₀) (hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0) :
    ContDiff ℝ ∞ (scteW a c φ) := by
  have h1 := contDiff_test a (contDiff_const (c := (1 : ℝ))) hφ_s hs₀ hlow
  have heq : scteW a c φ = fun x => c⁻¹ * (x.1 ^ a * (1 : ℝ) * φ x) := by
    funext x; simp [scteW]
  rw [heq]
  exact contDiff_const.mul h1

private lemma scteW_per {a c : ℝ} {φ : Coord → ℝ} (hφ_p : ∀ x, φ (qShift c x) = φ x) (x : Coord) :
    scteW a c φ (qShift c x) = scteW a c φ x := by
  simp only [scteW, coef_qShift_fst, hφ_p x]

private lemma scteW_van {a c s₀ s₁ L : ℝ} {φ : Coord → ℝ}
    (hφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → φ x = 0) (x : Coord)
    (hx : x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) : scteW a c φ x = 0 := by
  simp only [scteW, hφ_v x hx, mul_zero]

private lemma scteW_mul_theta_isTest {a c s₀ s₁ L : ℝ} {θ : ℝ → ℝ}
    (hθ_cd : ContDiff ℝ ∞ θ) (hθ_cs : HasCompactSupport θ)
    {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ) (hs₀ : 0 < s₀)
    (hφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → φ x = 0) :
    IsCoordTest (fun x : Coord => θ x.2.1 * scteW a c φ x) := by
  have hcs := support_test a hθ_cs hs₀ hφ_v
  have hraw : IsCoordTest (fun x : Coord => x.1 ^ a * θ x.2.1 * φ x) :=
    ⟨contDiff_test a hθ_cd hφ_s hs₀ (fun y hy => hφ_v y (Or.inl hy)), hcs.1, hcs.2⟩
  have hmul := isCoordTest_mul_smooth (contDiff_const (c := c⁻¹)) hraw
  have heq : (fun x : Coord => c⁻¹ * (x.1 ^ a * θ x.2.1 * φ x)) =
      fun x : Coord => θ x.2.1 * scteW a c φ x := by
    funext x; simp [scteW]; ring
  rwa [heq] at hmul

private lemma scte_cpd_scteW {a c s₀ : ℝ} {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ)
    (hs₀ : 0 < s₀) (hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0) (x : Coord) :
    cpd 0 (scteW a c φ) x = c⁻¹ * (a * x.1 ^ (a - 1) * φ x + x.1 ^ a * cpd 0 φ x) ∧
      cpd 1 (scteW a c φ) x = c⁻¹ * (x.1 ^ a * cpd 1 φ x) ∧
      cpd 2 (scteW a c φ) x = c⁻¹ * (x.1 ^ a * cpd 2 φ x) := by
  have hWs := scteW_contDiff (a := a) (c := c) hφ_s hs₀ hlow
  by_cases hx : x.1 < s₀
  · have hU : IsOpen {y : Coord | y.1 < s₀} := isOpen_lt continuous_fst continuous_const
    have hWz : ∀ y ∈ {y : Coord | y.1 < s₀}, scteW a c φ y = 0 := fun y hy => by
      simp [scteW, hlow y hy]
    have hφz : ∀ y ∈ {y : Coord | y.1 < s₀}, φ y = 0 := fun y hy => hlow y hy
    rw [hlow x hx,
      coef_cpd_vanish hU hWz 0 x hx, coef_cpd_vanish hU hWz 1 x hx, coef_cpd_vanish hU hWz 2 x hx,
      coef_cpd_vanish hU hφz 0 x hx, coef_cpd_vanish hU hφz 1 x hx, coef_cpd_vanish hU hφz 2 x hx]
    simp
  · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
    have hpow : HasFDerivAt (fun y : Coord => y.1 ^ a)
        ((a * x.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
      (Real.hasDerivAt_rpow_const (p := a) (Or.inl hxpos.ne')).comp_hasFDerivAt x
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
    have hφd : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ_s.differentiable (by simp) x).hasFDerivAt
    have hprod : HasFDerivAt (scteW a c φ)
        (c⁻¹ • (x.1 ^ a • fderiv ℝ φ x +
          φ x • ((a * x.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))) x :=
      (hpow.mul hφd).const_mul c⁻¹
    unfold cpd
    rw [hprod.fderiv]
    refine ⟨?_, ?_, ?_⟩
    · simp [cdir]; ring
    · simp [cdir]
    · simp [cdir]

private lemma scte_cpd_q_only {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (x : Coord) :
    cpd 0 (fun y : Coord => θ y.2.1) x = 0 ∧
      cpd 1 (fun y : Coord => θ y.2.1) x = iteratedDeriv 1 θ x.2.1 ∧
      cpd 2 (fun y : Coord => θ y.2.1) x = 0 := by
  let projQ : Coord →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hd : HasFDerivAt (fun y : Coord => θ y.2.1) (deriv θ x.2.1 • projQ) x :=
    (hθ.differentiable (by simp) x.2.1).hasDerivAt.comp_hasFDerivAt x projQ.hasFDerivAt
  unfold cpd
  rw [hd.fderiv, iteratedDeriv_one]
  refine ⟨?_, ?_, ?_⟩ <;> simp [projQ, cdir]

private lemma scte_vGrad_q_only (v : Coord → Fin 3 → ℝ) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (x : Coord) :
    vGrad v (fun y : Coord => θ y.2.1) x = v x 1 * iteratedDeriv 1 θ x.2.1 := by
  obtain ⟨h0, h1, h2⟩ := scte_cpd_q_only hθ x
  unfold vGrad
  rw [Fin.sum_univ_three, h0, h1, h2]
  ring

private lemma scte_coordT_scteW_eta {c s₀ : ℝ} {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ)
    (hs₀ : 0 < s₀) (hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0) (x : Coord) :
    coordTranspose vEta dZero (scteW (-(1 / 2 : ℝ)) c φ) x =
      - scteW (-(1 / 2 : ℝ)) c (cpd 2 φ) x := by
  obtain ⟨-, -, h2⟩ := scte_cpd_scteW (a := -(1 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow x
  rw [qd_coordT_eq]
  have e0 : cpd 0 (fun y => vEta y 0 * scteW (-(1 / 2 : ℝ)) c φ y) x = 0 := by
    simp [vEta, cpd]
  have e1 : cpd 1 (fun y => vEta y 1 * scteW (-(1 / 2 : ℝ)) c φ y) x = 0 := by
    simp [vEta, cpd]
  have e2 : cpd 2 (fun y => vEta y 2 * scteW (-(1 / 2 : ℝ)) c φ y) x =
      cpd 2 (scteW (-(1 / 2 : ℝ)) c φ) x := by
    simp [vEta]
  rw [e0, e1, e2, h2]
  simp [dZero, scteW]

private lemma scte_coordT_scteW_qeps (ε : ℝ) {c s₀ : ℝ} {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ)
    (hs₀ : 0 < s₀) (hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0) (x : Coord) :
    coordTranspose (vQ ε) (dQ ε) (scteW (-(1 / 2 : ℝ)) c φ) x =
      - scteW (-(1 / 2 : ℝ)) c
        (fun y => -2 * ε * y.1 * cpd 0 φ y + cpd 1 φ y - ε * y.2.2 * cpd 2 φ y - ε * φ y) x := by
  set ψ₁ := scteW (-(1 / 2 : ℝ)) c φ
  have hψ₁d : Differentiable ℝ ψ₁ :=
    (scteW_contDiff (a := -(1 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow).differentiable (by simp)
  obtain ⟨c0, c1, c2⟩ := scte_cpd_scteW (a := -(1 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow x
  have m0 := qd_cpd_mul 0 ((contDiff_vQ ε 0).differentiable (by simp)) hψ₁d x
  have m1 := qd_cpd_mul 1 ((contDiff_vQ ε 1).differentiable (by simp)) hψ₁d x
  have m2 := qd_cpd_mul 2 ((contDiff_vQ ε 2).differentiable (by simp)) hψ₁d x
  have dv0 : cpd 0 (fun y : Coord => vQ ε y 0) x = -2 * ε := by
    have hd : HasFDerivAt (fun y : Coord => -2 * ε * y.1)
        ((-2 * ε) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.const_mul (-2 * ε)
    change fderiv ℝ (fun y : Coord => -2 * ε * y.1) x (cdir 0) = -2 * ε
    rw [hd.fderiv]
    simp [cdir]
  have dv1 : cpd 1 (fun y : Coord => vQ ε y 1) x = 0 := by
    change fderiv ℝ (fun _ : Coord => (1 : ℝ)) x (cdir 1) = 0
    simp
  have dv2 : cpd 2 (fun y : Coord => vQ ε y 2) x = -ε := by
    let projEta : Coord →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    have hd : HasFDerivAt (fun y : Coord => -ε * y.2.2) ((-ε) • projEta) x :=
      projEta.hasFDerivAt.const_mul (-ε)
    change fderiv ℝ (fun y : Coord => -ε * y.2.2) x (cdir 2) = -ε
    rw [hd.fderiv]
    simp [projEta, cdir]
  rw [qd_coordT_eq, m0, m1, m2, dv0, dv1, dv2, c0, c1, c2]
  dsimp [ψ₁, scteW, vQ, dQ]
  by_cases hx : x.1 < s₀
  · have hU : IsOpen {y : Coord | y.1 < s₀} := isOpen_lt continuous_fst continuous_const
    have hφz : ∀ y ∈ {y : Coord | y.1 < s₀}, φ y = 0 := fun y hy => hlow y hy
    rw [hlow x hx, coef_cpd_vanish hU hφz 0 x hx, coef_cpd_vanish hU hφz 1 x hx,
      coef_cpd_vanish hU hφz 2 x hx]
    ring
  · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
    have hpow : x.1 * x.1 ^ (-(1 / 2 : ℝ) - 1) = x.1 ^ (-(1 / 2 : ℝ)) := by
      calc x.1 * x.1 ^ (-(1 / 2 : ℝ) - 1)
          = x.1 ^ (1 : ℝ) * x.1 ^ (-(1 / 2 : ℝ) - 1) := by rw [Real.rpow_one]
        _ = x.1 ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    have hpow' : -(1 / 2 : ℝ) * x.1 ^ (-(1 / 2 : ℝ) - 1) * φ x * (-2 * ε * x.1) =
        ε * x.1 ^ (-(1 / 2 : ℝ)) * φ x := by
      calc -(1 / 2 : ℝ) * x.1 ^ (-(1 / 2 : ℝ) - 1) * φ x * (-2 * ε * x.1)
          = ε * (x.1 * x.1 ^ (-(1 / 2 : ℝ) - 1)) * φ x := by ring
        _ = ε * x.1 ^ (-(1 / 2 : ℝ)) * φ x := by rw [hpow]
    linear_combination -(c⁻¹ * hpow')

private lemma scte_lhs_sqrtS_unfold {c s₀ s₁ L : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {Gb : CProf} (hGb : InHr c 2 (sqrtS Gb)) (i : Fin 2)
    {θ : ℝ → ℝ} (hθ_cd : ContDiff ℝ ∞ θ) (hθ_cs : HasCompactSupport θ)
    (hθ_sum1 : ∀ q : ℝ, HasSum (fun n : ℤ => θ (q - n * c)) 1)
    {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ) (hφ_p : ∀ x, φ (qShift c x) = φ x)
    (hφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → φ x = 0) :
    ∫ x, Gb x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c φ x : ℝ) : ℂ) =
      ∫ x, (x.1 : ℂ) * (Gb x i * (φ x : ℂ)) ∂(hMeas c 2) := by
  have hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0 := fun y hy => hφ_v y (Or.inl hy)
  have hW_cd := scteW_contDiff (a := (-1 : ℝ)) (c := c) hφ_s hs₀ hlow
  have hW_per := scteW_per (a := (-1 : ℝ)) hφ_p
  have hW_van := scteW_van (a := (-1 : ℝ)) (c := c) hφ_v
  obtain ⟨-, -, hunf⟩ := scte_unfold_comp hc hs₀ hGb i hθ_cd.continuous hθ_cs hθ_sum1
    hW_cd.continuous hW_per hW_van
  have hptL : (fun x : Coord => Gb x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c φ x : ℝ) : ℂ)) =
      fun x : Coord => (θ x.2.1 : ℂ) * (sqrtS Gb x i * (scteW (-1 : ℝ) c φ x : ℂ)) := by
    funext x
    by_cases hx : x.1 < s₀
    · simp [scteW, hlow x hx]
    · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
      have hsq : Real.sqrt x.1 * x.1 ^ (-1 : ℝ) = x.1 ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
        norm_num
      have hsq_c : ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 ^ (-1 : ℝ) : ℝ) : ℂ) =
          ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hsq
      simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, scteW]
      push_cast
      linear_combination (θ x.2.1 : ℂ) * Gb x i * (c⁻¹ : ℂ) * (φ x : ℂ) * hsq_c.symm
  have hptC : (fun x : Coord => sqrtS Gb x i * (scteW (-1 : ℝ) c φ x : ℂ)) =
      fun x : Coord => ((c⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ((x.1 : ℂ) * (Gb x i * (φ x : ℂ))) := by
    funext x
    by_cases hx : x.1 < s₀
    · simp [scteW, hlow x hx]
    · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
      have h1 : Real.sqrt x.1 * x.1 ^ (-1 : ℝ) = x.1 ^ (-(3 / 2 : ℝ)) * x.1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos,
          show x.1 ^ (-(3 / 2 : ℝ)) * x.1 = x.1 ^ (-(3 / 2 : ℝ)) * x.1 ^ (1 : ℝ) by
            rw [Real.rpow_one], ← Real.rpow_add hxpos]
        norm_num
      have h1_c : ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 ^ (-1 : ℝ) : ℝ) : ℂ) =
          ((x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (x.1 : ℂ) := by exact_mod_cast h1
      simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, scteW]
      push_cast
      linear_combination Gb x i * (c⁻¹ : ℂ) * (φ x : ℂ) * h1_c
  rw [hptL, hunf, Complex.ofReal_one, one_mul, hptC]
  exact scte_cell_to_hMeas hc hs₀ (fun x hx => by simp [hlow x hx])

private lemma scte_rhs_b_unfold {c s₀ s₁ L : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {b : CProf} (hb : InHr c 2 b) (i : Fin 2)
    {θ : ℝ → ℝ} (hθ_cd : ContDiff ℝ ∞ θ) (hθ_cs : HasCompactSupport θ)
    (hθ_sum1 : ∀ q : ℝ, HasSum (fun n : ℤ => θ (q - n * c)) 1)
    {ψ : Coord → ℝ} (hψ_s : ContDiff ℝ ∞ ψ) (hψ_p : ∀ x, ψ (qShift c x) = ψ x)
    (hψ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → ψ x = 0) :
    ∫ x, b x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c ψ x : ℝ) : ℂ) =
      ∫ x, (x.1 : ℂ) * (b x i * (ψ x : ℂ)) ∂(hMeas c 2) := by
  have hlow : ∀ y : Coord, y.1 < s₀ → ψ y = 0 := fun y hy => hψ_v y (Or.inl hy)
  have hW_cd := scteW_contDiff (a := -(1 / 2 : ℝ)) (c := c) hψ_s hs₀ hlow
  have hW_per := scteW_per (a := -(1 / 2 : ℝ)) hψ_p
  have hW_van := scteW_van (a := -(1 / 2 : ℝ)) (c := c) hψ_v
  obtain ⟨-, -, hunf⟩ := scte_unfold_comp hc hs₀ hb i hθ_cd.continuous hθ_cs hθ_sum1
    hW_cd.continuous hW_per hW_van
  have hptL : (fun x : Coord => b x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c ψ x : ℝ) : ℂ)) =
      fun x : Coord => (θ x.2.1 : ℂ) * (b x i * (scteW (-(1 / 2 : ℝ)) c ψ x : ℂ)) := by
    funext x; push_cast; ring
  have hptC : (fun x : Coord => b x i * (scteW (-(1 / 2 : ℝ)) c ψ x : ℂ)) =
      fun x : Coord => ((c⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ((x.1 : ℂ) * (b x i * (ψ x : ℂ))) := by
    funext x
    by_cases hx : x.1 < s₀
    · simp [scteW, hlow x hx]
    · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
      have h1 : x.1 ^ (-(1 / 2 : ℝ)) = x.1 ^ (-(3 / 2 : ℝ)) * x.1 := by
        rw [show x.1 ^ (-(3 / 2 : ℝ)) * x.1 = x.1 ^ (-(3 / 2 : ℝ)) * x.1 ^ (1 : ℝ) by
          rw [Real.rpow_one], ← Real.rpow_add hxpos]
        norm_num
      have h1_c : ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          ((x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (x.1 : ℂ) := by exact_mod_cast h1
      simp only [scteW]
      push_cast
      linear_combination b x i * (c⁻¹ : ℂ) * (ψ x : ℂ) * h1_c
  rw [hptL, hunf, Complex.ofReal_one, one_mul, hptC]
  exact scte_cell_to_hMeas hc hs₀ (fun x hx => by simp [hlow x hx])

private lemma scte_periodic_ibp_Eta_scalar {c s₀ s₁ L : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {b Eb : CProf} (hb : InHr c 2 b) (hEb : InHr c 2 (sqrtS Eb))
    (hw : HasWeakVec vEta dZero b Eb) (i : Fin 2)
    {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ) (hφ_p : ∀ x, φ (qShift c x) = φ x)
    (hφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → φ x = 0) :
    ∫ x, (x.1 : ℂ) * (Eb x i * (φ x : ℂ)) ∂(hMeas c 2) =
      - ∫ x, (x.1 : ℂ) * (b x i * (cpd 2 φ x : ℂ)) ∂(hMeas c 2) := by
  obtain ⟨θ, hθ_cd, hθ_cs, -, hθ_sum1, -⟩ := CellPart.exists_partition_of_derivs hc
  have hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0 := fun y hy => hφ_v y (Or.inl hy)
  set ψ₁ := scteW (-(1 / 2 : ℝ)) c φ
  have htest := scteW_mul_theta_isTest (a := -(1 / 2 : ℝ)) (c := c) hθ_cd hθ_cs hφ_s hs₀ hφ_v
  have heq := (hw i).2 _ htest
  rw [scte_lhs_sqrtS_unfold hc hs₀ hEb i hθ_cd hθ_cs hθ_sum1 hφ_s hφ_p hφ_v] at heq
  have hT : (fun x : Coord => b x i * (coordTranspose vEta dZero (fun y => θ y.2.1 * ψ₁ y) x : ℂ)) =
      fun x : Coord => -(b x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c (cpd 2 φ) x : ℝ) : ℂ)) := by
    funext x
    have hθy : Differentiable ℝ (fun y : Coord => θ y.2.1) :=
      (hθ_cd.comp (contDiff_fst.comp contDiff_snd)).differentiable (by simp)
    have hψ₁d : Differentiable ℝ ψ₁ :=
      (scteW_contDiff (a := -(1 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow).differentiable (by simp)
    rw [coordTranspose_mul_smooth dZero (fun j => (contDiff_vEta j).differentiable (by simp))
      hθy hψ₁d x, scte_vGrad_q_only vEta hθ_cd x,
      show vEta x 1 = 0 from rfl, scte_coordT_scteW_eta hφ_s hs₀ hlow x]
    push_cast
    ring
  have hcpd_s : ContDiff ℝ ∞ (cpd 2 φ) := coef_cpd_contDiff hφ_s 2
  have hcpd_p : ∀ x, cpd 2 φ (qShift c x) = cpd 2 φ x := coef_cpd_per hφ_p 2
  have hcpd_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → cpd 2 φ x = 0 :=
    fun x hx => coef_cpd_vanish (coef_isOpen s₀ s₁ L) hφ_v 2 x hx
  rw [hT, integral_neg,
    scte_rhs_b_unfold hc hs₀ hb i hθ_cd hθ_cs hθ_sum1 hcpd_s hcpd_p hcpd_v] at heq
  exact heq

private lemma scte_periodic_ibp_Q_scalar (ε : ℝ) {c s₀ s₁ L : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {b Qb : CProf} (hb : InHr c 2 b) (hQb : InHr c 2 (sqrtS Qb))
    (hw : HasWeakVec (vQ ε) (dQ ε) b Qb) (i : Fin 2)
    {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ) (hφ_p : ∀ x, φ (qShift c x) = φ x)
    (hφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → φ x = 0) :
    ∫ x, (x.1 : ℂ) * (Qb x i * (φ x : ℂ)) ∂(hMeas c 2) =
      - ∫ x, (x.1 : ℂ) * (b x i *
        ((-2 * ε * x.1 * cpd 0 φ x + cpd 1 φ x - ε * x.2.2 * cpd 2 φ x - ε * φ x : ℝ) : ℂ))
        ∂(hMeas c 2) := by
  obtain ⟨θ, hθ_cd, hθ_cs, -, hθ_sum1, hθ_sumd⟩ := CellPart.exists_partition_of_derivs hc
  have hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0 := fun y hy => hφ_v y (Or.inl hy)
  set ψ₁ := scteW (-(1 / 2 : ℝ)) c φ
  set qφ : Coord → ℝ :=
    fun y => -2 * ε * y.1 * cpd 0 φ y + cpd 1 φ y - ε * y.2.2 * cpd 2 φ y - ε * φ y
  have htest := scteW_mul_theta_isTest (a := -(1 / 2 : ℝ)) (c := c) hθ_cd hθ_cs hφ_s hs₀ hφ_v
  have heq := (hw i).2 _ htest
  rw [scte_lhs_sqrtS_unfold hc hs₀ hQb i hθ_cd hθ_cs hθ_sum1 hφ_s hφ_p hφ_v] at heq
  have hqφ_s : ContDiff ℝ ∞ qφ := by
    dsimp [qφ]
    exact (((((contDiff_const.mul contDiff_fst).mul (coef_cpd_contDiff hφ_s 0)).add
      (coef_cpd_contDiff hφ_s 1)).sub
      ((contDiff_const.mul (contDiff_snd.comp contDiff_snd)).mul (coef_cpd_contDiff hφ_s 2))).sub
      (contDiff_const.mul hφ_s))
  have hqφ_p : ∀ x, qφ (qShift c x) = qφ x := by
    intro x
    dsimp [qφ]
    rw [show (qShift c x).2.2 = x.2.2 from rfl,
      coef_cpd_per hφ_p 0 x, coef_cpd_per hφ_p 1 x, coef_cpd_per hφ_p 2 x, hφ_p x]
  have hqφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → qφ x = 0 := by
    intro x hx
    have hU := coef_isOpen s₀ s₁ L
    dsimp [qφ]
    rw [coef_cpd_vanish hU hφ_v 0 x hx, coef_cpd_vanish hU hφ_v 1 x hx,
      coef_cpd_vanish hU hφ_v 2 x hx, hφ_v x hx]
    ring
  have hlow_q : ∀ y : Coord, y.1 < s₀ → qφ y = 0 := fun y hy => hqφ_v y (Or.inl hy)
  have hWq_cd := scteW_contDiff (a := -(1 / 2 : ℝ)) (c := c) hqφ_s hs₀ hlow_q
  have hW_cd := scteW_contDiff (a := -(1 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow
  have hdθ_cont : Continuous (iteratedDeriv 1 θ) := by
    rw [iteratedDeriv_one]; exact hθ_cd.continuous_deriv (by simp)
  have hdθ_cs : HasCompactSupport (iteratedDeriv 1 θ) := by
    rw [iteratedDeriv_one]; exact hθ_cs.deriv
  obtain ⟨iA, -, -⟩ := scte_unfold_comp hc hs₀ hb i hθ_cd.continuous hθ_cs hθ_sum1
    hWq_cd.continuous (scteW_per hqφ_p) (scteW_van hqφ_v)
  obtain ⟨iB, -, hunfB⟩ := scte_unfold_comp hc hs₀ hb i hdθ_cont hdθ_cs (hθ_sumd 0)
    hW_cd.continuous (scteW_per hφ_p) (scteW_van hφ_v)
  have hT : (fun x : Coord => b x i *
        (coordTranspose (vQ ε) (dQ ε) (fun y => θ y.2.1 * ψ₁ y) x : ℂ)) =
      fun x : Coord =>
        -(b x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c qφ x : ℝ) : ℂ)) -
          (((iteratedDeriv 1 θ x.2.1 : ℝ) : ℂ) * (b x i * (ψ₁ x : ℂ))) := by
    funext x
    have hθy : Differentiable ℝ (fun y : Coord => θ y.2.1) :=
      (hθ_cd.comp (contDiff_fst.comp contDiff_snd)).differentiable (by simp)
    rw [coordTranspose_mul_smooth (dQ ε) (fun j => (contDiff_vQ ε j).differentiable (by simp))
      hθy (hW_cd.differentiable (by simp)) x,
      scte_vGrad_q_only (vQ ε) hθ_cd x, show vQ ε x 1 = 1 from rfl, one_mul,
      scte_coordT_scteW_qeps ε hφ_s hs₀ hlow x]
    push_cast
    ring
  have iA' : Integrable (fun x : Coord =>
      -(b x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c qφ x : ℝ) : ℂ))) volume := by
    refine iA.neg.congr (ae_of_all _ fun x => ?_)
    change -((θ x.2.1 : ℂ) * (b x i * (scteW (-(1 / 2 : ℝ)) c qφ x : ℂ))) = _
    push_cast
    ring
  rw [hT, integral_sub iA' iB, hunfB, Complex.ofReal_zero, zero_mul, sub_zero, integral_neg,
    scte_rhs_b_unfold hc hs₀ hb i hθ_cd hθ_cs hθ_sum1 hqφ_s hqφ_p hqφ_v] at heq
  exact heq

private lemma scte_nice_add {c : ℝ} {f g : CProf} (hf : NiceProf c f) (hg : NiceProf c g) :
    NiceProf c (fun x => f x + g x) := by
  obtain ⟨hfs, hfp, s₀, s₁, L, hs₀, hfv⟩ := hf
  obtain ⟨hgs, hgp, t₀, t₁, M, ht₀, hgv⟩ := hg
  refine ⟨hfs.add hgs, fun x => by dsimp only; rw [hfp x, hgp x],
    min s₀ t₀, max s₁ t₁, max L M, lt_min hs₀ ht₀, fun x hx => ?_⟩
  have hf0 : f x = 0 := by
    apply hfv x
    rcases hx with h1 | h2 | h3
    · exact Or.inl (lt_of_lt_of_le h1 (min_le_left _ _))
    · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_left _ _) h2))
    · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_left _ _) h3))
  have hg0 : g x = 0 := by
    apply hgv x
    rcases hx with h1 | h2 | h3
    · exact Or.inl (lt_of_lt_of_le h1 (min_le_right _ _))
    · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_right _ _) h2))
    · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_right _ _) h3))
  dsimp only
  rw [hf0, hg0, add_zero]

private lemma scte_nice_smul {c : ℝ} (a : ℂ) {f : CProf} (hf : NiceProf c f) :
    NiceProf c (fun x => a • f x) := by
  obtain ⟨hfs, hfp, s₀, s₁, L, hs₀, hfv⟩ := hf
  have hcd : ContDiff ℝ ∞ (fun x : Coord => a • f x) := (contDiff_const (c := a)).smul hfs
  exact ⟨hcd, fun x => by dsimp only; rw [hfp x], s₀, s₁, L, hs₀,
    fun x hx => by dsimp only; rw [hfv x hx, smul_zero]⟩

private lemma scte_nice_sub {c : ℝ} {f g : CProf} (hf : NiceProf c f) (hg : NiceProf c g) :
    NiceProf c (fun x => f x - g x) := by
  have h := scte_nice_add hf (scte_nice_smul (-1 : ℂ) hg)
  simpa [sub_eq_add_neg] using h

private lemma scte_nice_mulS {c : ℝ} {f : CProf} (hf : NiceProf c f) :
    NiceProf c (fun x => (x.1 : ℂ) • f x) := by
  obtain ⟨hfs, hfp, s₀, s₁, L, hs₀, hfv⟩ := hf
  have hcd : ContDiff ℝ ∞ (fun x : Coord => (x.1 : ℂ) • f x) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul hfs
  exact ⟨hcd, fun x => by simp [hfp x],
    s₀, s₁, L, hs₀, fun x hx => by dsimp only; rw [hfv x hx, smul_zero]⟩

private lemma scte_nice_sqrtS {c : ℝ} {f : CProf} (hf : NiceProf c f) :
    NiceProf c (sqrtS f) := by
  obtain ⟨hfs, hfp, s₀, s₁, L, hs₀, hfv⟩ := hf
  have hcd : ContDiff ℝ ∞ (sqrtS f) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : s₀ ≤ x.1
    · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ hx
      have hsq : ContDiffAt ℝ ∞ (fun y : Coord => (Real.sqrt y.1 : ℂ)) x := by
        have h1 : ContDiffAt ℝ ∞ (fun y : Coord => y.1 ^ (1 / 2 : ℝ)) x :=
          (Real.contDiffAt_rpow_const_of_ne (n := ∞) (p := (1 / 2 : ℝ)) hxpos.ne').comp x
            contDiffAt_fst
        have heq : (fun y : Coord => (Real.sqrt y.1 : ℂ)) =
            fun y : Coord => ((y.1 ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
          funext y; rw [Real.sqrt_eq_rpow]
        rw [heq]
        exact Complex.ofRealCLM.contDiff.contDiffAt.comp x h1
      exact hsq.smul hfs.contDiffAt
    · have hx' : x.1 < s₀ := lt_of_not_ge hx
      have hev : (fun _ : Coord => (0 : CMerid)) =ᶠ[𝓝 x] sqrtS f := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hx'] with y hy
        simp [sqrtS, hfv y (Or.inl hy)]
      exact contDiffAt_const.congr_of_eventuallyEq hev.symm
  exact ⟨hcd, fun x => by simp [sqrtS, hfp x],
    s₀, s₁, L, hs₀, fun x hx => by simp [sqrtS, hfv x hx]⟩

private def scteHoopCLM : CMerid →L[ℝ] CMerid :=
  LinearMap.toContinuousLinearMap
    { toFun := hoopE
      map_add' := fun v w => by
        ext i; unfold hoopE EuclideanSpace.single; fin_cases i <;> simp
      map_smul' := fun r v => by
        ext i; unfold hoopE EuclideanSpace.single; fin_cases i <;> simp }

private lemma scte_nice_hoopE {c : ℝ} {f : CProf} (hf : NiceProf c f) :
    NiceProf c (fun x => hoopE (f x)) := by
  obtain ⟨hfs, hfp, s₀, s₁, L, hs₀, hfv⟩ := hf
  have hcd : ContDiff ℝ ∞ (fun x => hoopE (f x)) := scteHoopCLM.contDiff.comp hfs
  exact ⟨hcd, fun x => by simp [hoopE, hfp x],
    s₀, s₁, L, hs₀, fun x hx => by simp [hoopE, hfv x hx]⟩

private lemma scte_nice_fderiv_dir {c : ℝ} (j : Fin 3) {f : CProf} (hf : NiceProf c f) :
    NiceProf c (fun x => fderiv ℝ f x (cdir j)) := by
  obtain ⟨hfs, hfp, s₀, s₁, L, hs₀, hfv⟩ := hf
  have hfd : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (cdir j)) :=
    (hfs.fderiv_right (by simp)).clm_apply contDiff_const
  refine ⟨hfd, fun x => ?_, s₀, s₁, L, hs₀, fun x hx => ?_⟩
  · have hqy : ∀ y : Coord, y + (0, (c, 0)) = qShift c y := fun ⟨s, q, η⟩ => by simp [qShift]
    have hcomp_eq : (fun y : Coord => f (y + (0, (c, 0)))) = f :=
      funext fun y => by rw [hqy y, hfp y]
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (0, (c, 0))
    rw [hcomp_eq, hqy x] at h
    dsimp only
    rw [← h]
  · have hev : f =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventuallyEq_of_mem ((coef_isOpen s₀ s₁ L).mem_nhds hx) fun y hy => hfv y hy
    dsimp only
    rw [hev.fderiv_eq]
    simp

private lemma scte_weighted_comp_int {c : ℝ} (hc : 0 < c) {Gb Ψ : CProf}
    (hGb : InHr c 2 (sqrtS Gb)) (hΨ : NiceProf c Ψ) (i : Fin 2) :
    Integrable (fun x : Coord => (x.1 : ℂ) * (Gb x i * Ψ x i)) (hMeas c 2) := by
  have hsΨ : InHr c 2 (sqrtS Ψ) := scte_nice_inHr hc (scte_nice_sqrtS hΨ)
  have hint := scte_comp_unconj_int hGb.meas hGb.finite hsΨ.meas hsΨ.finite i
  refine hint.congr ?_
  filter_upwards [scte_hMeas_pos c 2] with x hxpos
  have hsq : ((Real.sqrt x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = (x.1 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hxpos.le]
  simp only [sqrtS, PiLp.smul_apply, smul_eq_mul]
  linear_combination Gb x i * Ψ x i * hsq

private lemma scte_periodic_ibp_Eta_nice {c : ℝ} (hc : 0 < c) {b Eb Ψ : CProf}
    (hb : InHr c 2 b) (hEb : InHr c 2 (sqrtS Eb)) (hw : HasWeakVec vEta dZero b Eb)
    (hΨ : NiceProf c Ψ) :
    ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Eb x i * Ψ x i ∂(hMeas c 2) =
      - ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, b x i * classEta Ψ x i ∂(hMeas c 2) := by
  have hEΨ_nice : NiceProf c (classEta Ψ) := (lapNiceClass_proof c 0 Ψ hΨ).2
  have hsEΨ_in : InHr c 2 (fun x => (x.1 : ℂ) • classEta Ψ x) :=
    scte_nice_inHr hc (scte_nice_mulS hEΨ_nice)
  have hcomp : ∀ i : Fin 2,
      ∫ x, (x.1 : ℂ) * (Eb x i * Ψ x i) ∂(hMeas c 2) =
        - ∫ x, (x.1 : ℂ) * (b x i * classEta Ψ x i) ∂(hMeas c 2) := by
    intro i
    obtain ⟨hre_s, hre_p, him_s, him_p, s₀, s₁, L, hs₀, hre_v, him_v⟩ := scte_nice_comp_props hΨ i
    have ere := scte_periodic_ibp_Eta_scalar hc hs₀ hb hEb hw i hre_s hre_p hre_v
    have eim := scte_periodic_ibp_Eta_scalar hc hs₀ hb hEb hw i him_s him_p him_v
    have iL_full := scte_weighted_comp_int hc hEb hΨ i
    have iR_full : Integrable (fun x => (x.1 : ℂ) * (b x i * classEta Ψ x i)) (hMeas c 2) := by
      have h := scte_comp_unconj_int hb.meas hb.finite hsEΨ_in.meas hsEΨ_in.finite i
      refine h.congr (ae_of_all _ fun x => ?_)
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    set fL1 : Coord → ℂ := fun x => (x.1 : ℂ) * (Eb x i * (((Ψ x i).re : ℝ) : ℂ))
    set fL2 : Coord → ℂ := fun x => (x.1 : ℂ) * (Eb x i * (((Ψ x i).im : ℝ) : ℂ))
    set fR1 : Coord → ℂ := fun x => (x.1 : ℂ) * (b x i * ((cpd 2 (fun y => (Ψ y i).re) x : ℝ) : ℂ))
    set fR2 : Coord → ℂ := fun x => (x.1 : ℂ) * (b x i * ((cpd 2 (fun y => (Ψ y i).im) x : ℝ) : ℂ))
    have hmEb : AEStronglyMeasurable (fun x => (x.1 : ℂ) * Eb x i) (hMeas c 2) := by
      have hm1 : AEStronglyMeasurable (fun x => sqrtS Eb x i) (hMeas c 2) :=
        (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hEb.meas
      have hm2 : Measurable (fun x : Coord => (Real.sqrt x.1 : ℂ)) :=
        Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)
      refine (hm2.aestronglyMeasurable.mul hm1).congr ?_
      filter_upwards [scte_hMeas_pos c 2] with x hxpos
      simp only [Pi.mul_apply, sqrtS, PiLp.smul_apply, smul_eq_mul]
      have hsq : ((Real.sqrt x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = (x.1 : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hxpos.le]
      linear_combination Eb x i * hsq
    have iL1 : Integrable fL1 (hMeas c 2) := by
      refine iL_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmEb.mul (Complex.continuous_ofReal.comp hre_s.continuous).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fL1]; ring)
      · dsimp [fL1]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have iL2 : Integrable fL2 (hMeas c 2) := by
      refine iL_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmEb.mul (Complex.continuous_ofReal.comp him_s.continuous).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fL2]; ring)
      · dsimp [fL2]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have hmb : AEStronglyMeasurable (fun x => (x.1 : ℂ) * b x i) (hMeas c 2) :=
      (Complex.measurable_ofReal.comp measurable_fst).aestronglyMeasurable.mul
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb.meas)
    have iR1 : Integrable fR1 (hMeas c 2) := by
      refine iR_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmb.mul (Complex.continuous_ofReal.comp
          (coef_cpd_contDiff hre_s 2).continuous).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fR1]; ring)
      · dsimp [fR1]
        have hre_eq : cpd 2 (fun y => (Ψ y i).re) x = (classEta Ψ x i).re := by
          unfold classEta; rw [scte_fderiv_re_im hΨ.1 x 2 i]; simp
        rw [hre_eq, norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have iR2 : Integrable fR2 (hMeas c 2) := by
      refine iR_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmb.mul (Complex.continuous_ofReal.comp
          (coef_cpd_contDiff him_s 2).continuous).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fR2]; ring)
      · dsimp [fR2]
        have him_eq : cpd 2 (fun y => (Ψ y i).im) x = (classEta Ψ x i).im := by
          unfold classEta; rw [scte_fderiv_re_im hΨ.1 x 2 i]; simp
        rw [him_eq, norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have hsplitL : (fun x => (x.1 : ℂ) * (Eb x i * Ψ x i)) =
        fun x => fL1 x + Complex.I * fL2 x := by
      funext x
      have h1 : (((Ψ x i).re : ℝ) : ℂ) + Complex.I * (((Ψ x i).im : ℝ) : ℂ) = Ψ x i := by
        rw [mul_comm]; exact Complex.re_add_im _
      dsimp [fL1, fL2]
      linear_combination (x.1 : ℂ) * Eb x i * h1.symm
    have hsplitR : (fun x => (x.1 : ℂ) * (b x i * classEta Ψ x i)) =
        fun x => fR1 x + Complex.I * fR2 x := by
      funext x
      unfold classEta
      rw [scte_fderiv_re_im hΨ.1 x 2 i]
      dsimp [fR1, fR2]
      ring
    change ∫ x, fL1 x ∂(hMeas c 2) = - ∫ x, fR1 x ∂(hMeas c 2) at ere
    change ∫ x, fL2 x ∂(hMeas c 2) = - ∫ x, fR2 x ∂(hMeas c 2) at eim
    rw [hsplitL, integral_add iL1 (iL2.const_mul Complex.I), integral_const_mul,
      ere, eim, hsplitR, integral_add iR1 (iR2.const_mul Complex.I), integral_const_mul]
    ring
  have hsumL : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2, Eb x i * Ψ x i) =
      fun x => (x.1 : ℂ) * (Eb x 0 * Ψ x 0) + (x.1 : ℂ) * (Eb x 1 * Ψ x 1) := by
    funext x; rw [Fin.sum_univ_two]; ring
  have hsumR : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2, b x i * classEta Ψ x i) =
      fun x => (x.1 : ℂ) * (b x 0 * classEta Ψ x 0) + (x.1 : ℂ) * (b x 1 * classEta Ψ x 1) := by
    funext x; rw [Fin.sum_univ_two]; ring
  have i0L := scte_weighted_comp_int hc hEb hΨ 0
  have i1L := scte_weighted_comp_int hc hEb hΨ 1
  have i0R : Integrable (fun x => (x.1 : ℂ) * (b x 0 * classEta Ψ x 0)) (hMeas c 2) :=
    (scte_comp_unconj_int hb.meas hb.finite hsEΨ_in.meas hsEΨ_in.finite 0).congr
      (ae_of_all _ fun x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
  have i1R : Integrable (fun x => (x.1 : ℂ) * (b x 1 * classEta Ψ x 1)) (hMeas c 2) :=
    (scte_comp_unconj_int hb.meas hb.finite hsEΨ_in.meas hsEΨ_in.finite 1).congr
      (ae_of_all _ fun x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
  rw [hsumL, hsumR, integral_add i0L i1L, integral_add i0R i1R, hcomp 0, hcomp 1]
  ring

private lemma scte_periodic_ibp_Q_nice {c : ℝ} (hc : 0 < c) (ε : ℝ) {b Qb Ψ : CProf}
    (hb : InHr c 2 b) (hQb : InHr c 2 (sqrtS Qb)) (hw : HasWeakVec (vQ ε) (dQ ε) b Qb)
    (hΨ : NiceProf c Ψ) :
    ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qb x i * Ψ x i ∂(hMeas c 2) =
      - ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, b x i * classQ ε Ψ x i ∂(hMeas c 2) := by
  have hQΨ_nice : NiceProf c (classQ ε Ψ) := (lapNiceClass_proof c ε Ψ hΨ).1
  have hsQΨ_in : InHr c 2 (fun x => (x.1 : ℂ) • classQ ε Ψ x) :=
    scte_nice_inHr hc (scte_nice_mulS hQΨ_nice)
  have hclassQ_re_im : ∀ (x : Coord) (i : Fin 2),
      classQ ε Ψ x i =
        ((-2 * ε * x.1 * cpd 0 (fun y => (Ψ y i).re) x + cpd 1 (fun y => (Ψ y i).re) x -
            ε * x.2.2 * cpd 2 (fun y => (Ψ y i).re) x - ε * (Ψ x i).re : ℝ) : ℂ) +
        Complex.I *
          ((-2 * ε * x.1 * cpd 0 (fun y => (Ψ y i).im) x + cpd 1 (fun y => (Ψ y i).im) x -
              ε * x.2.2 * cpd 2 (fun y => (Ψ y i).im) x - ε * (Ψ x i).im : ℝ) : ℂ) := by
    intro x i
    have h1 : Ψ x i = (((Ψ x i).re : ℝ) : ℂ) + Complex.I * (((Ψ x i).im : ℝ) : ℂ) := by
      rw [mul_comm]; exact (Complex.re_add_im _).symm
    unfold classQ
    rw [Fin.sum_univ_three]
    dsimp [vQ, dQ]
    rw [scte_fderiv_re_im hΨ.1 x 0 i, scte_fderiv_re_im hΨ.1 x 1 i, scte_fderiv_re_im hΨ.1 x 2 i]
    conv_lhs => rw [h1]
    push_cast
    ring
  have hcomp : ∀ i : Fin 2,
      ∫ x, (x.1 : ℂ) * (Qb x i * Ψ x i) ∂(hMeas c 2) =
        - ∫ x, (x.1 : ℂ) * (b x i * classQ ε Ψ x i) ∂(hMeas c 2) := by
    intro i
    obtain ⟨hre_s, hre_p, him_s, him_p, s₀, s₁, L, hs₀, hre_v, him_v⟩ := scte_nice_comp_props hΨ i
    have ere := scte_periodic_ibp_Q_scalar ε hc hs₀ hb hQb hw i hre_s hre_p hre_v
    have eim := scte_periodic_ibp_Q_scalar ε hc hs₀ hb hQb hw i him_s him_p him_v
    have iL_full := scte_weighted_comp_int hc hQb hΨ i
    have iR_full : Integrable (fun x => (x.1 : ℂ) * (b x i * classQ ε Ψ x i)) (hMeas c 2) :=
      (scte_comp_unconj_int hb.meas hb.finite hsQΨ_in.meas hsQΨ_in.finite i).congr
        (ae_of_all _ fun x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
    set qre : Coord → ℝ := fun x =>
      -2 * ε * x.1 * cpd 0 (fun y => (Ψ y i).re) x + cpd 1 (fun y => (Ψ y i).re) x -
        ε * x.2.2 * cpd 2 (fun y => (Ψ y i).re) x - ε * (Ψ x i).re
    set qim : Coord → ℝ := fun x =>
      -2 * ε * x.1 * cpd 0 (fun y => (Ψ y i).im) x + cpd 1 (fun y => (Ψ y i).im) x -
        ε * x.2.2 * cpd 2 (fun y => (Ψ y i).im) x - ε * (Ψ x i).im
    set fL1 : Coord → ℂ := fun x => (x.1 : ℂ) * (Qb x i * (((Ψ x i).re : ℝ) : ℂ))
    set fL2 : Coord → ℂ := fun x => (x.1 : ℂ) * (Qb x i * (((Ψ x i).im : ℝ) : ℂ))
    set fR1 : Coord → ℂ := fun x => (x.1 : ℂ) * (b x i * (qre x : ℂ))
    set fR2 : Coord → ℂ := fun x => (x.1 : ℂ) * (b x i * (qim x : ℂ))
    have hmQb : AEStronglyMeasurable (fun x => (x.1 : ℂ) * Qb x i) (hMeas c 2) := by
      have hm1 : AEStronglyMeasurable (fun x => sqrtS Qb x i) (hMeas c 2) :=
        (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hQb.meas
      have hm2 : Measurable (fun x : Coord => (Real.sqrt x.1 : ℂ)) :=
        Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)
      refine (hm2.aestronglyMeasurable.mul hm1).congr ?_
      filter_upwards [scte_hMeas_pos c 2] with x hxpos
      simp only [Pi.mul_apply, sqrtS, PiLp.smul_apply, smul_eq_mul]
      have hsq : ((Real.sqrt x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = (x.1 : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hxpos.le]
      linear_combination Qb x i * hsq
    have iL1 : Integrable fL1 (hMeas c 2) := by
      refine iL_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmQb.mul (Complex.continuous_ofReal.comp hre_s.continuous).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fL1]; ring)
      · dsimp [fL1]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have iL2 : Integrable fL2 (hMeas c 2) := by
      refine iL_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmQb.mul (Complex.continuous_ofReal.comp him_s.continuous).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fL2]; ring)
      · dsimp [fL2]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have hmb : AEStronglyMeasurable (fun x => (x.1 : ℂ) * b x i) (hMeas c 2) :=
      (Complex.measurable_ofReal.comp measurable_fst).aestronglyMeasurable.mul
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb.meas)
    have hqre_c : Continuous qre := by
      dsimp [qre]
      exact (((((continuous_const.mul continuous_fst).mul
        (coef_cpd_contDiff hre_s 0).continuous).add (coef_cpd_contDiff hre_s 1).continuous).sub
        ((continuous_const.mul (continuous_snd.comp continuous_snd)).mul
          (coef_cpd_contDiff hre_s 2).continuous)).sub (continuous_const.mul hre_s.continuous))
    have hqim_c : Continuous qim := by
      dsimp [qim]
      exact (((((continuous_const.mul continuous_fst).mul
        (coef_cpd_contDiff him_s 0).continuous).add (coef_cpd_contDiff him_s 1).continuous).sub
        ((continuous_const.mul (continuous_snd.comp continuous_snd)).mul
          (coef_cpd_contDiff him_s 2).continuous)).sub (continuous_const.mul him_s.continuous))
    have iR1 : Integrable fR1 (hMeas c 2) := by
      refine iR_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmb.mul (Complex.continuous_ofReal.comp hqre_c).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fR1]; ring)
      · dsimp [fR1]
        have hre_eq : qre x = (classQ ε Ψ x i).re := by
          rw [hclassQ_re_im x i]; simp [qre]
        rw [hre_eq, norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have iR2 : Integrable fR2 (hMeas c 2) := by
      refine iR_full.mono ?_ (ae_of_all _ fun x => ?_)
      · exact (hmb.mul (Complex.continuous_ofReal.comp hqim_c).aestronglyMeasurable).congr
          (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply, fR2]; ring)
      · dsimp [fR2]
        have him_eq : qim x = (classQ ε Ψ x i).im := by
          rw [hclassQ_re_im x i]; simp [qim]
        rw [him_eq, norm_mul, norm_mul, norm_mul, norm_mul]
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)) (abs_nonneg _)
    have hsplitL : (fun x => (x.1 : ℂ) * (Qb x i * Ψ x i)) =
        fun x => fL1 x + Complex.I * fL2 x := by
      funext x
      have h1 : (((Ψ x i).re : ℝ) : ℂ) + Complex.I * (((Ψ x i).im : ℝ) : ℂ) = Ψ x i := by
        rw [mul_comm]; exact Complex.re_add_im _
      dsimp [fL1, fL2]
      linear_combination (x.1 : ℂ) * Qb x i * h1.symm
    have hsplitR : (fun x => (x.1 : ℂ) * (b x i * classQ ε Ψ x i)) =
        fun x => fR1 x + Complex.I * fR2 x := by
      funext x
      rw [hclassQ_re_im x i]
      dsimp [fR1, fR2, qre, qim]
      ring
    change ∫ x, fL1 x ∂(hMeas c 2) = - ∫ x, fR1 x ∂(hMeas c 2) at ere
    change ∫ x, fL2 x ∂(hMeas c 2) = - ∫ x, fR2 x ∂(hMeas c 2) at eim
    rw [hsplitL, integral_add iL1 (iL2.const_mul Complex.I), integral_const_mul,
      ere, eim, hsplitR, integral_add iR1 (iR2.const_mul Complex.I), integral_const_mul]
    ring
  have hsumL : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2, Qb x i * Ψ x i) =
      fun x => (x.1 : ℂ) * (Qb x 0 * Ψ x 0) + (x.1 : ℂ) * (Qb x 1 * Ψ x 1) := by
    funext x; rw [Fin.sum_univ_two]; ring
  have hsumR : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2, b x i * classQ ε Ψ x i) =
      fun x => (x.1 : ℂ) * (b x 0 * classQ ε Ψ x 0) + (x.1 : ℂ) * (b x 1 * classQ ε Ψ x 1) := by
    funext x; rw [Fin.sum_univ_two]; ring
  have i0L := scte_weighted_comp_int hc hQb hΨ 0
  have i1L := scte_weighted_comp_int hc hQb hΨ 1
  have i0R : Integrable (fun x => (x.1 : ℂ) * (b x 0 * classQ ε Ψ x 0)) (hMeas c 2) :=
    (scte_comp_unconj_int hb.meas hb.finite hsQΨ_in.meas hsQΨ_in.finite 0).congr
      (ae_of_all _ fun x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
  have i1R : Integrable (fun x => (x.1 : ℂ) * (b x 1 * classQ ε Ψ x 1)) (hMeas c 2) :=
    (scte_comp_unconj_int hb.meas hb.finite hsQΨ_in.meas hsQΨ_in.finite 1).congr
      (ae_of_all _ fun x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
  rw [hsumL, hsumR, integral_add i0L i1L, integral_add i0R i1R, hcomp 0, hcomp 1]
  ring

private def scte_CL2 : ℝ :=
  letI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨(ENNReal.one_lt_ofReal.2 one_lt_two).le⟩
  ‖UnforcedLeray.RieszLp.lerayC (ENNReal.ofReal 2)
    (ENNReal.one_lt_ofReal.2 one_lt_two) ENNReal.ofReal_ne_top‖

private lemma scte_CL2_nonneg : 0 ≤ scte_CL2 := by
  unfold scte_CL2
  exact norm_nonneg _

private lemma scte_phys_nice_eq {ν c ε : ℝ} {μ : ℂ} (hc : 0 < c) (_hν : 0 < ν) (hε : 0 < ε)
    {F bε Sbε' Qbε' Ebε' B : CProf}
    (hF : InHr c 2 F) (hbε_in : InHr c 2 bε) (hbε_resp : IsResponse ν c ε μ 2 F bε)
    (hSbε'_in : InHr c 2 Sbε') (hQbε'_in : InHr c 2 (sqrtS Qbε'))
    (hEbε'_in : InHr c 2 (sqrtS Ebε'))
    (hSε' : HasWeakVec vS dZero bε Sbε') (hQε' : HasWeakVec (vQ ε) (dQ ε) bε Qbε')
    (hEε' : HasWeakVec vEta dZero bε Ebε') (hB : NiceProf c B) :
    ‖(μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qbε' x i * (starRingEnd ℂ) (classQ ε B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Ebε' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) +
        ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
          (bε x 0 * (starRingEnd ℂ) (B x 0)) ∂(hMeas c 2))‖ ≤
      3 * scte_CL2 * (hNorm c 2 F).toReal * (hNorm c 2 B).toReal := by
  set P := 2 * ε * c
  have hP0 : 0 < P := by positivity
  let _ : Fact (0 < P) := ⟨hP0⟩
  have h1' : 1 < ENNReal.ofReal 2 := ENNReal.one_lt_ofReal.2 one_lt_two
  let _ : Fact (1 ≤ ENNReal.ofReal 2) := ⟨h1'.le⟩
  set Ψ := scteConj B
  have hΨ : NiceProf c Ψ := scteConj_nice hB
  have hΨ_in : InHr c 2 Ψ := scte_nice_inHr hc hΨ
  set QΨ := classQ ε Ψ
  set EΨ := classEta Ψ
  have hQΨ : NiceProf c QΨ := (lapNiceClass_proof c ε Ψ hΨ).1
  have hEΨ : NiceProf c EΨ := (lapNiceClass_proof c ε Ψ hΨ).2
  set Q2Ψ := classQ ε QΨ
  set E2Ψ := classEta EΨ
  have hQ2Ψ : NiceProf c Q2Ψ := (lapNiceClass_proof c ε QΨ hQΨ).1
  have hE2Ψ : NiceProf c E2Ψ := (lapNiceClass_proof c ε EΨ hEΨ).2
  set D0 : CProf := fun x => x.1 • fderiv ℝ Ψ x (cdir 0) + (1 / 2 : ℂ) • Ψ x
  have hD0_nice : NiceProf c D0 :=
    scte_nice_add
      (by
        have h := scte_nice_mulS (scte_nice_fderiv_dir 0 hΨ)
        simpa [Complex.real_smul] using h)
      (scte_nice_smul (1 / 2 : ℂ) hΨ)
  set LΨ : CProf := lapProf ν ε Ψ Q2Ψ E2Ψ
  have hLΨ_nice : NiceProf c LΨ := by
    have h1 := scte_nice_sub (scte_nice_add hQ2Ψ hE2Ψ)
      (scte_nice_smul ((ε ^ 2 : ℝ) : ℂ) (scte_nice_hoopE hΨ))
    have h2 := scte_nice_smul (ν : ℂ) (scte_nice_mulS h1)
    refine ⟨?_, ?_, ?_⟩
    · have heq : LΨ = fun x => (ν : ℂ) • ((x.1 : ℂ) • ((Q2Ψ x + E2Ψ x) - ((ε ^ 2 : ℝ) : ℂ) • hoopE (Ψ x))) := by
        funext x; unfold LΨ lapProf; push_cast; module
      rw [heq]; exact h2.1
    · intro x
      have heq : ∀ y, LΨ y = (ν : ℂ) • ((y.1 : ℂ) • ((Q2Ψ y + E2Ψ y) - ((ε ^ 2 : ℝ) : ℂ) • hoopE (Ψ y))) := by
        intro y; unfold LΨ lapProf; push_cast; module
      rw [heq, heq]; exact h2.2.1 x
    · obtain ⟨s₀, s₁, L, hs₀, hv⟩ := h2.2.2
      refine ⟨s₀, s₁, L, hs₀, fun x hx => ?_⟩
      have h0 := hv x hx
      dsimp only at h0
      have heq : LΨ x = (ν : ℂ) • ((x.1 : ℂ) • ((Q2Ψ x + E2Ψ x) - ((ε ^ 2 : ℝ) : ℂ) • hoopE (Ψ x))) := by
        unfold LΨ lapProf; push_cast; module
      rw [heq, h0]
  set H_phys : CProf := fun x => ((μ + 1 : ℂ) • Ψ x - D0 x) - LΨ x
  have hH_nice : NiceProf c H_phys :=
    scte_nice_sub (scte_nice_sub (scte_nice_smul (μ + 1 : ℂ) hΨ) hD0_nice) hLΨ_nice
  set Φ := NvC ε⁻¹ Ψ
  have hΦ : UnforcedLeray.PhaseSpace.IsPhaseTest P Φ := nvCNicePhaseTest_proof c ε Ψ hc hε hΨ
  have hpt_op : (fun p : ℝ × Space => UnforcedLeray.B0411.L0T ν Φ p + μ • Φ p) =
      NvC ε⁻¹ H_phys := by
    funext p
    have hd := _root_.nvCDriftPtw_proof c ε Ψ hc hε hΨ p
    have hl := lapPtwise_proof c ε ν Ψ hc hε hΨ p.1 p.2
    have hlin1 := nvCLin_proof ε⁻¹ (μ + 1 : ℂ) Ψ D0 p
    have hlin2 := nvCLin_proof ε⁻¹ (1 : ℂ) (fun x => (μ + 1 : ℂ) • Ψ x - D0 x) LΨ p
    have hH_eq : NvC ε⁻¹ H_phys p = (μ + 1 : ℂ) • Φ p - NvC ε⁻¹ D0 p - NvC ε⁻¹ LΨ p := by
      simpa only [H_phys, Φ, one_smul, hlin1] using hlin2
    rw [hH_eq, ← hd, ← hl]
    simp only [UnforcedLeray.B0411.L0T, UnforcedLeray.PhaseSpace.driftT, Pi.sub_apply,
      Pi.smul_apply]
    module
  -- Abstract body equation pairing
  have hfY := nvCInYr_proof c ε 2 F hc hε two_pos hF
  obtain ⟨Ff, hFrep, hFn⟩ := exists_hasRepY P 2 two_pos (NvC ε⁻¹ F) hfY
  obtain ⟨Wq, hWrep, -⟩ := exists_hasRepY P 2 two_pos (NvC ε⁻¹ bε) hbε_resp.mem_w
  obtain ⟨-, hD, -, hbody⟩ :=
    (isFreeResponse_iff two_pos lerayPairSol solSeparation one_lt_two hFrep hWrep).1 hbε_resp
  set PF_q := UnforcedLeray.RieszLp.lerayY P (ENNReal.ofReal 2) h1' ENNReal.ofReal_ne_top Ff
  obtain ⟨PF_field, hPF_isRep⟩ := UnforcedLeray.Short.PartIIa.Rep.exists_isRep ENNReal.ofReal_ne_top PF_q
  have hPF_rep : HasRepY PF_q PF_field := ⟨hPF_isRep.meas.aestronglyMeasurable, hPF_isRep.slice⟩
  have hPF_norm : phaseLpNorm P 2 PF_field = ‖PF_q‖ₑ :=
    phaseLpNorm_eq_enorm 2 two_pos PF_field PF_q hPF_isRep
  have hT : UnforcedLeray.PhaseSpace.IsPhaseTest P
      (fun p => UnforcedLeray.B0411.L0T ν Φ p + μ • Φ p) :=
    (UnforcedLeray.B0411.isPhaseTest_L0T hΦ ν).add (hΦ.const_smul μ)
  have hpair_eq : pairF P (NvC ε⁻¹ H_phys) (NvC ε⁻¹ bε) = pairF P Φ PF_field := by
    rw [← hpt_op, ← phasePair_eq_pairF_of_hasRepY Wq _ hWrep hT,
      ← phasePair_bodyOp μ ⟨Wq, hD⟩ hΦ, hbody,
      phasePair_eq_pairF_of_hasRepY PF_q PF_field hPF_rep hΦ]
  rw [scte_pairF_NvC hc hε hH_nice hbε_in] at hpair_eq
  -- Expand the chart integral into the 5 IBP pieces
  set sDΨ : CProf := fun x => (1 / 2 : ℂ) • Ψ x - x.1 • fderiv ℝ Ψ x (cdir 0)
  have hsDΨ_nice : NiceProf c sDΨ :=
    scte_nice_sub (scte_nice_smul (1 / 2 : ℂ) hΨ)
      (by
        have h := scte_nice_mulS (scte_nice_fderiv_dir 0 hΨ)
        simpa [Complex.real_smul] using h)
  have hsDΨ_in : InHr c 2 sDΨ := scte_nice_inHr hc hsDΨ_nice
  have hsQ2_in : InHr c 2 (fun x => (x.1 : ℂ) • Q2Ψ x) :=
    scte_nice_inHr hc (scte_nice_mulS hQ2Ψ)
  have hsE2_in : InHr c 2 (fun x => (x.1 : ℂ) • E2Ψ x) :=
    scte_nice_inHr hc (scte_nice_mulS hE2Ψ)
  have hshoop_in : InHr c 2 (fun x => (x.1 : ℂ) • hoopE (Ψ x)) :=
    scte_nice_inHr hc (scte_nice_mulS (scte_nice_hoopE hΨ))
  have int_sum : ∀ {G : CProf}, InHr c 2 G →
      Integrable (fun x => ∑ i : Fin 2, bε x i * G x i) (hMeas c 2) := fun {G} hG => by
    have h0 := scte_comp_unconj_int hbε_in.meas hbε_in.finite hG.meas hG.finite 0
    have h1 := scte_comp_unconj_int hbε_in.meas hbε_in.finite hG.meas hG.finite 1
    exact (h0.add h1).congr (ae_of_all _ fun x => by
      change bε x 0 * G x 0 + bε x 1 * G x 1 = _
      exact (Fin.sum_univ_two fun i : Fin 2 => bε x i * G x i).symm)
  have hhoop0 : ∀ v : CMerid, hoopE v 0 = v 0 := fun v => by simp [hoopE, EuclideanSpace.single]
  have hhoop1 : ∀ v : CMerid, hoopE v 1 = 0 := fun v => by simp [hoopE, EuclideanSpace.single]
  have i1 := (int_sum hΨ_in).const_mul μ
  have i2 := int_sum hsDΨ_in
  have i3 : Integrable (fun x => (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * Q2Ψ x i))
      (hMeas c 2) := by
    refine ((int_sum hsQ2_in).const_mul (ν : ℂ)).congr (ae_of_all _ fun x => ?_)
    simp only [Fin.sum_univ_two, PiLp.smul_apply, smul_eq_mul]
    ring
  have i4 : Integrable (fun x => (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * E2Ψ x i))
      (hMeas c 2) := by
    refine ((int_sum hsE2_in).const_mul (ν : ℂ)).congr (ae_of_all _ fun x => ?_)
    simp only [Fin.sum_univ_two, PiLp.smul_apply, smul_eq_mul]
    ring
  have i5 : Integrable (fun x => ((ν * ε ^ 2 : ℝ) : ℂ) * ((x.1 : ℂ) * (bε x 0 * Ψ x 0)))
      (hMeas c 2) := by
    refine ((int_sum hshoop_in).const_mul ((ν * ε ^ 2 : ℝ) : ℂ)).congr (ae_of_all _ fun x => ?_)
    simp only [Fin.sum_univ_two, PiLp.smul_apply, smul_eq_mul, hhoop0, hhoop1]
    ring
  have hH_expand : (fun x : Coord => ∑ i : Fin 2, H_phys x i * bε x i) =
      fun x : Coord =>
        (((μ * ∑ i : Fin 2, bε x i * Ψ x i) + (∑ i : Fin 2, bε x i * sDΨ x i)) -
          (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * Q2Ψ x i) -
          (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * E2Ψ x i)) +
          ((ν * ε ^ 2 : ℝ) : ℂ) * ((x.1 : ℂ) * (bε x 0 * Ψ x 0)) := by
    funext x
    simp only [Fin.sum_univ_two, H_phys, D0, sDΨ, LΨ, lapProf,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Complex.real_smul, smul_eq_mul,
      hhoop0, hhoop1]
    push_cast
    ring
  have hIBP_S : ∫ x, ∑ i : Fin 2, bε x i * sDΨ x i ∂(hMeas c 2) =
      ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) := by
    have h := (scte_periodic_ibp_S_nice hc hbε_in hSbε'_in hSε' hΨ).symm
    have heq1 : (fun x => ∑ i : Fin 2, bε x i *
        ((1 / 2 : ℂ) * Ψ x i - (x.1 : ℂ) * fderiv ℝ Ψ x (cdir 0) i)) =
        fun x => ∑ i : Fin 2, bε x i * sDΨ x i := by
      funext x; simp [sDΨ, Complex.real_smul]
    rw [heq1] at h
    rw [h]
    rfl
  have hIBP_Q : -(ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, bε x i * Q2Ψ x i ∂(hMeas c 2) =
      (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qbε' x i * (starRingEnd ℂ) (classQ ε B x i) ∂(hMeas c 2) := by
    have h := scte_periodic_ibp_Q_nice hc ε hbε_in hQbε'_in hQε' hQΨ
    have heqQ : ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qbε' x i * QΨ x i ∂(hMeas c 2) =
        ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qbε' x i * (starRingEnd ℂ) (classQ ε B x i) ∂(hMeas c 2) := by
      congr 1; funext x; congr 1; apply Finset.sum_congr rfl; intro i _
      dsimp [QΨ, Ψ]; rw [scteConj_classQ ε hB.1 x i]
    rw [heqQ] at h
    linear_combination -(ν : ℂ) * h
  have hIBP_E : -(ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, bε x i * E2Ψ x i ∂(hMeas c 2) =
      (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Ebε' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) := by
    have h := scte_periodic_ibp_Eta_nice hc hbε_in hEbε'_in hEε' hEΨ
    have heqE : ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ebε' x i * EΨ x i ∂(hMeas c 2) =
        ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ebε' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) := by
      congr 1; funext x; congr 1; apply Finset.sum_congr rfl; intro i _
      dsimp [EΨ, Ψ]; rw [scteConj_classEta hB.1 x i]
    rw [heqE] at h
    linear_combination -(ν : ℂ) * h
  have hint_total : ∫ x, ∑ i : Fin 2, H_phys x i * bε x i ∂(hMeas c 2) =
      μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qbε' x i * (starRingEnd ℂ) (classQ ε B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Ebε' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) +
        ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
          (bε x 0 * (starRingEnd ℂ) (B x 0)) ∂(hMeas c 2) := by
    have i12 : Integrable (fun x : Coord =>
        (μ * ∑ i : Fin 2, bε x i * Ψ x i) + (∑ i : Fin 2, bε x i * sDΨ x i)) (hMeas c 2) := i1.add i2
    have i123 : Integrable (fun x : Coord =>
        ((μ * ∑ i : Fin 2, bε x i * Ψ x i) + (∑ i : Fin 2, bε x i * sDΨ x i)) -
          (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * Q2Ψ x i)) (hMeas c 2) := i12.sub i3
    have i1234 : Integrable (fun x : Coord =>
        (((μ * ∑ i : Fin 2, bε x i * Ψ x i) + (∑ i : Fin 2, bε x i * sDΨ x i)) -
          (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * Q2Ψ x i)) -
          (ν : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2, bε x i * E2Ψ x i)) (hMeas c 2) := i123.sub i4
    rw [hH_expand,
      integral_add i1234 i5,
      integral_sub i123 i4,
      integral_sub i12 i3,
      integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      hIBP_S]
    dsimp [Ψ, scteConj, scteConjMap]
    linear_combination hIBP_Q + hIBP_E
  rw [hint_total] at hpair_eq
  -- Bound the RHS pairing and cancel `π ε⁻²`
  have hΦ_norm : phaseLpNorm P 2 Φ =
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ))) * hNorm c 2 B := by
    rw [phaseLpNorm_NvC hc two_pos hε Ψ hΨ_in.periodic hΨ_in.meas, scteConj_hNorm]
  have hNF : phaseLpNorm P 2 (NvC ε⁻¹ F) =
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ))) * hNorm c 2 F :=
    phaseLpNorm_NvC hc two_pos hε F hF.periodic hF.meas
  have hΦ_fin : phaseLpNorm P 2 Φ < ⊤ := by
    rw [hΦ_norm]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (scte_nice_inHr hc hB).finite
  have hPF_fin : phaseLpNorm P 2 PF_field < ⊤ := by
    rw [hPF_norm]; exact enorm_lt_top
  have hpair_bd := scte_pairF_l2_bound hP0 hΦ.continuous.measurable hΦ_fin
    hPF_isRep.meas.measurable hPF_fin
  have hlp : ‖PF_q‖ ≤ scte_CL2 * ‖Ff‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (UnforcedLeray.RieszLp.norm_lerayY_le h1' ENNReal.ofReal_ne_top)
        (norm_nonneg _))
  set κ : ℝ := Real.pi * (ε⁻¹) ^ 2
  have hκ_pos : 0 < κ := mul_pos Real.pi_pos (pow_pos (inv_pos.2 hε) 2)
  have hκ_sq : κ ^ (1 / (2 : ℝ)) * κ ^ (1 / (2 : ℝ)) = κ := by
    rw [← Real.rpow_add hκ_pos]; norm_num
  have hΦ_tr : (phaseLpNorm P 2 Φ).toReal = κ ^ (1 / (2 : ℝ)) * (hNorm c 2 B).toReal := by
    rw [hΦ_norm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hκ_pos.le _)]
  have hPF_tr : (phaseLpNorm P 2 PF_field).toReal ≤
      scte_CL2 * (κ ^ (1 / (2 : ℝ)) * (hNorm c 2 F).toReal) := by
    rw [hPF_norm, toReal_enorm]
    refine hlp.trans ?_
    rw [hFn, hNF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hκ_pos.le _)]
  have hprod_bd : κ * ‖(μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qbε' x i * (starRingEnd ℂ) (classQ ε B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Ebε' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) +
        ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
          (bε x 0 * (starRingEnd ℂ) (B x 0)) ∂(hMeas c 2))‖ ≤
      κ * (3 * scte_CL2 * (hNorm c 2 F).toReal * (hNorm c 2 B).toReal) := by
    have hnormL : κ * ‖(μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qbε' x i * (starRingEnd ℂ) (classQ ε B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Ebε' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) +
        ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
          (bε x 0 * (starRingEnd ℂ) (B x 0)) ∂(hMeas c 2))‖ = ‖pairF P Φ PF_field‖ := by
      rw [← hpair_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ_pos.le]
    rw [hnormL]
    calc ‖pairF P Φ PF_field‖
        ≤ 3 * (phaseLpNorm P 2 Φ).toReal * (phaseLpNorm P 2 PF_field).toReal := hpair_bd
      _ ≤ 3 * (κ ^ (1 / (2 : ℝ)) * (hNorm c 2 B).toReal) *
            (scte_CL2 * (κ ^ (1 / (2 : ℝ)) * (hNorm c 2 F).toReal)) := by
          rw [hΦ_tr]
          exact mul_le_mul_of_nonneg_left hPF_tr
            (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hκ_pos.le _) ENNReal.toReal_nonneg))
      _ = (κ ^ (1 / (2 : ℝ)) * κ ^ (1 / (2 : ℝ))) *
            (3 * scte_CL2 * (hNorm c 2 F).toReal * (hNorm c 2 B).toReal) := by ring
      _ = κ * (3 * scte_CL2 * (hNorm c 2 F).toReal * (hNorm c 2 B).toReal) := by rw [hκ_sq]
  exact le_of_mul_le_mul_left hprod_bd hκ_pos

/-! ## Section 4: Flat `NiceProf` tested equation via `FullFlatEq` -/

private def scte_flat_CL : ℝ :=
  Classical.choose (flatLerayLiftOfSlice cylinderHelmholtzLr 2 one_lt_two (by norm_num))

private lemma scte_flat_CL_pos : 0 < scte_flat_CL :=
  (Classical.choose_spec (flatLerayLiftOfSlice cylinderHelmholtzLr 2 one_lt_two (by norm_num))).1

private lemma scte_exists_fullFlatEq {ν c : ℝ} {μ : ℂ} (hc : 0 < c) (hν : 0 < ν)
    (ha : 0 < μ.re + 1 / 4) {F b0 : CProf}
    (hF : InHr c 2 F) (hb0_resp : IsFlatResponse ν μ F b0) (hb0_class : InFlatClass c 2 b0) :
    ∃ G : CProf, InHr c 2 G ∧
      hNorm c 2 G ≤ ENNReal.ofReal scte_flat_CL * hNorm c 2 F ∧
      FullFlatEq ν μ G b0 := by
  have hCL := scte_flat_CL_pos
  have hL :=
    (Classical.choose_spec (flatLerayLiftOfSlice cylinderHelmholtzLr 2 one_lt_two (by norm_num))).2
  have ha' : 0 < μ.re + (3 / (2 : ℝ) - 1) / 2 := by
    have : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
    rwa [this]
  obtain ⟨G, hGH, hGn, hGs, hGp⟩ := hL c hc F hF
  have hbm := duhamelMeasurable 2 one_lt_two (by norm_num) μ ha' ν c hν hc G hGH
  have hbn := duhamelBound 2 one_lt_two (by norm_num) μ ha' ν c hν hc G hGH
  have hbper := duhamelPeriodic ν μ c G hc hGH.periodic
  set b := flatDuhamel ν μ G
  have hbH : InHr c 2 b :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal 2 one_lt_two (by norm_num) μ ha' ν c hν hc G hGH hGs hbH
  have hresp : IsFlatResponse ν μ F b := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation 2 one_lt_two (by norm_num) μ ha' ν c hν hc G hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]; exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]; exact he
  have hfull := duhamelFullEq 2 one_lt_two (by norm_num) μ ha' ν c hν hc G hGH hbH
  obtain ⟨K, hK, hWK⟩ :=
    (windowBound_of winCutProps (windowHeatEq_of winCutProps) cylHeatMaxReg cylGradInterp
      windowWeightCompare) 2 one_lt_two (by norm_num) μ
  obtain ⟨S, Q, E, hw⟩ := hWK ν c hν hc G b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := weakGlue vS fw_vS_smooth c b S
    (fun a ha0 => (hw a ha0).1) (fun a ha0 => (hw a ha0).2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := weakGlue vQ0 fw_vQ0_smooth c b Q
    (fun a ha0 => (hw a ha0).2.1) (fun a ha0 => (hw a ha0).2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := weakGlue vEta fw_vEta_smooth c b E
    (fun a ha0 => (hw a ha0).2.2.1) (fun a ha0 => (hw a ha0).2.2.2.2.2.1)
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hGb_fin : ENNReal.ofReal (4 * K) * (hNorm c 2 G + hNorm c 2 b) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hGH.finite, hbH.finite⟩)
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c 2 (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.1
  have hSn : hNorm c 2 Sb < ⊤ := by
    have h := dyadicSummation 2 c one_lt_two.le hc Sb G b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c 2)) hGH.meas hbH.meas hSk
    rw [ENNReal.ofReal_one, one_mul] at h
    exact lt_of_le_of_lt h hGb_fin
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c 2 (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.1
  have hQn := dyadicSummation 2 c one_lt_two.le hc (sqrtS Qb) G b (Real.sqrt ν) K
    (Real.sqrt_nonneg _) hK.le (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c 2)))
    hGH.meas hbH.meas hQk
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c 2 (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2
  have hEn := dyadicSummation 2 c one_lt_two.le hc (sqrtS Eb) G b (Real.sqrt ν) K
    (Real.sqrt_nonneg _) hK.le (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c 2)))
    hGH.meas hbH.meas hEk
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQfin : hNorm c 2 (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hGb_fin).ne hsq0
  have hEfin : hNorm c 2 (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hGb_fin).ne hsq0
  have hbc : InFlatClass c 2 b :=
    ⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
      ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c 2), hSn⟩,
      ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c 2)), hQfin⟩,
      ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c 2)), hEfin⟩⟩
  have h0 : b0 - b =ᵐ[hMeas c 2] 0 :=
    flat_unique hc hν one_lt_two (by norm_num) ha' (b0 - b)
      (flatClassSub c 2 b0 b hb0_class hbc) (flatResponseSub ν μ F b0 b hb0_resp hresp)
  have hbb0 : b0 =ᵐ[hMeas c 2] b := by
    filter_upwards [h0] with x hx
    exact sub_eq_zero.mp hx
  have hae : ∀ᵐ x : Coord, 0 < x.1 → b0 x = b x :=
    CongrHelp.ae_volume_of_ageμ hc hb0_class.inHr.periodic hbc.inHr.periodic hbb0
  refine ⟨G, hGH, hGn, fun i φ hφ => ?_⟩
  obtain ⟨hI1, hI2, heq⟩ := hfull i φ hφ
  have hae_φ : (fun x : Coord => b0 x i * flatTransposeS ν μ φ x) =ᵐ[volume]
      fun x : Coord => b x i * flatTransposeS ν μ φ x := by
    filter_upwards [hae] with x hx
    by_cases hxpos : 0 < x.1
    · rw [hx hxpos]
    · have hnotin : x ∉ tsupport φ := fun hm => hxpos (hφ.supp hm).1
      have hU : IsOpen (tsupport φ)ᶜ := isClosed_tsupport φ |>.isOpen_compl
      have hφz : ∀ y ∈ (tsupport φ)ᶜ, φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
      have c0 := coef_cpd_vanish hU hφz 0 x hnotin
      have c1 := coef_cpd_vanish hU hφz 1
      have c11 := coef_cpd_vanish hU c1 1 x hnotin
      have c2 := coef_cpd_vanish hU hφz 2
      have c22 := coef_cpd_vanish hU c2 2 x hnotin
      unfold flatTransposeS
      rw [hφz x hnotin, c0, c11, c22]
      simp
  exact ⟨hI1.congr hae_φ.symm, hI2, (integral_congr_ae hae_φ).trans heq⟩

private lemma scte_isCoordTest_s_cpd (j : Fin 3) {Φ : Coord → ℝ} (hΦ : IsCoordTest Φ) :
    IsCoordTest (fun y : Coord => y.1 * cpd j Φ y) := by
  have hsub : tsupport (cpd j Φ) ⊆ tsupport Φ := by
    refine closure_minimal (fun x hx => ?_) (isClosed_tsupport Φ)
    by_contra hnotin
    exact hx (coef_cpd_vanish (isClosed_tsupport Φ).isOpen_compl
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) j x hnotin)
  have hd : IsCoordTest (cpd j Φ) :=
    ⟨coef_cpd_contDiff hΦ.smooth j, cpd_compact hΦ.compact j, hsub.trans hΦ.supp⟩
  exact isCoordTest_mul_smooth (contDiff_fst (n := ∞)) hd

private lemma scte_flatTransposeS_split (ν : ℝ) (μ : ℂ) {Φ : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (x : Coord) :
    flatTransposeS ν μ Φ x =
      μ * (Φ x : ℂ) + (coordTranspose vS dZero Φ x : ℂ) +
        (ν : ℂ) * (coordTranspose vQ0 dZero (fun y => y.1 * cpd 1 Φ y) x : ℂ) +
        (ν : ℂ) * (coordTranspose vEta dZero (fun y => y.1 * cpd 2 Φ y) x : ℂ) := by
  have hS := coordTranspose_vS_eq hΦ x
  have h1d : Differentiable ℝ (cpd 1 Φ) := (coef_cpd_contDiff hΦ 1).differentiable (by simp)
  have h2d : Differentiable ℝ (cpd 2 Φ) := (coef_cpd_contDiff hΦ 2).differentiable (by simp)
  have hfst : Differentiable ℝ (fun y : Coord => y.1) := differentiable_fst
  have hfst_fd : HasFDerivAt (fun y : Coord => y.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hfst1 : cpd 1 (fun y : Coord => y.1) x = 0 := by
    unfold cpd; rw [hfst_fd.fderiv]; simp [cdir]
  have hfst2 : cpd 2 (fun y : Coord => y.1) x = 0 := by
    unfold cpd; rw [hfst_fd.fderiv]; simp [cdir]
  have hQ0 : coordTranspose vQ0 dZero (fun y => y.1 * cpd 1 Φ y) x =
      -(x.1 * cpd 1 (cpd 1 Φ) x) := by
    rw [qd_coordT_eq]
    have e0 : cpd 0 (fun y => vQ0 y 0 * (y.1 * cpd 1 Φ y)) x = 0 := by simp [vQ0, cpd]
    have e2 : cpd 2 (fun y => vQ0 y 2 * (y.1 * cpd 1 Φ y)) x = 0 := by simp [vQ0, cpd]
    have e1 : cpd 1 (fun y => vQ0 y 1 * (y.1 * cpd 1 Φ y)) x =
        cpd 1 (fun y => y.1 * cpd 1 Φ y) x := by simp [vQ0]
    rw [e0, e1, e2, qd_cpd_mul 1 hfst h1d x, hfst1]
    simp [dZero]
  have hEta : coordTranspose vEta dZero (fun y => y.1 * cpd 2 Φ y) x =
      -(x.1 * cpd 2 (cpd 2 Φ) x) := by
    rw [qd_coordT_eq]
    have e0 : cpd 0 (fun y => vEta y 0 * (y.1 * cpd 2 Φ y)) x = 0 := by simp [vEta, cpd]
    have e1 : cpd 1 (fun y => vEta y 1 * (y.1 * cpd 2 Φ y)) x = 0 := by simp [vEta, cpd]
    have e2 : cpd 2 (fun y => vEta y 2 * (y.1 * cpd 2 Φ y)) x =
        cpd 2 (fun y => y.1 * cpd 2 Φ y) x := by simp [vEta]
    rw [e0, e1, e2, qd_cpd_mul 2 hfst h2d x, hfst2]
    simp [dZero]
  rw [hS, hQ0, hEta]
  unfold flatTransposeS
  push_cast
  ring

private lemma scte_flat_nice_scalar {ν c s₀ s₁ L : ℝ} {μ : ℂ} (hc : 0 < c) (hs₀ : 0 < s₀)
    {G b0 Sb0' Qb0' Eb0' : CProf}
    (hG : InHr c 2 G) (hb0 : InHr c 2 b0) (hSb0' : InHr c 2 Sb0')
    (hQb0' : InHr c 2 (sqrtS Qb0')) (hEb0' : InHr c 2 (sqrtS Eb0'))
    (hfull : FullFlatEq ν μ G b0)
    (hS0' : HasWeakVec vS dZero b0 Sb0') (hQ0' : HasWeakVec vQ0 dZero b0 Qb0')
    (hE0' : HasWeakVec vEta dZero b0 Eb0') (i : Fin 2)
    {φ : Coord → ℝ} (hφ_s : ContDiff ℝ ∞ φ) (hφ_p : ∀ x, φ (qShift c x) = φ x)
    (hφ_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → φ x = 0) :
    μ * ∫ x, b0 x i * (φ x : ℂ) ∂(hMeas c 2) +
        ∫ x, Sb0' x i * (φ x : ℂ) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * (Qb0' x i * (cpd 1 φ x : ℂ)) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * (Eb0' x i * (cpd 2 φ x : ℂ)) ∂(hMeas c 2) =
      ∫ x, G x i * (φ x : ℂ) ∂(hMeas c 2) := by
  obtain ⟨θ, hθ_cd, hθ_cs, -, hθ_sum1, hθ_sumd⟩ := CellPart.exists_partition_of_derivs hc
  have hlow : ∀ y : Coord, y.1 < s₀ → φ y = 0 := fun y hy => hφ_v y (Or.inl hy)
  set ψ₀ := scteW (-(3 / 2 : ℝ)) c φ
  set Φ := fun x : Coord => θ x.2.1 * ψ₀ x
  have hΦ : IsCoordTest Φ :=
    scteW_mul_theta_isTest (a := -(3 / 2 : ℝ)) (c := c) hθ_cd hθ_cs hφ_s hs₀ hφ_v
  have hΦ1 : IsCoordTest (fun y => y.1 * cpd 1 Φ y) := scte_isCoordTest_s_cpd 1 hΦ
  have hΦ2 : IsCoordTest (fun y => y.1 * cpd 2 Φ y) := scte_isCoordTest_s_cpd 2 hΦ
  -- Unfold `(u, Φ)` for `u ∈ {G, b0, Sb0'}`
  have hunf_u : ∀ {u : CProf}, InHr c 2 u →
      Integrable (fun x : Coord => u x i * (Φ x : ℂ)) volume ∧
        ∫ x, u x i * (Φ x : ℂ) = ∫ x, u x i * (φ x : ℂ) ∂(hMeas c 2) := by
    intro u hu
    have hW_cd := scteW_contDiff (a := -(3 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow
    obtain ⟨hint, -, hunf⟩ := scte_unfold_comp hc hs₀ hu i hθ_cd.continuous hθ_cs hθ_sum1
      hW_cd.continuous (scteW_per hφ_p) (scteW_van hφ_v)
    have hpt1 : (fun x : Coord => u x i * (Φ x : ℂ)) =
        fun x : Coord => (θ x.2.1 : ℂ) * (u x i * (ψ₀ x : ℂ)) := by
      funext x; dsimp [Φ]; push_cast; ring
    have hpt2 : (fun x : Coord => u x i * (ψ₀ x : ℂ)) =
        fun x : Coord => ((c⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (u x i * (φ x : ℂ)) := by
      funext x; dsimp [ψ₀, scteW]; push_cast; ring
    refine ⟨hint.congr (ae_of_all _ fun x => (congrFun hpt1 x).symm), ?_⟩
    rw [hpt1, hunf, Complex.ofReal_one, one_mul, hpt2]
    exact scte_cell_to_hMeas hc hs₀ (fun x hx => by simp [hlow x hx])
  obtain ⟨-, eG⟩ := hunf_u hG
  obtain ⟨ib0, eb0⟩ := hunf_u hb0
  obtain ⟨-, eSb0⟩ := hunf_u hSb0'
  -- Expand `FullFlatEq` using `hS0'`, `hQ0'`, `hE0'`
  obtain ⟨-, -, hfeq⟩ := hfull i Φ hΦ
  have iTS : Integrable (fun x => b0 x i * (coordTranspose vS dZero Φ x : ℂ)) volume :=
    ((hS0' i).1 Φ hΦ).1
  have iTQ : Integrable
      (fun x => b0 x i * (coordTranspose vQ0 dZero (fun y => y.1 * cpd 1 Φ y) x : ℂ)) volume :=
    ((hQ0' i).1 _ hΦ1).1
  have iTE : Integrable
      (fun x => b0 x i * (coordTranspose vEta dZero (fun y => y.1 * cpd 2 Φ y) x : ℂ)) volume :=
    ((hE0' i).1 _ hΦ2).1
  have iF1 : Integrable (fun x => μ * (b0 x i * (Φ x : ℂ))) volume := ib0.const_mul μ
  have iF12 : Integrable
      (fun x => μ * (b0 x i * (Φ x : ℂ)) + b0 x i * (coordTranspose vS dZero Φ x : ℂ)) volume :=
    iF1.add iTS
  have iF3 : Integrable
      (fun x => (ν : ℂ) * (b0 x i * (coordTranspose vQ0 dZero (fun y => y.1 * cpd 1 Φ y) x : ℂ)))
      volume := iTQ.const_mul (ν : ℂ)
  have iF123 : Integrable (fun x =>
      (μ * (b0 x i * (Φ x : ℂ)) + b0 x i * (coordTranspose vS dZero Φ x : ℂ)) +
        (ν : ℂ) * (b0 x i * (coordTranspose vQ0 dZero (fun y => y.1 * cpd 1 Φ y) x : ℂ))) volume :=
    iF12.add iF3
  have iF4 : Integrable
      (fun x => (ν : ℂ) * (b0 x i * (coordTranspose vEta dZero (fun y => y.1 * cpd 2 Φ y) x : ℂ)))
      volume := iTE.const_mul (ν : ℂ)
  have hptF : (fun x : Coord => b0 x i * flatTransposeS ν μ Φ x) =
      fun x : Coord =>
        ((μ * (b0 x i * (Φ x : ℂ)) + b0 x i * (coordTranspose vS dZero Φ x : ℂ)) +
          (ν : ℂ) * (b0 x i * (coordTranspose vQ0 dZero (fun y => y.1 * cpd 1 Φ y) x : ℂ))) +
          (ν : ℂ) * (b0 x i * (coordTranspose vEta dZero (fun y => y.1 * cpd 2 Φ y) x : ℂ)) := by
    funext x
    rw [scte_flatTransposeS_split ν μ hΦ.smooth x]
    ring
  rw [hptF,
    integral_add iF123 iF4,
    integral_add iF12 iF3,
    integral_add iF1 iTS,
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← (hS0' i).2 Φ hΦ, ← (hQ0' i).2 _ hΦ1, ← (hE0' i).2 _ hΦ2,
    eb0, eSb0, eG] at hfeq
  -- Compute `s * cpd 1 Φ` and `s * cpd 2 Φ`
  have hθy : Differentiable ℝ (fun y : Coord => θ y.2.1) :=
    (hθ_cd.comp (contDiff_fst.comp contDiff_snd)).differentiable (by simp)
  have hψ₀d : Differentiable ℝ ψ₀ :=
    (scteW_contDiff (a := -(3 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow).differentiable (by simp)
  have hs_pow : ∀ x : Coord, ¬(x.1 < s₀) → x.1 * x.1 ^ (-(3 / 2 : ℝ)) = x.1 ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
    calc x.1 * x.1 ^ (-(3 / 2 : ℝ)) = x.1 ^ (1 : ℝ) * x.1 ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = x.1 ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
  have hscpd1 : ∀ x : Coord, x.1 * cpd 1 Φ x =
      θ x.2.1 * scteW (-(1 / 2 : ℝ)) c (cpd 1 φ) x +
        iteratedDeriv 1 θ x.2.1 * scteW (-(1 / 2 : ℝ)) c φ x := by
    intro x
    obtain ⟨-, dθ1, -⟩ := scte_cpd_q_only hθ_cd x
    obtain ⟨-, c1, -⟩ := scte_cpd_scteW (a := -(3 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow x
    have hm := qd_cpd_mul 1 hθy hψ₀d x
    change x.1 * cpd 1 (fun y => θ y.2.1 * ψ₀ y) x = _
    rw [hm, dθ1, c1]
    by_cases hx : x.1 < s₀
    · have h1 : cpd 1 φ x = 0 := coef_cpd_vanish (coef_isOpen s₀ s₁ L) hφ_v 1 x (Or.inl hx)
      simp [ψ₀, scteW, hlow x hx, h1]
    · have hp := hs_pow x hx
      dsimp [ψ₀, scteW]
      linear_combination
        (θ x.2.1 * c⁻¹ * cpd 1 φ x + iteratedDeriv 1 θ x.2.1 * c⁻¹ * φ x) * hp
  have hscpd2 : ∀ x : Coord, x.1 * cpd 2 Φ x =
      θ x.2.1 * scteW (-(1 / 2 : ℝ)) c (cpd 2 φ) x := by
    intro x
    obtain ⟨-, -, dθ2⟩ := scte_cpd_q_only hθ_cd x
    obtain ⟨-, -, c2⟩ := scte_cpd_scteW (a := -(3 / 2 : ℝ)) (c := c) hφ_s hs₀ hlow x
    have hm := qd_cpd_mul 2 hθy hψ₀d x
    change x.1 * cpd 2 (fun y => θ y.2.1 * ψ₀ y) x = _
    rw [hm, dθ2, c2, mul_zero, add_zero]
    by_cases hx : x.1 < s₀
    · have h2 : cpd 2 φ x = 0 := coef_cpd_vanish (coef_isOpen s₀ s₁ L) hφ_v 2 x (Or.inl hx)
      simp [scteW, h2]
    · have hp := hs_pow x hx
      dsimp [scteW]
      linear_combination θ x.2.1 * c⁻¹ * cpd 2 φ x * hp
  have hcpd1_s := coef_cpd_contDiff hφ_s 1
  have hcpd1_p := coef_cpd_per hφ_p 1
  have hcpd1_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → cpd 1 φ x = 0 :=
    fun x hx => coef_cpd_vanish (coef_isOpen s₀ s₁ L) hφ_v 1 x hx
  have hcpd2_s := coef_cpd_contDiff hφ_s 2
  have hcpd2_p := coef_cpd_per hφ_p 2
  have hcpd2_v : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → cpd 2 φ x = 0 :=
    fun x hx => coef_cpd_vanish (coef_isOpen s₀ s₁ L) hφ_v 2 x hx
  -- Unfold `Eb0'` term
  have eEb0 : ∫ x, Eb0' x i * ((x.1 * cpd 2 Φ x : ℝ) : ℂ) =
      ∫ x, (x.1 : ℂ) * (Eb0' x i * (cpd 2 φ x : ℂ)) ∂(hMeas c 2) := by
    simp_rw [hscpd2]
    exact scte_lhs_sqrtS_unfold hc hs₀ hEb0' i hθ_cd hθ_cs hθ_sum1 hcpd2_s hcpd2_p hcpd2_v
  -- Unfold `Qb0'` term (principal `θ` piece + vanishing `θ'` piece)
  have hdθ_cont : Continuous (iteratedDeriv 1 θ) := by
    rw [iteratedDeriv_one]; exact hθ_cd.continuous_deriv (by simp)
  have hdθ_cs : HasCompactSupport (iteratedDeriv 1 θ) := by
    rw [iteratedDeriv_one]; exact hθ_cs.deriv
  have hWm1_cd := scteW_contDiff (a := (-1 : ℝ)) (c := c) hφ_s hs₀ hlow
  have hWm1_c1_cd := scteW_contDiff (a := (-1 : ℝ)) (c := c) hcpd1_s hs₀
    (fun y hy => hcpd1_v y (Or.inl hy))
  obtain ⟨iQ1_raw, -, -⟩ := scte_unfold_comp hc hs₀ hQb0' i hθ_cd.continuous hθ_cs hθ_sum1
    hWm1_c1_cd.continuous (scteW_per hcpd1_p) (scteW_van hcpd1_v)
  obtain ⟨iQ2_raw, -, hunfQ2⟩ := scte_unfold_comp hc hs₀ hQb0' i hdθ_cont hdθ_cs
    (hθ_sumd 0) hWm1_cd.continuous (scteW_per hφ_p) (scteW_van hφ_v)
  have hQ_pt1 : ∀ x : Coord,
      Qb0' x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c (cpd 1 φ) x : ℝ) : ℂ) =
        (θ x.2.1 : ℂ) * (sqrtS Qb0' x i * (scteW (-1 : ℝ) c (cpd 1 φ) x : ℂ)) := by
    intro x
    by_cases hx : x.1 < s₀
    · simp [scteW, hcpd1_v x (Or.inl hx)]
    · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
      have hsq : Real.sqrt x.1 * x.1 ^ (-1 : ℝ) = x.1 ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]; norm_num
      have hsq_c : ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 ^ (-1 : ℝ) : ℝ) : ℂ) =
          ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hsq
      simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, scteW]
      push_cast
      linear_combination (θ x.2.1 : ℂ) * Qb0' x i * (c⁻¹ : ℂ) * (cpd 1 φ x : ℂ) * hsq_c.symm
  have hQ_pt2 : ∀ x : Coord,
      Qb0' x i * ((iteratedDeriv 1 θ x.2.1 * scteW (-(1 / 2 : ℝ)) c φ x : ℝ) : ℂ) =
        ((iteratedDeriv 1 θ x.2.1 : ℝ) : ℂ) * (sqrtS Qb0' x i * (scteW (-1 : ℝ) c φ x : ℂ)) := by
    intro x
    by_cases hx : x.1 < s₀
    · simp [scteW, hlow x hx]
    · have hxpos : 0 < x.1 := lt_of_lt_of_le hs₀ (not_lt.1 hx)
      have hsq : Real.sqrt x.1 * x.1 ^ (-1 : ℝ) = x.1 ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]; norm_num
      have hsq_c : ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 ^ (-1 : ℝ) : ℝ) : ℂ) =
          ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hsq
      simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, scteW]
      push_cast
      linear_combination
        ((iteratedDeriv 1 θ x.2.1 : ℝ) : ℂ) * Qb0' x i * (c⁻¹ : ℂ) * (φ x : ℂ) * hsq_c.symm
  have iQ1 := iQ1_raw.congr (ae_of_all _ fun x => (hQ_pt1 x).symm)
  have iQ2 := iQ2_raw.congr (ae_of_all _ fun x => (hQ_pt2 x).symm)
  have eQb0 : ∫ x, Qb0' x i * ((x.1 * cpd 1 Φ x : ℝ) : ℂ) =
      ∫ x, (x.1 : ℂ) * (Qb0' x i * (cpd 1 φ x : ℂ)) ∂(hMeas c 2) := by
    have hsplit : (fun x : Coord => Qb0' x i * ((x.1 * cpd 1 Φ x : ℝ) : ℂ)) =
        fun x : Coord =>
          Qb0' x i * ((θ x.2.1 * scteW (-(1 / 2 : ℝ)) c (cpd 1 φ) x : ℝ) : ℂ) +
            Qb0' x i * ((iteratedDeriv 1 θ x.2.1 * scteW (-(1 / 2 : ℝ)) c φ x : ℝ) : ℂ) := by
      funext x; rw [hscpd1 x]; push_cast; ring
    rw [hsplit, integral_add iQ1 iQ2,
      scte_lhs_sqrtS_unfold hc hs₀ hQb0' i hθ_cd hθ_cs hθ_sum1 hcpd1_s hcpd1_p hcpd1_v,
      funext hQ_pt2, hunfQ2, Complex.ofReal_zero, zero_mul, add_zero]
  rw [eQb0, eEb0] at hfeq
  exact hfeq

private lemma scte_flat_nice_eq {ν c : ℝ} {μ : ℂ} (hc : 0 < c) (hν : 0 < ν)
    (ha : 0 < μ.re + 1 / 4) {F b0 Sb0' Qb0' Eb0' B : CProf}
    (hF : InHr c 2 F) (hb0_resp : IsFlatResponse ν μ F b0) (hb0_class : InFlatClass c 2 b0)
    (hSb0'_in : InHr c 2 Sb0') (hQb0'_in : InHr c 2 (sqrtS Qb0'))
    (hEb0'_in : InHr c 2 (sqrtS Eb0'))
    (hS0' : HasWeakVec vS dZero b0 Sb0') (hQ0' : HasWeakVec vQ0 dZero b0 Qb0')
    (hE0' : HasWeakVec vEta dZero b0 Eb0') (hB : NiceProf c B) :
    ‖(μ * ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qb0' x i * (starRingEnd ℂ) (fderiv ℝ B x (cdir 1) i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Eb0' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2))‖ ≤
      2 * scte_flat_CL * (hNorm c 2 F).toReal * (hNorm c 2 B).toReal := by
  obtain ⟨G, hG, hGn, hfull⟩ := scte_exists_fullFlatEq hc hν ha hF hb0_resp hb0_class
  have hb0_in : InHr c 2 b0 := hb0_class.inHr
  set Ψ := scteConj B
  have hΨ : NiceProf c Ψ := scteConj_nice hB
  have hΨ_in : InHr c 2 Ψ := scte_nice_inHr hc hΨ
  have hD1Ψ : NiceProf c (fun x => fderiv ℝ Ψ x (cdir 1)) := scte_nice_fderiv_dir 1 hΨ
  have hEΨ : NiceProf c (classEta Ψ) := (lapNiceClass_proof c 0 Ψ hΨ).2
  have hcomp : ∀ i : Fin 2,
      μ * ∫ x, b0 x i * Ψ x i ∂(hMeas c 2) +
        ∫ x, Sb0' x i * Ψ x i ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * (Qb0' x i * fderiv ℝ Ψ x (cdir 1) i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * (Eb0' x i * classEta Ψ x i) ∂(hMeas c 2) =
      ∫ x, G x i * Ψ x i ∂(hMeas c 2) := by
    intro i
    obtain ⟨hre_s, hre_p, him_s, him_p, s₀, s₁, L, hs₀, hre_v, him_v⟩ := scte_nice_comp_props hΨ i
    have ere := scte_flat_nice_scalar hc hs₀ hG hb0_in hSb0'_in hQb0'_in hEb0'_in
      hfull hS0' hQ0' hE0' i hre_s hre_p hre_v
    have eim := scte_flat_nice_scalar hc hs₀ hG hb0_in hSb0'_in hQb0'_in hEb0'_in
      hfull hS0' hQ0' hE0' i him_s him_p him_v
    -- Real/imag integrable pieces
    have split_u : ∀ {u : CProf}, InHr c 2 u →
        ∫ x, u x i * Ψ x i ∂(hMeas c 2) =
          ∫ x, u x i * (((Ψ x i).re : ℝ) : ℂ) ∂(hMeas c 2) +
            Complex.I * ∫ x, u x i * (((Ψ x i).im : ℝ) : ℂ) ∂(hMeas c 2) := by
      intro u hu
      have ifull := scte_comp_unconj_int hu.meas hu.finite hΨ_in.meas hΨ_in.finite i
      have ire : Integrable (fun x => u x i * (((Ψ x i).re : ℝ) : ℂ)) (hMeas c 2) := by
        refine ifull.mono
          (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hu.meas).mul
            (Complex.continuous_ofReal.comp hre_s.continuous).aestronglyMeasurable)
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)
      have iim : Integrable (fun x => u x i * (((Ψ x i).im : ℝ) : ℂ)) (hMeas c 2) := by
        refine ifull.mono
          (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hu.meas).mul
            (Complex.continuous_ofReal.comp him_s.continuous).aestronglyMeasurable)
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)
      have hsp : (fun x => u x i * Ψ x i) =
          fun x => u x i * (((Ψ x i).re : ℝ) : ℂ) +
            Complex.I * (u x i * (((Ψ x i).im : ℝ) : ℂ)) := by
        funext x
        have h1 : (((Ψ x i).re : ℝ) : ℂ) + Complex.I * (((Ψ x i).im : ℝ) : ℂ) = Ψ x i := by
          rw [mul_comm]; exact Complex.re_add_im _
        linear_combination u x i * h1.symm
      rw [hsp, integral_add ire (iim.const_mul Complex.I), integral_const_mul]
    have split_w : ∀ (j : Fin 3) {Gb : CProf}, InHr c 2 (sqrtS Gb) →
        NiceProf c (fun x => fderiv ℝ Ψ x (cdir j)) →
        ∫ x, (x.1 : ℂ) * (Gb x i * fderiv ℝ Ψ x (cdir j) i) ∂(hMeas c 2) =
          ∫ x, (x.1 : ℂ) * (Gb x i * ((cpd j (fun y => (Ψ y i).re) x : ℝ) : ℂ)) ∂(hMeas c 2) +
            Complex.I *
              ∫ x, (x.1 : ℂ) * (Gb x i * ((cpd j (fun y => (Ψ y i).im) x : ℝ) : ℂ)) ∂(hMeas c 2) := by
      intro j Gb hGb hDj
      have ifull := scte_weighted_comp_int hc hGb hDj i
      have hmGb : AEStronglyMeasurable (fun x => (x.1 : ℂ) * Gb x i) (hMeas c 2) := by
        have hm1 : AEStronglyMeasurable (fun x => sqrtS Gb x i) (hMeas c 2) :=
          (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hGb.meas
        have hm2 : Measurable (fun x : Coord => (Real.sqrt x.1 : ℂ)) :=
          Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)
        refine (hm2.aestronglyMeasurable.mul hm1).congr ?_
        filter_upwards [scte_hMeas_pos c 2] with x hxpos
        simp only [Pi.mul_apply, sqrtS, PiLp.smul_apply, smul_eq_mul]
        have hsq : ((Real.sqrt x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = (x.1 : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt hxpos.le]
        linear_combination Gb x i * hsq
      have ire : Integrable (fun x => (x.1 : ℂ) *
          (Gb x i * ((cpd j (fun y => (Ψ y i).re) x : ℝ) : ℂ))) (hMeas c 2) := by
        refine ifull.mono ?_ (ae_of_all _ fun x => ?_)
        · exact (hmGb.mul (Complex.continuous_ofReal.comp
            (coef_cpd_contDiff hre_s j).continuous).aestronglyMeasurable).congr
            (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply]; ring)
        · have hre_eq : cpd j (fun y => (Ψ y i).re) x = (fderiv ℝ Ψ x (cdir j) i).re := by
            rw [scte_fderiv_re_im hΨ.1 x j i]; simp
          rw [hre_eq, norm_mul, norm_mul, norm_mul, norm_mul]
          simp_rw [Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)) (abs_nonneg _)
      have iim : Integrable (fun x => (x.1 : ℂ) *
          (Gb x i * ((cpd j (fun y => (Ψ y i).im) x : ℝ) : ℂ))) (hMeas c 2) := by
        refine ifull.mono ?_ (ae_of_all _ fun x => ?_)
        · exact (hmGb.mul (Complex.continuous_ofReal.comp
            (coef_cpd_contDiff him_s j).continuous).aestronglyMeasurable).congr
            (ae_of_all _ fun x => by simp only [Pi.mul_apply, Function.comp_apply]; ring)
        · have him_eq : cpd j (fun y => (Ψ y i).im) x = (fderiv ℝ Ψ x (cdir j) i).im := by
            rw [scte_fderiv_re_im hΨ.1 x j i]; simp
          rw [him_eq, norm_mul, norm_mul, norm_mul, norm_mul]
          simp_rw [Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)) (abs_nonneg _)
      have hsp : (fun x => (x.1 : ℂ) * (Gb x i * fderiv ℝ Ψ x (cdir j) i)) =
          fun x => (x.1 : ℂ) * (Gb x i * ((cpd j (fun y => (Ψ y i).re) x : ℝ) : ℂ)) +
            Complex.I * ((x.1 : ℂ) * (Gb x i * ((cpd j (fun y => (Ψ y i).im) x : ℝ) : ℂ))) := by
        funext x; rw [scte_fderiv_re_im hΨ.1 x j i]; ring
      rw [hsp, integral_add ire (iim.const_mul Complex.I), integral_const_mul]
    rw [split_u hb0_in, split_u hSb0'_in, split_u hG,
      split_w 1 hQb0'_in hD1Ψ, show classEta Ψ = fun x => fderiv ℝ Ψ x (cdir 2) from rfl,
      split_w 2 hEb0'_in hEΨ]
    linear_combination ere + Complex.I * eim
  -- Sum over `i = 0, 1` and conjugate rewrite
  have sum_u : ∀ {u : CProf}, InHr c 2 u →
      ∫ x, ∑ i : Fin 2, u x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) =
        ∫ x, u x 0 * Ψ x 0 ∂(hMeas c 2) + ∫ x, u x 1 * Ψ x 1 ∂(hMeas c 2) := by
    intro u hu
    have i0 := scte_comp_unconj_int hu.meas hu.finite hΨ_in.meas hΨ_in.finite 0
    have i1 := scte_comp_unconj_int hu.meas hu.finite hΨ_in.meas hΨ_in.finite 1
    have heq : (fun x => ∑ i : Fin 2, u x i * (starRingEnd ℂ) (B x i)) =
        fun x => u x 0 * Ψ x 0 + u x 1 * Ψ x 1 := by
      funext x; rw [Fin.sum_univ_two]; rfl
    rw [heq, integral_add i0 i1]
  have iQ0 := scte_weighted_comp_int hc hQb0'_in hD1Ψ 0
  have iQ1 := scte_weighted_comp_int hc hQb0'_in hD1Ψ 1
  have eQ_sum : ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qb0' x i * (starRingEnd ℂ) (fderiv ℝ B x (cdir 1) i) ∂(hMeas c 2) =
      ∫ x, (x.1 : ℂ) * (Qb0' x 0 * fderiv ℝ Ψ x (cdir 1) 0) ∂(hMeas c 2) +
        ∫ x, (x.1 : ℂ) * (Qb0' x 1 * fderiv ℝ Ψ x (cdir 1) 1) ∂(hMeas c 2) := by
    have heq : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2,
          Qb0' x i * (starRingEnd ℂ) (fderiv ℝ B x (cdir 1) i)) =
        fun x : Coord => (x.1 : ℂ) * (Qb0' x 0 * fderiv ℝ Ψ x (cdir 1) 0) +
          (x.1 : ℂ) * (Qb0' x 1 * fderiv ℝ Ψ x (cdir 1) 1) := by
      funext x
      rw [Fin.sum_univ_two]
      dsimp [Ψ]
      rw [scteConj_fderiv hB.1 x (cdir 1) 0, scteConj_fderiv hB.1 x (cdir 1) 1]
      ring
    rw [heq, integral_add iQ0 iQ1]
  have iE0 := scte_weighted_comp_int hc hEb0'_in hEΨ 0
  have iE1 := scte_weighted_comp_int hc hEb0'_in hEΨ 1
  have eE_sum : ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Eb0' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) =
      ∫ x, (x.1 : ℂ) * (Eb0' x 0 * classEta Ψ x 0) ∂(hMeas c 2) +
        ∫ x, (x.1 : ℂ) * (Eb0' x 1 * classEta Ψ x 1) ∂(hMeas c 2) := by
    have heq : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2,
          Eb0' x i * (starRingEnd ℂ) (classEta B x i)) =
        fun x : Coord => (x.1 : ℂ) * (Eb0' x 0 * classEta Ψ x 0) +
          (x.1 : ℂ) * (Eb0' x 1 * classEta Ψ x 1) := by
      funext x
      rw [Fin.sum_univ_two]
      dsimp [Ψ]
      rw [scteConj_classEta hB.1 x 0, scteConj_classEta hB.1 x 1]
      ring
    rw [heq, integral_add iE0 iE1]
  have hLHS_eq :
      μ * ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qb0' x i * (starRingEnd ℂ) (fderiv ℝ B x (cdir 1) i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Eb0' x i * (starRingEnd ℂ) (classEta B x i) ∂(hMeas c 2) =
      ∫ x, ∑ i : Fin 2, G x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2) := by
    rw [sum_u hb0_in, sum_u hSb0'_in, sum_u hG, eQ_sum, eE_sum]
    linear_combination hcomp 0 + hcomp 1
  rw [hLHS_eq]
  have hB_in : InHr c 2 B := scte_nice_inHr hc hB
  obtain ⟨-, hGB_bd⟩ := scte_h2_pair_bound hG.meas hG.finite hB_in.meas hB_in.finite
  have hG_tr : (hNorm c 2 G).toReal ≤ scte_flat_CL * (hNorm c 2 F).toReal := by
    have hfin : ENNReal.ofReal scte_flat_CL * hNorm c 2 F ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.finite.ne
    have hle := ENNReal.toReal_mono hfin hGn
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal scte_flat_CL_pos.le] at hle
  calc ‖∫ x, ∑ i : Fin 2, G x i * (starRingEnd ℂ) (B x i) ∂(hMeas c 2)‖
      ≤ 2 * (hNorm c 2 G).toReal * (hNorm c 2 B).toReal := hGB_bd
    _ ≤ 2 * (scte_flat_CL * (hNorm c 2 F).toReal) * (hNorm c 2 B).toReal :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG_tr (by norm_num))
          ENNReal.toReal_nonneg
    _ = 2 * scte_flat_CL * (hNorm c 2 F).toReal * (hNorm c 2 B).toReal := by ring

/-! ## Section 5: Friedrichs mollification of compactly-supported `s, η` profiles in `H_2` -/

private lemma scte_strip_measure_cmp {a₀ a₁ : ℝ} (c : ℝ) (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ a₁) :
    let W : Set Coord := Icc a₀ a₁ ×ˢ (univ : Set (ℝ × ℝ))
    (cylMeas c).restrict W ≤ ENNReal.ofReal (a₁ ^ (3 / 2 : ℝ)) • (hMeas c 2).restrict W ∧
      (hMeas c 2).restrict W ≤ ENNReal.ofReal (a₀ ^ (-(3 / 2 : ℝ))) • (cylMeas c).restrict W := by
  intro W
  have hW : MeasurableSet W := measurableSet_Icc.prod MeasurableSet.univ
  have ha₁_pos : 0 < a₁ := lt_of_lt_of_le ha₀ ha₁
  have h2_eq : (2 : ℝ) / 2 - 5 / 2 = -(3 / 2 : ℝ) := by norm_num
  have hm_eq : hMeas c 2 = Axi.ageμ c (-(3 / 2 : ℝ)) := by unfold hMeas; rw [h2_eq]
  have slice_zero : ∀ {E : Set Coord}, E ⊆ W → ∀ {x : ℝ}, x ∉ Icc a₀ a₁ →
      (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) = 0 := by
    intro E hsub x hx
    have hemp : Prod.mk x ⁻¹' E = ∅ := by
      ext z; simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hz; exact hx (hsub hz).1
    rw [hemp, measure_empty]
  have cyl_eq : ∀ {E : Set Coord}, MeasurableSet E → E ⊆ W →
      cylMeas c E = ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
        ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
    intro E hE hsub
    rw [wwc_cyl_apply c hE]
    refine (setLIntegral_eq_of_support_subset fun x hx => ?_).symm
    have hxI : x ∈ Icc a₀ a₁ := by
      by_contra hnot; exact hx (slice_zero hsub hnot)
    exact lt_of_lt_of_le ha₀ hxI.1
  constructor
  · rw [Measure.le_iff]
    intro B hB
    set E := B ∩ W
    have hE : MeasurableSet E := hB.inter hW
    have hsub : E ⊆ W := inter_subset_right
    simp only [Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
    rw [cyl_eq hE hsub, hm_eq, wwc_ageμ_apply c (-(3 / 2 : ℝ)) hE,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Icc a₀ a₁
    · have hxpos : 0 < x := lt_of_lt_of_le ha₀ hx.1
      have h1 : 1 ≤ a₁ ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ)) := by
        have hp1 : a₁ ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hxpos hx.2 (by norm_num)
        have hp0 : a₁ ^ (3 / 2 : ℝ) * a₁ ^ (-(3 / 2 : ℝ)) = 1 := by
          rw [← Real.rpow_add ha₁_pos]; norm_num
        calc (1 : ℝ) = a₁ ^ (3 / 2 : ℝ) * a₁ ^ (-(3 / 2 : ℝ)) := hp0.symm
          _ ≤ a₁ ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hp1 (Real.rpow_nonneg ha₁_pos.le _)
      have henn : (1 : ℝ≥0∞) ≤
          ENNReal.ofReal (a₁ ^ (3 / 2 : ℝ)) * ENNReal.ofReal (x ^ (-(3 / 2 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha₁_pos.le _), ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal h1
      calc (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E)
          = 1 * (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) := (one_mul _).symm
        _ ≤ (ENNReal.ofReal (a₁ ^ (3 / 2 : ℝ)) * ENNReal.ofReal (x ^ (-(3 / 2 : ℝ)))) *
              (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) := mul_le_mul_of_nonneg_right henn zero_le
        _ = ENNReal.ofReal (a₁ ^ (3 / 2 : ℝ)) *
              ((UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) *
                ENNReal.ofReal (x ^ (-(3 / 2 : ℝ)))) := by ring
    · rw [slice_zero hsub hx]; simp
  · rw [Measure.le_iff]
    intro B hB
    set E := B ∩ W
    have hE : MeasurableSet E := hB.inter hW
    have hsub : E ⊆ W := inter_subset_right
    simp only [Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
    rw [cyl_eq hE hsub, hm_eq, wwc_ageμ_apply c (-(3 / 2 : ℝ)) hE,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Icc a₀ a₁
    · have hle : x ^ (-(3 / 2 : ℝ)) ≤ a₀ ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha₀ hx.1 (by norm_num)
      calc (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) * ENNReal.ofReal (x ^ (-(3 / 2 : ℝ)))
          ≤ (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) *
              ENNReal.ofReal (a₀ ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle) zero_le
        _ = ENNReal.ofReal (a₀ ^ (-(3 / 2 : ℝ))) *
              (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) := mul_comm _ _
    · rw [slice_zero hsub hx]; simp

private lemma scte_inHr_to_cyl {c a₀ a₁ : ℝ} (hc : 0 < c) (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ a₁)
    {u : CProf} (hu : InHr c 2 u)
    (hsupp : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1) → u x = 0) (i : Fin 2) :
    QPeriodicS c (fun x => u x i) ∧
      AEStronglyMeasurable (fun x => u x i) volume ∧
      cylNorm c 2 (fun x => u x i) < ⊤ := by
  have hper : QPeriodicS c (fun x => u x i) := by
    filter_upwards [QPerHalf.ae_imp hu.periodic] with x hx
    by_cases hpos : 0 < x.1
    · exact congrArg (fun v => v i) (hx hpos)
    · have hx1 : x.1 < a₀ := lt_of_le_of_lt (not_lt.mp hpos) ha₀
      rw [hsupp (qShift c x) (Or.inl hx1), hsupp x (Or.inl hx1)]
  obtain ⟨u', hu's, hua⟩ := exists_periodic_rep (a := (2 : ℝ) / 2 - 5 / 2) hc hu.periodic
    (hu.meas : AEStronglyMeasurable u (Axi.ageμ c ((2 : ℝ) / 2 - 5 / 2)))
  have hmeas : AEStronglyMeasurable (fun x => u x i) volume := by
    set gm : Coord → ℂ := fun x => if x.1 < a₀ then 0 else u' x i
    have hgm : Measurable gm := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_const ((EuclideanSpace.proj i).continuous.measurable.comp hu's.measurable)
    refine hgm.aestronglyMeasurable.congr ?_
    filter_upwards [hua] with x hx
    dsimp [gm]
    by_cases hlt : x.1 < a₀
    · simp only [hlt, ↓reduceIte]
      exact (congrArg (fun v : CMerid => v i) (hsupp x (Or.inl hlt))).symm
    · simp only [hlt, ↓reduceIte]
      exact (congrArg (fun v : CMerid => v i) (hx (lt_of_lt_of_le ha₀ (not_lt.mp hlt)))).symm
  set W : Set Coord := Icc a₀ a₁ ×ˢ (univ : Set (ℝ × ℝ))
  have hW : MeasurableSet W := measurableSet_Icc.prod MeasurableSet.univ
  have hind : (fun x => u x i) = W.indicator (fun x => u x i) := by
    funext x
    by_cases hx : x ∈ W
    · exact (indicator_of_mem hx (fun x => u x i)).symm
    · rw [indicator_of_notMem hx]
      have hout : x.1 < a₀ ∨ a₁ < x.1 := by
        by_contra hnot; push Not at hnot; exact hx ⟨hnot, trivial⟩
      exact congrArg (fun v : CMerid => v i) (hsupp x hout)
  have hcyl_eq : cylNorm c 2 (fun x => u x i) =
      eLpNorm (fun x => u x i) (ENNReal.ofReal 2) ((cylMeas c).restrict W) := by
    unfold cylNorm
    conv_lhs => rw [hind]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hW
  have ha₁_pos : 0 < a₁ := lt_of_lt_of_le ha₀ ha₁
  have hcmp := (scte_strip_measure_cmp c ha₀ ha₁).1
  have hfin : cylNorm c 2 (fun x => u x i) < ⊤ := by
    rw [hcyl_eq]
    have h1 := eLpNorm_mono_measure (p := ENNReal.ofReal 2) (fun x => u x i) hcmp
    rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top, smul_eq_mul,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ha₁_pos.le _) (by positivity)] at h1
    have h2 : eLpNorm (fun x => u x i) (ENNReal.ofReal 2) ((hMeas c 2).restrict W) ≤
        hNorm c 2 u :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (eLpNorm_mono fun x => PiLp.norm_apply_le (u x) i)
    exact lt_of_le_of_lt (h1.trans (mul_le_mul_of_nonneg_left h2 zero_le))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.finite)
  exact ⟨hper, hmeas, hfin⟩

private lemma scte_hNorm_le_cylNorm_strip {c a₀ a₁ : ℝ} (hc : 0 < c) (ha₀ : 0 < a₀)
    (ha₁ : a₀ ≤ a₁) {G : CProf}
    (hm0 : AEStronglyMeasurable (fun x => G x 0) volume)
    (hm1 : AEStronglyMeasurable (fun x => G x 1) volume)
    (hsupp : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1) → G x = 0) :
    hNorm c 2 G ≤
      ENNReal.ofReal ((a₀ ^ (-(3 / 2 : ℝ))) ^ (1 / ENNReal.ofReal 2).toReal) *
        (cylNorm c 2 (fun x => G x 0) + cylNorm c 2 (fun x => G x 1)) := by
  set W : Set Coord := Icc a₀ a₁ ×ˢ (univ : Set (ℝ × ℝ))
  have hW : MeasurableSet W := measurableSet_Icc.prod MeasurableSet.univ
  have hind : G = W.indicator G := by
    funext x
    by_cases hx : x ∈ W
    · exact (indicator_of_mem hx G).symm
    · rw [indicator_of_notMem hx]
      have hout : x.1 < a₀ ∨ a₁ < x.1 := by
        by_contra hnot; push Not at hnot; exact hx ⟨hnot, trivial⟩
      exact hsupp x hout
  have hh_eq : hNorm c 2 G = eLpNorm G (ENNReal.ofReal 2) ((hMeas c 2).restrict W) := by
    unfold hNorm
    conv_lhs => rw [hind]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hW
  have hcmp := (scte_strip_measure_cmp c ha₀ ha₁).2
  have h1 : hNorm c 2 G ≤
      ENNReal.ofReal ((a₀ ^ (-(3 / 2 : ℝ))) ^ (1 / ENNReal.ofReal 2).toReal) *
        eLpNorm G (ENNReal.ofReal 2) (cylMeas c) := by
    rw [hh_eq]
    have hm := eLpNorm_mono_measure (p := ENNReal.ofReal 2) G hcmp
    rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top, smul_eq_mul,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ha₀.le _) (by positivity)] at hm
    exact hm.trans
      (mul_le_mul_of_nonneg_left (eLpNorm_mono_measure _ Measure.restrict_le_self) zero_le)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hm0c : AEStronglyMeasurable (fun x => G x 0) (cylMeas c) :=
    hm0.mono_ac (chm_cylMeas_ac c hc)
  have hm1c : AEStronglyMeasurable (fun x => G x 1) (cylMeas c) :=
    hm1.mono_ac (chm_cylMeas_ac c hc)
  have h2 : eLpNorm G (ENNReal.ofReal 2) (cylMeas c) ≤
      cylNorm c 2 (fun x => G x 0) + cylNorm c 2 (fun x => G x 1) := by
    have hpt : ∀ x : Coord, ‖G x‖ ≤ ‖G x 0‖ + ‖G x 1‖ := by
      intro x
      have hsq : ‖G x‖ ^ 2 ≤ (‖G x 0‖ + ‖G x 1‖) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
        nlinarith [norm_nonneg (G x 0), norm_nonneg (G x 1)]
      exact (abs_le_of_sq_le_sq' hsq (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
    calc eLpNorm G (ENNReal.ofReal 2) (cylMeas c)
        ≤ eLpNorm (fun x => ‖G x 0‖ + ‖G x 1‖) (ENNReal.ofReal 2) (cylMeas c) :=
          eLpNorm_mono_real hpt
      _ ≤ eLpNorm (fun x => ‖G x 0‖) (ENNReal.ofReal 2) (cylMeas c) +
            eLpNorm (fun x => ‖G x 1‖) (ENNReal.ofReal 2) (cylMeas c) :=
          eLpNorm_add_le hm0c.norm hm1c.norm hp1
      _ = cylNorm c 2 (fun x => G x 0) + cylNorm c 2 (fun x => G x 1) := by
          rw [eLpNorm_norm, eLpNorm_norm]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)

private def scte_mollShift (σ : ℝ) : ℕ := Nat.ceil (8 / σ) + 1

private def scte_mollIdx (σ : ℝ) (n : ℕ) : ℕ := n + scte_mollShift σ

private lemma scte_mollIdx_rad_lt {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    1 / ((scte_mollIdx σ n : ℝ) + 2) < σ / 8 := by
  have hceil : 8 / σ ≤ (Nat.ceil (8 / σ) : ℝ) := Nat.le_ceil (8 / σ)
  have hgt : 8 / σ < (scte_mollIdx σ n : ℝ) + 2 := by
    dsimp [scte_mollIdx, scte_mollShift]
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hpos : 0 < 8 / σ := by positivity
  have h := one_div_lt_one_div_of_lt hpos hgt
  simpa [one_div_div] using h

private lemma scte_chmRho_cpd_vanish (m : ℕ) (j : Fin 3) {y : Coord}
    (hy : 1 / ((m : ℝ) + 2) < ‖y‖) :
    chmRho m y = 0 ∧ cpd j (chmRho m) y = 0 := by
  refine ⟨(chm_rho_props m).2.2.2.2 y hy, ?_⟩
  exact coef_cpd_vanish (isOpen_lt continuous_const continuous_norm)
    (fun z hz => (chm_rho_props m).2.2.2.2 z hz) j y hy

private lemma scte_chmConv_vanish_box {σ H₁ L₁ : ℝ} (hσ : 0 < σ) (n : ℕ)
    {K : Coord → ℝ} (hK : ∀ y : Coord, 1 / ((scte_mollIdx σ n : ℝ) + 2) < ‖y‖ → K y = 0)
    {g : Coord → ℂ}
    (hg : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → g z = 0)
    {x : Coord} (hx : x.1 < σ / 4 ∨ 2 * H₁ + σ / 4 < x.1 ∨ L₁ + 1 + σ / 4 < |x.2.2|) :
    chmConv K g x = 0 := by
  unfold chmConv
  refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
  by_cases hy : 1 / ((scte_mollIdx σ n : ℝ) + 2) < ‖y‖
  · simp [hK y hy]
  · have hrad : ‖y‖ < σ / 8 := lt_of_le_of_lt (not_lt.mp hy) (scte_mollIdx_rad_lt hσ n)
    have hy1 : |y.1| < σ / 8 :=
      lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using norm_fst_le y) hrad
    have hy3 : |y.2.2| < σ / 8 :=
      lt_of_le_of_lt ((Real.norm_eq_abs _).symm.le.trans ((norm_snd_le y.2).trans (norm_snd_le y)))
        hrad
    obtain ⟨hy1l, hy1u⟩ := abs_lt.mp hy1
    obtain ⟨hy3l, hy3u⟩ := abs_lt.mp hy3
    have hgz : g (x - y) = 0 := by
      apply hg (x - y)
      rcases hx with hx1 | hx2 | hx3
      · exact Or.inl (by change x.1 - y.1 < σ / 2; linarith)
      · exact Or.inr (Or.inl (by change 2 * H₁ < x.1 - y.1; linarith))
      · refine Or.inr (Or.inr ?_)
        change L₁ + 1 < |x.2.2 - y.2.2|
        rcases lt_abs.mp hx3 with hx3a | hx3b
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))
    simp [hgz]

private def sctePairCLM : (ℂ × ℂ) →L[ℝ] CMerid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 fun i => if i = 0 then p.1 else p.2
      map_add' := fun p q => by ext i; fin_cases i <;> simp
      map_smul' := fun r p => by ext i; fin_cases i <;> simp }

@[simp]
private lemma sctePairCLM_zero (a b : ℂ) : sctePairCLM (a, b) 0 = a := rfl

@[simp]
private lemma sctePairCLM_one (a b : ℂ) : sctePairCLM (a, b) 1 = b := rfl

private def scte_mollProf (σ : ℝ) (n : ℕ) (G : CProf) : CProf :=
  fun x => sctePairCLM
    (chmConv (chmRho (scte_mollIdx σ n)) (fun z => G z 0) x,
     chmConv (chmRho (scte_mollIdx σ n)) (fun z => G z 1) x)

@[simp]
private lemma scte_mollProf_apply (σ : ℝ) (n : ℕ) (G : CProf) (x : Coord) (i : Fin 2) :
    scte_mollProf σ n G x i = chmConv (chmRho (scte_mollIdx σ n)) (fun z => G z i) x := by
  unfold scte_mollProf sctePairCLM
  fin_cases i <;> rfl

private lemma scte_fderiv_comp_apply {B : CProf} (hB : ContDiff ℝ ∞ B) (j : Fin 3) (x : Coord)
    (i : Fin 2) :
    fderiv ℝ B x (cdir j) i = cdv j (fun y => B y i) x := by
  set L : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj i).restrictScalars ℝ
  have hd : DifferentiableAt ℝ B x := (hB.differentiable (by simp)) x
  have hcomp : HasFDerivAt (fun y => B y i) (L.comp (fderiv ℝ B x)) x :=
    L.hasFDerivAt.comp x hd.hasFDerivAt
  unfold cdv
  rw [hcomp.fderiv]
  rfl

private lemma scte_mollProf_nice_tendsto {c σ H₁ L₁ : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH₁ : σ ≤ H₁) {G : CProf} (hG : InHr c 2 G)
    (hsupp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → G z = 0) :
    (∀ n : ℕ, NiceProf c (scte_mollProf σ n G)) ∧
      (∀ (n : ℕ) (x : Coord),
        (x.1 < σ / 4 ∨ 2 * H₁ + σ / 4 < x.1 ∨ L₁ + 1 + σ / 4 < |x.2.2|) →
          scte_mollProf σ n G x = 0) ∧
      Tendsto (fun n : ℕ => hNorm c 2 (fun x => scte_mollProf σ n G x - G x)) atTop (𝓝 0) := by
  have ha₀ : 0 < σ / 2 := half_pos hσ
  have ha₁ : σ / 2 ≤ 2 * H₁ := by linarith
  have hstrip : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1) → G z = 0 := by
    intro z hz
    rcases hz with h1 | h2
    · exact hsupp z (Or.inl h1)
    · exact hsupp z (Or.inr (Or.inl h2))
  obtain ⟨hp0, hm0, hn0⟩ := scte_inHr_to_cyl hc ha₀ ha₁ hG hstrip 0
  obtain ⟨hp1, hm1, hn1⟩ := scte_inHr_to_cyl hc ha₀ ha₁ hG hstrip 1
  have hvan : ∀ (n : ℕ) (x : Coord),
      (x.1 < σ / 4 ∨ 2 * H₁ + σ / 4 < x.1 ∨ L₁ + 1 + σ / 4 < |x.2.2|) →
        scte_mollProf σ n G x = 0 := by
    intro n x hx
    ext i
    rw [scte_mollProf_apply]
    exact scte_chmConv_vanish_box hσ n (fun y hy => (scte_chmRho_cpd_vanish _ 0 hy).1)
      (fun z hz => congrArg (fun v : CMerid => v i) (hsupp z hz)) hx
  have hnice : ∀ n : ℕ, NiceProf c (scte_mollProf σ n G) := by
    intro n
    set m := scte_mollIdx σ n
    have hs0 := (chmMollNice 2 one_lt_two c hc _ hp0 hm0 hn0 m).smooth
    have hs1 := (chmMollNice 2 one_lt_two c hc _ hp1 hm1 hn1 m).smooth
    have hsm : ContDiff ℝ ∞ (scte_mollProf σ n G) :=
      sctePairCLM.contDiff.comp (hs0.prodMk hs1)
    refine ⟨hsm, fun x => ?_, σ / 4, 2 * H₁ + σ / 4, L₁ + 1 + σ / 4, by positivity, hvan n⟩
    ext i
    rw [scte_mollProf_apply, scte_mollProf_apply]
    fin_cases i
    · exact chm_periodic hp0 (chmRho m) x
    · exact chm_periodic hp1 (chmRho m) x
  have hc0 : Tendsto (fun n => cylNorm c 2 (fun x => scte_mollProf σ n G x 0 - G x 0))
      atTop (𝓝 0) :=
    (chmMollConv 2 one_lt_two c hc _ hp0 hm0 hn0).comp (tendsto_add_atTop_nat (scte_mollShift σ))
  have hc1 : Tendsto (fun n => cylNorm c 2 (fun x => scte_mollProf σ n G x 1 - G x 1))
      atTop (𝓝 0) :=
    (chmMollConv 2 one_lt_two c hc _ hp1 hm1 hn1).comp (tendsto_add_atTop_nat (scte_mollShift σ))
  have hlim : Tendsto (fun n : ℕ => hNorm c 2 (fun x => scte_mollProf σ n G x - G x))
      atTop (𝓝 0) := by
    set K := ENNReal.ofReal (((σ / 4) ^ (-(3 / 2 : ℝ))) ^ (1 / ENNReal.ofReal 2).toReal)
    have hb0 : 0 < σ / 4 := by positivity
    have hb1 : σ / 4 ≤ 2 * H₁ + σ / 4 := by linarith
    have hmaj : Tendsto (fun n => K *
        (cylNorm c 2 (fun x => scte_mollProf σ n G x 0 - G x 0) +
          cylNorm c 2 (fun x => scte_mollProf σ n G x 1 - G x 1))) atTop (𝓝 0) := by
      have hsum : Tendsto (fun n =>
          cylNorm c 2 (fun x => scte_mollProf σ n G x 0 - G x 0) +
            cylNorm c 2 (fun x => scte_mollProf σ n G x 1 - G x 1)) atTop (𝓝 0) := by
        simpa only [add_zero] using hc0.add hc1
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul (a := K) hsum (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj
      (fun _ => bot_le) fun n => ?_
    have hd0 : AEStronglyMeasurable (fun x => scte_mollProf σ n G x 0 - G x 0) volume :=
      (chmMollNice 2 one_lt_two c hc _ hp0 hm0 hn0 _).smooth.continuous.aestronglyMeasurable.sub
        hm0
    have hd1 : AEStronglyMeasurable (fun x => scte_mollProf σ n G x 1 - G x 1) volume :=
      (chmMollNice 2 one_lt_two c hc _ hp1 hm1 hn1 _).smooth.continuous.aestronglyMeasurable.sub
        hm1
    refine scte_hNorm_le_cylNorm_strip hc hb0 hb1 hd0 hd1 fun x hx => ?_
    have h1 : scte_mollProf σ n G x = 0 := by
      rcases hx with hx1 | hx2
      · exact hvan n x (Or.inl hx1)
      · exact hvan n x (Or.inr (Or.inl hx2))
    have h2 : G x = 0 := by
      rcases hx with hx1 | hx2
      · exact hsupp x (Or.inl (by linarith))
      · exact hsupp x (Or.inr (Or.inl (by linarith)))
    simp [h1, h2]
  exact ⟨hnice, hvan, hlim⟩

private lemma scte_mollProf_fderiv_eq {c σ H₁ L₁ : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH₁ : σ ≤ H₁) {t St' Dt' Et' : CProf}
    (ht : InHr c 2 t) (hSt'_in : InHr c 2 St')
    (ht_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → t z = 0)
    (hSt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → St' z = 0)
    (hDt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Dt' z = 0)
    (hEt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Et' z = 0)
    (hSt' : HasWeakVec vS dZero t St')
    (hDt' : HasWeakVec vQ0 dZero t Dt')
    (hEt' : HasWeakVec vEta dZero t Et') :
    let Us : CProf := fun z => if z.1 < σ / 2 then 0 else ((z.1⁻¹ : ℝ) : ℂ) • St' z
    InHr c 2 Us ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Us z = 0) ∧
      ∀ (n : ℕ) (x : Coord),
        fderiv ℝ (scte_mollProf σ n t) x (cdir 0) = scte_mollProf σ n Us x ∧
        fderiv ℝ (scte_mollProf σ n t) x (cdir 1) = scte_mollProf σ n Dt' x ∧
        fderiv ℝ (scte_mollProf σ n t) x (cdir 2) = scte_mollProf σ n Et' x := by
  intro Us
  have hUs_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Us z = 0 := by
    intro z hz
    dsimp [Us]
    by_cases hz1 : z.1 < σ / 2
    · simp only [hz1, ↓reduceIte]
    · simp only [hz1, ↓reduceIte, hSt'_supp z hz, smul_zero]
  have hUs_in : InHr c 2 Us := by
    have hper : QPeriodic c Us := by
      filter_upwards [hSt'_in.periodic] with z hz
      change (if z.1 < σ / 2 then 0 else ((z.1⁻¹ : ℝ) : ℂ) • St' (qShift c z)) =
        if z.1 < σ / 2 then 0 else ((z.1⁻¹ : ℝ) : ℂ) • St' z
      rw [hz]
    have hmul_m : Measurable (fun z : Coord =>
        if z.1 < σ / 2 then (0 : ℂ) else ((z.1⁻¹ : ℝ) : ℂ)) :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_const
        (Complex.measurable_ofReal.comp measurable_fst.inv)
    have hmeas : AEStronglyMeasurable Us (hMeas c 2) := by
      refine (hmul_m.aestronglyMeasurable.smul hSt'_in.meas).congr (ae_of_all _ fun z => ?_)
      change (if z.1 < σ / 2 then (0 : ℂ) else ((z.1⁻¹ : ℝ) : ℂ)) • St' z =
        if z.1 < σ / 2 then 0 else ((z.1⁻¹ : ℝ) : ℂ) • St' z
      by_cases hz1 : z.1 < σ / 2 <;> simp only [hz1, ↓reduceIte, zero_smul]
    have hpt : ∀ z : Coord, ‖Us z‖ ≤ (σ / 2)⁻¹ * ‖St' z‖ := by
      intro z
      dsimp [Us]
      by_cases hz1 : z.1 < σ / 2
      · simp only [hz1, ↓reduceIte, norm_zero]
        exact mul_nonneg (inv_nonneg.2 (half_pos hσ).le) (norm_nonneg _)
      · have hz_ge : σ / 2 ≤ z.1 := not_lt.mp hz1
        have hz_pos : 0 < z.1 := lt_of_lt_of_le (half_pos hσ) hz_ge
        simp only [hz1, ↓reduceIte, norm_smul, norm_inv, Real.norm_of_nonneg hz_pos.le]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ (half_pos hσ) hz_ge) (norm_nonneg _)
    have hfin : hNorm c 2 Us < ⊤ := by
      have h1 : hNorm c 2 Us ≤
          eLpNorm ((((σ / 2)⁻¹ : ℝ) : ℂ) • St') (ENNReal.ofReal 2) (hMeas c 2) := by
        refine eLpNorm_mono fun z => ?_
        simp only [Pi.smul_apply, Complex.ofReal_inv, norm_smul, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg (half_pos hσ).le]
        exact hpt z
      rw [eLpNorm_const_smul] at h1
      exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top enorm_lt_top hSt'_in.finite)
    exact ⟨hper, hmeas, hfin⟩
  obtain ⟨ht_nice, -, -⟩ := scte_mollProf_nice_tendsto hc hσ hσH₁ ht ht_supp
  have ha₀ : 0 < σ / 2 := half_pos hσ
  have ha₁ : σ / 2 ≤ 2 * H₁ := by linarith
  have ht_strip : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1) → t z = 0 := by
    intro z hz
    rcases hz with h1 | h2
    · exact ht_supp z (Or.inl h1)
    · exact ht_supp z (Or.inr (Or.inl h2))
  have ht_loc : ∀ i : Fin 2, LocallyIntegrable (fun z => t z i) volume := by
    intro i
    obtain ⟨hp, hm, hn⟩ := scte_inHr_to_cyl hc ha₀ ha₁ ht ht_strip i
    exact chmLocInt c hc 2 one_lt_two _ hp hm hn
  refine ⟨hUs_in, hUs_supp, fun n x => ?_⟩
  set m := scte_mollIdx σ n
  have hρ : ContDiff ℝ ∞ (chmRho m) := chmRho_contDiff m
  have hcs : HasCompactSupport (chmRho m) := chmRho_compact m
  have hρd : Differentiable ℝ (chmRho m) := hρ.differentiable (by simp)
  have hfd_eq : ∀ (j : Fin 3) (i : Fin 2),
      fderiv ℝ (scte_mollProf σ n t) x (cdir j) i =
        chmConv (cpd j (chmRho m)) (fun z => t z i) x := by
    intro j i
    rw [scte_fderiv_comp_apply (ht_nice n).1 j x i]
    have hfun : (fun y => scte_mollProf σ n t y i) = chmConv (chmRho m) (fun z => t z i) :=
      funext fun y => scte_mollProf_apply σ n t y i
    rw [hfun]
    exact chm_cdvConv_aux hρ hcs (ht_loc i) j x
  by_cases hx1 : x.1 < σ / 4
  · refine ⟨?_, ?_, ?_⟩ <;> ext i <;> rw [hfd_eq _ i, scte_mollProf_apply]
    · rw [scte_chmConv_vanish_box (H₁ := H₁) (L₁ := L₁) hσ n
        (fun y hy => (scte_chmRho_cpd_vanish m 0 hy).2)
        (fun z hz => congrArg (fun v : CMerid => v i) (ht_supp z hz)) (Or.inl hx1),
        scte_chmConv_vanish_box (H₁ := H₁) (L₁ := L₁) hσ n
        (fun y hy => (scte_chmRho_cpd_vanish m 0 hy).1)
        (fun z hz => congrArg (fun v : CMerid => v i) (hUs_supp z hz)) (Or.inl hx1)]
    · rw [scte_chmConv_vanish_box (H₁ := H₁) (L₁ := L₁) hσ n
        (fun y hy => (scte_chmRho_cpd_vanish m 1 hy).2)
        (fun z hz => congrArg (fun v : CMerid => v i) (ht_supp z hz)) (Or.inl hx1),
        scte_chmConv_vanish_box (H₁ := H₁) (L₁ := L₁) hσ n
        (fun y hy => (scte_chmRho_cpd_vanish m 0 hy).1)
        (fun z hz => congrArg (fun v : CMerid => v i) (hDt'_supp z hz)) (Or.inl hx1)]
    · rw [scte_chmConv_vanish_box (H₁ := H₁) (L₁ := L₁) hσ n
        (fun y hy => (scte_chmRho_cpd_vanish m 2 hy).2)
        (fun z hz => congrArg (fun v : CMerid => v i) (ht_supp z hz)) (Or.inl hx1),
        scte_chmConv_vanish_box (H₁ := H₁) (L₁ := L₁) hσ n
        (fun y hy => (scte_chmRho_cpd_vanish m 0 hy).1)
        (fun z hz => congrArg (fun v : CMerid => v i) (hEt'_supp z hz)) (Or.inl hx1)]
  · have hx_ge : σ / 4 ≤ x.1 := not_lt.mp hx1
    set φ : Coord → ℝ := fun z => chmRho m (x - z)
    have hφ_s : ContDiff ℝ ∞ φ := hρ.comp (contDiff_const.sub contDiff_id)
    have hφ_c : HasCompactSupport φ :=
      hcs.comp_homeomorph ((Homeomorph.neg Coord).trans (Homeomorph.addLeft x))
    have hφ_low : ∀ z : Coord, z.1 < σ / 8 → φ z = 0 := by
      intro z hz
      have hrad := scte_mollIdx_rad_lt hσ n
      have hdiff : σ / 8 < ‖x - z‖ := by
        have h1 : σ / 8 < x.1 - z.1 := by linarith
        have h2 : x.1 - z.1 ≤ |x.1 - z.1| := le_abs_self _
        have h3 : |(x - z).1| ≤ ‖x - z‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (x - z)
        exact lt_of_lt_of_le h1 (h2.trans h3)
      exact (chm_rho_props m).2.2.2.2 (x - z) (hrad.trans hdiff)
    have hφ_supp : tsupport φ ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
      have hsub : tsupport φ ⊆ {z : Coord | σ / 8 ≤ z.1} :=
        closure_minimal
          (Function.support_subset_iff'.2 fun z hz => hφ_low z (lt_of_not_ge hz))
          (isClosed_le continuous_const continuous_fst)
      exact hsub.trans fun z hz => ⟨lt_of_lt_of_le (by positivity : 0 < σ / 8) hz, trivial⟩
    have hφ_test : IsCoordTest φ := ⟨hφ_s, hφ_c, hφ_supp⟩
    have hconv_φ : ∀ g : Coord → ℂ, chmConv (chmRho m) g x = ∫ z, g z * (φ z : ℂ) := by
      intro g
      unfold chmConv
      rw [← integral_sub_left_eq_self (fun y => (chmRho m y : ℂ) * g (x - y)) volume x]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [sub_sub_cancel, φ]
      ring
    set ψ : Coord → ℝ := scteW (-1 : ℝ) 1 φ
    have hψ_s : ContDiff ℝ ∞ ψ :=
      scteW_contDiff (a := (-1 : ℝ)) (c := 1) hφ_s (by positivity : 0 < σ / 8) hφ_low
    have hsupp_φ : Function.support ψ ⊆ Function.support φ := by
      intro z hz
      rw [Function.mem_support] at hz ⊢
      intro h0
      exact hz (by simp [ψ, scteW, h0])
    have hψ_c : HasCompactSupport ψ :=
      HasCompactSupport.of_support_subset_isCompact hφ_c (hsupp_φ.trans (subset_tsupport φ))
    have hψ_supp : tsupport ψ ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
      (closure_minimal (hsupp_φ.trans (subset_tsupport φ)) (isClosed_tsupport φ)).trans hφ_supp
    have hψ_test : IsCoordTest ψ := ⟨hψ_s, hψ_c, hψ_supp⟩
    have hs_mul_ψ : (fun w : Coord => w.1 * ψ w) = φ := by
      funext w
      by_cases hw : w.1 < σ / 8
      · simp [ψ, scteW, hφ_low w hw]
      · have hw_pos : 0 < w.1 := lt_of_lt_of_le (by positivity : 0 < σ / 8) (not_lt.mp hw)
        dsimp [ψ, scteW]
        rw [inv_one, one_mul, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
    refine ⟨?_, ?_, ?_⟩
    · ext i
      rw [hfd_eq 0 i, scte_mollProf_apply, hconv_φ]
      unfold chmConv
      rw [← integral_sub_left_eq_self (fun y => (cpd 0 (chmRho m) y : ℂ) * t (x - y) i) volume x]
      have hLHS : ∫ z, (cpd 0 (chmRho m) (x - z) : ℂ) * t (x - (x - z)) i =
          ∫ z, t z i * (coordTranspose vS dZero ψ z : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        have hT : coordTranspose vS dZero ψ z = cpd 0 (chmRho m) (x - z) := by
          rw [qd_coordT_eq]
          have e0 : cpd 0 (fun w => vS w 0 * ψ w) z = cpd 0 φ z := by
            change cpd 0 (fun w => w.1 * ψ w) z = cpd 0 φ z
            rw [hs_mul_ψ]
          have e1 : cpd 1 (fun w => vS w 1 * ψ w) z = 0 := by simp [vS, cpd]
          have e2 : cpd 2 (fun w => vS w 2 * ψ w) z = 0 := by simp [vS, cpd]
          rw [e0, e1, e2, cpd_reflect hρd x z 0]
          simp [dZero]
        simp only [sub_sub_cancel, hT]
        ring
      have hRHS : ∫ z, St' z i * (ψ z : ℂ) = ∫ z, Us z i * (φ z : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        by_cases hz1 : z.1 < σ / 2
        · have hU0 : Us z i = 0 := by dsimp [Us]; simp only [hz1, ↓reduceIte]; rfl
          have hS0 : St' z i = 0 := congrArg (fun v : CMerid => v i) (hSt'_supp z (Or.inl hz1))
          rw [hU0, hS0, zero_mul, zero_mul]
        · have hU1 : Us z i = ((z.1⁻¹ : ℝ) : ℂ) * St' z i := by
            dsimp [Us]; simp only [hz1, ↓reduceIte]; rfl
          have hψ1 : ψ z = z.1⁻¹ * φ z := by
            dsimp [ψ, scteW]; rw [inv_one, one_mul, Real.rpow_neg_one]
          rw [hU1, hψ1]
          push_cast
          ring
      rw [hLHS, ← (hSt' i).2 ψ hψ_test, hRHS]
    · ext i
      rw [hfd_eq 1 i, scte_mollProf_apply, hconv_φ]
      unfold chmConv
      rw [← integral_sub_left_eq_self (fun y => (cpd 1 (chmRho m) y : ℂ) * t (x - y) i) volume x]
      have hLHS : ∫ z, (cpd 1 (chmRho m) (x - z) : ℂ) * t (x - (x - z)) i =
          ∫ z, t z i * (coordTranspose vQ0 dZero φ z : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        have hT : coordTranspose vQ0 dZero φ z = cpd 1 (chmRho m) (x - z) := by
          rw [qd_coordT_eq]
          have e0 : cpd 0 (fun w => vQ0 w 0 * φ w) z = 0 := by simp [vQ0, cpd]
          have e1 : cpd 1 (fun w => vQ0 w 1 * φ w) z = cpd 1 φ z := by simp [vQ0]
          have e2 : cpd 2 (fun w => vQ0 w 2 * φ w) z = 0 := by simp [vQ0, cpd]
          rw [e0, e1, e2, cpd_reflect hρd x z 1]
          simp [dZero]
        simp only [sub_sub_cancel, hT]
        ring
      rw [hLHS, ← (hDt' i).2 φ hφ_test]
    · ext i
      rw [hfd_eq 2 i, scte_mollProf_apply, hconv_φ]
      unfold chmConv
      rw [← integral_sub_left_eq_self (fun y => (cpd 2 (chmRho m) y : ℂ) * t (x - y) i) volume x]
      have hLHS : ∫ z, (cpd 2 (chmRho m) (x - z) : ℂ) * t (x - (x - z)) i =
          ∫ z, t z i * (coordTranspose vEta dZero φ z : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        have hT : coordTranspose vEta dZero φ z = cpd 2 (chmRho m) (x - z) := by
          rw [qd_T_E, cpd_reflect hρd x z 2, neg_neg]
        simp only [sub_sub_cancel, hT]
        ring
      rw [hLHS, ← (hEt' i).2 φ hφ_test]

private lemma scte_hNorm_mul_box_le {c a₀ a₁ M : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hM : 0 ≤ M)
    {H : CProf} (hH : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → H x = 0) :
    hNorm c 2 (sqrtS H) ≤ ENNReal.ofReal (Real.sqrt a₁) * hNorm c 2 H ∧
      hNorm c 2 (fun x => (x.1 : ℂ) • H x) ≤ ENNReal.ofReal a₁ * hNorm c 2 H ∧
      hNorm c 2 (fun x => (x.2.2 : ℂ) • H x) ≤ ENNReal.ofReal M * hNorm c 2 H := by
  have bdd_smul : ∀ (K : ℝ), 0 ≤ K → ∀ (f : Coord → ℂ),
      (∀ x : Coord, ¬ (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → ‖f x‖ ≤ K) →
      hNorm c 2 (fun x => f x • H x) ≤ ENNReal.ofReal K * hNorm c 2 H := by
    intro K hK f hf
    have hle : hNorm c 2 (fun x => f x • H x) ≤
        eLpNorm ((K : ℂ) • H) (ENNReal.ofReal 2) (hMeas c 2) := by
      refine eLpNorm_mono fun x => ?_
      rw [Pi.smul_apply, norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hK]
      by_cases hx : x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|
      · rw [hH x hx, norm_zero, mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right (hf x hx) (norm_nonneg _)
    rw [eLpNorm_const_smul] at hle
    have hK_eq : ‖(K : ℂ)‖ₑ = ENNReal.ofReal K := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hK]
    rwa [hK_eq] at hle
  refine ⟨?_, ?_, ?_⟩
  · refine bdd_smul (Real.sqrt a₁) (Real.sqrt_nonneg _) (fun x => (Real.sqrt x.1 : ℂ))
      fun x hx => ?_
    push Not at hx
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hx.2.1
  · refine bdd_smul a₁ ha₁ (fun x => (x.1 : ℂ)) fun x hx => ?_
    push Not at hx
    rw [Complex.norm_real, Real.norm_of_nonneg (ha₀.trans hx.1)]
    exact hx.2.1
  · refine bdd_smul M hM (fun x => (x.2.2 : ℂ)) fun x hx => ?_
    push Not at hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx.2.2

private lemma scte_mollProf_all_tendsto {c σ H₁ L₁ ε : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH₁ : σ ≤ H₁) (hL₁0 : 0 ≤ L₁) (hε0 : 0 < ε)
    {t St' Dt' Qt' Et' : CProf}
    (ht : InHr c 2 t) (hSt'_in : InHr c 2 St')
    (hDt'_in : InHr c 2 Dt') (hEt'_in : InHr c 2 Et')
    (ht_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → t z = 0)
    (hSt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → St' z = 0)
    (hDt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Dt' z = 0)
    (hEt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Et' z = 0)
    (hSt' : HasWeakVec vS dZero t St')
    (hDt' : HasWeakVec vQ0 dZero t Dt')
    (hQt' : HasWeakVec (vQ ε) (dQ ε) t Qt')
    (hEt' : HasWeakVec vEta dZero t Et') :
    let B_n := fun n : ℕ => scte_mollProf σ n t
    (∀ n : ℕ, NiceProf c (B_n n)) ∧
      Tendsto (fun n => hNorm c 2 (fun x => B_n n x - t x)) atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c 2 (fun x => (x.1 : ℂ) • B_n n x - (x.1 : ℂ) • t x))
        atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c 2 (fun x =>
        sqrtS (fun y => fderiv ℝ (B_n n) y (cdir 1)) x - sqrtS Dt' x)) atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c 2 (fun x =>
        sqrtS (classEta (B_n n)) x - sqrtS Et' x)) atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c 2 (fun x =>
        sqrtS (classQ ε (B_n n)) x - sqrtS Qt' x)) atTop (𝓝 0) := by
  intro B_n
  obtain ⟨hUs_in, hUs_supp, hfd_eq⟩ := scte_mollProf_fderiv_eq hc hσ hσH₁ ht hSt'_in
    ht_supp hSt'_supp hDt'_supp hEt'_supp hSt' hDt' hEt'
  set Us : CProf := fun z => if z.1 < σ / 2 then 0 else ((z.1⁻¹ : ℝ) : ℂ) • St' z
  obtain ⟨ht_nice, ht_van, ht_lim⟩ := scte_mollProf_nice_tendsto hc hσ hσH₁ ht ht_supp
  obtain ⟨-, hUs_van, hUs_lim⟩ := scte_mollProf_nice_tendsto hc hσ hσH₁ hUs_in hUs_supp
  obtain ⟨-, hDt_van, hDt_lim⟩ := scte_mollProf_nice_tendsto hc hσ hσH₁ hDt'_in hDt'_supp
  obtain ⟨-, hEt_van, hEt_lim⟩ := scte_mollProf_nice_tendsto hc hσ hσH₁ hEt'_in hEt'_supp
  set a₀ := σ / 4
  set a₁ := 2 * H₁ + σ / 4
  set M := L₁ + 1 + σ / 4
  have ha₀ : 0 ≤ a₀ := by dsimp [a₀]; positivity
  have ha₁ : 0 ≤ a₁ := by dsimp [a₁]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have widen_supp : ∀ {G : CProf},
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → G z = 0) →
      ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → G x = 0 := by
    intro G hG x hx
    apply hG x
    rcases hx with h1 | h2 | h3
    · exact Or.inl (by dsimp [a₀] at h1; linarith)
    · exact Or.inr (Or.inl (by dsimp [a₁] at h2; linarith))
    · exact Or.inr (Or.inr (by dsimp [M] at h3; linarith))
  have tendsto_of_le_const : ∀ (K : ℝ) {fn : ℕ → ℝ≥0∞} {gn : ℕ → ℝ≥0∞},
      (∀ n, fn n ≤ ENNReal.ofReal K * gn n) → Tendsto gn atTop (𝓝 0) →
      Tendsto fn atTop (𝓝 0) := by
    intro K fn gn hle hgn
    have hmaj : Tendsto (fun n => ENNReal.ofReal K * gn n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hgn (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj (fun _ => bot_le) hle
  have hsB_lim : Tendsto (fun n => hNorm c 2 (fun x => (x.1 : ℂ) • B_n n x - (x.1 : ℂ) • t x))
      atTop (𝓝 0) := by
    refine tendsto_of_le_const a₁ (fun n => ?_) ht_lim
    have heq : (fun x : Coord => (x.1 : ℂ) • B_n n x - (x.1 : ℂ) • t x) =
        fun x => (x.1 : ℂ) • (B_n n x - t x) := by funext x; rw [smul_sub]
    rw [heq]
    exact (scte_hNorm_mul_box_le ha₀ ha₁ hM fun x hx => by
      dsimp only [B_n]; simp [ht_van n x hx, widen_supp ht_supp x hx]).2.1
  have hsqD_lim : Tendsto (fun n => hNorm c 2 (fun x =>
      sqrtS (fun y => fderiv ℝ (B_n n) y (cdir 1)) x - sqrtS Dt' x)) atTop (𝓝 0) := by
    refine tendsto_of_le_const (Real.sqrt a₁) (fun n => ?_) hDt_lim
    have heq : (fun x => sqrtS (fun y => fderiv ℝ (B_n n) y (cdir 1)) x - sqrtS Dt' x) =
        sqrtS (fun x => scte_mollProf σ n Dt' x - Dt' x) := by
      funext x; dsimp only [B_n, sqrtS]; rw [(hfd_eq n x).2.1, smul_sub]
    rw [heq]
    exact (scte_hNorm_mul_box_le ha₀ ha₁ hM fun x hx => by
      simp [hDt_van n x hx, widen_supp hDt'_supp x hx]).1
  have hsqE_lim : Tendsto (fun n => hNorm c 2 (fun x =>
      sqrtS (classEta (B_n n)) x - sqrtS Et' x)) atTop (𝓝 0) := by
    refine tendsto_of_le_const (Real.sqrt a₁) (fun n => ?_) hEt_lim
    have heq : (fun x => sqrtS (classEta (B_n n)) x - sqrtS Et' x) =
        sqrtS (fun x => scte_mollProf σ n Et' x - Et' x) := by
      funext x; dsimp only [B_n, classEta, sqrtS]; rw [(hfd_eq n x).2.2, smul_sub]
    rw [heq]
    exact (scte_hNorm_mul_box_le ha₀ ha₁ hM fun x hx => by
      simp [hEt_van n x hx, widen_supp hEt'_supp x hx]).1
  have hS_lim : Tendsto (fun n => hNorm c 2 (fun x =>
      (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x)) atTop (𝓝 0) := by
    refine tendsto_of_le_const a₁ (fun n => ?_) hUs_lim
    have heq : (fun x : Coord => (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) =
        fun x => (x.1 : ℂ) • (scte_mollProf σ n Us x - Us x) := by
      funext x
      dsimp only [B_n]
      rw [(hfd_eq n x).1, smul_sub]
      congr 1
      by_cases hx1 : x.1 < σ / 2
      · have hU0 : Us x = 0 := by dsimp [Us]; simp only [hx1, ↓reduceIte]
        rw [hU0, smul_zero, hSt'_supp x (Or.inl hx1)]
      · have hx_pos : 0 < x.1 := lt_of_lt_of_le (half_pos hσ) (not_lt.mp hx1)
        have hU1 : Us x = ((x.1⁻¹ : ℝ) : ℂ) • St' x := by dsimp [Us]; simp only [hx1, ↓reduceIte]
        have hc_inv : (x.1 : ℂ) * ((x.1⁻¹ : ℝ) : ℂ) = 1 := by
          push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hx_pos.ne')
        rw [hU1, smul_smul, hc_inv, one_smul]
    rw [heq]
    exact (scte_hNorm_mul_box_le ha₀ ha₁ hM fun x hx => by
      simp [hUs_van n x hx, widen_supp hUs_supp x hx]).2.1
  have hηE_lim : Tendsto (fun n => hNorm c 2 (fun x =>
      (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x))) atTop (𝓝 0) := by
    refine tendsto_of_le_const M (fun n => ?_) hEt_lim
    have heq : (fun x : Coord => (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) =
        fun x => (x.2.2 : ℂ) • (scte_mollProf σ n Et' x - Et' x) := by
      funext x; dsimp only [B_n, classEta]; rw [(hfd_eq n x).2.2]
    rw [heq]
    exact (scte_hNorm_mul_box_le ha₀ ha₁ hM fun x hx => by
      simp [hEt_van n x hx, widen_supp hEt'_supp x hx]).2.2
  have hQ_raw_lim : Tendsto (fun n => hNorm c 2 (fun x =>
      classQ ε (B_n n) x - qepsOf ε t St' Dt' Et' x)) atTop (𝓝 0) := by
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
    have hmaj : Tendsto (fun n =>
        hNorm c 2 (fun x => scte_mollProf σ n Dt' x - Dt' x) +
          ENNReal.ofReal (2 * ε) *
            hNorm c 2 (fun x => (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) +
          ENNReal.ofReal ε *
            hNorm c 2 (fun x => (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) +
          ENNReal.ofReal ε * hNorm c 2 (fun x => B_n n x - t x)) atTop (𝓝 0) := by
      have t2 : Tendsto (fun n => ENNReal.ofReal (2 * ε) *
          hNorm c 2 (fun x => (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x)) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * ε)) hS_lim
            (Or.inr ENNReal.ofReal_ne_top)
      have t3 : Tendsto (fun n => ENNReal.ofReal ε *
          hNorm c 2 (fun x => (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x))) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ε) hηE_lim
            (Or.inr ENNReal.ofReal_ne_top)
      have t4 : Tendsto (fun n => ENNReal.ofReal ε *
          hNorm c 2 (fun x => B_n n x - t x)) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ε) ht_lim
            (Or.inr ENNReal.ofReal_ne_top)
      simpa only [add_zero] using ((hDt_lim.add t2).add t3).add t4
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj
      (fun _ => bot_le) fun n => ?_
    have hpt : ∀ x : Coord,
        ‖classQ ε (B_n n) x - qepsOf ε t St' Dt' Et' x‖ ≤
          ‖scte_mollProf σ n Dt' x - Dt' x‖ +
            (2 * ε) * ‖(x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x‖ +
            ε * ‖(x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)‖ +
            ε * ‖B_n n x - t x‖ := by
      intro x
      have hid : classQ ε (B_n n) x - qepsOf ε t St' Dt' Et' x =
          (scte_mollProf σ n Dt' x - Dt' x) -
            ((2 * ε : ℝ) : ℂ) • ((x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) -
            (ε : ℂ) • ((x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) -
            (ε : ℂ) • (B_n n x - t x) := by
        ext i
        dsimp only [B_n]
        unfold classQ classEta
        rw [Fin.sum_univ_three, ← (hfd_eq n x).2.1]
        dsimp [vQ, dQ]
        push_cast
        ring
      rw [hid]
      calc ‖(scte_mollProf σ n Dt' x - Dt' x) -
              ((2 * ε : ℝ) : ℂ) • ((x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) -
              (ε : ℂ) • ((x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) -
              (ε : ℂ) • (B_n n x - t x)‖
          ≤ ‖(scte_mollProf σ n Dt' x - Dt' x) -
              ((2 * ε : ℝ) : ℂ) • ((x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) -
              (ε : ℂ) • ((x.2.2 : ℂ) • (classEta (B_n n) x - Et' x))‖ +
            ‖(ε : ℂ) • (B_n n x - t x)‖ := norm_sub_le _ _
        _ ≤ ‖(scte_mollProf σ n Dt' x - Dt' x) -
              ((2 * ε : ℝ) : ℂ) • ((x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x)‖ +
            ‖(ε : ℂ) • ((x.2.2 : ℂ) • (classEta (B_n n) x - Et' x))‖ +
            ‖(ε : ℂ) • (B_n n x - t x)‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ ‖scte_mollProf σ n Dt' x - Dt' x‖ +
            ‖((2 * ε : ℝ) : ℂ) • ((x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x)‖ +
            ‖(ε : ℂ) • ((x.2.2 : ℂ) • (classEta (B_n n) x - Et' x))‖ +
            ‖(ε : ℂ) • (B_n n x - t x)‖ :=
          add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
        _ = ‖scte_mollProf σ n Dt' x - Dt' x‖ +
            (2 * ε) * ‖(x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x‖ +
            ε * ‖(x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)‖ +
            ε * ‖B_n n x - t x‖ := by
          simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε0.le,
            Real.norm_of_nonneg (by positivity : 0 ≤ 2 * ε)]
    have hm1 : AEStronglyMeasurable (fun x => scte_mollProf σ n Dt' x - Dt' x) (hMeas c 2) :=
      (scte_nice_inHr hc ((scte_mollProf_nice_tendsto hc hσ hσH₁ hDt'_in hDt'_supp).1 n)).meas.sub
        hDt'_in.meas
    have hm2 : AEStronglyMeasurable
        (fun x => (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) (hMeas c 2) :=
      (scte_nice_inHr hc (scte_nice_mulS (scte_nice_fderiv_dir 0 (ht_nice n)))).meas.sub
        hSt'_in.meas
    have hm3 : AEStronglyMeasurable
        (fun x => (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) (hMeas c 2) :=
      (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_snd)).aestronglyMeasurable.smul
        ((scte_nice_inHr hc ((lapNiceClass_proof c 0 _ (ht_nice n)).2)).meas.sub hEt'_in.meas)
    have hm4 : AEStronglyMeasurable (fun x => B_n n x - t x) (hMeas c 2) :=
      (scte_nice_inHr hc (ht_nice n)).meas.sub ht.meas
    calc hNorm c 2 (fun x => classQ ε (B_n n) x - qepsOf ε t St' Dt' Et' x)
        ≤ eLpNorm (fun x => ‖scte_mollProf σ n Dt' x - Dt' x‖ +
            (2 * ε) * ‖(x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x‖ +
            ε * ‖(x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)‖ +
            ε * ‖B_n n x - t x‖) (ENNReal.ofReal 2) (hMeas c 2) := eLpNorm_mono_real hpt
      _ ≤ eLpNorm (fun x => ‖scte_mollProf σ n Dt' x - Dt' x‖ +
            (2 * ε) * ‖(x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x‖ +
            ε * ‖(x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)‖) (ENNReal.ofReal 2) (hMeas c 2) +
          eLpNorm (fun x => ε * ‖B_n n x - t x‖) (ENNReal.ofReal 2) (hMeas c 2) :=
        eLpNorm_add_le
          ((hm1.norm.add (hm2.norm.const_smul (2 * ε))).add (hm3.norm.const_smul ε))
          (hm4.norm.const_smul ε) hp1
      _ ≤ eLpNorm (fun x => ‖scte_mollProf σ n Dt' x - Dt' x‖ +
            (2 * ε) * ‖(x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x‖)
            (ENNReal.ofReal 2) (hMeas c 2) +
          eLpNorm (fun x => ε * ‖(x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)‖)
            (ENNReal.ofReal 2) (hMeas c 2) +
          eLpNorm (fun x => ε * ‖B_n n x - t x‖) (ENNReal.ofReal 2) (hMeas c 2) :=
        add_le_add (eLpNorm_add_le (hm1.norm.add (hm2.norm.const_smul (2 * ε)))
          (hm3.norm.const_smul ε) hp1) le_rfl
      _ ≤ hNorm c 2 (fun x => scte_mollProf σ n Dt' x - Dt' x) +
          ENNReal.ofReal (2 * ε) *
            hNorm c 2 (fun x => (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) +
          ENNReal.ofReal ε *
            hNorm c 2 (fun x => (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) +
          ENNReal.ofReal ε * hNorm c 2 (fun x => B_n n x - t x) := by
        have c2 : eLpNorm ((2 * ε) • fun x => ‖(x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x‖)
            (ENNReal.ofReal 2) (hMeas c 2) =
            ENNReal.ofReal (2 * ε) *
              hNorm c 2 (fun x => (x.1 : ℂ) • fderiv ℝ (B_n n) x (cdir 0) - St' x) := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity : 0 ≤ 2 * ε), eLpNorm_norm]
          rfl
        have c3 : eLpNorm (ε • fun x => ‖(x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)‖)
            (ENNReal.ofReal 2) (hMeas c 2) =
            ENNReal.ofReal ε *
              hNorm c 2 (fun x => (x.2.2 : ℂ) • (classEta (B_n n) x - Et' x)) := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hε0.le, eLpNorm_norm]; rfl
        have c4 : eLpNorm (ε • fun x => ‖B_n n x - t x‖) (ENNReal.ofReal 2) (hMeas c 2) =
            ENNReal.ofReal ε * hNorm c 2 (fun x => B_n n x - t x) := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hε0.le, eLpNorm_norm]; rfl
        have h12 := eLpNorm_add_le hm1.norm (hm2.norm.const_smul (2 * ε)) hp1
        rw [eLpNorm_norm] at h12
        exact add_le_add (add_le_add (h12.trans (by rw [c2]; rfl)) (by exact c3.le))
          (by exact c4.le)
  have hQt_ae : Qt' =ᵐ[hMeas c 2] qepsOf ε t St' Dt' Et' :=
    hasWeakVec_unique_ae hc hQt' (hasWeakVec_qepsOf ε hSt' hDt' hEt')
  have hsqQ_lim : Tendsto (fun n => hNorm c 2 (fun x =>
      sqrtS (classQ ε (B_n n)) x - sqrtS Qt' x)) atTop (𝓝 0) := by
    have hcongr : ∀ n : ℕ,
        hNorm c 2 (fun x => sqrtS (classQ ε (B_n n)) x - sqrtS Qt' x) =
          hNorm c 2 (sqrtS (fun x => classQ ε (B_n n) x - qepsOf ε t St' Dt' Et' x)) := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [sqrtS_congr_ae hQt_ae] with x hx
      simp [sqrtS, smul_sub] at hx ⊢
      rw [hx]
    simp_rw [hcongr]
    refine tendsto_of_le_const (Real.sqrt a₁) (fun n => ?_) hQ_raw_lim
    refine (scte_hNorm_mul_box_le ha₀ ha₁ hM fun x hx => ?_).1
    have hQ0 : classQ ε (B_n n) x = 0 := by
      dsimp only [B_n]
      unfold classQ
      rw [Fin.sum_univ_three, (hfd_eq n x).1, (hfd_eq n x).2.1, (hfd_eq n x).2.2,
        hUs_van n x hx, hDt_van n x hx, hEt_van n x hx, ht_van n x hx]
      simp
    have hq0 : qepsOf ε t St' Dt' Et' x = 0 := by
      rw [qepsOf_eq_sub, widen_supp hDt'_supp x hx, widen_supp hSt'_supp x hx,
        widen_supp hEt'_supp x hx, widen_supp ht_supp x hx]
      simp
    simp [hQ0, hq0]
  exact ⟨ht_nice, ht_lim, hsB_lim, hsqD_lim, hsqE_lim, hsqQ_lim⟩

/-! ## Section 6: Subtracted tested equation, limit `n → ∞`, radial hoop bound, and assembly -/

private lemma scte_exists_inHr_derivs_of_isResponse {Γ ν c ε : ℝ} {μ : ℂ}
    (hΓ1 : 1 ≤ Γ) (hμΓ : ‖μ‖ ≤ Γ) (hgap : Γ⁻¹ ≤ μ.re + 1 / 4)
    (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (hε1 : ε ≤ 1) (hP : 2 * ε * c ≤ 1)
    {F bε : CProf} (hF : InHr c 2 F) (hbε_resp : IsResponse ν c ε μ 2 F bε) :
    ∃ Sbε' Qbε' Ebε' : CProf,
      InHr c 2 Sbε' ∧ InHr c 2 (sqrtS Qbε') ∧ InHr c 2 (sqrtS Ebε') ∧
      HasWeakVec vS dZero bε Sbε' ∧
      HasWeakVec (vQ ε) (dQ ε) bε Qbε' ∧
      HasWeakVec vEta dZero bε Ebε' := by
  have hP0 : 0 < 2 * ε * c := by positivity
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have hμ : 0 < μ.re + (3 / (2 : ℝ) - 1) / 2 := by
    have : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
    rw [this]
    exact lt_of_lt_of_le (inv_pos.mpr hΓ0) hgap
  obtain ⟨b', hbb'p, -, hb'H, hNN⟩ := profileRegularize_proof c ε 2 bε hc hε two_pos hbε_resp.mem_w
  have hb'R : IsFreeResponse ν μ 2 (2 * ε * c) (NvC ε⁻¹ F) (NvC ε⁻¹ b') :=
    freeResponseCongr_proof ν μ 2 _ _ _ _ _ hP0 Filter.EventuallyEq.rfl hNN.symm hbε_resp
  have hfY := nvCInYr_proof c ε 2 F hc hε two_pos hF
  obtain ⟨_, _, hC₁⟩ :=
    field_graph_bound lerayPairSol solSeparation (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (2 : ℝ) < 3)
  obtain ⟨d, hdY, hdp⟩ := hb'R.drift
  obtain ⟨g, hgY, hgp, -⟩ := hC₁ (2 * ε * c) ν μ _ _ hP0 hP hν hμ hfY hb'R
  obtain ⟨Sb', hSb, hSbH, -⟩ := driftRecovery_proof c ε 2 b' d hc hε one_lt_two hb'H hdY hdp
  obtain ⟨Qb', Eb', hQ, hE, hQp, hQm, hEp, hEm⟩ :=
    gradWeak_proof c ε 2 b' g hc hε one_lt_two (by norm_num) hb'H hgY hgp
  have hsym : ∀ᵐ x ∂posReg, bε x = b' x := hbb'p.mono fun x hx => hx.symm
  have hS' := weakVecCongr_proof vS dZero b' bε Sb' hsym hSb
  have hQ' := weakVecCongr_proof _ _ b' bε Qb' hsym hQ
  have hE' := weakVecCongr_proof _ _ b' bε Eb' hsym hE
  obtain ⟨Cp, -, hphys⟩ := phys_graph_poly_two_given
  have hbd := hphys Γ ν c ε μ hΓ1 hμΓ hgap hν hc hε hε1 hP F bε Sb' Qb' Eb' hF hbε_resp hS' hQ' hE'
  have hRHS_fin : ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c 2 F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  have hprod_fin :
      ENNReal.ofReal (Real.sqrt ν) * (hNorm c 2 (sqrtS Qb') + hNorm c 2 (sqrtS Eb')) < ⊤ :=
    lt_of_le_of_lt (le_add_self.trans hbd) hRHS_fin
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQE_fin : hNorm c 2 (sqrtS Qb') + hNorm c 2 (sqrtS Eb') < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right hprod_fin.ne hsq0
  exact ⟨Sb', Qb', Eb', hSbH, ⟨hQp, hQm, (ENNReal.add_lt_top.1 hQE_fin).1⟩,
    ⟨hEp, hEm, (ENNReal.add_lt_top.1 hQE_fin).2⟩, hS', hQ', hE'⟩

private lemma scte_inHr_add {c : ℝ} {f g : CProf} (hf : InHr c 2 f) (hg : InHr c 2 g) :
    InHr c 2 (fun x => f x + g x) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine ⟨?_, hf.meas.add hg.meas, ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x hxf hxg
    rw [hxf, hxg]
  · exact lt_of_le_of_lt (eLpNorm_add_le hf.meas hg.meas hp1)
      (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

private lemma scte_inHr_const_smul {c : ℝ} (a : ℂ) {f : CProf} (hf : InHr c 2 f) :
    InHr c 2 (fun x => a • f x) := by
  refine ⟨?_, hf.meas.const_smul a, ?_⟩
  · filter_upwards [hf.periodic] with x hx
    rw [hx]
  · unfold hNorm
    rw [show (fun x => a • f x) = a • f from rfl, eLpNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hf.finite

private lemma scte_qPeriodic_of_sqrtS {c : ℝ} {u : CProf} (hu : QPeriodic c (sqrtS u)) :
    QPeriodic c u := by
  refine QPerHalf.of_ae_imp ?_
  filter_upwards [QPerHalf.ae_imp hu] with x hx hpos
  have hsq : Real.sqrt x.1 ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hsq_c : ((Real.sqrt x.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsq
  have heq := hx hpos
  simp only [sqrtS, show (qShift c x).1 = x.1 from rfl] at heq
  exact smul_right_injective CMerid hsq_c heq

private lemma scte_inHr_of_sqrtS_box {c a₀ a₁ M : ℝ} (ha₀ : 0 < a₀) {G : CProf}
    (hG_per : QPeriodic c G) (hG_sq : InHr c 2 (sqrtS G))
    (hG_supp : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → G x = 0) :
    InHr c 2 G := by
  have hmul_m : Measurable (fun x : Coord =>
      if x.1 < a₀ then (0 : ℂ) else (((Real.sqrt x.1)⁻¹ : ℝ) : ℂ)) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_const
      (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst).inv)
  have hmeas : AEStronglyMeasurable G (hMeas c 2) := by
    refine (hmul_m.aestronglyMeasurable.smul hG_sq.meas).congr (ae_of_all _ fun x => ?_)
    change (if x.1 < a₀ then (0 : ℂ) else (((Real.sqrt x.1)⁻¹ : ℝ) : ℂ)) • sqrtS G x = G x
    by_cases hx1 : x.1 < a₀
    · simp only [hx1, ↓reduceIte, zero_smul, hG_supp x (Or.inl hx1)]
    · have hpos : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 (lt_of_lt_of_le ha₀ (not_lt.mp hx1))
      have hc_inv : (((Real.sqrt x.1)⁻¹ : ℝ) : ℂ) * (Real.sqrt x.1 : ℂ) = 1 := by
        push_cast; exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne')
      simp only [hx1, ↓reduceIte, sqrtS, smul_smul, hc_inv, one_smul]
  have hfin : hNorm c 2 G < ⊤ := by
    have hsq_pos : 0 < Real.sqrt a₀ := Real.sqrt_pos.2 ha₀
    have hle : hNorm c 2 G ≤
        eLpNorm ((((Real.sqrt a₀)⁻¹ : ℝ) : ℂ) • sqrtS G) (ENNReal.ofReal 2) (hMeas c 2) := by
      refine eLpNorm_mono fun x => ?_
      simp only [Pi.smul_apply, Complex.ofReal_inv, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hsq_pos.le]
      by_cases hx1 : x.1 < a₀
      · rw [hG_supp x (Or.inl hx1), norm_zero]
        exact mul_nonneg (inv_nonneg.2 hsq_pos.le) (norm_nonneg _)
      · have hx_ge : a₀ ≤ x.1 := not_lt.mp hx1
        have hrx_pos : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 (lt_of_lt_of_le ha₀ hx_ge)
        rw [norm_sqrtS]
        calc ‖G x‖ = (Real.sqrt x.1)⁻¹ * (Real.sqrt x.1 * ‖G x‖) := by
              rw [← mul_assoc, inv_mul_cancel₀ hrx_pos.ne', one_mul]
          _ ≤ (Real.sqrt a₀)⁻¹ * (Real.sqrt x.1 * ‖G x‖) :=
              mul_le_mul_of_nonneg_right
                (inv_anti₀ hsq_pos (Real.sqrt_le_sqrt hx_ge))
                (mul_nonneg hrx_pos.le (norm_nonneg _))
    rw [eLpNorm_const_smul] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top enorm_lt_top hG_sq.finite)
  exact ⟨hG_per, hmeas, hfin⟩

private lemma scte_inHr_sqrtS_of_box {c a₀ a₁ M : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hM : 0 ≤ M)
    {G : CProf} (hG : InHr c 2 G)
    (hG_supp : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → G x = 0) :
    InHr c 2 (sqrtS G) :=
  ⟨qPeriodic_sqrtS hG.periodic, aestronglyMeasurable_sqrtS_of hG.meas,
    lt_of_le_of_lt (scte_hNorm_mul_box_le ha₀ ha₁ hM hG_supp).1
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.finite)⟩

private lemma scte_inHr_smul_cutoff {c a₀ a₁ M : ℝ} {φ : Coord → ℝ}
    (hφ_s : ContDiff ℝ ∞ φ) (hφ_p : ∀ x, φ (qShift c x) = φ x)
    (hφ_v : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → φ x = 0)
    {u : CProf} (hu : InHr c 2 u) :
    InHr c 2 (fun x => (φ x : ℂ) • u x) ∧
      ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → (φ x : ℂ) • u x = 0 := by
  have hvan : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → (φ x : ℂ) • u x = 0 := by
    intro x hx; rw [hφ_v x hx, Complex.ofReal_zero, zero_smul]
  set K : Set Coord := Icc a₀ a₁ ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M) M)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    (s := K) hφ_s.continuous.continuousOn
  have hq_ae : ∀ᵐ x ∂(hMeas c 2), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
    rw [ae_iff]
    unfold hMeas Axi.ageμ
    have heq : {x : Coord | ¬ x.2.1 ∈ Ico (-c / 2) (c / 2)} =
        (univ : Set ℝ) ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) := by
      ext x; simp
    rw [heq, Measure.prod_prod]
    have h0 : Cyl.avgμ c ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Cyl.avgμ, Measure.smul_apply, Cyl.cellμ, Measure.restrict_apply
        (measurableSet_Ico.compl.prod MeasurableSet.univ)]
      have hInt : (Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ) ∩ Cyl.cell c = ∅ := by
        ext x; simp [Cyl.cell]
      simp [hInt]
    simp [h0]
  have hae_bd : ∀ᵐ x ∂(hMeas c 2),
      ‖(φ x : ℂ) • u x‖ ≤ ‖((max C 0 : ℝ) : ℂ) • u x‖ := by
    filter_upwards [hq_ae] with x hxq
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_of_nonneg (le_max_right C 0)]
    by_cases hx : x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|
    · rw [hφ_v x hx, abs_zero, zero_mul]
      exact mul_nonneg (le_max_right C 0) (norm_nonneg _)
    · push Not at hx
      have hxK : x ∈ K := ⟨⟨hx.1, hx.2.1⟩, ⟨Ico_subset_Icc_self hxq, abs_le.mp hx.2.2⟩⟩
      have hCx : |φ x| ≤ max C 0 :=
        le_max_of_le_left (by simpa [Real.norm_eq_abs] using hC x hxK)
      exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)
  have hper : QPeriodic c (fun x => (φ x : ℂ) • u x) := by
    filter_upwards [hu.periodic] with x hx
    rw [hφ_p x, hx]
  have hmeas : AEStronglyMeasurable (fun x => (φ x : ℂ) • u x) (hMeas c 2) :=
    (Complex.continuous_ofReal.comp hφ_s.continuous).aestronglyMeasurable.smul hu.meas
  have hfin : hNorm c 2 (fun x => (φ x : ℂ) • u x) < ⊤ := by
    have hle : hNorm c 2 (fun x => (φ x : ℂ) • u x) ≤
        eLpNorm (((max C 0 : ℝ) : ℂ) • u) (ENNReal.ofReal 2) (hMeas c 2) :=
      eLpNorm_mono_ae hae_bd
    rw [eLpNorm_const_smul] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top enorm_lt_top hu.finite)
  exact ⟨⟨hper, hmeas, hfin⟩, hvan⟩

private lemma scte_inHr_smul_cutoff_of_sqrtS {c a₀ a₁ M : ℝ} (ha₀ : 0 < a₀) {φ : Coord → ℝ}
    (hφ_s : ContDiff ℝ ∞ φ) (hφ_p : ∀ x, φ (qShift c x) = φ x)
    (hφ_v : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → φ x = 0)
    {u : CProf} (hu : InHr c 2 (sqrtS u)) :
    InHr c 2 (fun x => (φ x : ℂ) • u x) ∧
      ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → (φ x : ℂ) • u x = 0 := by
  have hu_per : QPeriodic c u := scte_qPeriodic_of_sqrtS hu.periodic
  obtain ⟨hsq_in, -⟩ := scte_inHr_smul_cutoff hφ_s hφ_p hφ_v hu
  have hsq_eq : sqrtS (fun x => (φ x : ℂ) • u x) = fun x => (φ x : ℂ) • sqrtS u x :=
    funext fun x => smul_comm (Real.sqrt x.1 : ℂ) (φ x : ℂ) (u x)
  have hper : QPeriodic c (fun x => (φ x : ℂ) • u x) := by
    filter_upwards [hu_per] with x hx
    rw [hφ_p x, hx]
  have hvan' : ∀ x : Coord, (x.1 < a₀ ∨ a₁ < x.1 ∨ M < |x.2.2|) → (φ x : ℂ) • u x = 0 := by
    intro x hx; rw [hφ_v x hx, Complex.ofReal_zero, zero_smul]
  refine ⟨scte_inHr_of_sqrtS_box ha₀ hper ?_ hvan', hvan'⟩
  rwa [hsq_eq]

private lemma scte_hoop_discrepancy_bound {c ν H₁ ε : ℝ} (hν : 0 < ν) (hH₁ : 0 < H₁)
    (hε0 : 0 < ε) {bε b0 : CProf} (hbε_in : InHr c 2 bε) (hb0_in : InHr c 2 b0)
    {χ : Coord → ℝ} (hχ_s : ContDiff ℝ ∞ χ)
    (hχ_le1 : ∀ x : Coord, |χ x| ≤ 1)
    (hχ_v : ∀ x : Coord, (x.1 < 0 ∨ 2 * H₁ < x.1) → χ x = 0) :
    let w := bε - b0;
    let t : CProf := fun x => ((χ x ^ 2 : ℝ) : ℂ) • w x;
    (-(ν * ε ^ 2)) *
        (∫ x, (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)).re ≤
      (1 / 2) * ν * H₁ * ε ^ 2 * (hNorm c 2 b0).toReal ^ 2 := by
  intro w t
  have hw_in : InHr c 2 w := flatCls_inHr_sub hbε_in hb0_in
  have hts_meas : AEStronglyMeasurable (fun x : Coord => (x.1 : ℂ) • t x) (hMeas c 2) := by
    have hm : Continuous (fun x : Coord => ((x.1 * χ x ^ 2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_fst.mul (hχ_s.continuous.pow 2))
    refine (hm.aestronglyMeasurable.smul hw_in.meas).congr (ae_of_all _ fun x => ?_)
    dsimp [t]; rw [smul_smul]
  have hts_fin : hNorm c 2 (fun x : Coord => (x.1 : ℂ) • t x) < ⊤ := by
    have hle : hNorm c 2 (fun x : Coord => (x.1 : ℂ) • t x) ≤
        eLpNorm (((2 * H₁ : ℝ) : ℂ) • w) (ENNReal.ofReal 2) (hMeas c 2) := by
      refine eLpNorm_mono fun x => ?_
      change ‖(x.1 : ℂ) • ((χ x ^ 2 : ℝ) : ℂ) • w x‖ ≤ ‖((2 * H₁ : ℝ) : ℂ) • w x‖
      rw [norm_smul, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _),
        Real.norm_of_nonneg (by positivity : 0 ≤ 2 * H₁), ← mul_assoc]
      by_cases hx : x.1 < 0 ∨ 2 * H₁ < x.1
      · rw [hχ_v x hx]; simp; exact mul_nonneg (by positivity) (norm_nonneg _)
      · push Not at hx
        have hχ2 : χ x ^ 2 ≤ 1 := by
          calc χ x ^ 2 = |χ x| ^ 2 := (sq_abs _).symm
            _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hχ_le1 x) 2
            _ = 1 := one_pow 2
        have hsχ : |x.1| * χ x ^ 2 ≤ 2 * H₁ := by
          rw [abs_of_nonneg hx.1]
          calc x.1 * χ x ^ 2 ≤ x.1 * 1 := mul_le_mul_of_nonneg_left hχ2 hx.1
            _ ≤ 2 * H₁ := by linarith [hx.2]
        exact mul_le_mul_of_nonneg_right hsχ (norm_nonneg _)
    rw [eLpNorm_const_smul] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top enorm_lt_top hw_in.finite)
  have hint_hoop :
      Integrable (fun x : Coord => (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)))
        (hMeas c 2) := by
    obtain ⟨hi, -⟩ := scte_pair_comp_int_bound hbε_in.meas hbε_in.finite hts_meas hts_fin 0
    refine hi.congr (ae_of_all _ fun x => ?_)
    simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    ring
  have hb0_fin2 : eLpNorm b0 2 (hMeas c 2) < ⊤ := by
    have h : eLpNorm b0 (ENNReal.ofReal 2) (hMeas c 2) < ⊤ := hb0_in.finite
    rwa [scte_ofReal_two] at h
  have hmem_b0 : MemLp b0 2 (hMeas c 2) := ⟨hb0_in.meas, hb0_fin2⟩
  have hint_b0_sq : Integrable (fun x : Coord => ‖b0 x‖ ^ 2) (hMeas c 2) :=
    hmem_b0.integrable_norm_pow (by norm_num)
  have hb0_sq_eq : ∫ x, ‖b0 x‖ ^ 2 ∂(hMeas c 2) = (hNorm c 2 b0).toReal ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg ‖b0 x‖)
      (hb0_in.meas.norm.pow 2)]
    unfold hNorm
    rw [scte_ofReal_two, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, one_div]
    have hcongr : (fun x => ENNReal.ofReal (‖b0 x‖ ^ 2)) = fun x => ‖b0 x‖ₑ ^ (2 : ℝ) := by
      funext x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
      norm_num
    rw [hcongr, ← ENNReal.toReal_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  have hre_int :
      (∫ x, (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)).re =
        ∫ x, ((x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0))).re ∂(hMeas c 2) := by
    have h := integral_re hint_hoop
    simpa only [RCLike.re_to_complex] using h.symm
  have hpt_lower : ∀ᵐ x ∂(hMeas c 2),
      -(1 / 2 * H₁) * ‖b0 x‖ ^ 2 ≤
        ((x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0))).re := by
    filter_upwards [scte_hMeas_pos c 2] with x hxpos
    by_cases hx2 : 2 * H₁ < x.1
    · have h0 : χ x = 0 := hχ_v x (Or.inr hx2)
      dsimp [t]; rw [h0]; simp
      exact mul_nonneg (by positivity) (sq_nonneg _)
    · have hx_le : x.1 ≤ 2 * H₁ := not_lt.mp hx2
      have hχ2 : χ x ^ 2 ≤ 1 := by
        calc χ x ^ 2 = |χ x| ^ 2 := (sq_abs _).symm
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hχ_le1 x) 2
          _ = 1 := one_pow 2
      have hsχ_nonneg : 0 ≤ x.1 * χ x ^ 2 := mul_nonneg hxpos.le (sq_nonneg _)
      have hsχ_le : x.1 * χ x ^ 2 ≤ 2 * H₁ := by
        calc x.1 * χ x ^ 2 ≤ x.1 * 1 := mul_le_mul_of_nonneg_left hχ2 hxpos.le
          _ ≤ 2 * H₁ := by linarith
      have hbε_eq : bε x 0 = w x 0 + b0 x 0 := by dsimp [w]; simp
      have hre_pt : ((x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0))).re =
          (x.1 * χ x ^ 2) * (‖w x 0‖ ^ 2 + (b0 x 0 * (starRingEnd ℂ) (w x 0)).re) := by
        dsimp [t]
        rw [hbε_eq]
        simp only [map_mul, Complex.conj_ofReal]
        have hwc : w x 0 * (starRingEnd ℂ) (w x 0) = ((‖w x 0‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have halg : (x.1 : ℂ) * ((w x 0 + b0 x 0) * (((χ x ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (w x 0))) =
            ((x.1 * χ x ^ 2 : ℝ) : ℂ) *
              (((‖w x 0‖ ^ 2 : ℝ) : ℂ) + b0 x 0 * (starRingEnd ℂ) (w x 0)) := by
          calc (x.1 : ℂ) * ((w x 0 + b0 x 0) * (((χ x ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (w x 0)))
              = ((x.1 : ℂ) * ((χ x ^ 2 : ℝ) : ℂ)) *
                  (w x 0 * (starRingEnd ℂ) (w x 0) + b0 x 0 * (starRingEnd ℂ) (w x 0)) := by ring
            _ = ((x.1 * χ x ^ 2 : ℝ) : ℂ) *
                  (((‖w x 0‖ ^ 2 : ℝ) : ℂ) + b0 x 0 * (starRingEnd ℂ) (w x 0)) := by
                rw [hwc, Complex.ofReal_mul]
        rw [halg, re_ofReal_mul, Complex.add_re, Complex.ofReal_re]
      have hre_cross : -(‖b0 x 0‖ * ‖w x 0‖) ≤ (b0 x 0 * (starRingEnd ℂ) (w x 0)).re := by
        have h1 : |(b0 x 0 * (starRingEnd ℂ) (w x 0)).re| ≤ ‖b0 x 0‖ * ‖w x 0‖ := by
          calc |(b0 x 0 * (starRingEnd ℂ) (w x 0)).re|
              ≤ ‖b0 x 0 * (starRingEnd ℂ) (w x 0)‖ := Complex.abs_re_le_norm _
            _ = ‖b0 x 0‖ * ‖w x 0‖ := by rw [norm_mul, RCLike.norm_conj]
        exact (abs_le.mp h1).1
      have hyoung : -(1 / 4) * ‖b0 x 0‖ ^ 2 ≤
          ‖w x 0‖ ^ 2 + (b0 x 0 * (starRingEnd ℂ) (w x 0)).re := by
        have hsq0 : 0 ≤ (‖w x 0‖ - (1 / 2) * ‖b0 x 0‖) ^ 2 := sq_nonneg _
        have hexp : (‖w x 0‖ - (1 / 2) * ‖b0 x 0‖) ^ 2 =
            ‖w x 0‖ ^ 2 - (‖b0 x 0‖ * ‖w x 0‖) + (1 / 4) * ‖b0 x 0‖ ^ 2 := by ring
        linarith only [hsq0, hexp, hre_cross]
      have hb0_comp : ‖b0 x 0‖ ^ 2 ≤ ‖b0 x‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (b0 x) 0) 2
      rw [hre_pt]
      calc -(1 / 2 * H₁) * ‖b0 x‖ ^ 2
          ≤ -(1 / 2 * H₁) * ‖b0 x 0‖ ^ 2 :=
            mul_le_mul_of_nonpos_left hb0_comp (neg_nonpos.mpr (by positivity))
        _ = (2 * H₁) * (-(1 / 4) * ‖b0 x 0‖ ^ 2) := by ring
        _ ≤ (x.1 * χ x ^ 2) * (-(1 / 4) * ‖b0 x 0‖ ^ 2) := by
          have hneg : -(1 / 4) * ‖b0 x 0‖ ^ 2 ≤ 0 := by
            have h0 : 0 ≤ ‖b0 x 0‖ ^ 2 := sq_nonneg _
            linarith only [h0]
          exact mul_le_mul_of_nonpos_right hsχ_le hneg
        _ ≤ (x.1 * χ x ^ 2) * (‖w x 0‖ ^ 2 + (b0 x 0 * (starRingEnd ℂ) (w x 0)).re) :=
          mul_le_mul_of_nonneg_left hyoung hsχ_nonneg
  have hint_re : Integrable
      (fun x : Coord => ((x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0))).re) (hMeas c 2) := by
    simpa only [RCLike.re_to_complex] using hint_hoop.re
  have hint_low : ∫ x, (-(1 / 2 * H₁) * ‖b0 x‖ ^ 2) ∂(hMeas c 2) ≤
      ∫ x, ((x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0))).re ∂(hMeas c 2) :=
    integral_mono_ae (hint_b0_sq.const_mul _) hint_re hpt_lower
  rw [integral_const_mul, hb0_sq_eq] at hint_low
  rw [hre_int]
  calc -(ν * ε ^ 2) * ∫ x, ((x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0))).re ∂(hMeas c 2)
      ≤ -(ν * ε ^ 2) * (-(1 / 2 * H₁) * (hNorm c 2 b0).toReal ^ 2) :=
        mul_le_mul_of_nonpos_left hint_low (neg_nonpos.mpr (by positivity))
    _ = (1 / 2) * ν * H₁ * ε ^ 2 * (hNorm c 2 b0).toReal ^ 2 := by ring

private lemma scte_hNorm_toReal_tendsto {c : ℝ} {t : CProf} {B_n : ℕ → CProf}
    (ht : InHr c 2 t) (hBn : ∀ n, InHr c 2 (B_n n))
    (hlim : Tendsto (fun n => hNorm c 2 (fun x => B_n n x - t x)) atTop (𝓝 0)) :
    Tendsto (fun n => (hNorm c 2 (B_n n)).toReal) atTop (𝓝 (hNorm c 2 t).toReal) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hdiff_tr : Tendsto (fun n => (hNorm c 2 (fun x => B_n n x - t x)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have hbd : ∀ n : ℕ, ‖(hNorm c 2 (B_n n)).toReal - (hNorm c 2 t).toReal‖ ≤
      (hNorm c 2 (fun x => B_n n x - t x)).toReal := by
    intro n
    have hdiff_fin : hNorm c 2 (fun x => B_n n x - t x) < ⊤ :=
      lt_of_le_of_lt (eLpNorm_sub_le (hBn n).meas ht.meas hp1)
        (ENNReal.add_lt_top.2 ⟨(hBn n).finite, ht.finite⟩)
    have h1 : hNorm c 2 (B_n n) ≤ hNorm c 2 (fun x => B_n n x - t x) + hNorm c 2 t := by
      unfold hNorm
      have heq : B_n n = (B_n n - t) + t := (sub_add_cancel _ _).symm
      conv_lhs => rw [heq]
      exact eLpNorm_add_le ((hBn n).meas.sub ht.meas) ht.meas hp1
    have h2 : hNorm c 2 t ≤ hNorm c 2 (fun x => B_n n x - t x) + hNorm c 2 (B_n n) := by
      unfold hNorm
      have heq : t = (t - B_n n) + B_n n := (sub_add_cancel _ _).symm
      have hneg : eLpNorm (t - B_n n) (ENNReal.ofReal 2) (hMeas c 2) =
          eLpNorm (B_n n - t) (ENNReal.ofReal 2) (hMeas c 2) :=
        eLpNorm_congr_norm_ae (ae_of_all _ fun x => norm_sub_rev _ _)
      conv_lhs => rw [heq]
      exact (eLpNorm_add_le (ht.meas.sub (hBn n).meas) (hBn n).meas hp1).trans (by rw [hneg]; rfl)
    have tr1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdiff_fin.ne, ht.finite.ne⟩) h1
    have tr2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdiff_fin.ne, (hBn n).finite.ne⟩) h2
    rw [ENNReal.toReal_add hdiff_fin.ne ht.finite.ne] at tr1
    rw [ENNReal.toReal_add hdiff_fin.ne (hBn n).finite.ne] at tr2
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  simpa using (squeeze_zero_norm hbd hdiff_tr).add_const (hNorm c 2 t).toReal

private lemma scte_cutoff_test_props_aux {c σ H₁ L₁ ε : ℝ}
    (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (hL₁0 : 0 ≤ L₁)
    {bε b0 Sbε' Qbε' Ebε' Sb0' Qb0' Eb0' : CProf}
    (hbε_in : InHr c 2 bε) (hb0_in : InHr c 2 b0)
    (hSbε'_in : InHr c 2 Sbε') (hQbε'_in : InHr c 2 (sqrtS Qbε')) (hEbε'_in : InHr c 2 (sqrtS Ebε'))
    (hSb0'_in : InHr c 2 Sb0') (hQb0'_in : InHr c 2 (sqrtS Qb0')) (hEb0'_in : InHr c 2 (sqrtS Eb0'))
    (hSε' : HasWeakVec vS dZero bε Sbε') (hQε' : HasWeakVec (vQ ε) (dQ ε) bε Qbε')
    (hEε' : HasWeakVec vEta dZero bε Ebε')
    (hS0' : HasWeakVec vS dZero b0 Sb0') (hQ0' : HasWeakVec vQ0 dZero b0 Qb0')
    (hE0' : HasWeakVec vEta dZero b0 Eb0') :
    let ψ : Coord → ℝ := fun x => boxCutoff σ H₁ L₁ x ^ 2
    let w := bε - b0
    let Sw' := Sbε' - Sb0'
    let Dw' := dqOf ε bε Sbε' Qbε' Ebε' - Qb0'
    let Qv' := qepsOf ε b0 Sb0' Qb0' Eb0'
    let Qw' := Qbε' - Qv'
    let Ew' := Ebε' - Eb0'
    let t : CProf := fun x => (ψ x : ℂ) • w x
    let St' := weakSmul vS ψ w Sw'
    let Dt' := weakSmul vQ0 ψ w Dw'
    let Qt' := weakSmul (vQ ε) ψ w Qw'
    let Et' := weakSmul vEta ψ w Ew'
    let θ_enl := boxCutoff (σ / 2) (2 * H₁) (L₁ + 1)
    InHr c 2 t ∧ InHr c 2 St' ∧ InHr c 2 Dt' ∧ InHr c 2 Qt' ∧ InHr c 2 Et' ∧
      InHr c 2 (sqrtS Dt') ∧ InHr c 2 (sqrtS Qt') ∧ InHr c 2 (sqrtS Et') ∧
      InHr c 2 (fun x : Coord => (x.1 : ℂ) • t x) ∧
      InHr c 2 (sqrtS (fun x => (θ_enl x : ℂ) • Qv' x)) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → t z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → St' z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Dt' z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Qt' z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Et' z = 0) ∧
      HasWeakVec vS dZero w Sw' ∧ HasWeakVec vEta dZero w Ew' ∧
      HasWeakVec (vQ ε) (dQ ε) b0 Qv' ∧ HasWeakVec (vQ ε) (dQ ε) w Qw' ∧
      HasWeakVec vS dZero t St' ∧ HasWeakVec vQ0 dZero t Dt' ∧
      HasWeakVec (vQ ε) (dQ ε) t Qt' ∧ HasWeakVec vEta dZero t Et' := by
  intro ψ w Sw' Dw' Qv' Qw' Ew' t St' Dt' Qt' Et' θ_enl
  have hH₁0 : 0 < H₁ := lt_of_lt_of_le hσ hσH₁
  have hχ_s : ContDiff ℝ ∞ (boxCutoff σ H₁ L₁) := boxCutoff_contDiff σ H₁ L₁
  have hψ_s : ContDiff ℝ ∞ ψ := hχ_s.pow 2
  have hψ_p : ∀ x, ψ (qShift c x) = ψ x := fun x => by
    dsimp [ψ]; rw [boxCutoff_periodic c σ H₁ L₁ x]
  have hψ_v : ∀ x : Coord, (x.1 < σ / 2 ∨ 2 * H₁ < x.1 ∨ L₁ + 1 < |x.2.2|) → ψ x = 0 := by
    intro x hx; dsimp [ψ]; rw [boxCutoff_eq_zero_of_outside hσ hσH₁ hx, zero_pow two_ne_zero]
  have hηψ_s : ContDiff ℝ ∞ (fun x : Coord => x.2.2 * ψ x) :=
    (contDiff_snd.comp contDiff_snd).mul hψ_s
  have hηψ_p : ∀ x, (qShift c x).2.2 * ψ (qShift c x) = x.2.2 * ψ x := fun x => by
    rw [show (qShift c x).2.2 = x.2.2 from rfl, hψ_p x]
  have hηψ_v : ∀ x : Coord, (x.1 < σ / 2 ∨ 2 * H₁ < x.1 ∨ L₁ + 1 < |x.2.2|) →
      x.2.2 * ψ x = 0 := fun x hx => by rw [hψ_v x hx, mul_zero]
  have hvG_props : ∀ {v : Coord → Fin 3 → ℝ},
      (∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j)) →
      (∀ (x : Coord) (j : Fin 3), v (qShift c x) j = v x j) →
      ContDiff ℝ ∞ (vGrad v ψ) ∧
        (∀ x, vGrad v ψ (qShift c x) = vGrad v ψ x) ∧
        (∀ x : Coord, (x.1 < σ / 2 ∨ 2 * H₁ < x.1 ∨ L₁ + 1 < |x.2.2|) → vGrad v ψ x = 0) := by
    intro v hv hvp
    refine ⟨contDiff_vGrad hv hψ_s, fun x => ?_, fun x hx => ?_⟩
    · unfold vGrad
      rw [Fin.sum_univ_three, Fin.sum_univ_three, hvp x 0, hvp x 1, hvp x 2,
        coef_cpd_per hψ_p 0 x, coef_cpd_per hψ_p 1 x, coef_cpd_per hψ_p 2 x]
    · have hU := coef_isOpen (σ / 2) (2 * H₁) (L₁ + 1)
      unfold vGrad
      rw [Fin.sum_univ_three, coef_cpd_vanish hU hψ_v 0 x hx,
        coef_cpd_vanish hU hψ_v 1 x hx, coef_cpd_vanish hU hψ_v 2 x hx]
      ring
  obtain ⟨hvGS_s, hvGS_p, hvGS_v⟩ :=
    hvG_props contDiff_vS fun x j => by fin_cases j <;> rfl
  obtain ⟨hvGD_s, hvGD_p, hvGD_v⟩ :=
    hvG_props contDiff_vQ0 fun x j => by fin_cases j <;> rfl
  obtain ⟨hvGQ_s, hvGQ_p, hvGQ_v⟩ :=
    hvG_props (contDiff_vQ ε) fun x j => by fin_cases j <;> rfl
  obtain ⟨hvGE_s, hvGE_p, hvGE_v⟩ :=
    hvG_props contDiff_vEta fun x j => by fin_cases j <;> rfl
  have ha₀_box : 0 < σ / 2 := half_pos hσ
  have hw_in : InHr c 2 w := flatCls_inHr_sub hbε_in hb0_in
  have hSw'_in : InHr c 2 Sw' := flatCls_inHr_sub hSbε'_in hSb0'_in
  have hEw'_sq : InHr c 2 (sqrtS Ew') := by
    rw [flatCls_sqrtS_sub]; exact flatCls_inHr_sub hEbε'_in hEb0'_in
  obtain ⟨ht_in, ht_supp⟩ := scte_inHr_smul_cutoff hψ_s hψ_p hψ_v hw_in
  have hSt'_in : InHr c 2 St' :=
    scte_inHr_add (scte_inHr_smul_cutoff hψ_s hψ_p hψ_v hSw'_in).1
      (scte_inHr_smul_cutoff hvGS_s hvGS_p hvGS_v hw_in).1
  have hSt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → St' z = 0 := by
    intro z hz; dsimp [St', weakSmul]; rw [hψ_v z hz, hvGS_v z hz]; simp
  have hψQv'_in : InHr c 2 (fun x => (ψ x : ℂ) • Qv' x) := by
    have heq : (fun x : Coord => (ψ x : ℂ) • Qv' x) =
        fun x => (ψ x : ℂ) • Qb0' x -
          (ε : ℂ) • ((2 : ℂ) • ((ψ x : ℂ) • Sb0' x) +
            ((x.2.2 * ψ x : ℝ) : ℂ) • Eb0' x + (ψ x : ℂ) • b0 x) := by
      ext x i
      simp only [Qv', PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, qepsOf_apply,
        smul_eq_mul]
      push_cast
      ring
    rw [heq]
    have i1 := (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hψ_s hψ_p hψ_v hQb0'_in).1
    have i2 := scte_inHr_const_smul (2 : ℂ) (scte_inHr_smul_cutoff hψ_s hψ_p hψ_v hSb0'_in).1
    have i3 := (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hηψ_s hηψ_p hηψ_v hEb0'_in).1
    have i4 := (scte_inHr_smul_cutoff hψ_s hψ_p hψ_v hb0_in).1
    exact flatCls_inHr_sub i1 (scte_inHr_const_smul (ε : ℂ) (scte_inHr_add (scte_inHr_add i2 i3) i4))
  have hψDw'_in : InHr c 2 (fun x => (ψ x : ℂ) • Dw' x) := by
    have heq : (fun x : Coord => (ψ x : ℂ) • Dw' x) =
        fun x => ((ψ x : ℂ) • Qbε' x +
          (ε : ℂ) • ((2 : ℂ) • ((ψ x : ℂ) • Sbε' x) +
            ((x.2.2 * ψ x : ℝ) : ℂ) • Ebε' x + (ψ x : ℂ) • bε x)) -
          (ψ x : ℂ) • Qb0' x := by
      ext x i
      simp only [Dw', Pi.sub_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, dqOf_apply,
        smul_eq_mul]
      push_cast
      ring
    rw [heq]
    have i1 := (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hψ_s hψ_p hψ_v hQbε'_in).1
    have i2 := scte_inHr_const_smul (2 : ℂ) (scte_inHr_smul_cutoff hψ_s hψ_p hψ_v hSbε'_in).1
    have i3 := (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hηψ_s hηψ_p hηψ_v hEbε'_in).1
    have i4 := (scte_inHr_smul_cutoff hψ_s hψ_p hψ_v hbε_in).1
    have i5 := (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hψ_s hψ_p hψ_v hQb0'_in).1
    exact flatCls_inHr_sub
      (scte_inHr_add i1 (scte_inHr_const_smul (ε : ℂ) (scte_inHr_add (scte_inHr_add i2 i3) i4))) i5
  have hψQw'_in : InHr c 2 (fun x => (ψ x : ℂ) • Qw' x) := by
    have heq : (fun x : Coord => (ψ x : ℂ) • Qw' x) =
        (fun x => (ψ x : ℂ) • Qbε' x) - (fun x => (ψ x : ℂ) • Qv' x) := by
      funext x; dsimp [Qw']; exact smul_sub _ _ _
    rw [heq]
    exact flatCls_inHr_sub
      (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hψ_s hψ_p hψ_v hQbε'_in).1 hψQv'_in
  have hDt'_in : InHr c 2 Dt' :=
    scte_inHr_add hψDw'_in (scte_inHr_smul_cutoff hvGD_s hvGD_p hvGD_v hw_in).1
  have hQt'_in : InHr c 2 Qt' :=
    scte_inHr_add hψQw'_in (scte_inHr_smul_cutoff hvGQ_s hvGQ_p hvGQ_v hw_in).1
  have hEt'_in : InHr c 2 Et' :=
    scte_inHr_add (scte_inHr_smul_cutoff_of_sqrtS ha₀_box hψ_s hψ_p hψ_v hEw'_sq).1
      (scte_inHr_smul_cutoff hvGE_s hvGE_p hvGE_v hw_in).1
  have hDt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Dt' z = 0 := by
    intro z hz; dsimp [Dt', weakSmul]; rw [hψ_v z hz, hvGD_v z hz]; simp
  have hQt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Qt' z = 0 := by
    intro z hz; dsimp [Qt', weakSmul]; rw [hψ_v z hz, hvGQ_v z hz]; simp
  have hEt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Et' z = 0 := by
    intro z hz; dsimp [Et', weakSmul]; rw [hψ_v z hz, hvGE_v z hz]; simp
  have ha₁_nn : 0 ≤ 2 * H₁ := by positivity
  have hM_nn : 0 ≤ L₁ + 1 := by positivity
  have hsqDt'_in : InHr c 2 (sqrtS Dt') :=
    scte_inHr_sqrtS_of_box ha₀_box.le ha₁_nn hM_nn hDt'_in hDt'_supp
  have hsqQt'_in : InHr c 2 (sqrtS Qt') :=
    scte_inHr_sqrtS_of_box ha₀_box.le ha₁_nn hM_nn hQt'_in hQt'_supp
  have hsqEt'_in : InHr c 2 (sqrtS Et') :=
    scte_inHr_sqrtS_of_box ha₀_box.le ha₁_nn hM_nn hEt'_in hEt'_supp
  have hts_in : InHr c 2 (fun x : Coord => (x.1 : ℂ) • t x) := by
    have hper : QPeriodic c (fun x : Coord => (x.1 : ℂ) • t x) := by
      filter_upwards [ht_in.periodic] with x hx
      change (x.1 : ℂ) • t (qShift c x) = (x.1 : ℂ) • t x
      exact congrArg ((x.1 : ℂ) • ·) hx
    have hmeas : AEStronglyMeasurable (fun x : Coord => (x.1 : ℂ) • t x) (hMeas c 2) :=
      (Complex.measurable_ofReal.comp measurable_fst).aestronglyMeasurable.smul ht_in.meas
    exact ⟨hper, hmeas, lt_of_le_of_lt
      (scte_hNorm_mul_box_le ha₀_box.le ha₁_nn hM_nn ht_supp).2.1
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ht_in.finite)⟩
  have hθ_s : ContDiff ℝ ∞ θ_enl := boxCutoff_contDiff (σ / 2) (2 * H₁) (L₁ + 1)
  have hθ_p : ∀ x, θ_enl (qShift c x) = θ_enl x := boxCutoff_periodic c (σ / 2) (2 * H₁) (L₁ + 1)
  have hθ_v : ∀ x : Coord, (x.1 < (σ / 2) / 2 ∨ 2 * (2 * H₁) < x.1 ∨ (L₁ + 1) + 1 < |x.2.2|) →
      θ_enl x = 0 := fun x hx => boxCutoff_eq_zero_of_outside ha₀_box (by linarith) hx
  have hηθ_s : ContDiff ℝ ∞ (fun x : Coord => x.2.2 * θ_enl x) :=
    (contDiff_snd.comp contDiff_snd).mul hθ_s
  have hηθ_p : ∀ x, (qShift c x).2.2 * θ_enl (qShift c x) = x.2.2 * θ_enl x := fun x => by
    rw [show (qShift c x).2.2 = x.2.2 from rfl, hθ_p x]
  have hηθ_v : ∀ x : Coord,
      (x.1 < (σ / 2) / 2 ∨ 2 * (2 * H₁) < x.1 ∨ (L₁ + 1) + 1 < |x.2.2|) →
        x.2.2 * θ_enl x = 0 := fun x hx => by rw [hθ_v x hx, mul_zero]
  have hθQv'_in : InHr c 2 (fun x => (θ_enl x : ℂ) • Qv' x) := by
    have ha₀' : 0 < (σ / 2) / 2 := by positivity
    have heq : (fun x : Coord => (θ_enl x : ℂ) • Qv' x) =
        fun x => (θ_enl x : ℂ) • Qb0' x -
          (ε : ℂ) • ((2 : ℂ) • ((θ_enl x : ℂ) • Sb0' x) +
            ((x.2.2 * θ_enl x : ℝ) : ℂ) • Eb0' x + (θ_enl x : ℂ) • b0 x) := by
      ext x i
      simp only [Qv', PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, qepsOf_apply,
        smul_eq_mul]
      push_cast
      ring
    rw [heq]
    have j1 := (scte_inHr_smul_cutoff_of_sqrtS ha₀' hθ_s hθ_p hθ_v hQb0'_in).1
    have j2 := scte_inHr_const_smul (2 : ℂ) (scte_inHr_smul_cutoff hθ_s hθ_p hθ_v hSb0'_in).1
    have j3 := (scte_inHr_smul_cutoff_of_sqrtS ha₀' hηθ_s hηθ_p hηθ_v hEb0'_in).1
    have j4 := (scte_inHr_smul_cutoff hθ_s hθ_p hθ_v hb0_in).1
    exact flatCls_inHr_sub j1
      (scte_inHr_const_smul (ε : ℂ) (scte_inHr_add (scte_inHr_add j2 j3) j4))
  have hsqθQv'_in : InHr c 2 (sqrtS (fun x => (θ_enl x : ℂ) • Qv' x)) :=
    scte_inHr_sqrtS_of_box (a₀ := (σ / 2) / 2) (a₁ := 2 * (2 * H₁)) (M := (L₁ + 1) + 1)
      (by positivity) (by positivity) (by positivity)
      hθQv'_in fun x hx => by rw [hθ_v x hx, Complex.ofReal_zero, zero_smul]
  have hSw' : HasWeakVec vS dZero w Sw' := flatCls_hasWeakVec_sub hSε' hS0'
  have hEw' : HasWeakVec vEta dZero w Ew' := flatCls_hasWeakVec_sub hEε' hE0'
  have hDw' : HasWeakVec vQ0 dZero w Dw' :=
    flatCls_hasWeakVec_sub (hasWeakVec_dqOf ε hSε' hQε' hEε') hQ0'
  have hQv' : HasWeakVec (vQ ε) (dQ ε) b0 Qv' := hasWeakVec_qepsOf ε hS0' hQ0' hE0'
  have hQw' : HasWeakVec (vQ ε) (dQ ε) w Qw' := flatCls_hasWeakVec_sub hQε' hQv'
  have hSt' : HasWeakVec vS dZero t St' := hasWeakVec_smul_smooth contDiff_vS hψ_s hSw' hEw'
  have hDt' : HasWeakVec vQ0 dZero t Dt' := hasWeakVec_smul_smooth contDiff_vQ0 hψ_s hDw' hEw'
  have hQt' : HasWeakVec (vQ ε) (dQ ε) t Qt' :=
    hasWeakVec_smul_smooth (contDiff_vQ ε) hψ_s hQw' hEw'
  have hEt' : HasWeakVec vEta dZero t Et' := hasWeakVec_smul_smooth contDiff_vEta hψ_s hEw' hEw'
  exact ⟨ht_in, hSt'_in, hDt'_in, hQt'_in, hEt'_in,
    hsqDt'_in, hsqQt'_in, hsqEt'_in, hts_in, hsqθQv'_in,
    ht_supp, hSt'_supp, hDt'_supp, hQt'_supp, hEt'_supp,
    hSw', hEw', hQv', hQw', hSt', hDt', hQt', hEt'⟩

private lemma scte_cutoff_test_props {c σ H₁ L₁ ε : ℝ}
    (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (hL₁0 : 0 ≤ L₁)
    {bε b0 Sbε' Qbε' Ebε' Sb0' Qb0' Eb0' : CProf}
    (hbε_in : InHr c 2 bε) (hb0_in : InHr c 2 b0)
    (hSbε'_in : InHr c 2 Sbε') (hQbε'_in : InHr c 2 (sqrtS Qbε'))
    (hEbε'_in : InHr c 2 (sqrtS Ebε'))
    (hSb0'_in : InHr c 2 Sb0') (hQb0'_in : InHr c 2 (sqrtS Qb0'))
    (hEb0'_in : InHr c 2 (sqrtS Eb0'))
    (hSε' : HasWeakVec vS dZero bε Sbε') (hQε' : HasWeakVec (vQ ε) (dQ ε) bε Qbε')
    (hEε' : HasWeakVec vEta dZero bε Ebε')
    (hS0' : HasWeakVec vS dZero b0 Sb0') (hQ0' : HasWeakVec vQ0 dZero b0 Qb0')
    (hE0' : HasWeakVec vEta dZero b0 Eb0')
    (ψ θ_enl : Coord → ℝ)
    (w Sw' Dw' Qv' Qw' Ew' t St' Dt' Qt' Et' : CProf)
    (hψ_eq : ψ = fun x => boxCutoff σ H₁ L₁ x ^ 2)
    (hθ_eq : θ_enl = boxCutoff (σ / 2) (2 * H₁) (L₁ + 1))
    (hw_eq : w = bε - b0)
    (hSw'_eq : Sw' = Sbε' - Sb0')
    (hDw'_eq : Dw' = dqOf ε bε Sbε' Qbε' Ebε' - Qb0')
    (hQv'_eq : Qv' = qepsOf ε b0 Sb0' Qb0' Eb0')
    (hQw'_eq : Qw' = Qbε' - Qv')
    (hEw'_eq : Ew' = Ebε' - Eb0')
    (ht_eq : t = fun x => (ψ x : ℂ) • w x)
    (hSt'_eq : St' = weakSmul vS ψ w Sw')
    (hDt'_eq : Dt' = weakSmul vQ0 ψ w Dw')
    (hQt'_eq : Qt' = weakSmul (vQ ε) ψ w Qw')
    (hEt'_eq : Et' = weakSmul vEta ψ w Ew') :
    InHr c 2 t ∧ InHr c 2 St' ∧ InHr c 2 Dt' ∧ InHr c 2 Qt' ∧ InHr c 2 Et' ∧
      InHr c 2 (sqrtS Dt') ∧ InHr c 2 (sqrtS Qt') ∧ InHr c 2 (sqrtS Et') ∧
      InHr c 2 (fun x : Coord => (x.1 : ℂ) • t x) ∧
      InHr c 2 (sqrtS (fun x => (θ_enl x : ℂ) • Qv' x)) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → t z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → St' z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Dt' z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Qt' z = 0) ∧
      (∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Et' z = 0) ∧
      HasWeakVec vS dZero w Sw' ∧ HasWeakVec vEta dZero w Ew' ∧
      HasWeakVec (vQ ε) (dQ ε) b0 Qv' ∧ HasWeakVec (vQ ε) (dQ ε) w Qw' ∧
      HasWeakVec vS dZero t St' ∧ HasWeakVec vQ0 dZero t Dt' ∧
      HasWeakVec (vQ ε) (dQ ε) t Qt' ∧ HasWeakVec vEta dZero t Et' := by
  subst hSt'_eq; subst hDt'_eq; subst hQt'_eq; subst hEt'_eq; subst ht_eq
  subst hQw'_eq; subst hQv'_eq; subst hDw'_eq; subst hSw'_eq; subst hEw'_eq
  subst hw_eq; subst hθ_eq; subst hψ_eq
  exact scte_cutoff_test_props_aux hσ hσH₁ hL₁0 hbε_in hb0_in
    hSbε'_in hQbε'_in hEbε'_in hSb0'_in hQb0'_in hEb0'_in
    hSε' hQε' hEε' hS0' hQ0' hE0'

private lemma scte_subtracted_limit_ineq {ν c σ H₁ L₁ ε : ℝ} {μ : ℂ}
    (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (hL₁0 : 0 ≤ L₁)
    (hε0 : 0 < ε) (ha : 0 < μ.re + 1 / 4)
    {F bε b0 Sbε' Qbε' Ebε' Sb0' Qb0' Eb0' t St' Dt' Qt' Et' : CProf}
    (hF : InHr c 2 F) (hbε_in : InHr c 2 bε) (hbε_resp : IsResponse ν c ε μ 2 F bε)
    (hb0_resp : IsFlatResponse ν μ F b0) (hb0_class : InFlatClass c 2 b0)
    (hSbε'_in : InHr c 2 Sbε') (hQbε'_in : InHr c 2 (sqrtS Qbε')) (hEbε'_in : InHr c 2 (sqrtS Ebε'))
    (hSε' : HasWeakVec vS dZero bε Sbε') (hQε' : HasWeakVec (vQ ε) (dQ ε) bε Qbε')
    (hEε' : HasWeakVec vEta dZero bε Ebε')
    (hSb0'_in : InHr c 2 Sb0') (hQb0'_in : InHr c 2 (sqrtS Qb0')) (hEb0'_in : InHr c 2 (sqrtS Eb0'))
    (hS0' : HasWeakVec vS dZero b0 Sb0') (hQ0' : HasWeakVec vQ0 dZero b0 Qb0')
    (hE0' : HasWeakVec vEta dZero b0 Eb0')
    (ht_in : InHr c 2 t) (hSt'_in : InHr c 2 St') (hDt'_in : InHr c 2 Dt') (hEt'_in : InHr c 2 Et')
    (hsqDt'_in : InHr c 2 (sqrtS Dt')) (hsqQt'_in : InHr c 2 (sqrtS Qt'))
    (hsqEt'_in : InHr c 2 (sqrtS Et'))
    (hts_in : InHr c 2 (fun x : Coord => (x.1 : ℂ) • t x))
    (ht_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → t z = 0)
    (hSt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → St' z = 0)
    (hDt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Dt' z = 0)
    (hEt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Et' z = 0)
    (hSt' : HasWeakVec vS dZero t St') (hDt' : HasWeakVec vQ0 dZero t Dt')
    (hQt' : HasWeakVec (vQ ε) (dQ ε) t Qt') (hEt' : HasWeakVec vEta dZero t Et') :
    ((μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qbε' x i * (starRingEnd ℂ) (Qt' x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Ebε' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2) +
        ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
          (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)) -
      (μ * ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qb0' x i * (starRingEnd ℂ) (Dt' x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Eb0' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2))).re ≤
      (3 * scte_CL2 + 2 * scte_flat_CL) * (hNorm c 2 F).toReal * (hNorm c 2 t).toReal := by
  have hb0_in : InHr c 2 b0 := hb0_class.inHr
  obtain ⟨hBn_nice, hBn_lim, hsBn_lim, hsqDBn_lim, hsqEBn_lim, hsqQBn_lim⟩ :=
    scte_mollProf_all_tendsto hc hσ hσH₁ hL₁0 hε0 ht_in hSt'_in hDt'_in hEt'_in
      ht_supp hSt'_supp hDt'_supp hEt'_supp hSt' hDt' hQt' hEt'
  set B_n := fun n : ℕ => scte_mollProf σ n t
  set L_phys : ℕ → ℂ := fun n =>
    μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (B_n n x i) ∂(hMeas c 2) +
      ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (B_n n x i) ∂(hMeas c 2) +
      (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qbε' x i * (starRingEnd ℂ) (classQ ε (B_n n) x i) ∂(hMeas c 2) +
      (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Ebε' x i * (starRingEnd ℂ) (classEta (B_n n) x i) ∂(hMeas c 2) +
      ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
        (bε x 0 * (starRingEnd ℂ) (B_n n x 0)) ∂(hMeas c 2)
  set L_flat : ℕ → ℂ := fun n =>
    μ * ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (B_n n x i) ∂(hMeas c 2) +
      ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (B_n n x i) ∂(hMeas c 2) +
      (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qb0' x i * (starRingEnd ℂ) (fderiv ℝ (B_n n) x (cdir 1) i) ∂(hMeas c 2) +
      (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Eb0' x i * (starRingEnd ℂ) (classEta (B_n n) x i) ∂(hMeas c 2)
  have hdiff_re_le : ∀ n : ℕ,
      (L_phys n - L_flat n).re ≤
        (3 * scte_CL2 + 2 * scte_flat_CL) * (hNorm c 2 F).toReal * (hNorm c 2 (B_n n)).toReal := by
    intro n
    have hp := scte_phys_nice_eq hc hν hε0 hF hbε_in hbε_resp
      hSbε'_in hQbε'_in hEbε'_in hSε' hQε' hEε' (hBn_nice n)
    have hf := scte_flat_nice_eq hc hν ha hF hb0_resp hb0_class
      hSb0'_in hQb0'_in hEb0'_in hS0' hQ0' hE0' (hBn_nice n)
    calc (L_phys n - L_flat n).re
        ≤ ‖L_phys n - L_flat n‖ := Complex.re_le_norm _
      _ ≤ ‖L_phys n‖ + ‖L_flat n‖ := norm_sub_le _ _
      _ ≤ 3 * scte_CL2 * (hNorm c 2 F).toReal * (hNorm c 2 (B_n n)).toReal +
            2 * scte_flat_CL * (hNorm c 2 F).toReal * (hNorm c 2 (B_n n)).toReal :=
          add_le_add hp hf
      _ = (3 * scte_CL2 + 2 * scte_flat_CL) * (hNorm c 2 F).toReal *
            (hNorm c 2 (B_n n)).toReal := by ring
  have hBn_in : ∀ n : ℕ, InHr c 2 (B_n n) := fun n => scte_nice_inHr hc (hBn_nice n)
  have hsBn_in : ∀ n : ℕ, InHr c 2 (fun x => (x.1 : ℂ) • B_n n x) :=
    fun n => scte_nice_inHr hc (scte_nice_mulS (hBn_nice n))
  have hsqQBn_in : ∀ n : ℕ, InHr c 2 (sqrtS (classQ ε (B_n n))) :=
    fun n => scte_nice_inHr hc (scte_nice_sqrtS ((lapNiceClass_proof c ε _ (hBn_nice n)).1))
  have hsqEBn_in : ∀ n : ℕ, InHr c 2 (sqrtS (classEta (B_n n))) :=
    fun n => scte_nice_inHr hc (scte_nice_sqrtS ((lapNiceClass_proof c 0 _ (hBn_nice n)).2))
  have hsqDBn_in : ∀ n : ℕ, InHr c 2 (sqrtS (fun x => fderiv ℝ (B_n n) x (cdir 1))) :=
    fun n => scte_nice_inHr hc (scte_nice_sqrtS (scte_nice_fderiv_dir 1 (hBn_nice n)))
  have t_bε := scte_pair_tendsto hbε_in.meas hbε_in.finite ht_in.meas ht_in.finite
    (fun n => (hBn_in n).meas) (fun n => (hBn_in n).finite) hBn_lim
  have t_b0 := scte_pair_tendsto hb0_in.meas hb0_in.finite ht_in.meas ht_in.finite
    (fun n => (hBn_in n).meas) (fun n => (hBn_in n).finite) hBn_lim
  have t_Sε := scte_pair_tendsto hSbε'_in.meas hSbε'_in.finite ht_in.meas ht_in.finite
    (fun n => (hBn_in n).meas) (fun n => (hBn_in n).finite) hBn_lim
  have t_S0 := scte_pair_tendsto hSb0'_in.meas hSb0'_in.finite ht_in.meas ht_in.finite
    (fun n => (hBn_in n).meas) (fun n => (hBn_in n).finite) hBn_lim
  have t_Qε : Tendsto (fun n => ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qbε' x i * (starRingEnd ℂ) (classQ ε (B_n n) x i) ∂(hMeas c 2))
      atTop (𝓝 (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qbε' x i * (starRingEnd ℂ) (Qt' x i) ∂(hMeas c 2))) := by
    simp_rw [scte_weighted_pair_eq_sqrtS]
    exact scte_pair_tendsto hQbε'_in.meas hQbε'_in.finite hsqQt'_in.meas hsqQt'_in.finite
      (fun n => (hsqQBn_in n).meas) (fun n => (hsqQBn_in n).finite) hsqQBn_lim
  have t_Q0 : Tendsto (fun n => ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qb0' x i * (starRingEnd ℂ) (fderiv ℝ (B_n n) x (cdir 1) i) ∂(hMeas c 2))
      atTop (𝓝 (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Qb0' x i * (starRingEnd ℂ) (Dt' x i) ∂(hMeas c 2))) := by
    simp_rw [scte_weighted_pair_eq_sqrtS]
    exact scte_pair_tendsto hQb0'_in.meas hQb0'_in.finite hsqDt'_in.meas hsqDt'_in.finite
      (fun n => (hsqDBn_in n).meas) (fun n => (hsqDBn_in n).finite) hsqDBn_lim
  have t_Eε : Tendsto (fun n => ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Ebε' x i * (starRingEnd ℂ) (classEta (B_n n) x i) ∂(hMeas c 2))
      atTop (𝓝 (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Ebε' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2))) := by
    simp_rw [scte_weighted_pair_eq_sqrtS]
    exact scte_pair_tendsto hEbε'_in.meas hEbε'_in.finite hsqEt'_in.meas hsqEt'_in.finite
      (fun n => (hsqEBn_in n).meas) (fun n => (hsqEBn_in n).finite) hsqEBn_lim
  have t_E0 : Tendsto (fun n => ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Eb0' x i * (starRingEnd ℂ) (classEta (B_n n) x i) ∂(hMeas c 2))
      atTop (𝓝 (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        Eb0' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2))) := by
    simp_rw [scte_weighted_pair_eq_sqrtS]
    exact scte_pair_tendsto hEb0'_in.meas hEb0'_in.finite hsqEt'_in.meas hsqEt'_in.finite
      (fun n => (hsqEBn_in n).meas) (fun n => (hsqEBn_in n).finite) hsqEBn_lim
  have t_hoop : Tendsto (fun n => ∫ x, (x.1 : ℂ) *
        (bε x 0 * (starRingEnd ℂ) (B_n n x 0)) ∂(hMeas c 2))
      atTop (𝓝 (∫ x, (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2))) := by
    set bε0 : CProf := fun x => sctePairCLM (bε x 0, 0)
    have hbε0_in : InHr c 2 bε0 := by
      have hper : QPeriodic c bε0 := by
        filter_upwards [hbε_in.periodic] with x hx
        dsimp [bε0]; rw [hx]
      have hmeas : AEStronglyMeasurable bε0 (hMeas c 2) :=
        sctePairCLM.continuous.comp_aestronglyMeasurable
          (((EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
            hbε_in.meas).prodMk aestronglyMeasurable_const)
      have hle : hNorm c 2 bε0 ≤ hNorm c 2 bε := by
        refine eLpNorm_mono fun x => ?_
        have hsq : ‖bε0 x‖ ^ 2 = ‖bε x 0‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
          simp [bε0]
        have h1 : ‖bε0 x‖ ≤ ‖bε x 0‖ :=
          (abs_le_of_sq_le_sq' hsq.le (norm_nonneg _)).2
        exact h1.trans (PiLp.norm_apply_le (bε x) 0)
      exact ⟨hper, hmeas, lt_of_le_of_lt hle hbε_in.finite⟩
    have hpt : ∀ (G : CProf),
        (fun x : Coord => (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (G x 0))) =
          fun x => ∑ i : Fin 2, bε0 x i * (starRingEnd ℂ) (((x.1 : ℂ) • G x) i) := by
      intro G; funext x
      rw [Fin.sum_univ_two]
      simp only [bε0, sctePairCLM_zero, sctePairCLM_one, PiLp.smul_apply, smul_eq_mul, map_mul,
        Complex.conj_ofReal]
      ring
    simp_rw [hpt]
    exact scte_pair_tendsto hbε0_in.meas hbε0_in.finite hts_in.meas hts_in.finite
      (fun n => (hsBn_in n).meas) (fun n => (hsBn_in n).finite) hsBn_lim
  have t_norm_Bn := scte_hNorm_toReal_tendsto ht_in hBn_in hBn_lim
  have t_L_phys :=
    ((((t_bε.const_mul μ).add t_Sε).add (t_Qε.const_mul (ν : ℂ))).add
      (t_Eε.const_mul (ν : ℂ))).add (t_hoop.const_mul ((ν * ε ^ 2 : ℝ) : ℂ))
  have t_L_flat :=
    (((t_b0.const_mul μ).add t_S0).add (t_Q0.const_mul (ν : ℂ))).add (t_E0.const_mul (ν : ℂ))
  have t_LHS_re := (Complex.continuous_re.tendsto _).comp (t_L_phys.sub t_L_flat)
  have t_RHS : Tendsto
      (fun n => (3 * scte_CL2 + 2 * scte_flat_CL) * (hNorm c 2 F).toReal *
        (hNorm c 2 (B_n n)).toReal)
      atTop (𝓝 ((3 * scte_CL2 + 2 * scte_flat_CL) * (hNorm c 2 F).toReal *
        (hNorm c 2 t).toReal)) :=
    t_norm_Bn.const_mul _
  exact le_of_tendsto_of_tendsto t_LHS_re t_RHS (Eventually.of_forall hdiff_re_le)

private lemma scte_recombine_limit_integrals {c ν σ H₁ L₁ ε : ℝ} {μ : ℂ}
    {χ θ_enl : Coord → ℝ}
    {bε b0 w Sw Ew Qw Qv Qb0 Dt Qt Et Sbε' Qbε' Ebε' Sb0' Qb0' Eb0'
      Sw' Ew' Qw' Qv' t Dt' Qt' Et' : CProf}
    (hθ_one : ∀ x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1), θ_enl x = 1)
    (hw_def : ∀ x, w x = bε x - b0 x)
    (ht_def : ∀ x, t x = ((χ x ^ 2 : ℝ) : ℂ) • w x)
    (hSw'_def : ∀ x, Sw' x = Sbε' x - Sb0' x)
    (hEw'_def : ∀ x, Ew' x = Ebε' x - Eb0' x)
    (hQw'_def : ∀ x, Qw' x = Qbε' x - Qv' x)
    (hbε_in : InHr c 2 bε) (hb0_in : InHr c 2 b0) (ht_in : InHr c 2 t)
    (hSbε'_in : InHr c 2 Sbε') (hSb0'_in : InHr c 2 Sb0')
    (hQbε'_in : InHr c 2 (sqrtS Qbε')) (hQb0'_in : InHr c 2 (sqrtS Qb0'))
    (hEbε'_in : InHr c 2 (sqrtS Ebε')) (hEb0'_in : InHr c 2 (sqrtS Eb0'))
    (hsqDt'_in : InHr c 2 (sqrtS Dt')) (hsqQt'_in : InHr c 2 (sqrtS Qt'))
    (hsqEt'_in : InHr c 2 (sqrtS Et'))
    (hsqθQv'_in : InHr c 2 (sqrtS (fun x => (θ_enl x : ℂ) • Qv' x)))
    (hQt'_supp : ∀ z : Coord, (z.1 < σ / 2 ∨ 2 * H₁ < z.1 ∨ L₁ + 1 < |z.2.2|) → Qt' z = 0)
    (hae_Sw : Sw' =ᵐ[hMeas c 2] Sw) (hae_Ew : Ew' =ᵐ[hMeas c 2] Ew)
    (hae_Qw : Qw' =ᵐ[hMeas c 2] Qw) (hae_Qv : Qv' =ᵐ[hMeas c 2] Qv)
    (hae_Qb0 : Qb0' =ᵐ[hMeas c 2] Qb0) (hae_Dt : Dt' =ᵐ[hMeas c 2] Dt)
    (hae_Qt : Qt' =ᵐ[hMeas c 2] Qt) (hae_Et : Et' =ᵐ[hMeas c 2] Et) :
    ((μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qbε' x i * (starRingEnd ℂ) (Qt' x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Ebε' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2) +
        ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
          (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)) -
      (μ * ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Qb0' x i * (starRingEnd ℂ) (Dt' x i) ∂(hMeas c 2) +
        (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          Eb0' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2))).re =
      (μ.re * ∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) +
        (∫ x, ∑ i : Fin 2, Sw x i *
          (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * w x i) ∂(hMeas c 2)).re +
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)).re -
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          (Qb0 x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i))
          ∂(hMeas c 2)).re +
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2)).re) +
      (ν * ε ^ 2) *
        (∫ x, (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)).re := by
  have ew_int :
      (∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2)) -
        ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) =
      ((∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) : ℝ) : ℂ) := by
    obtain ⟨i1, -⟩ := scte_h2_pair_bound hbε_in.meas hbε_in.finite ht_in.meas ht_in.finite
    obtain ⟨i2, -⟩ := scte_h2_pair_bound hb0_in.meas hb0_in.finite ht_in.meas ht_in.finite
    calc (∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2)) -
          ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2)
        = ∫ x, (∑ i : Fin 2, bε x i * (starRingEnd ℂ) (t x i) -
            ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (t x i)) ∂(hMeas c 2) :=
          (integral_sub i1 i2).symm
      _ = ∫ x, ((χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 : ℝ) : ℂ) ∂(hMeas c 2) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, ht_def x, hw_def x]
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
          have c0 : (bε x 0 - b0 x 0) * (starRingEnd ℂ) (bε x 0 - b0 x 0) =
              ((‖bε x 0 - b0 x 0‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have c1 : (bε x 1 - b0 x 1) * (starRingEnd ℂ) (bε x 1 - b0 x 1) =
              ((‖bε x 1 - b0 x 1‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          calc ((bε x 0) * (((χ x ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (bε x 0 - b0 x 0)) +
                (bε x 1) * (((χ x ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (bε x 1 - b0 x 1))) -
               ((b0 x 0) * (((χ x ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (bε x 0 - b0 x 0)) +
                (b0 x 1) * (((χ x ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (bε x 1 - b0 x 1)))
              = ((χ x ^ 2 : ℝ) : ℂ) *
                  ((bε x 0 - b0 x 0) * (starRingEnd ℂ) (bε x 0 - b0 x 0) +
                   (bε x 1 - b0 x 1) * (starRingEnd ℂ) (bε x 1 - b0 x 1)) := by ring
            _ = ((χ x ^ 2 * (‖bε x 0 - b0 x 0‖ ^ 2 + ‖bε x 1 - b0 x 1‖ ^ 2) : ℝ) : ℂ) := by
                rw [c0, c1]; push_cast; ring
      _ = ((∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) : ℝ) : ℂ) := integral_ofReal
  have eS_int :
      (∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2)) -
        ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) =
      ∫ x, ∑ i : Fin 2, Sw x i *
        (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * w x i) ∂(hMeas c 2) := by
    obtain ⟨i1, -⟩ := scte_h2_pair_bound hSbε'_in.meas hSbε'_in.finite ht_in.meas ht_in.finite
    obtain ⟨i2, -⟩ := scte_h2_pair_bound hSb0'_in.meas hSb0'_in.finite ht_in.meas ht_in.finite
    rw [← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hae_Sw] with x hx
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, ht_def x, ← hx, hSw'_def x]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have w_int_of : ∀ {U V : CProf}, InHr c 2 (sqrtS U) → InHr c 2 (sqrtS V) →
      Integrable (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2,
        U x i * (starRingEnd ℂ) (V x i)) (hMeas c 2) := by
    intro U V hU hV
    obtain ⟨hi, -⟩ := scte_h2_pair_bound hU.meas hU.finite hV.meas hV.finite
    refine hi.congr ?_
    filter_upwards [scte_hMeas_pos c 2] with x hxpos
    have hsq : ((Real.sqrt x.1 : ℂ) * (Real.sqrt x.1 : ℂ)) = (x.1 : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hxpos.le]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    calc ((Real.sqrt x.1 : ℂ) * U x 0) * ((Real.sqrt x.1 : ℂ) * (starRingEnd ℂ) (V x 0)) +
          ((Real.sqrt x.1 : ℂ) * U x 1) * ((Real.sqrt x.1 : ℂ) * (starRingEnd ℂ) (V x 1))
        = ((Real.sqrt x.1 : ℂ) * (Real.sqrt x.1 : ℂ)) *
            (U x 0 * (starRingEnd ℂ) (V x 0) + U x 1 * (starRingEnd ℂ) (V x 1)) := by ring
      _ = (x.1 : ℂ) * (U x 0 * (starRingEnd ℂ) (V x 0) + U x 1 * (starRingEnd ℂ) (V x 1)) := by
            rw [hsq]
  have eE_int :
      (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ebε' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2)) -
        ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Eb0' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2) =
      ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2) := by
    rw [← integral_sub (w_int_of hEbε'_in hsqEt'_in) (w_int_of hEb0'_in hsqEt'_in)]
    refine integral_congr_ae ?_
    filter_upwards [hae_Ew, hae_Et] with x hxEw hxEt
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, ← hxEt, ← hxEw, hEw'_def x]
    simp only [PiLp.sub_apply]
    ring
  have eQ_int :
      (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qbε' x i * (starRingEnd ℂ) (Qt' x i) ∂(hMeas c 2)) -
        ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qb0' x i * (starRingEnd ℂ) (Dt' x i) ∂(hMeas c 2) =
      (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)) -
        ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          (Qb0 x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i))
          ∂(hMeas c 2) := by
    have iQε := w_int_of hQbε'_in hsqQt'_in
    have iQ0 := w_int_of hQb0'_in hsqDt'_in
    have iQv : Integrable (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2,
        Qv' x i * (starRingEnd ℂ) (Qt' x i)) (hMeas c 2) := by
      refine (w_int_of hsqθQv'_in hsqQt'_in).congr (ae_of_all _ fun x => ?_)
      dsimp only
      by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
      · rw [hθ_one x hx, Complex.ofReal_one, one_smul]
      · have hout : x.1 < σ / 2 ∨ 2 * H₁ < x.1 ∨ L₁ + 1 < |x.2.2| := by
          by_contra hnot
          push Not at hnot
          exact hx ⟨⟨hnot.1, hnot.2.1⟩, trivial, abs_le.mp hnot.2.2⟩
        rw [hQt'_supp x hout]
        simp
    have hsplit :
        (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qbε' x i * (starRingEnd ℂ) (Qt' x i) ∂(hMeas c 2)) -
          ∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qb0' x i * (starRingEnd ℂ) (Dt' x i) ∂(hMeas c 2) =
        (∫ x, ((x.1 : ℂ) * ∑ i : Fin 2, Qbε' x i * (starRingEnd ℂ) (Qt' x i) -
            (x.1 : ℂ) * ∑ i : Fin 2, Qv' x i * (starRingEnd ℂ) (Qt' x i)) ∂(hMeas c 2)) -
          ∫ x, ((x.1 : ℂ) * ∑ i : Fin 2, Qb0' x i * (starRingEnd ℂ) (Dt' x i) -
            (x.1 : ℂ) * ∑ i : Fin 2, Qv' x i * (starRingEnd ℂ) (Qt' x i)) ∂(hMeas c 2) := by
      rw [integral_sub iQε iQv, integral_sub iQ0 iQv]
      ring
    rw [hsplit]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [hae_Qw, hae_Qt] with x hxQw hxQt
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, ← hxQt, ← hxQw, hQw'_def x]
      simp only [PiLp.sub_apply]
      ring
    · refine integral_congr_ae ?_
      filter_upwards [hae_Qb0, hae_Dt, hae_Qv, hae_Qt] with x hxQb0 hxDt hxQv hxQt
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, ← hxQb0, ← hxDt, ← hxQv, ← hxQt]
      ring
  have hLim_eq :
      (μ * ∫ x, ∑ i : Fin 2, bε x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
          ∫ x, ∑ i : Fin 2, Sbε' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
          (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
            Qbε' x i * (starRingEnd ℂ) (Qt' x i) ∂(hMeas c 2) +
          (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
            Ebε' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2) +
          ((ν * ε ^ 2 : ℝ) : ℂ) * ∫ x, (x.1 : ℂ) *
            (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)) -
        (μ * ∫ x, ∑ i : Fin 2, b0 x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
          ∫ x, ∑ i : Fin 2, Sb0' x i * (starRingEnd ℂ) (t x i) ∂(hMeas c 2) +
          (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
            Qb0' x i * (starRingEnd ℂ) (Dt' x i) ∂(hMeas c 2) +
          (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
            Eb0' x i * (starRingEnd ℂ) (Et' x i) ∂(hMeas c 2)) =
      μ * ((∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) : ℝ) : ℂ) +
      (∫ x, ∑ i : Fin 2, Sw x i *
        (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * w x i) ∂(hMeas c 2)) +
      (ν : ℂ) * ((∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)) -
        ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          (Qb0 x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i))
          ∂(hMeas c 2)) +
      (ν : ℂ) * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2)) +
      ((ν * ε ^ 2 : ℝ) : ℂ) *
        ∫ x, (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2) := by
    linear_combination μ * ew_int + eS_int + (ν : ℂ) * eQ_int + (ν : ℂ) * eE_int
  rw [hLim_eq]
  simp only [Complex.add_re, Complex.sub_re, re_ofReal_mul]
  have hμre : ∀ R : ℝ, (μ * (R : ℂ)).re = μ.re * R := fun R => by simp [Complex.mul_re]
  rw [hμre]
  ring

private lemma scte_final_scalar_ineq
    {E_main I_hoop Lim_diff N_F N_t N_b0 C_src Cf Γ ν H₁ ε om : ℝ}
    (hC_src : 0 ≤ C_src) (hCf : 0 < Cf) (hΓ1 : 1 ≤ Γ)
    (hν : 0 < ν) (hH₁ : 0 < H₁) (hνΓ : ν ≤ Γ) (hH₁Γ : H₁ ≤ Γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hom0 : 0 ≤ om)
    (hNF : 0 ≤ N_F) (hNb0 : 0 ≤ N_b0)
    (hLim_ineq : Lim_diff ≤ C_src * N_F * N_t)
    (hLim_re : Lim_diff = E_main + (ν * ε ^ 2) * I_hoop)
    (ht_le : N_t ≤ om * N_F)
    (hhoop_bd : -(ν * ε ^ 2) * I_hoop ≤ (1 / 2) * ν * H₁ * ε ^ 2 * N_b0 ^ 2)
    (hb0_le : N_b0 ≤ Cf * Γ ^ 2 * N_F) :
    E_main ≤ (C_src + Cf ^ 2 + 1) * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2 := by
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have hΓ6 : 1 ≤ Γ ^ 6 := one_le_pow₀ hΓ1
  have hNF2 : 0 ≤ N_F ^ 2 := sq_nonneg N_F
  have hom2 : 0 ≤ om ^ 2 := sq_nonneg om
  have hsrc1 : C_src * N_F * N_t ≤ C_src * om * N_F ^ 2 := by
    calc C_src * N_F * N_t ≤ C_src * N_F * (om * N_F) :=
          mul_le_mul_of_nonneg_left ht_le (mul_nonneg hC_src hNF)
      _ = C_src * om * N_F ^ 2 := by ring
  have hom_le : om ≤ Γ ^ 6 * (om + om ^ 2 + ε) := by
    calc om = 1 * om := (one_mul om).symm
      _ ≤ 1 * (om + om ^ 2 + ε) := by linarith only [hom2, hε0]
      _ ≤ Γ ^ 6 * (om + om ^ 2 + ε) :=
          mul_le_mul_of_nonneg_right hΓ6 (by linarith only [hom0, hom2, hε0])
  have hsrc2 : C_src * om * N_F ^ 2 ≤ C_src * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2 := by
    calc C_src * om * N_F ^ 2 = (C_src * N_F ^ 2) * om := by ring
      _ ≤ (C_src * N_F ^ 2) * (Γ ^ 6 * (om + om ^ 2 + ε)) :=
          mul_le_mul_of_nonneg_left hom_le (mul_nonneg hC_src hNF2)
      _ = C_src * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2 := by ring
  have hb0_sq : N_b0 ^ 2 ≤ (Cf * Γ ^ 2 * N_F) ^ 2 := pow_le_pow_left₀ hNb0 hb0_le 2
  have hε_sq : ε ^ 2 ≤ ε := by
    calc ε ^ 2 = ε * ε := sq ε
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε0.le
      _ = ε := mul_one ε
  have hνH : ν * H₁ ≤ Γ ^ 2 := by
    calc ν * H₁ ≤ Γ * Γ := mul_le_mul hνΓ hH₁Γ hH₁.le hΓ0.le
      _ = Γ ^ 2 := (sq Γ).symm
  have hhoop1 : (1 / 2) * ν * H₁ * ε ^ 2 * N_b0 ^ 2 ≤ Cf ^ 2 * Γ ^ 6 * ε * N_F ^ 2 := by
    have hp1 : (1 / 2) * ν * H₁ * ε ^ 2 ≤ (ν * H₁) * ε := by
      have h1 : (1 / 2 : ℝ) * (ν * H₁) ≤ ν * H₁ := by
        have hpos : 0 < ν * H₁ := mul_pos hν hH₁
        linarith only [hpos]
      calc (1 / 2) * ν * H₁ * ε ^ 2 = ((1 / 2) * (ν * H₁)) * ε ^ 2 := by ring
        _ ≤ (ν * H₁) * ε := mul_le_mul h1 hε_sq (sq_nonneg ε) (mul_pos hν hH₁).le
    calc (1 / 2) * ν * H₁ * ε ^ 2 * N_b0 ^ 2
        ≤ ((ν * H₁) * ε) * (Cf * Γ ^ 2 * N_F) ^ 2 :=
          mul_le_mul hp1 hb0_sq (sq_nonneg N_b0) (mul_nonneg (mul_pos hν hH₁).le hε0.le)
      _ ≤ (Γ ^ 2 * ε) * (Cf * Γ ^ 2 * N_F) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hνH hε0.le) (sq_nonneg _)
      _ = Cf ^ 2 * Γ ^ 6 * ε * N_F ^ 2 := by ring
  have hhoop2 : Cf ^ 2 * Γ ^ 6 * ε * N_F ^ 2 ≤
      (Cf ^ 2 + 1) * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2 := by
    have h1 : Cf ^ 2 ≤ Cf ^ 2 + 1 := le_add_of_nonneg_right zero_le_one
    have h2 : ε ≤ om + om ^ 2 + ε := by linarith only [hom0, hom2]
    have h3 : Cf ^ 2 * ε ≤ (Cf ^ 2 + 1) * (om + om ^ 2 + ε) :=
      mul_le_mul h1 h2 hε0.le (by positivity)
    calc Cf ^ 2 * Γ ^ 6 * ε * N_F ^ 2
        = (Cf ^ 2 * ε) * (Γ ^ 6 * N_F ^ 2) := by ring
      _ ≤ ((Cf ^ 2 + 1) * (om + om ^ 2 + ε)) * (Γ ^ 6 * N_F ^ 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (Cf ^ 2 + 1) * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2 := by ring
  have hneg_eq : -(ν * ε ^ 2) * I_hoop = -((ν * ε ^ 2) * I_hoop) := neg_mul (ν * ε ^ 2) I_hoop
  have hsum : (C_src * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2) +
      ((Cf ^ 2 + 1) * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2) =
      (C_src + Cf ^ 2 + 1) * Γ ^ 6 * (om + om ^ 2 + ε) * N_F ^ 2 := by ring
  linarith only [hLim_ineq, hLim_re, hsrc1, hsrc2, hhoop_bd, hneg_eq, hhoop1, hhoop2, hsum]

/-- **Main Proof (`PartII-b:T16/2/1`, `SubtractedChartTestedEq`)**. -/
theorem subtractedChartTestedEq_proof : UnforcedLeray.Short.IIb.SubtractedChartTestedEq := by
  obtain ⟨Cf, hCf, hflat_poly⟩ := flat_graph_poly_two_given
  have hCL2_nn := scte_CL2_nonneg
  have hCL0_pos := scte_flat_CL_pos
  refine ⟨6, (3 * scte_CL2 + 2 * scte_flat_CL) + Cf ^ 2 + 1, by positivity, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ hνiΓ hcΓ hciΓ hσiΓ hH₁Γ hL₁Γ hμΓ hgap
    hν hc hσ hσH₁ hL₁0 ε hε0 hε1 hP
    F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0
    hF hbε_in hbε_resp hb0_resp hb0_class
    hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0
    om hom0 hom_bd
    χ ψ w Sw Dw Qv Qw Ew Dt Qt Et
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have ha : 0 < μ.re + 1 / 4 := lt_of_lt_of_le (inv_pos.mpr hΓ0) hgap
  have hH₁0 : 0 < H₁ := lt_of_lt_of_le hσ hσH₁
  have ha₀_box : 0 < σ / 2 := half_pos hσ
  obtain ⟨Sbε', Qbε', Ebε', hSbε'_in, hQbε'_in, hEbε'_in, hSε', hQε', hEε'⟩ :=
    scte_exists_inHr_derivs_of_isResponse hΓ1 hμΓ hgap hc hν hε0 hε1 hP hF hbε_resp
  obtain ⟨Sb0', Qb0', Eb0', hS0', hQ0', hE0', hSb0'_in, hQb0'_in, hEb0'_in⟩ := hb0_class.deriv
  have hb0_in : InHr c 2 b0 := hb0_class.inHr
  set Sw' := Sbε' - Sb0'
  set Dw' := dqOf ε bε Sbε' Qbε' Ebε' - Qb0'
  set Qv' := qepsOf ε b0 Sb0' Qb0' Eb0'
  set Qw' := Qbε' - Qv'
  set Ew' := Ebε' - Eb0'
  set t : CProf := fun x => (ψ x : ℂ) • w x
  set St' := weakSmul vS ψ w Sw'
  set Dt' := weakSmul vQ0 ψ w Dw'
  set Qt' := weakSmul (vQ ε) ψ w Qw'
  set Et' := weakSmul vEta ψ w Ew'
  set θ_enl := boxCutoff (σ / 2) (2 * H₁) (L₁ + 1)
  obtain ⟨ht_in, hSt'_in, hDt'_in, hQt'_in, hEt'_in,
      hsqDt'_in, hsqQt'_in, hsqEt'_in, hts_in, hsqθQv'_in,
      ht_supp, hSt'_supp, hDt'_supp, hQt'_supp, hEt'_supp,
      hSw', hEw', hQv', hQw', hSt', hDt', hQt', hEt'⟩ :=
    scte_cutoff_test_props hσ hσH₁ hL₁0 hbε_in hb0_in
      hSbε'_in hQbε'_in hEbε'_in hSb0'_in hQb0'_in hEb0'_in
      hSε' hQε' hEε' hS0' hQ0' hE0'
      ψ θ_enl w Sw' Dw' Qv' Qw' Ew' t St' Dt' Qt' Et'
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hχ_s : ContDiff ℝ ∞ χ := boxCutoff_contDiff σ H₁ L₁
  have hψ_s : ContDiff ℝ ∞ ψ := hχ_s.pow 2
  have hSw_w : HasWeakVec vS dZero w Sw := flatCls_hasWeakVec_sub hSε hS0
  have hEw_w : HasWeakVec vEta dZero w Ew := flatCls_hasWeakVec_sub hEε hE0
  have hDw_w : HasWeakVec vQ0 dZero w Dw :=
    flatCls_hasWeakVec_sub (hasWeakVec_dqOf ε hSε hQε hEε) hQ0
  have hQv_w : HasWeakVec (vQ ε) (dQ ε) b0 Qv := hasWeakVec_qepsOf ε hS0 hQ0 hE0
  have hQw_w : HasWeakVec (vQ ε) (dQ ε) w Qw := flatCls_hasWeakVec_sub hQε hQv_w
  have hDt_w : HasWeakVec vQ0 dZero t Dt := hasWeakVec_smul_smooth contDiff_vQ0 hψ_s hDw_w hEw_w
  have hQt_w : HasWeakVec (vQ ε) (dQ ε) t Qt :=
    hasWeakVec_smul_smooth (contDiff_vQ ε) hψ_s hQw_w hEw_w
  have hEt_w : HasWeakVec vEta dZero t Et := hasWeakVec_smul_smooth contDiff_vEta hψ_s hEw_w hEw_w
  have hLim_ineq := scte_subtracted_limit_ineq hc hν hσ hσH₁ hL₁0 hε0 ha hF
    hbε_in hbε_resp hb0_resp hb0_class
    hSbε'_in hQbε'_in hEbε'_in hSε' hQε' hEε'
    hSb0'_in hQb0'_in hEb0'_in hS0' hQ0' hE0'
    ht_in hSt'_in hDt'_in hEt'_in hsqDt'_in hsqQt'_in hsqEt'_in hts_in
    ht_supp hSt'_supp hDt'_supp hEt'_supp hSt' hDt' hQt' hEt'
  have hae_Sw : Sw' =ᵐ[hMeas c 2] Sw := hasWeakVec_unique_ae hc hSw' hSw_w
  have hae_Ew : Ew' =ᵐ[hMeas c 2] Ew := hasWeakVec_unique_ae hc hEw' hEw_w
  have hae_Qw : Qw' =ᵐ[hMeas c 2] Qw := hasWeakVec_unique_ae hc hQw' hQw_w
  have hae_Qv : Qv' =ᵐ[hMeas c 2] Qv := hasWeakVec_unique_ae hc hQv' hQv_w
  have hae_Qb0 : Qb0' =ᵐ[hMeas c 2] Qb0 := hasWeakVec_unique_ae hc hQ0' hQ0
  have hae_Dt : Dt' =ᵐ[hMeas c 2] Dt := hasWeakVec_unique_ae hc hDt' hDt_w
  have hae_Qt : Qt' =ᵐ[hMeas c 2] Qt := hasWeakVec_unique_ae hc hQt' hQt_w
  have hae_Et : Et' =ᵐ[hMeas c 2] Et := hasWeakVec_unique_ae hc hEt' hEt_w
  have hLim_re := scte_recombine_limit_integrals (ν := ν) (ε := ε) (μ := μ) (χ := χ)
    (fun x hx => boxCutoff_eq_one_of_mem ha₀_box (by linarith) hx)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    hbε_in hb0_in ht_in hSbε'_in hSb0'_in hQbε'_in hQb0'_in hEbε'_in hEb0'_in
    hsqDt'_in hsqQt'_in hsqEt'_in hsqθQv'_in hQt'_supp
    hae_Sw hae_Ew hae_Qw hae_Qv hae_Qb0 hae_Dt hae_Qt hae_Et
  have ht_tr_le : (hNorm c 2 t).toReal ≤ om * (hNorm c 2 F).toReal := by
    have h1 : hNorm c 2 t ≤ ENNReal.ofReal om * hNorm c 2 F :=
      (hNorm_boxCutoff_sq_smul_le_enlarged hσ hσH₁ w).trans hom_bd
    have hfin : ENNReal.ofReal om * hNorm c 2 F ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.finite.ne
    have htr := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hom0] at htr
  have hhoop_bd :
      -(ν * ε ^ 2) *
          (∫ x, (x.1 : ℂ) * (bε x 0 * (starRingEnd ℂ) (t x 0)) ∂(hMeas c 2)).re ≤
        (1 / 2) * ν * H₁ * ε ^ 2 * (hNorm c 2 b0).toReal ^ 2 := by
    refine scte_hoop_discrepancy_bound hν hH₁0 hε0 hbε_in hb0_in hχ_s (fun x => ?_) (fun x hx => ?_)
    · rw [abs_of_nonneg (boxCutoff_nonneg σ H₁ L₁ x)]
      exact boxCutoff_le_one σ H₁ L₁ x
    · apply boxCutoff_eq_zero_of_outside hσ hσH₁
      rcases hx with hx1 | hx2
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl hx2)
  have hb0_tr_le : (hNorm c 2 b0).toReal ≤ Cf * Γ ^ 2 * (hNorm c 2 F).toReal := by
    have hg0 := hflat_poly Γ ν c μ hΓ1 hμΓ hgap hν hc F b0 Sb0 Qb0 Eb0
      hF hb0_resp hb0_class hS0 hQ0 hE0
    have h1 : hNorm c 2 b0 ≤ ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F :=
      (le_self_add.trans le_self_add).trans hg0
    have hfin : ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.finite.ne
    have htr := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Cf * Γ ^ 2)] at htr
  exact scte_final_scalar_ineq (by positivity) hCf hΓ1 hν hH₁0 hνΓ hH₁Γ hε0 hε1 hom0
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hLim_ineq hLim_re ht_tr_le hhoop_bd hb0_tr_le

end UnforcedLeray.Short.IIb

