import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.Design
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.LinFree
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.H0Mode
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.AmplInt

/-!
# Leaf `PartIII-a:T21/c3/3/1/1/2/2/3`: `ComplWeakEq`

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2958.

Proves `complWeakEq`: along any zero-circulation weak linearised flow `(w, u)` and any backward
moving free adjoint flow `Φ` with terminal datum `Γ ∈ X_{-m, d(s)}`, the complement
`W⊥ = movingW ν w - ∑ j, α_j E_j` satisfies the Duhamel pairing identity
`⟨W⊥(s), Γ⟩ = ⟨W⊥(t₁), Φ(t₁)⟩ + ∫_{(t₁,s]} a(r)⁻² ⟨complSource(r), Φ(r)⟩ dr`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqProof

open Leaf2WeakEqFrame Leaf2WeakEqFrame.FramePairing1Aux

/-! ### 1. Fubini integration by parts for indefinite `L¹` integrals -/

private theorem continuousOn_indef_Ioc {t₁ s : ℝ} (hts : t₁ ≤ s) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioc t₁ s)) :
    ContinuousOn (fun r => ∫ q in Ioc t₁ r, f q) (Icc t₁ s) := by
  have hf_u : IntegrableOn f (Set.uIcc t₁ s) := by
    rw [Set.uIcc_of_le hts]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hf
  have hcont := intervalIntegral.continuousOn_primitive_interval hf_u
  rw [Set.uIcc_of_le hts] at hcont
  refine hcont.congr fun r hr => ?_
  rw [← intervalIntegral.integral_of_le hr.1]

private theorem fubini_ibp {t₁ s : ℝ} (hts : t₁ ≤ s) {α β f g : ℝ → ℂ}
    (hf : IntegrableOn f (Ioc t₁ s)) (hg : IntegrableOn g (Ioc t₁ s))
    (hα : ∀ r ∈ Icc t₁ s, α r - α t₁ = ∫ q in Ioc t₁ r, f q)
    (hβ : ∀ q ∈ Icc t₁ s, β s - β q = ∫ r in Ioc q s, g r) :
    IntegrableOn (fun q => f q * β q + α q * g q) (Ioc t₁ s) ∧
      α s * β s - α t₁ * β t₁ = ∫ q in Ioc t₁ s, (f q * β q + α q * g q) := by
  have hα_cont : ContinuousOn α (Icc t₁ s) := by
    have heq : EqOn α (fun r => α t₁ + ∫ q in Ioc t₁ r, f q) (Icc t₁ s) := fun r hr => by
      linear_combination hα r hr
    exact (continuousOn_const.add (continuousOn_indef_Ioc hts hf)).congr heq
  have hβ_cont : ContinuousOn β (Icc t₁ s) := by
    have hcont_g : ContinuousOn (fun q => ∫ r in Ioc t₁ q, g r) (Icc t₁ s) :=
      continuousOn_indef_Ioc hts hg
    have heq : EqOn β (fun q => β s - (∫ r in Ioc t₁ s, g r) + ∫ r in Ioc t₁ q, g r) (Icc t₁ s) := by
      intro q hq
      have hsplit : ∫ r in Ioc t₁ s, g r = (∫ r in Ioc t₁ q, g r) + ∫ r in Ioc q s, g r := by
        rw [← intervalIntegral.integral_of_le hts, ← intervalIntegral.integral_of_le hq.1,
          ← intervalIntegral.integral_of_le hq.2]
        have hi1 : IntervalIntegrable g volume t₁ q :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hq.1).2
            (hg.mono_set (Ioc_subset_Ioc_right hq.2))
        have hi2 : IntervalIntegrable g volume q s :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hq.2).2
            (hg.mono_set (Ioc_subset_Ioc_left hq.1))
        exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
      linear_combination -(hβ q hq) + hsplit
    exact (continuousOn_const.add hcont_g).congr heq
  obtain ⟨B_α, hBα⟩ := (isCompact_Icc.bddAbove_image hα_cont.norm)
  obtain ⟨B_β, hBβ⟩ := (isCompact_Icc.bddAbove_image hβ_cont.norm)
  have hfβ : IntegrableOn (fun q => f q * β q) (Ioc t₁ s) := by
    refine hf.norm.smul_const B_β |>.mono' ?_ ?_
    · exact hf.aestronglyMeasurable.mul
        ((hβ_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun q hq => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBβ ⟨q, Ioc_subset_Icc_self hq, rfl⟩) (norm_nonneg _)
  have hαg : IntegrableOn (fun q => α q * g q) (Ioc t₁ s) := by
    refine hg.norm.smul_const B_α |>.mono' ?_ ?_
    · exact ((hα_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).mul
        hg.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun q hq => ?_
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hBα ⟨q, Ioc_subset_Icc_self hq, rfl⟩) (norm_nonneg _)
  refine ⟨hfβ.add hαg, ?_⟩
  -- Fubini on `Ioc t₁ s ×ˢ Ioc t₁ s`
  set μ := volume.restrict (Ioc t₁ s)
  have : SFinite μ := inferInstance
  have hprod_int : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) (μ.prod μ) :=
    hf.integrable.mul_prod hg.integrable
  have hS_meas : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hind_int : Integrable ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2))
      (μ.prod μ) :=
    hprod_int.indicator hS_meas
  have hswap := integral_integral_swap
    (f := fun q r => {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2) (q, r)) hind_int
  have hlhs_eq : (∫ q, ∫ r, {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2) (q, r)
      ∂μ ∂μ) = ∫ q in Ioc t₁ s, f q * (β s - β q) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
    have hq_Icc : q ∈ Icc t₁ s := Ioc_subset_Icc_self hq
    -- Restricting to `μ = volume.restrict (Ioc t₁ s)`, `Ioc q s ⊆ Ioc t₁ s`
    have hind_ae : (fun r => {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2) (q, r))
        =ᵐ[μ] (Ioc q s).indicator (fun r => f q * g r) := by
      change ∀ᵐ r ∂(volume.restrict (Ioc t₁ s)), _
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun r hr => ?_
      by_cases hqr : q < r <;> simp [hqr, hr.2]
    rw [integral_congr_ae hind_ae, integral_indicator measurableSet_Ioc]
    dsimp only [μ]
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 (Ioc_subset_Ioc_left hq.1.le),
      integral_const_mul, ← hβ q hq_Icc]
  have hrhs_eq : (∫ r, ∫ q, {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2) (q, r)
      ∂μ ∂μ) = ∫ r in Ioc t₁ s, (α r - α t₁) * g r := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hr_Icc : r ∈ Icc t₁ s := Ioc_subset_Icc_self hr
    have hne : ∀ᵐ q ∂μ, q ≠ r :=
      ae_restrict_of_ae (ae_iff.2 (by simp [measure_singleton] : volume {q | ¬q ≠ r} = 0))
    have hind_ae : (fun q => {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2) (q, r))
        =ᵐ[μ] (Ioc t₁ r).indicator (fun q => f q * g r) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with q hq hqr_ne
      by_cases hqr : q < r
      · simp [hqr, hq.1, hqr.le]
      · have hqm : q ∉ Ioc t₁ r := fun h => hqr (lt_of_le_of_ne h.2 hqr_ne)
        simp [hqr, hqm]
    rw [integral_congr_ae hind_ae, integral_indicator measurableSet_Ioc]
    dsimp only [μ]
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 (Ioc_subset_Ioc_right hr.2),
      integral_mul_const, ← hα r hr_Icc]
  have hfub : ∫ q in Ioc t₁ s, f q * (β s - β q) = ∫ r in Ioc t₁ s, (α r - α t₁) * g r := by
    rw [← hlhs_eq, ← hrhs_eq, hswap]
  have hf_sub : (∫ q in Ioc t₁ s, f q * (β s - β q)) =
      (∫ q in Ioc t₁ s, f q) * β s - ∫ q in Ioc t₁ s, f q * β q := by
    have heq : (fun q => f q * (β s - β q)) = fun q => f q * β s - f q * β q := by
      funext q; ring
    rw [heq, integral_sub (hf.mul_const _) hfβ, integral_mul_const]
  have hg_sub : (∫ r in Ioc t₁ s, (α r - α t₁) * g r) =
      (∫ r in Ioc t₁ s, α r * g r) - α t₁ * ∫ r in Ioc t₁ s, g r := by
    have heq : (fun r => (α r - α t₁) * g r) = fun r => α r * g r - α t₁ * g r := by
      funext r; ring
    rw [heq, integral_sub hαg (hg.const_mul _), integral_const_mul]
  rw [hf_sub, hg_sub, ← hα s ⟨hts, le_rfl⟩, ← hβ t₁ ⟨le_rfl, hts⟩] at hfub
  rw [integral_add hfβ hαg]
  linear_combination hfub

/-! ### 2. Frame pairing FTC + `IntegrableOn` for `0 < ν ≤ 1`, `1 ≤ b ≤ θ(s)` -/

private theorem framePairingFTC_uncond
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    (P : PlanarData) (hP : IsPlanarReference P)
    {ν m b K : ℝ} (hm : 8 < m) (hν : 0 < ν) (hν1 : ν ≤ 1) (hb : 1 ≤ b)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (htr : PartI.IsBUCTrain tr)
    (hBddAll : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    {t₁ s : ℝ} (ht₁ : 0 ≤ t₁) (hts : t₁ ≤ s) (hbs : b ≤ clockTheta ν s)
    {Γ : ℝ × ℝ → ℂ} {Φ : ℝ → ℝ × ℝ → ℂ}
    (hΓ : MemLp Γ 2 (B0579.cellMeasure (dd ν s) (-m)))
    (hΦ : MovingFreeAdjoint ν m tr t₁ s Γ Φ) (j : Fin 2) :
    let ψ : ℝ → ℂ := fun q =>
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ∫ y in B0579.cell (dd ν q),
          (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y
    IntegrableOn ψ (Ioc t₁ s) ∧
      ∀ r ∈ Icc t₁ s, ∀ s' ∈ Icc r s,
        (∫ y in B0579.cell (dd ν s'), perE κ (dd ν s') j y * Φ s' y) -
            ∫ y in B0579.cell (dd ν r), perE κ (dd ν r) j y * Φ r y =
          ∫ q in Ioc r s', ψ q := by
  intro ψ
  obtain ⟨φ, hφ, hΦ_ae⟩ := hΦ
  let c : ℝ := ν ^ (-2 : ℝ)
  have hs0 : 0 ≤ s := ht₁.trans hts
  obtain ⟨C_tr, hBdd⟩ := hBddAll s hs0
  obtain ⟨K_cut, hK0, hK⟩ := ladCutProps
  have hp_cut : ∀ R' : ℝ, 0 < R' → ∀ (x : ℝ × ℝ) (k : Fin 2),
      |B0579.pd k (ladCut R') x| ≤ K_cut / R' :=
    fun R' hR' x k => (hK R' hR').2.2.2.2.1 x k
  have hl_cut : ∀ R' : ℝ, 0 < R' → ∀ x : ℝ × ℝ, |lapP (ladCut R') x| ≤ K_cut / R' ^ 2 :=
    fun R' hR' x => (hK R' hR').2.2.2.2.2 x
  obtain ⟨M_col, hMcol0, hUnif⟩ :=
    physFrameE_uniform_xNorm hκ hm hb ⟨hν, hν1⟩ hs0 hbs hBdd
  obtain ⟨B_φ, hBφ0, hBφ⟩ :=
    RateBoundAux.bdd_of_cont (RateBoundAux.contOn_norm φ hφ.memX hφ.strongCont)
  have hRate_all : ∀ q ∈ Icc t₁ s,
      Tendsto (fun R => FramePairing1Aux.cutRate κ tr φ R j q) atTop
        (𝓝 (∫ x in B0579.cell c, physFrameERate κ tr q j x * φ q x)) ∧
      ∀ R : ℝ, 1 ≤ R →
        ‖FramePairing1Aux.cutRate κ tr φ R j q‖ ≤
          M_col * B_φ + (3 * |ν| * K_cut + 2 * |C_tr| * K_cut) * (3 * (M_col * B_φ)) := by
    intro q hq
    obtain ⟨⟨hE_m, hE_n⟩, hpd, ⟨hR_m, hR_n⟩⟩ := hUnif q ⟨ht₁.trans hq.1, hq.2⟩ j
    exact cutRate_tendsto_and_bound hκ hν ht₁ hMcol0 hBφ0 hBdd hφ hBφ
      K_cut hK0 hp_cut hl_cut j hq hE_m hE_n (fun k => (hpd k).1) (fun k => (hpd k).2) hR_m hR_n
  set M_tot : ℝ := M_col * B_φ + (3 * |ν| * K_cut + 2 * |C_tr| * K_cut) * (3 * (M_col * B_φ))
  have hM_tot0 : 0 ≤ M_tot := by positivity
  have hψ_eq : ∀ q ∈ Icc t₁ s,
      ψ q = ∫ x in B0579.cell c, physFrameERate κ tr q j x * φ q x := by
    intro q hq
    have hq0 : 0 ≤ q := ht₁.trans hq.1
    have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hq0)
    set Res : ℝ × ℝ → ℂ := fun y =>
      interactionTerm tr q (perE κ (dd ν q) j) y -
        (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
          modeEigen P j * perE κ (dd ν q) j y)
    have hrate_eq : ∀ x : ℝ × ℝ, physFrameERate κ tr q j x * φ q x =
        (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * (Jscale (clockA ν q) Res x * φ q x) := by
      intro x
      rw [physFrameERate_eq_jscale hκ P hν hq0 tr j x, mul_assoc]
    have hae_q : (fun y => Res y * Φ q y) =ᵐ[volume.restrict (B0579.cell (dd ν q))]
        fun y => Res y * movingPhi ν φ q y := by
      filter_upwards [hΦ_ae q hq] with y hy
      rw [hy]
    dsimp only [ψ]
    rw [integral_congr_ae (Eventually.of_forall hrate_eq), integral_const_mul,
      ← cell_pair_jscale_movingPhi hν ha Res φ, integral_congr_ae hae_q.symm]
  have hψ_int : IntegrableOn ψ (Ioc t₁ s) := by
    rcases eq_or_lt_of_le hts with rfl | ht₁s
    · simp
    have hmeas_seq : ∀ n : ℕ,
        AEStronglyMeasurable (FramePairing1Aux.cutRate κ tr φ ((n : ℝ) + 1) j) (volume.restrict (Ioo t₁ s)) := by
      intro n
      have hR0 : 0 < (n : ℝ) + 1 := by positivity
      exact (continuousOn_cutRate hκ hν ht₁ hR0 hφ j).aestronglyMeasurable measurableSet_Ioo
    have hlim_ae : ∀ᵐ q ∂(volume.restrict (Ioo t₁ s)),
        Tendsto (fun n : ℕ => FramePairing1Aux.cutRate κ tr φ ((n : ℝ) + 1) j q) atTop (𝓝 (ψ q)) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Eventually.of_forall fun q hq => ?_
      have hqI : q ∈ Icc t₁ s := Ioo_subset_Icc_self hq
      rw [hψ_eq q hqI]
      have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact (hRate_all q hqI).1.comp hnat
    have hmeas_ψ : AEStronglyMeasurable ψ (volume.restrict (Ioo t₁ s)) :=
      aestronglyMeasurable_of_tendsto_ae atTop hmeas_seq hlim_ae
    have hbnd_ψ : ∀ᵐ q ∂(volume.restrict (Ioo t₁ s)), ‖ψ q‖ ≤ M_tot := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Eventually.of_forall fun q hq => ?_
      have hqI : q ∈ Icc t₁ s := Ioo_subset_Icc_self hq
      rw [hψ_eq q hqI]
      exact le_of_tendsto (hRate_all q hqI).1.norm
        (eventually_atTop.2 ⟨1, (hRate_all q hqI).2⟩)
    exact (IntegrableOn.of_bound measure_Ioo_lt_top hmeas_ψ M_tot hbnd_ψ).congr_set_ae
      Ioo_ae_eq_Ioc.symm
  refine ⟨hψ_int, fun r hr s' hs' => ?_⟩
  rcases eq_or_lt_of_le hs'.1 with rfl | hrs'_lt
  · simp
  -- Same FTC as `FramePairing1.framePairingFTC_proof`
  have hIoo_sub : Ioo r s' ⊆ Ioo t₁ s :=
    fun q hq => ⟨lt_of_le_of_lt hr.1 hq.1, lt_of_lt_of_le hq.2 hs'.2⟩
  have hIcc_sub : Icc r s' ⊆ Icc t₁ s := Icc_subset_Icc hr.1 hs'.2
  have hftc : ∀ R : ℝ, 1 ≤ R →
      IntervalIntegrable (FramePairing1Aux.cutRate κ tr φ R j) volume r s' ∧
        ∫ q in r..s', FramePairing1Aux.cutRate κ tr φ R j q =
          cutPair κ ν φ R j s' - cutPair κ ν φ R j r := by
    intro R hR1
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hcont_rate : ContinuousOn (FramePairing1Aux.cutRate κ tr φ R j) (Ioo r s') :=
      (continuousOn_cutRate hκ hν ht₁ hR0 hφ j).mono hIoo_sub
    have hmeas_Ioo : AEStronglyMeasurable (FramePairing1Aux.cutRate κ tr φ R j) (volume.restrict (Ioo r s')) :=
      hcont_rate.aestronglyMeasurable measurableSet_Ioo
    have hconst_Ioo : IntegrableOn (fun _ : ℝ => M_tot) (Ioo r s') volume := by
      apply integrableOn_const <;> first | exact enorm_ne_top | exact measure_Ioo_lt_top.ne
    have hbnd_Ioo : ∀ᵐ q ∂(volume.restrict (Ioo r s')), ‖FramePairing1Aux.cutRate κ tr φ R j q‖ ≤ M_tot := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall fun q hq =>
        (hRate_all q (hIcc_sub (Ioo_subset_Icc_self hq))).2 R hR1
    have hint_Ioo : IntegrableOn (FramePairing1Aux.cutRate κ tr φ R j) (Ioo r s') volume :=
      hconst_Ioo.mono' hmeas_Ioo hbnd_Ioo
    have hint_Ioc : IntegrableOn (FramePairing1Aux.cutRate κ tr φ R j) (Ioc r s') volume :=
      (integrableOn_Ioc_iff_integrableOn_Ioo (hb := enorm_ne_top)).2 hint_Ioo
    have hint_R : IntervalIntegrable (FramePairing1Aux.cutRate κ tr φ R j) volume r s' :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hrs'_lt.le).2 hint_Ioc
    have hcont_pair : ContinuousOn (cutPair κ ν φ R j) (Icc r s') :=
      (continuousOn_cutPair hκ hν ht₁ hR0 hφ j).mono hIcc_sub
    have hderiv_pair : ∀ q ∈ Ioo r s',
        HasDerivAt (cutPair κ ν φ R j) (FramePairing1Aux.cutRate κ tr φ R j q) q :=
      fun q hq => hasDerivAt_cutPair hκ hν ht₁ hR0 hφ j (hIoo_sub hq)
    exact ⟨hint_R,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrs'_lt.le hcont_pair hderiv_pair hint_R⟩
  have hI : Ι r s' = Ioc r s' := Set.uIoc_of_le hrs'_lt.le
  have hne_s' : ∀ᵐ q ∂volume, q ≠ s' := ae_iff.2 (by simp [measure_singleton])
  have hlim_int : Tendsto (fun R => ∫ q in r..s', FramePairing1Aux.cutRate κ tr φ R j q) atTop
      (𝓝 (∫ q in r..s', ∫ x in B0579.cell c, physFrameERate κ tr q j x * φ q x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := fun R q => FramePairing1Aux.cutRate κ tr φ R j q)
      (f := fun q => ∫ x in B0579.cell c, physFrameERate κ tr q j x * φ q x)
      (fun _ => M_tot) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      exact (intervalIntegrable_iff.mp (hftc R hR1).1).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      filter_upwards [hne_s'] with q hqs' hqI
      rw [hI] at hqI
      exact (hRate_all q (hIcc_sub (Ioc_subset_Icc_self hqI))).2 R hR1
    · filter_upwards [hne_s'] with q hqs' hqI
      rw [hI] at hqI
      exact (hRate_all q (hIcc_sub (Ioc_subset_Icc_self hqI))).1
  have hs'_Icc : s' ∈ Icc t₁ s := ⟨hr.1.trans hs'.1, hs'.2⟩
  have hE_s' := (hUnif s' ⟨ht₁.trans hs'_Icc.1, hs'_Icc.2⟩ j).1.1
  have hE_r := (hUnif r ⟨ht₁.trans hr.1, hr.2⟩ j).1.1
  have hlim_s' : Tendsto (fun R => cutPair κ ν φ R j s') atTop
      (𝓝 (∫ x in B0579.cell c, physFrameE κ ν s' j x * φ s' x)) := by
    have hpt : ∀ R x, cutCol κ ν R s' j x * φ s' x =
        physFrameE κ ν s' j x * ((ladCut R x : ℂ) * φ s' x) := fun R x => by
      unfold cutCol ladCutPhi; ring
    simp_rw [cutPair, hpt]
    exact ladCutLimit c m (physFrameE κ ν s' j) (φ s') hE_s' (hφ.memX s' hs'_Icc)
  have hlim_r : Tendsto (fun R => cutPair κ ν φ R j r) atTop
      (𝓝 (∫ x in B0579.cell c, physFrameE κ ν r j x * φ r x)) := by
    have hpt : ∀ R x, cutCol κ ν R r j x * φ r x =
        physFrameE κ ν r j x * ((ladCut R x : ℂ) * φ r x) := fun R x => by
      unfold cutCol ladCutPhi; ring
    simp_rw [cutPair, hpt]
    exact ladCutLimit c m (physFrameE κ ν r j) (φ r) hE_r (hφ.memX r hr)
  have hlim_diff : Tendsto (fun R => ∫ q in r..s', FramePairing1Aux.cutRate κ tr φ R j q) atTop
      (𝓝 ((∫ x in B0579.cell c, physFrameE κ ν s' j x * φ s' x) -
        ∫ x in B0579.cell c, physFrameE κ ν r j x * φ r x)) := by
    refine (hlim_s'.sub hlim_r).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    exact (hftc R hR1).2.symm
  have hphys_ftc : (∫ x in B0579.cell c, physFrameE κ ν s' j x * φ s' x) -
      ∫ x in B0579.cell c, physFrameE κ ν r j x * φ r x =
      ∫ q in r..s', ∫ x in B0579.cell c, physFrameERate κ tr q j x * φ q x :=
    tendsto_nhds_unique hlim_diff hlim_int
  have hend_eq : ∀ q₀ ∈ Icc t₁ s,
      ∫ y in B0579.cell (dd ν q₀), perE κ (dd ν q₀) j y * Φ q₀ y =
        ∫ x in B0579.cell c, physFrameE κ ν q₀ j x * φ q₀ x := by
    intro q₀ hq₀
    have ha : 0 < clockA ν q₀ :=
      lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht₁.trans hq₀.1))
    have hae : (fun y => perE κ (dd ν q₀) j y * Φ q₀ y) =ᵐ[volume.restrict (B0579.cell (dd ν q₀))]
        fun y => perE κ (dd ν q₀) j y * movingPhi ν φ q₀ y := by
      filter_upwards [hΦ_ae q₀ hq₀] with y hy
      rw [hy]
    rw [integral_congr_ae hae, cell_pair_jscale_movingPhi hν ha]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      rw [physFrameE_eq_jscale_perE κ ha j x])
  rw [hend_eq s' hs'_Icc, hend_eq r hr, hphys_ftc, intervalIntegral.integral_of_le hrs'_lt.le]
  exact setIntegral_congr_fun measurableSet_Ioc fun q hq =>
    (hψ_eq q (hIcc_sub (Ioc_subset_Icc_self hq))).symm

end Leaf2WeakEqProof

open Leaf2WeakEqProof Leaf2WeakEqFrame Leaf2WeakEqFrame.FramePairing1Aux in
/-- **`PartIII-a:T21/c3/3/1/1/2/2/3`** (SP 2898-2958): `ComplWeakEq`. -/
theorem complWeakEq (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.ComplWeakEq κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0 := by
  intro hκ hP hm hb htr ht₁ ht₁₂ hbt₂ hBddAll hForceFin f w u hw hf0 hAmplFTC _hLoc _hH0
    s hs Γ Φ hΓ hΦ hInt
  rcases eq_or_lt_of_le hs.1 with rfl | ht₁s
  · rw [Ioc_self, setIntegral_empty, add_zero]
    obtain ⟨φ, hφ, hΦ_ae⟩ := hΦ
    have ha : 0 < clockA ν t₁ := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le ht₁)
    have hΓ_eq : Γ = movingPhi ν (fun _ => physAdj (clockA ν t₁) Γ) t₁ := by
      funext y
      have hsa : Real.sqrt (clockA ν t₁) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
      unfold movingPhi physAdj
      have haC : (clockA ν t₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ haC, one_mul, mul_div_cancel_left₀ _ hsa,
        mul_div_cancel_left₀ _ hsa]
    have hae_Φ : (fun y => compl (periodizedFrame κ ν m b K hν hF) w t₁ y * Φ t₁ y) =ᵐ[
          volume.restrict (B0579.cell (dd ν t₁))]
        fun y => compl (periodizedFrame κ ν m b K hν hF) w t₁ y * movingPhi ν φ t₁ y := by
      filter_upwards [hΦ_ae t₁ ⟨le_rfl, le_rfl⟩] with y hy; rw [hy]
    have hae_term : (fun x => Jscale (clockA ν t₁) (compl (periodizedFrame κ ν m b K hν hF) w t₁) x *
          φ t₁ x) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
        fun x => Jscale (clockA ν t₁) (compl (periodizedFrame κ ν m b K hν hF) w t₁) x *
          physAdj (clockA ν t₁) Γ x := by
      filter_upwards [hφ.terminal] with x hx; rw [hx]
    rw [integral_congr_ae hae_Φ, cell_pair_jscale_movingPhi hν ha, integral_congr_ae hae_term,
      ← cell_pair_jscale_movingPhi hν ha _ (fun _ => physAdj (clockA ν t₁) Γ)]
    conv_lhs => rw [hΓ_eq]
  have hs0 : 0 ≤ s := ht₁.trans hs.1
  have hbs : b ≤ clockTheta ν s := hbt₂.trans (theta_anti hν hs0 hs.2)
  have hν1 : ν ≤ 1 := by
    have ha1 : 1 ≤ clockA ν s := one_le_clockA hν.le hs0
    have hθ1 : 1 ≤ clockTheta ν s := hb.trans hbs
    have hle : clockTheta ν s ≤ ν⁻¹ := by
      unfold clockTheta
      exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha1)
    exact (one_le_inv₀ hν).mp (hθ1.trans hle)
  let F := periodizedFrame κ ν m b K hν hF
  obtain ⟨φ, hφ, hΦ_ae⟩ := hΦ
  -- 1. Pairing of `movingW` against `Φ`
  have hJw_eq : ∀ r : ℝ, 0 < clockA ν r → Jscale (clockA ν r) (movingW ν w r) = w r := by
    intro r ha
    funext x
    have hsa : Real.sqrt (clockA ν r) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
    unfold Jscale movingW JscaleInv
    have h1 : clockA ν r ^ (-2 : ℝ) * clockA ν r ^ 2 = 1 := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')
    rw [mul_div_cancel₀ _ hsa, mul_div_cancel₀ _ hsa, ← mul_assoc, ← Complex.ofReal_mul, h1,
      Complex.ofReal_one, one_mul]
  have hW_pair : ∀ r ∈ Icc t₁ s,
      ∫ y in B0579.cell (dd ν r), movingW ν w r y * Φ r y =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * φ r x := by
    intro r hr
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht₁.trans hr.1))
    have hae : (fun y => movingW ν w r y * Φ r y) =ᵐ[volume.restrict (B0579.cell (dd ν r))]
        fun y => movingW ν w r y * movingPhi ν φ r y := by
      filter_upwards [hΦ_ae r hr] with y hy
      rw [hy]
    rw [integral_congr_ae hae, cell_pair_jscale_movingPhi hν ha (movingW ν w r) φ, hJw_eq r ha]
  have hW_s : ∫ y in B0579.cell (dd ν s), movingW ν w s y * Γ y =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * physAdj (clockA ν s) Γ x := by
    have ha : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hs0)
    have hΓ_eq : Γ = movingPhi ν (fun _ => physAdj (clockA ν s) Γ) s := by
      funext y
      have hc0 : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
      have hsa : Real.sqrt (clockA ν s) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
      unfold movingPhi physAdj
      have haC : (clockA ν s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ haC, one_mul, mul_div_cancel_left₀ _ hsa,
        mul_div_cancel_left₀ _ hsa]
    conv_lhs => rw [hΓ_eq]
    rw [cell_pair_jscale_movingPhi hν ha (movingW ν w s) (fun _ => physAdj (clockA ν s) Γ),
      hJw_eq s ha]
  have hLin := Leaf2WeakEqNeeded.linFreeAdjPairing ν m tr t₁ t₂ hm hν ht₁ ht₁₂ htr hBddAll
    f w u hw hf0 s hs (physAdj (clockA ν s) Γ) φ hφ t₁ ⟨le_rfl, hs.1⟩
  have hMovInt := Leaf2WeakEqFrame.movingInteractionForm_proof ν m tr t₁ hm hν ht₁ htr
    f w u hw hf0 s (physAdj (clockA ν s) Γ) φ hφ
  have hW_eq : (∫ y in B0579.cell (dd ν s), movingW ν w s y * Γ y) -
      (∫ y in B0579.cell (dd ν t₁), movingW ν w t₁ y * Φ t₁ y) =
      ∫ q in Ioc t₁ s, (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ∫ y in B0579.cell (dd ν q), interactionTerm tr q (movingW ν w q) y * Φ q y := by
    rw [hW_s, hW_pair t₁ ⟨le_rfl, hs.1⟩, hLin, sub_sub_cancel_left]
    rw [← intervalIntegral.integral_of_le hs.1, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_iff.2 (by simp [measure_singleton] : volume {q | ¬q ≠ s} = 0)] with q hqs hqI
    rw [Set.uIoc_of_le hs.1] at hqI
    have hq_Ico : q ∈ Ico t₁ s := ⟨hqI.1.le, lt_of_le_of_ne hqI.2 hqs⟩
    have hq_Icc : q ∈ Icc t₁ s := Ioc_subset_Icc_self hqI
    rw [hMovInt q hq_Ico, neg_neg]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hΦ_ae q hq_Icc] with y hy
    rw [hy]
  -- 2. Fubini product rule for `∑ j, α_j * ⟨E_j, Φ⟩`
  have hE_ftc : ∀ j : Fin 2, _ := fun j =>
    framePairingFTC_uncond κ hκ P hP hm hν hν1 hb (K := K) tr htr hBddAll ht₁ hs.1 hbs hΓ
      ⟨φ, hφ, hΦ_ae⟩ j
  have hα_int : ∀ j : Fin 2,
      IntegrableOn (fun q => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        movH0 κ tr q j (movingW ν w q)) (Ioc t₁ s) :=
    fun j => Leaf2WeakEqAmplInt.integrableOn_amplRate κ hκ hm hν hb hF tr htr hBddAll ht₁ hs
      hbt₂ hw hf0 j
  have hprod_j : ∀ j : Fin 2,
      IntegrableOn (fun q =>
        ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q j (movingW ν w q)) *
          (∫ y in B0579.cell (dd ν q), perE κ (dd ν q) j y * Φ q y) +
        ampl F w q j * ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν q),
            (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) * Φ q y)) (Ioc t₁ s) ∧
      ampl F w s j * (∫ y in B0579.cell (dd ν s), perE κ (dd ν s) j y * Γ y) -
        ampl F w t₁ j * (∫ y in B0579.cell (dd ν t₁), perE κ (dd ν t₁) j y * Φ t₁ y) =
      ∫ q in Ioc t₁ s,
        ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q j (movingW ν w q)) *
          (∫ y in B0579.cell (dd ν q), perE κ (dd ν q) j y * Φ q y) +
        ampl F w q j * ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν q),
            (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) * Φ q y) := by
    intro j
    have hΓ_Φ : ∫ y in B0579.cell (dd ν s), perE κ (dd ν s) j y * Γ y =
        ∫ y in B0579.cell (dd ν s), perE κ (dd ν s) j y * Φ s y := by
      have ha : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hs0)
      have hae : (fun y => perE κ (dd ν s) j y * Φ s y) =ᵐ[volume.restrict (B0579.cell (dd ν s))]
          fun y => perE κ (dd ν s) j y * movingPhi ν φ s y := by
        filter_upwards [hΦ_ae s ⟨hs.1, le_rfl⟩] with y hy
        rw [hy]
      have hΓ_eq : Γ = movingPhi ν (fun _ => physAdj (clockA ν s) Γ) s := by
        funext y
        have hsa : Real.sqrt (clockA ν s) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
        unfold movingPhi physAdj
        have haC : (clockA ν s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
        push_cast
        rw [← mul_assoc, inv_mul_cancel₀ haC, one_mul, mul_div_cancel_left₀ _ hsa,
        mul_div_cancel_left₀ _ hsa]
      have hae_term : (fun x => Jscale (clockA ν s) (perE κ (dd ν s) j) x * φ s x) =ᵐ[
            volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
          fun x => Jscale (clockA ν s) (perE κ (dd ν s) j) x * physAdj (clockA ν s) Γ x := by
        filter_upwards [hφ.terminal] with x hx
        rw [hx]
      rw [integral_congr_ae hae, cell_pair_jscale_movingPhi hν ha,
        integral_congr_ae hae_term,
        ← cell_pair_jscale_movingPhi hν ha (perE κ (dd ν s) j) (fun _ => physAdj (clockA ν s) Γ),
        ← hΓ_eq]
    have hfib := fubini_ibp
      (β := fun q => ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) j y * Φ q y)
      hs.1 (hα_int j) (hE_ftc j).1
      (fun r hr => hAmplFTC t₁ ⟨le_rfl, ht₁₂⟩ r ⟨hr.1, hr.2.trans hs.2⟩ j)
      (fun q hq => (hE_ftc j).2 q hq s ⟨hq.2, le_rfl⟩)
    rwa [← hΓ_Φ] at hfib
  -- 3. Combine Step A (`hW_eq`), Step B (`hprod_j`), and `h0ModeIdentity_of`
  have hH0Id : Leaf2WeakEqNeeded.H0ModeIdentity κ P ν b tr :=
    Leaf2WeakEqNeeded.h0ModeIdentity_of κ P hκ hm hν hF tr hBddAll
  have hint_pair : ∀ (d : ℝ) (g₁ g₂ : ℝ × ℝ → ℂ),
      MemLp g₁ 2 (B0579.cellMeasure d m) →
      MemLp g₂ 2 (B0579.cellMeasure d (-m)) →
      IntegrableOn (fun y => g₁ y * g₂ y) (B0579.cell d) volume := by
    intro d g₁ g₂ hg₁ hg₂
    have hnorm := CommVanishAux.integrableOn_cell_norm_mul d m hg₁ hg₂
    refine hnorm.mono' ?_ (Eventually.of_forall fun y => by simp)
    exact (hg₁.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d m)).mul
      (hg₂.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d (-m)))
  have hmem_Phi : ∀ q ∈ Icc t₁ s, MemLp (Φ q) 2 (B0579.cellMeasure (dd ν q) (-m)) := by
    intro q hq
    have hq0 : 0 ≤ q := ht₁.trans hq.1
    have ha1 : 1 ≤ clockA ν q := one_le_clockA hν.le hq0
    have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one ha1
    have hs_pos : 0 < Real.sqrt (clockA ν q) := Real.sqrt_pos.mpr ha
    have hsq : Real.sqrt (clockA ν q) ^ 2 = clockA ν q := Real.sq_sqrt ha.le
    set c : ℝ := ν ^ (-2 : ℝ)
    set s_a : ℝ := Real.sqrt (clockA ν q)
    have hΦ_ae_cell : Φ q =ᵐ[B0579.cellMeasure (dd ν q) (-m)] movingPhi ν φ q :=
      (B0579.cellMeasure_ac (dd ν q) (-m)) (hΦ_ae q hq)
    rw [memLp_congr_ae hΦ_ae_cell]
    have hφ_m : MemLp (φ q) 2 (B0579.cellMeasure c (-m)) := hφ.memX q hq
    have hφ_ind_aesm : AEStronglyMeasurable ((B0579.cell c).indicator (φ q)) volume :=
      (aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell c)).2
        (hφ_m.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m)))
    set ψ₁ := hφ_ind_aesm.mk ((B0579.cell c).indicator (φ q))
    have hψ₁_meas : Measurable ψ₁ := hφ_ind_aesm.stronglyMeasurable_mk.measurable
    have hψ₁_ae : (B0579.cell c).indicator (φ q) =ᵐ[volume] ψ₁ := hφ_ind_aesm.ae_eq_mk
    have hqmp : Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ => s_a • y) volume volume := by
      refine ⟨measurable_const_smul s_a, ?_⟩
      rw [Measure.map_addHaar_smul volume hs_pos.ne']
      exact Measure.smul_absolutelyContinuous
    have h_ae_smul : (fun y : ℝ × ℝ => (B0579.cell c).indicator (φ q) (s_a • y)) =ᵐ[volume]
        fun y : ℝ × ℝ => ψ₁ (s_a • y) := hqmp.ae_eq_comp hψ₁_ae
    have h_cell_mem : ∀ y ∈ B0579.cell (dd ν q), s_a • y ∈ B0579.cell c := by
      intro y hy
      simp only [B0579.cell, dd, cellLen, Set.mem_prod, Set.mem_univ, and_true, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul, Set.mem_Ico] at hy ⊢
      have e : c / 2 = (c / s_a / 2) * s_a := by field_simp [hs_pos.ne']
      have e' : -(c / 2) = -(c / s_a / 2) * s_a := by rw [e]; ring
      rw [e', e]
      exact ⟨by nlinarith, by nlinarith⟩
    have h_mov_ae : movingPhi ν φ q =ᵐ[B0579.cellMeasure (dd ν q) (-m)]
        fun y : ℝ × ℝ => (((clockA ν q)⁻¹ : ℝ) : ℂ) * ψ₁ (s_a • y) := by
      refine (B0579.cellMeasure_ac (dd ν q) (-m)) ?_
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell (dd ν q)),
        ae_restrict_of_ae (hqmp.ae_eq_comp hψ₁_ae)] with y hy hψy
      have hsm : s_a • y = (s_a * y.1, s_a * y.2) := rfl
      dsimp only [Function.comp_def] at hψy
      unfold movingPhi
      rw [← hsm, ← hψy, Set.indicator_of_mem (h_cell_mem y hy)]
    rw [memLp_congr_ae h_mov_ae]
    have h_meas_rhs : Measurable (fun y : ℝ × ℝ => (((clockA ν q)⁻¹ : ℝ) : ℂ) * ψ₁ (s_a • y)) :=
      measurable_const.mul (hψ₁_meas.comp (measurable_const_smul s_a))
    refine ⟨h_meas_rhs.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [B0579.cellMeasure, lintegral_withDensity_eq_lintegral_mul₀
      (B0579.measurable_density (-m)).coe_nnreal_ennreal.aemeasurable
      (h_meas_rhs.enorm.pow_const 2).aemeasurable]
    have h_jb_le : ∀ y : ℝ × ℝ, (B0579.density (-m) y : ℝ≥0∞) ≤
        ENNReal.ofReal (clockA ν q ^ m) * (B0579.density (-m) (s_a • y) : ℝ≥0∞) := by
      intro y
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le m)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [B0579.coe_density, B0579.coe_density]
      have hjb_le : B0579.jb (s_a • y) ≤ clockA ν q * B0579.jb y := by
        simp only [B0579.jb, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have h1 : (s_a * y.1) ^ 2 = clockA ν q * y.1 ^ 2 := by rw [mul_pow, hsq]
        have h2 : (s_a * y.2) ^ 2 = clockA ν q * y.2 ^ 2 := by rw [mul_pow, hsq]
        rw [h1, h2]
        nlinarith
      have hpow := Real.rpow_le_rpow_of_nonpos (B0579.jb_pos _) hjb_le (by linarith : -m ≤ 0)
      rw [Real.mul_rpow ha.le (B0579.jb_pos y).le] at hpow
      calc B0579.jb y ^ (-m) = clockA ν q ^ m * (clockA ν q ^ (-m) * B0579.jb y ^ (-m)) := by
            rw [← mul_assoc, ← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero, one_mul]
        _ ≤ clockA ν q ^ m * B0579.jb (s_a • y) ^ (-m) :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg ha.le m)
    set C_sc : ℝ≥0∞ := ENNReal.ofReal (clockA ν q ^ m) * ‖(((clockA ν q)⁻¹ : ℝ) : ℂ)‖ₑ ^ 2
    have hC_sc : C_sc < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr enorm_ne_top))
    have h_int_le : ∫⁻ y in B0579.cell (dd ν q),
          (B0579.density (-m) y : ℝ≥0∞) * ‖(((clockA ν q)⁻¹ : ℝ) : ℂ) * ψ₁ (s_a • y)‖ₑ ^ 2 ≤
        C_sc * ∫⁻ y, (B0579.cell c).indicator
          (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2) (s_a • y) := by
      rw [← lintegral_indicator (B0579.measurableSet_cell (dd ν q)), ← lintegral_const_mul' _ _ hC_sc.ne]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ B0579.cell (dd ν q)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h_cell_mem y hy), enorm_mul, mul_pow]
        calc (B0579.density (-m) y : ℝ≥0∞) * (‖(((clockA ν q)⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 * ‖ψ₁ (s_a • y)‖ₑ ^ 2)
            ≤ (ENNReal.ofReal (clockA ν q ^ m) * (B0579.density (-m) (s_a • y) : ℝ≥0∞)) *
                (‖(((clockA ν q)⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 * ‖ψ₁ (s_a • y)‖ₑ ^ 2) := by
              gcongr; exact h_jb_le y
          _ = C_sc * ((B0579.density (-m) (s_a • y) : ℝ≥0∞) * ‖ψ₁ (s_a • y)‖ₑ ^ 2) := by ring
      · rw [Set.indicator_of_notMem hy]; simp
    refine lt_of_le_of_lt h_int_le (ENNReal.mul_lt_top hC_sc ?_)
    have hG_meas : Measurable ((B0579.cell c).indicator
        (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2)) :=
      ((B0579.measurable_density (-m)).coe_nnreal_ennreal.mul
        (hψ₁_meas.enorm.pow_const 2)).indicator (B0579.measurableSet_cell c)
    let t := ((Homeomorph.smul (isUnit_iff_ne_zero.2 hs_pos.ne').unit).toMeasurableEquiv :
      (ℝ × ℝ) ≃ᵐ (ℝ × ℝ))
    have ht_eq : ∫⁻ y, (B0579.cell c).indicator
          (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2) (s_a • y) =
        ENNReal.ofReal |(s_a ^ Module.finrank ℝ (ℝ × ℝ))⁻¹| *
          ∫⁻ x, (B0579.cell c).indicator
            (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2) x := by
      have hmap : ∫⁻ y, (B0579.cell c).indicator
            (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2) (t y) =
          ∫⁻ x, (B0579.cell c).indicator
            (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2) x ∂(Measure.map t volume) :=
        (lintegral_map' hG_meas.aemeasurable t.measurable.aemeasurable).symm
      have ht_smul : (t : (ℝ × ℝ) → (ℝ × ℝ)) = fun y => s_a • y := funext fun _ => rfl
      rw [ht_smul] at hmap
      simpa [Measure.map_addHaar_smul volume hs_pos.ne', lintegral_smul_measure] using hmap
    rw [ht_eq]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have h_ae_ind : (B0579.cell c).indicator
          (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖ψ₁ x‖ₑ ^ 2) =ᵐ[volume]
        (B0579.cell c).indicator
          (fun x => (B0579.density (-m) x : ℝ≥0∞) * ‖φ q x‖ₑ ^ 2) := by
      filter_upwards [hψ₁_ae] with x hx
      by_cases hx_c : x ∈ B0579.cell c
      · simp only [Set.indicator_of_mem hx_c] at hx ⊢; rw [hx]
      · simp [Set.indicator_of_notMem hx_c]
    have h_wd : ∫⁻ a in B0579.cell c, (B0579.density (-m) a : ℝ≥0∞) * ‖φ q a‖ₑ ^ 2 =
        ∫⁻ a, ‖φ q a‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m)) :=
      (lintegral_withDensity_eq_lintegral_mul₀
        (B0579.measurable_density (-m)).coe_nnreal_ennreal.aemeasurable
        ((hφ_m.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m))).enorm.pow_const 2)).symm
    rw [lintegral_congr_ae h_ae_ind, lintegral_indicator (B0579.measurableSet_cell c), h_wd]
    have h_lt := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mp
      hφ_m.2
    simpa [B0579.cellMeasure, ENNReal.toReal_ofNat, ENNReal.rpow_two] using h_lt
  have hθ_le : ∀ {s₀ t₀ : ℝ}, 0 ≤ s₀ → s₀ ≤ t₀ → clockTheta ν t₀ ≤ clockTheta ν s₀ := by
    intro s₀ t₀ hs₀ hst₀
    unfold clockTheta clockA
    have h1 : 0 < ν * (1 + ν * s₀) := by positivity
    exact inv_anti₀ h1 (by nlinarith [mul_le_mul_of_nonneg_left hst₀ (mul_self_nonneg ν)])
  have hL_pair : (∫ y in B0579.cell (dd ν s), compl F w s y * Γ y) -
      (∫ y in B0579.cell (dd ν t₁), compl F w t₁ y * Φ t₁ y) =
      ((∫ y in B0579.cell (dd ν s), movingW ν w s y * Γ y) -
        (∫ y in B0579.cell (dd ν t₁), movingW ν w t₁ y * Φ t₁ y)) -
      ((ampl F w s 0 * (∫ y in B0579.cell (dd ν s), perE κ (dd ν s) 0 y * Γ y) -
        ampl F w t₁ 0 * (∫ y in B0579.cell (dd ν t₁), perE κ (dd ν t₁) 0 y * Φ t₁ y)) +
       (ampl F w s 1 * (∫ y in B0579.cell (dd ν s), perE κ (dd ν s) 1 y * Γ y) -
        ampl F w t₁ 1 * (∫ y in B0579.cell (dd ν t₁), perE κ (dd ν t₁) 1 y * Φ t₁ y))) := by
    have hpair_eq : ∀ (r : ℝ) (hr0 : 0 ≤ r) (hrb : b ≤ clockTheta ν r) (htr_r : t₁ ≤ r)
        (Ψ : ℝ × ℝ → ℂ) (hΨ : MemLp Ψ 2 (B0579.cellMeasure (dd ν r) (-m))),
        ∫ y in B0579.cell (dd ν r), compl F w r y * Ψ y =
          (∫ y in B0579.cell (dd ν r), movingW ν w r y * Ψ y) -
            (ampl F w r 0 * (∫ y in B0579.cell (dd ν r), perE κ (dd ν r) 0 y * Ψ y) +
              ampl F w r 1 * (∫ y in B0579.cell (dd ν r), perE κ (dd ν r) 1 y * Ψ y)) := by
      intro r hr0 hrb htr_r Ψ hΨ
      have hW_mem := ComplCouplingSub.memLp_movingW (le_trans (by norm_num) hm.le) hν ht₁ htr_r hw
      have hE_mem : ∀ j : Fin 2, MemLp (perE κ (dd ν r) j) 2 (B0579.cellMeasure (dd ν r) m) :=
        fun j => ComplCouplingSub.memLp_frame_E F hr0 hrb j
      have hiW := hint_pair (dd ν r) (movingW ν w r) Ψ hW_mem hΨ
      have hiE : ∀ j : Fin 2,
          IntegrableOn (fun y => ampl F w r j * (perE κ (dd ν r) j y * Ψ y)) (B0579.cell (dd ν r)) volume :=
        fun j => (hint_pair (dd ν r) (perE κ (dd ν r) j) Ψ (hE_mem j) hΨ).const_mul _
      have hpt : ∀ y, compl F w r y * Ψ y =
          movingW ν w r y * Ψ y -
            (ampl F w r 0 * (perE κ (dd ν r) 0 y * Ψ y) +
              ampl F w r 1 * (perE κ (dd ν r) 1 y * Ψ y)) := by
        intro y
        unfold compl F periodizedFrame
        simp only [Fin.sum_univ_two]
        ring
      have hiE_sum : IntegrableOn (fun y =>
          ampl F w r 0 * (perE κ (dd ν r) 0 y * Ψ y) +
            ampl F w r 1 * (perE κ (dd ν r) 1 y * Ψ y)) (B0579.cell (dd ν r)) volume :=
        (hiE 0).add (hiE 1)
      simp_rw [hpt]
      rw [integral_sub hiW hiE_sum, integral_add (hiE 0) (hiE 1),
        integral_const_mul, integral_const_mul]
    have hbt₁ : b ≤ clockTheta ν t₁ := le_trans hbt₂ (hθ_le ht₁ ht₁₂)
    have hbs' : b ≤ clockTheta ν s := le_trans hbt₂ (hθ_le (ht₁.trans hs.1) hs.2)
    rw [hpair_eq s (ht₁.trans hs.1) hbs' hs.1 Γ hΓ,
      hpair_eq t₁ ht₁ hbt₁ le_rfl (Φ t₁) (hmem_Phi t₁ ⟨le_rfl, hs.1⟩)]
    ring
  rw [show periodizedFrame κ ν m b K hν hF = F from rfl, ← sub_eq_iff_eq_add',
    hL_pair, hW_eq, (hprod_j 0).2, (hprod_j 1).2]
  have hbt₁ : b ≤ clockTheta ν t₁ := le_trans hbt₂ (hθ_le ht₁ ht₁₂)
  have h_integrand : ∀ q ∈ Ioo t₁ s,
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν q), complSource κ P F tr w q y * Φ q y =
        ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν q), interactionTerm tr q (movingW ν w q) y * Φ q y) -
        ((ampl F w q 0 *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ∫ y in B0579.cell (dd ν q),
                (interactionTerm tr q (perE κ (dd ν q) 0) y -
                  (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
                    modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y) +
          ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q)) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 0 y * Φ q y) +
         (ampl F w q 1 *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ∫ y in B0579.cell (dd ν q),
                (interactionTerm tr q (perE κ (dd ν q) 1) y -
                  (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
                    modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y) +
          ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q)) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 1 y * Φ q y)) := by
    intro q hq
    have hq_Icc : q ∈ Icc t₁ s := Ioo_subset_Icc_self hq
    have hq_Icc2 : q ∈ Icc t₁ t₂ := ⟨hq_Icc.1, hq_Icc.2.trans hs.2⟩
    have hq0 : 0 ≤ q := ht₁.trans hq_Icc.1
    have hqb : b ≤ clockTheta ν q := le_trans hbt₂ (hθ_le hq0 hq_Icc2.2)
    have ha1 : 1 ≤ clockA ν q := one_le_clockA hν.le hq0
    have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one ha1
    have hd1 : 1 ≤ dd ν q := by
      have hν1 : ν ≤ 1 := by
        have hθ1 : 1 ≤ clockTheta ν q := hb.trans hqb
        have hle : clockTheta ν q ≤ ν⁻¹ := by
          unfold clockTheta
          exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha1)
        exact (one_le_inv₀ hν).mp (hθ1.trans hle)
      have htheta_le : clockTheta ν q ≤ ν⁻¹ * clockTheta ν q :=
        le_mul_of_one_le_left (by unfold clockTheta; positivity) ((one_le_inv₀ hν).mpr hν1)
      have hcl : ν⁻¹ * clockTheta ν q ≤ dd ν q := by
        unfold dd cellLen clockTheta clockA
        rw [Real.rpow_neg hν.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have h1q : 1 ≤ 1 + ν * q := by unfold clockA at ha1; exact ha1
        have hsqrt_le : Real.sqrt (1 + ν * q) ≤ 1 + ν * q := by
          nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + ν * q), h1q, Real.sqrt_nonneg (1 + ν * q)]
        calc ν⁻¹ * (ν * (1 + ν * q))⁻¹ = (ν ^ 2)⁻¹ / (1 + ν * q) := by field_simp
          _ ≤ (ν ^ 2)⁻¹ / Real.sqrt (1 + ν * q) :=
            div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by positivity)) hsqrt_le
      exact (hb.trans hqb).trans (htheta_le.trans hcl)
    have hΦ_q : MemLp (Φ q) 2 (B0579.cellMeasure (dd ν q) (-m)) := hmem_Phi q hq_Icc
    have hW_q : MemLp (movingW ν w q) 2 (B0579.cellMeasure (dd ν q) m) :=
      ComplCouplingSub.memLp_movingW (le_trans (by norm_num) hm.le) hν ht₁ hq_Icc.1 hw
    have hE_q : ∀ j : Fin 2, MemLp (perE κ (dd ν q) j) 2 (B0579.cellMeasure (dd ν q) m) :=
      fun j => ComplCouplingSub.memLp_frame_E F hq0 hqb j
    have hLW_q : MemLp (interactionTerm tr q (movingW ν w q)) 2 (B0579.cellMeasure (dd ν q) m) := by
      have hL := ‹LocInteractionConcl ν m tr t₁ t₂ C_loc› q hq_Icc2 (movingW ν w q) hW_q
      refine ⟨hL.1, ?_⟩
      have hxn := hL.2
      unfold xNorm at hxn
      exact lt_of_le_of_lt hxn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW_q.2)
    have hLE_q : ∀ j : Fin 2,
        MemLp (interactionTerm tr q (perE κ (dd ν q) j)) 2 (B0579.cellMeasure (dd ν q) m) := by
      intro j
      have hL := ‹LocInteractionConcl ν m tr t₁ t₂ C_loc› q hq_Icc2 (perE κ (dd ν q) j) (hE_q j)
      refine ⟨hL.1, ?_⟩
      have hxn := hL.2
      unfold xNorm at hxn
      exact lt_of_le_of_lt hxn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hE_q j).2)
    have hRes_q : ∀ j : Fin 2,
        MemLp (fun y => movOscRes κ ν q j y + movEulerRes κ P tr q j y +
          modeEigen P j * perE κ (dd ν q) j y) 2 (B0579.cellMeasure (dd ν q) m) := by
      intro j
      have hbs : b ≤ clockTheta ν s := le_trans hbt₂ (hθ_le (ht₁.trans hs.1) hs.2)
      have hν1 : ν ≤ 1 := by
        have hθ1 : 1 ≤ clockTheta ν s := hb.trans hbs
        have ha_s : 1 ≤ clockA ν s := one_le_clockA hν.le (ht₁.trans hs.1)
        have hle : clockTheta ν s ≤ ν⁻¹ := by
          unfold clockTheta
          exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha_s)
        exact (one_le_inv₀ hν).mp (hθ1.trans hle)
      obtain ⟨C_tr, hBdd⟩ := hBddAll s (ht₁.trans hs.1)
      obtain ⟨M_col, _, hUnif⟩ :=
        physFrameE_uniform_xNorm hκ hm hb ⟨hν, hν1⟩ (ht₁.trans hs.1) hbs hBdd
      have hRate_mem : MemLp (FramePairing1Aux.physFrameERate κ tr q j) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
        (hUnif q ⟨hq0, hq_Icc.2⟩ j).2.2.1
      have hJ_mem : MemLp (JscaleInv (clockA ν q) (FramePairing1Aux.physFrameERate κ tr q j)) 2
          (B0579.cellMeasure (dd ν q) m) :=
        ComplCouplingSub.memLp_JscaleInv (le_trans (by norm_num) hm.le) ha1 hRate_mem
      have hJ_eq : JscaleInv (clockA ν q) (FramePairing1Aux.physFrameERate κ tr q j) =
          fun y => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
            (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) := by
        funext y
        have h1 : FramePairing1Aux.physFrameERate κ tr q j =
            fun x => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              Jscale (clockA ν q) (fun y' => interactionTerm tr q (perE κ (dd ν q) j) y' -
                (movOscRes κ ν q j y' + movEulerRes κ P tr q j y' +
                  modeEigen P j * perE κ (dd ν q) j y')) x := by
          funext x
          exact FramePairing1Aux.physFrameERate_eq_jscale hκ P hν hq0 tr j x
        rw [h1]
        have h2 : JscaleInv (clockA ν q) (fun x => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
            Jscale (clockA ν q) (fun y' => interactionTerm tr q (perE κ (dd ν q) j) y' -
              (movOscRes κ ν q j y' + movEulerRes κ P tr q j y' +
                modeEigen P j * perE κ (dd ν q) j y')) x) y =
            (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              JscaleInv (clockA ν q) (Jscale (clockA ν q) (fun y' =>
                interactionTerm tr q (perE κ (dd ν q) j) y' -
                  (movOscRes κ ν q j y' + movEulerRes κ P tr q j y' +
                    modeEigen P j * perE κ (dd ν q) j y'))) y := by
          unfold JscaleInv; ring
        rw [h2, FramePairing1Aux.jscaleInv_jscale ha]
      rw [hJ_eq] at hJ_mem
      have hsub_mem : MemLp (fun y => interactionTerm tr q (perE κ (dd ν q) j) y -
          (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
            modeEigen P j * perE κ (dd ν q) j y)) 2 (B0579.cellMeasure (dd ν q) m) := by
        have hmul := hJ_mem.const_mul (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ)
        refine (memLp_congr_ae (Eventually.of_forall fun y => ?_)).mp hmul
        rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add ha, add_neg_cancel,
          Real.rpow_zero, Complex.ofReal_one, one_mul]
      have hres_eq : (fun y => movOscRes κ ν q j y + movEulerRes κ P tr q j y +
          modeEigen P j * perE κ (dd ν q) j y) =
          fun y => interactionTerm tr q (perE κ (dd ν q) j) y -
            (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) := by
        funext y; ring
      rw [hres_eq]
      exact (hLE_q j).sub hsub_mem
    have hOscEul_q : ∀ j : Fin 2,
        MemLp (fun y => movOscRes κ ν q j y + movEulerRes κ P tr q j y) 2
          (B0579.cellMeasure (dd ν q) m) := by
      intro j
      have heq : (fun y => movOscRes κ ν q j y + movEulerRes κ P tr q j y) =
          fun y => (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
            modeEigen P j * perE κ (dd ν q) j y) - modeEigen P j * perE κ (dd ν q) j y := by
        funext y; ring
      rw [heq]
      exact (hRes_q j).sub ((hE_q j).const_mul (modeEigen P j))
    have hperLam_q : ∀ i : Fin 2,
        MemLp (perLam κ (dd ν q) i) 2 (B0579.cellMeasure (dd ν q) (-m)) := by
      intro i
      obtain ⟨_, _, hLam0⟩ := ComplCouplingHeat.memLp_and_xNorm_perLam0_neg κ (m := m) (by linarith)
      have h0 : ∀ k : Fin 2, MemLp (perLam0 κ (dd ν q) k) 2 (B0579.cellMeasure (dd ν q) (-m)) :=
        fun k => (hLam0 (dd ν q) hd1 k).1
      unfold perLam
      simp_rw [Fin.sum_univ_two]
      exact ((h0 0).const_mul _).add ((h0 1).const_mul _)
    have hH0_mode : ∀ i j : Fin 2,
        movH0 κ tr q i (perE κ (dd ν q) j) =
          (∫ x in B0579.cell (dd ν q),
            perLam κ (dd ν q) i x * (movOscRes κ ν q j x + movEulerRes κ P tr q j x)) +
          modeEigen P j * (if i = j then 1 else 0) := by
      intro i j
      rw [hH0Id q hq0 hqb i j]
      have h1 : IntegrableOn
          (fun x => perLam κ (dd ν q) i x * (movOscRes κ ν q j x + movEulerRes κ P tr q j x))
          (B0579.cell (dd ν q)) volume := by
        simpa only [mul_comm] using hint_pair (dd ν q) _ _ (hOscEul_q j) (hperLam_q i)
      have h2 : IntegrableOn
          (fun x => modeEigen P j * (perLam κ (dd ν q) i x * perE κ (dd ν q) j x))
          (B0579.cell (dd ν q)) volume := by
        have h2' : IntegrableOn
            (fun x => perLam κ (dd ν q) i x * perE κ (dd ν q) j x)
            (B0579.cell (dd ν q)) volume := by
          simpa only [mul_comm] using hint_pair (dd ν q) _ _ (hE_q j) (hperLam_q i)
        exact h2'.const_mul (modeEigen P j)
      have hpt : (fun x => perLam κ (dd ν q) i x *
          (movOscRes κ ν q j x + movEulerRes κ P tr q j x + modeEigen P j * perE κ (dd ν q) j x)) =
          fun x => perLam κ (dd ν q) i x * (movOscRes κ ν q j x + movEulerRes κ P tr q j x) +
            modeEigen P j * (perLam κ (dd ν q) i x * perE κ (dd ν q) j x) := by
        funext x; ring
      simp_rw [hpt]
      have hF1 : ∫ x in B0579.cell (dd ν q), perLam κ (dd ν q) i x * perE κ (dd ν q) j x =
          if i = j then 1 else 0 := hF.1 q hq0 hqb i j
      rw [show movingCell ν (ν ^ (-2 : ℝ)) q = B0579.cell (dd ν q) from rfl,
        integral_add h1 h2, integral_const_mul, hF1]
    -- Linearity of `interactionTerm` a.e. on `cell (dd ν q)`
    have hLint_ae : interactionTerm tr q (compl F w q) =ᵐ[volume.restrict (B0579.cell (dd ν q))]
        fun y => interactionTerm tr q (movingW ν w q) y -
          (ampl F w q 0 * interactionTerm tr q (perE κ (dd ν q) 0) y +
            ampl F w q 1 * interactionTerm tr q (perE κ (dd ν q) 1) y) := by
      have hm1 : 1 < m := by linarith
      have hiW := BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hd1 hm1 hW_q
      have hiE0 := BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hd1 hm1 (hE_q 0)
      have hiE1 := BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hd1 hm1 (hE_q 1)
      filter_upwards [hiW, hiE0, hiE1] with y hyW hyE0 hyE1
      have hk : ∀ k : Fin 2, kerVelCx (dd ν q) (compl F w q) y k =
          kerVelCx (dd ν q) (movingW ν w q) y k -
            (ampl F w q 0 * kerVelCx (dd ν q) (perE κ (dd ν q) 0) y k +
              ampl F w q 1 * kerVelCx (dd ν q) (perE κ (dd ν q) 1) y k) := by
        intro k
        unfold kerVelCx
        have hcomp : (fun z => compl F w q z * ((kerD (dd ν q) (y - z) k : ℝ) : ℂ)) =
            fun z => movingW ν w q z * ((kerD (dd ν q) (y - z) k : ℝ) : ℂ) -
              (ampl F w q 0 * (perE κ (dd ν q) 0 z * ((kerD (dd ν q) (y - z) k : ℝ) : ℂ)) +
                ampl F w q 1 * (perE κ (dd ν q) 1 z * ((kerD (dd ν q) (y - z) k : ℝ) : ℂ))) := by
          funext z; unfold compl F periodizedFrame; simp only [Fin.sum_univ_two]; ring
        have hiE_sum : IntegrableOn (fun z =>
            ampl F w q 0 * (perE κ (dd ν q) 0 z * ((kerD (dd ν q) (y - z) k : ℝ) : ℂ)) +
              ampl F w q 1 * (perE κ (dd ν q) 1 z * ((kerD (dd ν q) (y - z) k : ℝ) : ℂ)))
            (B0579.cell (dd ν q)) volume :=
          ((hyE0 k).const_mul _).add ((hyE1 k).const_mul _)
        simp_rw [hcomp]
        rw [integral_sub (hyW k) hiE_sum,
          integral_add ((hyE0 k).const_mul _) ((hyE1 k).const_mul _),
          integral_const_mul, integral_const_mul]
      simp only [interactionTerm, hk 0, hk 1]
      ring
    -- Linearity of `movH0` (for `q ∈ Ioo t₁ s`)
    have hDual_mem : ∀ i : Fin 2,
        MemLp (physLamDual κ tr q i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      fun i => (Leaf2WeakEqAmplInt.integrableOn_amplRate_and_dual κ hκ hm hν hb hF tr htr
        hBddAll ht₁ hs hbt₂ hw hf0 i).2 q hq
    have hH0_lin : ∀ i : Fin 2,
        movH0 κ tr q i (compl F w q) =
          movH0 κ tr q i (movingW ν w q) -
            (ampl F w q 0 * movH0 κ tr q i (perE κ (dd ν q) 0) +
              ampl F w q 1 * movH0 κ tr q i (perE κ (dd ν q) 1)) := by
      intro i
      unfold movH0
      have hcell : movingCell ν (ν ^ (-2 : ℝ)) q = B0579.cell (dd ν q) := rfl
      rw [hcell]
      have hpair_cov : ∀ W : ℝ × ℝ → ℂ,
          ∫ y in B0579.cell (dd ν q), movingPhi ν (fun r' => physLamDual κ tr r' i) q y * W y =
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), Jscale (clockA ν q) W x * physLamDual κ tr q i x := by
        intro W
        simp_rw [mul_comm (movingPhi ν (fun r' => physLamDual κ tr r' i) q _)]
        exact cell_pair_jscale_movingPhi hν ha W (fun r' => physLamDual κ tr r' i)
      rw [hpair_cov, hpair_cov, hpair_cov, hpair_cov]
      have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
      have hJw : Jscale (clockA ν q) (movingW ν w q) = w q := by
        funext x
        have hs_pos : Real.sqrt (clockA ν q) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
        unfold Jscale movingW JscaleInv
        have h1 : clockA ν q ^ (-2 : ℝ) * clockA ν q ^ 2 = 1 := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
          exact inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')
        rw [mul_div_cancel₀ _ hs_pos, mul_div_cancel₀ _ hs_pos, ← mul_assoc, ← Complex.ofReal_mul,
          h1, Complex.ofReal_one, one_mul]
      have hJe : ∀ j : Fin 2,
          Jscale (clockA ν q) (perE κ (dd ν q) j) = FramePairing1Aux.physFrameE κ ν q j := by
        intro j; funext x
        exact (FramePairing1Aux.physFrameE_eq_jscale_perE κ ha j x).symm
      have hJc : Jscale (clockA ν q) (compl F w q) =
          fun x => w q x - (ampl F w q 0 * FramePairing1Aux.physFrameE κ ν q 0 x +
            ampl F w q 1 * FramePairing1Aux.physFrameE κ ν q 1 x) := by
        funext x
        unfold Jscale compl F periodizedFrame
        simp only [Fin.sum_univ_two]
        have h1 : w q x = Jscale (clockA ν q) (movingW ν w q) x := by rw [hJw]
        have h2 : ∀ j : Fin 2, FramePairing1Aux.physFrameE κ ν q j x =
            Jscale (clockA ν q) (perE κ (dd ν q) j) x := fun j => by rw [hJe j]
        unfold Jscale at h1 h2
        rw [h1, h2 0, h2 1]
        ring
      have hν1 : ν ≤ 1 := by
        have hθ1 : 1 ≤ clockTheta ν q := hb.trans hqb
        have hle : clockTheta ν q ≤ ν⁻¹ := by
          unfold clockTheta
          exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha1)
        exact (one_le_inv₀ hν).mp (hθ1.trans hle)
      obtain ⟨C_tr, hBdd⟩ := hBddAll s (ht₁.trans hs.1)
      have hbs : b ≤ clockTheta ν s := le_trans hbt₂ (hθ_le (ht₁.trans hs.1) hs.2)
      obtain ⟨M_col, _, hUnif⟩ :=
        physFrameE_uniform_xNorm hκ hm hb ⟨hν, hν1⟩ (ht₁.trans hs.1) hbs hBdd
      have hw_mem : MemLp (w q) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hw.memX q hq_Icc.1
      have hpe_mem : ∀ j : Fin 2,
          MemLp (FramePairing1Aux.physFrameE κ ν q j) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
        fun j => (hUnif q ⟨hq0, hq_Icc.2⟩ j).1.1
      have hiw := hint_pair (ν ^ (-2 : ℝ)) (w q) (physLamDual κ tr q i) hw_mem (hDual_mem i)
      have hipe0 := (hint_pair (ν ^ (-2 : ℝ)) _ _ (hpe_mem 0) (hDual_mem i)).const_mul (ampl F w q 0)
      have hipe1 := (hint_pair (ν ^ (-2 : ℝ)) _ _ (hpe_mem 1) (hDual_mem i)).const_mul (ampl F w q 1)
      have hpt : (fun x => Jscale (clockA ν q) (compl F w q) x * physLamDual κ tr q i x) =
          fun x => w q x * physLamDual κ tr q i x -
            (ampl F w q 0 * (FramePairing1Aux.physFrameE κ ν q 0 x * physLamDual κ tr q i x) +
              ampl F w q 1 * (FramePairing1Aux.physFrameE κ ν q 1 x * physLamDual κ tr q i x)) := by
        rw [hJc]; funext x; ring
      have hipe_sum : IntegrableOn (fun x =>
          ampl F w q 0 * (FramePairing1Aux.physFrameE κ ν q 0 x * physLamDual κ tr q i x) +
            ampl F w q 1 * (FramePairing1Aux.physFrameE κ ν q 1 x * physLamDual κ tr q i x))
          (B0579.cell (ν ^ (-2 : ℝ))) volume := hipe0.add hipe1
      simp_rw [hpt]
      rw [integral_sub hiw hipe_sum, integral_add hipe0 hipe1,
        integral_const_mul, integral_const_mul, hJw, hJe 0, hJe 1]
      ring
    -- Now combine everything inside the spatial integral on `B0579.cell (dd ν q)`
    have hsrc_ae : (fun y => complSource κ P F tr w q y * Φ q y) =ᵐ[volume.restrict (B0579.cell (dd ν q))]
        fun y => interactionTerm tr q (movingW ν w q) y * Φ q y -
          ((ampl F w q 0 * (interactionTerm tr q (perE κ (dd ν q) 0) y -
              (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
                modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y +
            (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
              ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q)) *
              (perE κ (dd ν q) 0 y * Φ q y)) +
           (ampl F w q 1 * (interactionTerm tr q (perE κ (dd ν q) 1) y -
              (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
                modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y +
            (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
              ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q)) *
              (perE κ (dd ν q) 1 y * Φ q y))) := by
      filter_upwards [hLint_ae] with y hy
      have hAR : ∀ j : Fin 2,
          (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q j (movingW ν w q)) =
            movH0 κ tr q j (movingW ν w q) := by
        intro j
        rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add ha, add_neg_cancel,
          Real.rpow_zero, Complex.ofReal_one, one_mul]
      rw [hAR 0, hAR 1]
      have hy' := hy
      unfold complSource complFiniteRankCoupling complModeForce frameProj
      dsimp only
      rw [hy']
      simp only [Fin.sum_univ_two]
      rw [hH0_lin 0, hH0_lin 1]
      unfold F periodizedFrame
      dsimp only
      simp only [show movingCell ν (ν ^ (-2 : ℝ)) q = B0579.cell (dd ν q) from rfl,
        show cellLen (ν ^ (-2 : ℝ)) (clockA ν q) = dd ν q from rfl]
      rw [hH0_mode 0 0, hH0_mode 0 1, hH0_mode 1 0, hH0_mode 1 1]
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, mul_one, mul_zero, add_zero]
      ring
    have hi_LW := hint_pair (dd ν q) _ _ hLW_q hΦ_q
    have hi_LE : ∀ j : Fin 2,
        IntegrableOn (fun y => interactionTerm tr q (perE κ (dd ν q) j) y * Φ q y)
          (B0579.cell (dd ν q)) volume :=
      fun j => hint_pair (dd ν q) _ _ (hLE_q j) hΦ_q
    have hi_Res : ∀ j : Fin 2,
        IntegrableOn (fun y => (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
          modeEigen P j * perE κ (dd ν q) j y) * Φ q y) (B0579.cell (dd ν q)) volume :=
      fun j => hint_pair (dd ν q) _ _ (hRes_q j) hΦ_q
    have hi_E : ∀ j : Fin 2,
        IntegrableOn (fun y => perE κ (dd ν q) j y * Φ q y) (B0579.cell (dd ν q)) volume :=
      fun j => hint_pair (dd ν q) _ _ (hE_q j) hΦ_q
    have hi_term : ∀ j : Fin 2,
        IntegrableOn (fun y =>
          ampl F w q j * (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y +
          (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q j (movingW ν w q)) *
            (perE κ (dd ν q) j y * Φ q y)) (B0579.cell (dd ν q)) volume := by
      intro j
      have h1 : IntegrableOn (fun y => ampl F w q j *
          ((interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y))
          (B0579.cell (dd ν q)) volume := by
        refine Integrable.const_mul ?_ _
        have hsub : (fun y => (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y) =
            fun y => interactionTerm tr q (perE κ (dd ν q) j) y * Φ q y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y) * Φ q y := by
          funext y; ring
        rw [hsub]
        exact (hi_LE j).sub (hi_Res j)
      have h1' : IntegrableOn (fun y => ampl F w q j *
          (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y)
          (B0579.cell (dd ν q)) volume := by
        simpa only [mul_assoc] using h1
      exact h1'.add ((hi_E j).const_mul _)
    have hi_term_sum : IntegrableOn (fun y =>
        (ampl F w q 0 * (interactionTerm tr q (perE κ (dd ν q) 0) y -
            (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
              modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y +
          (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q)) *
            (perE κ (dd ν q) 0 y * Φ q y)) +
        (ampl F w q 1 * (interactionTerm tr q (perE κ (dd ν q) 1) y -
            (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
              modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y +
          (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q)) *
            (perE κ (dd ν q) 1 y * Φ q y))) (B0579.cell (dd ν q)) volume :=
      (hi_term 0).add (hi_term 1)
    rw [integral_congr_ae hsrc_ae, integral_sub hi_LW hi_term_sum,
      integral_add (hi_term 0) (hi_term 1)]
    have hsplit_j : ∀ j : Fin 2,
        ∫ y in B0579.cell (dd ν q),
          (ampl F w q j * (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) * Φ q y +
            (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
              ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q j (movingW ν w q)) *
              (perE κ (dd ν q) j y * Φ q y)) =
          ampl F w q j * (∫ y in B0579.cell (dd ν q),
            (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) * Φ q y) +
          (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q j (movingW ν w q)) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) j y * Φ q y := by
      intro j
      have h1 : IntegrableOn (fun y => ampl F w q j *
          (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y)
          (B0579.cell (dd ν q)) volume := by
        have hsub : (fun y => (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y) =
            fun y => interactionTerm tr q (perE κ (dd ν q) j) y * Φ q y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y) * Φ q y := by
          funext y; ring
        have hsub_int : IntegrableOn (fun y => (interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) * Φ q y)
            (B0579.cell (dd ν q)) volume := by
          rw [hsub]
          exact (hi_LE j).sub (hi_Res j)
        have hi := hsub_int.const_mul (ampl F w q j)
        simpa only [mul_assoc, IntegrableOn] using hi
      rw [integral_add h1 ((hi_E j).const_mul _),
        show (∫ y in B0579.cell (dd ν q),
            ampl F w q j * (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) * Φ q y) =
          ampl F w q j * ∫ y in B0579.cell (dd ν q),
            (interactionTerm tr q (perE κ (dd ν q) j) y -
              (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                modeEigen P j * perE κ (dd ν q) j y)) * Φ q y from by
          simp_rw [mul_assoc]; exact integral_const_mul _ _,
        integral_const_mul]
    rw [hsplit_j 0, hsplit_j 1]
    have ha_cancel : (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * (((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add ha, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one]
    have ha_cancel2 : ∀ z : ℂ,
        (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * ((((clockA ν q) ^ (2 : ℝ) : ℝ) : ℂ) * z) = z :=
      fun z => by rw [← mul_assoc, ha_cancel, one_mul]
    simp_rw [mul_sub, mul_add, mul_assoc, ha_cancel2]
    ring
  -- Combine integrals on Ioc t₁ s using hInt and (hprod_j 0).1, (hprod_j 1).1
  have hW_int : IntegrableOn (fun q => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
      ∫ y in B0579.cell (dd ν q), interactionTerm tr q (movingW ν w q) y * Φ q y) (Ioc t₁ s) := by
    have h_ae : (fun q => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ∫ y in B0579.cell (dd ν q), interactionTerm tr q (movingW ν w q) y * Φ q y) =ᵐ[
          volume.restrict (Ioc t₁ s)]
        fun q => ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν q),
            complSource κ P (periodizedFrame κ ν m b K hν hF) tr w q y * Φ q y) +
          (((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q) *
              (∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 0 y * Φ q y) +
            ampl F w q 0 *
              ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
                ∫ y in B0579.cell (dd ν q),
                  (interactionTerm tr q (perE κ (dd ν q) 0) y -
                    (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
                      modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y)) +
           ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q) *
              (∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 1 y * Φ q y) +
            ampl F w q 1 *
              ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
                ∫ y in B0579.cell (dd ν q),
                  (interactionTerm tr q (perE κ (dd ν q) 1) y -
                    (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
                      modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y))) := by
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      refine (ae_iff.2 (by simp [measure_singleton] : volume {q | ¬q ≠ s} = 0)).mono fun q hqs hq => ?_
      have hq_ioo : q ∈ Ioo t₁ s := ⟨hq.1, lt_of_le_of_ne hq.2 hqs⟩
      rw [show periodizedFrame κ ν m b K hν hF = F from rfl, h_integrand q hq_ioo]
      ring
    exact (Integrable.add hInt ((hprod_j 0).1.add (hprod_j 1).1)).congr h_ae.symm
  have hprod_sum : IntegrableOn (fun q =>
      (((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q) *
          ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 0 y * Φ q y) +
        ampl F w q 0 *
          ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
            ∫ y in B0579.cell (dd ν q),
              (interactionTerm tr q (perE κ (dd ν q) 0) y -
                (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
                  modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y)) +
      (((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q) *
          ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 1 y * Φ q y) +
        ampl F w q 1 *
          ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
            ∫ y in B0579.cell (dd ν q),
              (interactionTerm tr q (perE κ (dd ν q) 1) y -
                (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
                  modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y))) (Ioc t₁ s) :=
    (hprod_j 0).1.add (hprod_j 1).1
  have h_sum_int :
      (∫ q in Ioc t₁ s,
        ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 0 y * Φ q y) +
          ampl F w q 0 *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ∫ y in B0579.cell (dd ν q),
                (interactionTerm tr q (perE κ (dd ν q) 0) y -
                  (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
                    modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y)) +
      (∫ q in Ioc t₁ s,
        ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 1 y * Φ q y) +
          ampl F w q 1 *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ∫ y in B0579.cell (dd ν q),
                (interactionTerm tr q (perE κ (dd ν q) 1) y -
                  (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
                    modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y)) =
      ∫ q in Ioc t₁ s,
        (((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 0 (movingW ν w q) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 0 y * Φ q y) +
          ampl F w q 0 *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ∫ y in B0579.cell (dd ν q),
                (interactionTerm tr q (perE κ (dd ν q) 0) y -
                  (movOscRes κ ν q 0 y + movEulerRes κ P tr q 0 y +
                    modeEigen P 0 * perE κ (dd ν q) 0 y)) * Φ q y)) +
        (((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q 1 (movingW ν w q) *
            ∫ y in B0579.cell (dd ν q), perE κ (dd ν q) 1 y * Φ q y) +
          ampl F w q 1 *
            ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ∫ y in B0579.cell (dd ν q),
                (interactionTerm tr q (perE κ (dd ν q) 1) y -
                  (movOscRes κ ν q 1 y + movEulerRes κ P tr q 1 y +
                    modeEigen P 1 * perE κ (dd ν q) 1 y)) * Φ q y)) :=
    (integral_add (hprod_j 0).1 (hprod_j 1).1).symm
  have h_sub_int := (integral_sub hW_int hprod_sum).symm
  rw [h_sum_int, h_sub_int]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [ae_iff.2 (by simp [measure_singleton] : volume {q | ¬q ≠ s} = 0)] with q hqs hq
  rw [h_integrand q ⟨hq.1, lt_of_le_of_ne hq.2 hqs⟩]
  ring

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
