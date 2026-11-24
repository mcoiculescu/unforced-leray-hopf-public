import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2` (`VelCutoffEnergyIneq`): decomposition

Source of record: `the November 2 reference manuscript` lines 273-288 ("bounded
periodic pressure choice"; "Approximation and transverse cutoffs then give the velocity ... energy
identities").

With `φ = etaCutoff R`, `E_R(s) = ∫_cell φ |v|²` and the momentum equation
`∂_s v = νΔv - (v·∇)v - ∇p` (`B0140.IsTrain.momentum`, `div v = 0`), differentiation under the
integral gives, for `s > 0`,

`E_R' = T_visc + T_trans + T_pres`, with
* `T_visc = 2ν ∫ φ ⟨v, Δv⟩ = -2νD - 2ν ∫ φ' ⟨v, ∂_η v⟩`, `D = ∫ φ |∇v|²`;
* `T_trans = -2 ∫ φ ⟨v, (v·∇)v⟩ = ∫ |v|² v_η φ'` (`div v = 0`);
* `T_pres = -2 ∫ φ ⟨v, ∇p⟩ = 2 ∫ φ' p v_η` (`div v = 0`).

With `|v| ≤ M`, `|p| ≤ P`, `|φ'| ≤ (C₀/R) √φ`, and `φ' = 0` for `|η| ≥ 2R` (cell area of
`{|η| ≤ 2R}` is `4Rc`), each right side is bounded independently of `R ≥ 1`
(`Young` for the viscous cross term), so `E_R' ≤ -(3/2)νD + K ≤ K`.

This is the single-train analogue of the difference energy method of
`Tasks/TrainCutoffEnergyProof/*` (there `w = v - v'`; no zero train exists, so those proofs are
not directly applicable, but they are the models: set `v' = 0`, drop all `v'` terms and replace the
energy bound `∫|w|² ≤ 4M` by `|v| ≤ M` on the strip).

Proved here: `velCutoffContinuous_proof`, `velCutoffHasDeriv_proof` and the assembly
`velCutoffEnergyIneq_of`.  Leaves: `VelIntegrandDecomp`, the identity/estimate pairs for the
viscous, transport and pressure terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The cutoff dissipation `D(s) = ∫_cell φ_R |∇v|²` of a single train. -/
def velCutoffDissipation {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (tr.v s) z

/-- Viscous term `2ν ∫_cell φ_R ⟨v, Δv⟩`. -/
def velCutoffViscous {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  2 * ν * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.vecLaplacian (tr.v s) z)

/-- Transport term `-2 ∫_cell φ_R ⟨v, (v·∇)v⟩`. -/
def velCutoffTransport {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (tr.v s z) (bilinAdv (tr.v s) (tr.v s) z)

/-- Pressure term `-2 ∫_cell φ_R ⟨v, ∇p⟩`. -/
def velCutoffPressure {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.gradS (tr.p s) z)

/-- Right side of the viscous identity: `-2νD - 2ν ∫ φ' ⟨v, ∂_η v⟩`. -/
def velViscousRhs {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ν * velCutoffDissipation tr R s - 2 * ν * ∫ z in Cyl.cell c,
    deriv (etaCutoff R) z.2 * inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z)

/-- Right side of the transport identity: `∫ |v|² v_η φ'`. -/
def velTransportRhs {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2

/-- Right side of the pressure identity: `2 ∫ φ' p v_η`. -/
def velPressureRhs {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  2 * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1

/-- **Leaf `VelIntegrandDecomp`** (source lines 276-288; model `Tasks/TrainCutoffEnergyProof/
IntegrandDecomp.lean`): for `s > 0`, `∂_s v = νΔv - (v·∇)v - ∇p` splits the cutoff integral
`∫ φ 2⟨v, ∂_s v⟩` into the three terms (each integrand is continuous and vanishes for `|η| ≥ 2R`,
so integrable on the cell by `cellToolkit`). -/
def VelIntegrandDecomp : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 < s →
    (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (tr.v s z) (deriv (fun t => tr.v t z) s))) =
      velCutoffViscous tr R s + velCutoffTransport tr R s + velCutoffPressure tr R s

/-- **Leaf `VelViscousIdentity`** (model `ViscousIdentity.lean`, take `v' = 0`):
`velCutoffViscous = velViscousRhs` for `s ≥ 0` (cell integration by parts componentwise, `φ`
depends on `η` only). -/
def VelViscousIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    velCutoffViscous tr R s = velViscousRhs tr R s

/-- **Leaf `VelViscousEstimate`** (model `ViscousEstimate.lean`, `viscEst_young`): with
`‖v‖ ≤ M` on `[0, S]`, `velViscousRhs ≤ -(3/2) ν D + K`, `K` independent of `R ≥ 1`.
(Young: `-2νφ'⟨v,∂_ηv⟩ ≤ (ν/2)φ|∇v|² + 2ν(C₀/R)²M²` on `|η| ≤ 2R`, area `4Rc`; `0` beyond.) -/
def VelViscousEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    (∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, ‖tr.v s z‖ ≤ M) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      velViscousRhs tr R s ≤ -(3 / 2) * ν * velCutoffDissipation tr R s + K

/-- **Leaf `VelTransportIdentity`** (model `TransportIdentity.lean`, take `v' = 0`):
`velCutoffTransport = velTransportRhs` for `s ≥ 0` (`div v = 0`). -/
def VelTransportIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    velCutoffTransport tr R s = velTransportRhs tr R s

/-- **Leaf `VelTransportEstimate`** (model `TransportEstimate.lean`): `‖v‖ ≤ M` and
`|φ'| ≤ C₀/R`, `φ' = 0` for `|η| ≥ 2R`: `velTransportRhs ≤ 4 C₀ c M³`. -/
def VelTransportEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    (∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, ‖tr.v s z‖ ≤ M) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      velTransportRhs tr R s ≤ K

/-- **Leaf `VelPressureIdentity`** (model `PressureIdentity.lean`, take `π = p`, `w = v`):
`velCutoffPressure = velPressureRhs` for `s ≥ 0` (`div v = 0`; `p` and `v` are `c`-periodic). -/
def VelPressureIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    velCutoffPressure tr R s = velPressureRhs tr R s

/-- **Leaf `VelPressureEstimate`** (model `PressureEstimate.lean`): `‖v‖ ≤ M`, `|p| ≤ P`,
`|φ'| ≤ C₀/R`, `φ' = 0` for `|η| ≥ 2R`: `velPressureRhs ≤ 8 C₀ c P M`. -/
def VelPressureEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ S M P : ℝ, 0 ≤ S →
    (∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, ‖tr.v s z‖ ≤ M) →
    (∀ r ∈ Icc (0 : ℝ) S, ∀ z : Plane, |tr.p r z| ≤ P) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      velPressureRhs tr R s ≤ K

theorem velCutoffDissipation_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) :
    0 ≤ velCutoffDissipation tr R s :=
  integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (gradNormSq_nonneg _ z))

/-! ### Continuity and differentiation (proved) -/

/-- Continuity of `E_R` on `[0, S]` (dominated convergence, as `cutoffEnergyContinuous`). -/
theorem velCutoffContinuous_proof {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) (R : ℝ)
    (hR : 1 ≤ R) (S : ℝ) : ContinuousOn (velCutoffEnergy tr R) (Icc 0 S) := by
  have hR0 : 0 < R := by linarith
  have hv : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hq : ContinuousOn (fun x : ℝ × Plane => ‖tr.v x.1 x.2‖ ^ 2) (Ici 0 ×ˢ univ) :=
    hv.norm.pow 2
  have hK : IsCompact (Icc (0 : ℝ) S ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_sub : Icc (0 : ℝ) S ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ⊆
      Ici 0 ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mem_prod.2 ⟨Set.mem_Ici.2 (Set.mem_Icc.1 (Set.mem_prod.1 hx).1).1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hq.mono hK_sub)
  have hbox_meas : MeasurableSet (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hbox_fin : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hcell_meas : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hfin : (volume.restrict (Cyl.cell c)) (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ≠ ⊤ :=
    ne_top_of_le_ne_top hbox_fin.ne (Measure.restrict_apply_le _ _)
  have hbound_int : Integrable
      ((Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0))
      (volume.restrict (Cyl.cell c)) :=
    (integrable_indicator_iff hbox_meas).2 (integrableOn_const hfin)
  have hz : ∀ s : ℝ, 0 ≤ s →
      Continuous (fun z : Plane => etaCutoff R z.2 * ‖tr.v s z‖ ^ 2) := by
    intro s hs
    have hmap : ∀ z : Plane, (s, z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set Plane) :=
      fun z => Set.mk_mem_prod (Set.mem_Ici.2 hs) (mem_univ z)
    have hcont : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    have h1 : Continuous (fun z : Plane => tr.v s z) := hv.comp_continuous hcont hmap
    exact ((cutoffCont_eta_continuous R).comp continuous_snd).mul (h1.norm.pow 2)
  have hs_cont : ∀ a : Plane, ContinuousOn
      (fun s : ℝ => etaCutoff R a.2 * ‖tr.v s a‖ ^ 2) (Icc (0 : ℝ) S) := by
    intro a
    have hmap : MapsTo (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) S)
        (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      fun s hs => Set.mk_mem_prod (Set.mem_Ici.2 hs.1) (mem_univ a)
    have hcont : ContinuousOn (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) S) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc1 : ContinuousOn (fun s : ℝ => tr.v s a) (Icc (0 : ℝ) S) :=
      hv.comp hcont hmap
    exact continuousOn_const.mul (hc1.norm.pow 2)
  have hbound : ∀ s ∈ Icc (0 : ℝ) S, ∀ᵐ a ∂(volume.restrict (Cyl.cell c)),
      ‖etaCutoff R a.2 * ‖tr.v s a‖ ^ 2‖ ≤
        (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0) a := by
    intro s hs
    filter_upwards [ae_restrict_mem hcell_meas] with a ha
    have hq0 : 0 ≤ ‖tr.v s a‖ ^ 2 := sq_nonneg _
    by_cases hb : a ∈ Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
    · have hbC : ‖‖tr.v s a‖ ^ 2‖ ≤ C := hC (s, a) (Set.mk_mem_prod hs hb)
      rw [Real.norm_of_nonneg hq0] at hbC
      rw [Set.indicator_of_mem hb,
        Real.norm_of_nonneg (mul_nonneg (cutoffCont_eta_nonneg R a.2) hq0)]
      exact (mul_le_of_le_one_left hq0 (cutoffCont_eta_le_one R a.2)).trans
        (hbC.trans (le_max_left _ _))
    · have ha1 : a.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self (Set.mem_prod.1 ha).1
      have hR2 : 2 * R ≤ |a.2| := by
        by_contra hlt
        rw [not_le] at hlt
        apply hb
        exact Set.mem_prod.2 ⟨ha1, Set.mem_Icc.2
          ⟨by linarith [neg_abs_le a.2], by linarith [le_abs_self a.2]⟩⟩
      rw [Set.indicator_of_notMem hb]
      simp [cutoffCont_eta_eq_zero hR0 hR2]
  have hmain : ContinuousOn
      (fun s : ℝ => ∫ z, etaCutoff R z.2 * ‖tr.v s z‖ ^ 2 ∂(volume.restrict (Cyl.cell c)))
      (Icc (0 : ℝ) S) :=
    MeasureTheory.continuousOn_of_dominated
      (F := fun s z => etaCutoff R z.2 * ‖tr.v s z‖ ^ 2)
      (fun s hs => (hz s hs.1).aestronglyMeasurable) hbound hbound_int
      (ae_of_all _ (fun a => hs_cont a))
  unfold velCutoffEnergy
  exact hmain

/-- Differentiation under the integral sign: for `s > 0`, `E_R'(s) = ∫ φ 2⟨v, ∂_s v⟩`. -/
theorem velCutoffHasDeriv_proof {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) (R : ℝ)
    (hR : 1 ≤ R) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (velCutoffEnergy tr R)
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (tr.v s z) (deriv (fun t => tr.v t z) s))) s := by
  have hR0 : 0 < R := by linarith
  have hWd : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self subset_rfl)
  have hmain := cehd_generic hWd c R hc hR0 s hs
  have hdS : ∀ z : Plane, deriv (fun t => tr.v t z) s =
      fderiv ℝ (fun x : ℝ × Plane => tr.v x.1 x.2) (s, z) ((1 : ℝ), (0 : Plane)) :=
    fun z => (cehd_deriv_at hWd hs z).deriv
  simp only [hdS]
  exact hmain

/-! ### The conditional theorem -/

/-- **`VelCutoffEnergyIneq` from the leaves.** -/
theorem velCutoffEnergyIneq_of (hD : VelIntegrandDecomp) (hVi : VelViscousIdentity)
    (hVe : VelViscousEstimate) (hTi : VelTransportIdentity) (hTe : VelTransportEstimate)
    (hPi : VelPressureIdentity) (hPe : VelPressureEstimate) : VelCutoffEnergyIneq := by
  intro ν c hν hc tr htr S hS P hP
  have hc0 : 0 < c := by linarith
  obtain ⟨M, hM⟩ := htr.sup_bound hS.le
  obtain ⟨KV, hKV, HV⟩ := hVe ν c hν hc0 tr S M hS.le hM
  obtain ⟨KT, hKT, HT⟩ := hTe ν c hν hc0 tr S M hS.le hM
  obtain ⟨KP, hKP, HP⟩ := hPe ν c hν hc0 tr S M P hS.le hM hP
  refine ⟨KV + KT + KP, by linarith, fun R hR => ⟨velCutoffContinuous_proof hc0 tr R hR S, ?_⟩⟩
  intro s hs
  refine ⟨_, velCutoffHasDeriv_proof hc0 tr R hR s hs.1, ?_⟩
  have hs' : s ∈ Icc (0 : ℝ) S := ⟨hs.1.le, hs.2.le⟩
  rw [hD ν c hν hc0 tr R hR s hs.1, hVi ν c hν hc0 tr R hR s hs.1.le,
    hTi ν c hν hc0 tr R hR s hs.1.le, hPi ν c hν hc0 tr R hR s hs.1.le]
  have h1 := HV R hR s hs'
  have h2 := HT R hR s hs'
  have h3 := HP R hR s hs'
  have hD0 := velCutoffDissipation_nonneg tr R s
  have : 0 ≤ ν * velCutoffDissipation tr R s := mul_nonneg hν.le hD0
  linarith

end UnforcedLeray.Short.PartI
