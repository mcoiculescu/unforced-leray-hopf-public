import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivReduction
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.PairSplit
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ViscousIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.Quad
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundB.Expand
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Top
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetSupBridge
import UnforcedLeray.Short.PartI.Sub.PartI_T09.BootstrapContinuity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `PartI:T12`: high-norm energy inequality on the unit cylinder and uniform `H^N` bound

Source of record: `the November 2 reference manuscript`, lines 350-358 and 379-389:
* Tame higher-order inequality (`overlap_tame_energy_inequality`):
  `(1/2) d/dT ‖U‖_{H^k}² + ‖∇U‖_{H^k}² ≤ C_k e_c ‖∇U‖_∞ ‖U‖_{H^k}²`.
* High-norm energy inequality (`overlap_highnorm_energy_inequality`, `N ≥ 3`):
  `(1/2) d/dT ‖U‖_{H^N}² + (1 - C_N e_c ‖U‖_{H^N}) ‖∇U‖_{H^N}² ≤ 0`.
* Uniform high-norm bound for all `T ≥ 0` (`overlap_highnorm_uniform` /
  `overlapHighNormUniform_proof : OverlapHighNormUniform`):
  by continuity from the overlap datum bound (`PartI:T11`), `‖U(T)‖_{H^N}` stays `≤ C_N`
  for `e_c` small (`0 < ν ≤ ν₀`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology Pointwise

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc pc Qc width)

/-! ### 1. Unit-cylinder Sobolev and dissipation squared norms and dilation scaling -/

/-- Squared `H^k` word-jet energy on the unit cylinder (`c = 1`):
`‖f‖_{H^k}² = ∑_{j ≤ k} ‖D^j f‖_{L²(cell 1)}²`. -/
def cylSobolevSq (k : ℕ) (f : Plane → Vec) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), jetEnergy 1 j f

/-- Squared `H^k` dissipation on the unit cylinder (`c = 1`):
`‖∇f‖_{H^k}² = ∑_{j ≤ k} ‖D^{j+1} f‖_{L²(cell 1)}²`. -/
def cylDissipationSq (k : ℕ) (f : Plane → Vec) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), jetEnergy 1 (j + 1) f

theorem cylSobolevSq_nonneg (k : ℕ) (f : Plane → Vec) : 0 ≤ cylSobolevSq k f :=
  Finset.sum_nonneg fun j _ => jetEnergy_nonneg 1 j f

theorem cylDissipationSq_nonneg (k : ℕ) (f : Plane → Vec) : 0 ≤ cylDissipationSq k f :=
  Finset.sum_nonneg fun j _ => jetEnergy_nonneg 1 (j + 1) f

theorem jetEnergy_le_cylSobolevSq {j k : ℕ} (hjk : j ≤ k) (f : Plane → Vec) :
    jetEnergy 1 j f ≤ cylSobolevSq k f :=
  Finset.single_le_sum (fun i _ => jetEnergy_nonneg 1 i f)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))

theorem jetEnergy_le_cylDissipationSq {j k : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (f : Plane → Vec) :
    jetEnergy 1 j f ≤ cylDissipationSq k f := by
  have hj : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1).symm
  rw [hj]
  exact Finset.single_le_sum (fun i _ => jetEnergy_nonneg 1 (i + 1) f)
    (Finset.mem_range.2 (by omega))

/-- Word derivatives under spatial dilation `B0155.dil c`. -/
theorem derivWord_dil :
    ∀ (w : List Bool) (K c : ℝ) (f : Plane → ℝ),
      B0151.derivWord w (fun Z => K * f (B0155.dil c Z)) =
        fun Z => K * c ^ w.length * B0151.derivWord w f (B0155.dil c Z)
  | [], K, c, f => by
      funext Z
      simp [B0151.derivWord]
  | true :: w, K, c, f => by
      have ih := derivWord_dil w K c f
      show Cyl.partialQ (B0151.derivWord w (fun Z => K * f (B0155.dil c Z))) = _
      rw [ih, B0155.partialQ_dil (K * c ^ w.length) c (B0151.derivWord w f)]
      funext Z
      simp only [List.length_cons, pow_succ, B0151.derivWord, Cyl.partialQ_eq_partialX]
      ring
  | false :: w, K, c, f => by
      have ih := derivWord_dil w K c f
      show Cyl.partialEta (B0151.derivWord w (fun Z => K * f (B0155.dil c Z))) = _
      rw [ih, B0155.partialEta_dil (K * c ^ w.length) c (B0151.derivWord w f)]
      funext Z
      simp only [List.length_cons, pow_succ, B0151.derivWord, Cyl.partialEta_eq_partialY]
      ring

theorem wordComp_scaleField (w : List Bool) (c : ℝ) (u : Plane → Vec) (k : Fin 2) (Z : Plane) :
    wordComp w (scaleField c u) k Z =
      c ^ 3 * c ^ w.length * wordComp w u k (B0155.dil c Z) := by
  have h : (fun Y : Plane => scaleField c u Y k) = fun Y => c ^ 3 * u (B0155.dil c Y) k := by
    funext Y
    simp [scaleField, B0155.dil_eq_smul, PiLp.smul_apply]
  unfold wordComp
  rw [h]
  exact congrFun (derivWord_dil w (c ^ 3) c (fun z => u z k)) Z

theorem advection_scaleField (c : ℝ) (u : Plane → Vec) (Z : Plane) :
    Train.advection (scaleField c u) Z = c ^ 7 • Train.advection u (B0155.dil c Z) := by
  have h := B0155.advection_ovU 1 c (fun _ => u) 0 Z
  have hov : B0155.ovU 1 c (fun _ => u) 0 = scaleField c u := by
    funext Y
    simp [B0155.ovU, scaleField, B0155.dil_eq_smul]
  rw [hov] at h
  exact h

theorem wordComp_advection_scaleField (w : List Bool) (c : ℝ) (u : Plane → Vec) (k : Fin 2)
    (Z : Plane) :
    wordComp w (Train.advection (scaleField c u)) k Z =
      c ^ 7 * c ^ w.length * wordComp w (Train.advection u) k (B0155.dil c Z) := by
  have h : (fun Y : Plane => Train.advection (scaleField c u) Y k) =
      fun Y => c ^ 7 * Train.advection u (B0155.dil c Y) k := by
    funext Y
    rw [advection_scaleField, PiLp.smul_apply, smul_eq_mul]
  unfold wordComp
  rw [h]
  exact congrFun (derivWord_dil w (c ^ 7) c (fun z => Train.advection u z k)) Z

/-- Change of variables for integrals from the unit cell to the period-`c` cell. -/
theorem integral_cell_one_dil {c : ℝ} (hc : 0 < c) (g : Plane → ℝ) :
    ∫ Z in Cyl.cell 1, g (B0155.dil c Z) = (c ^ 2)⁻¹ * ∫ z in Cyl.cell c, g z := by
  have h := Measure.setIntegral_comp_smul (volume : Measure Plane) g (Cyl.cell 1) hc.ne'
  have hcell : c • Cyl.cell 1 = Cyl.cell c := by
    ext y
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (B0155.dil_mem_cell_iff hc x).2 hx
    · intro hy
      refine ⟨c⁻¹ • y, ?_, smul_inv_smul₀ hc.ne' y⟩
      apply (B0155.dil_mem_cell_iff hc _).1
      rw [B0155.dil_eq_smul, smul_inv_smul₀ hc.ne']
      exact hy
  rw [hcell, Module.finrank_prod, Module.finrank_self, show (1 + 1 : ℕ) = 2 from rfl,
    abs_of_pos (inv_pos.2 (sq_pos_of_pos hc)), smul_eq_mul] at h
  exact h

theorem jetEnergy_scaleField {c : ℝ} (hc : 0 < c) (j : ℕ) (u : Plane → Vec) :
    jetEnergy 1 j (scaleField c u) = c ^ 4 * c ^ (2 * j) * jetEnergy c j u := by
  unfold jetEnergy jetPair
  let G : Plane → ℝ := fun z =>
    ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w u k z * wordComp w u k z
  have hpt : (fun z : Plane => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      wordComp w (scaleField c u) k z * wordComp w (scaleField c u) k z) =
      fun z : Plane => (c ^ 3 * c ^ j) ^ 2 * G (B0155.dil c z) := by
    funext z
    dsimp only [G]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wordComp_scaleField, mem_wordsOfLength_length hw]
    ring
  rw [hpt, integral_const_mul, integral_cell_one_dil hc G]
  dsimp only [G]
  have hc0 : c ≠ 0 := hc.ne'
  rw [pow_mul]
  field_simp
  ring

theorem jetPair_advection_scaleField {c : ℝ} (hc : 0 < c) (j : ℕ) (u : Plane → Vec) :
    jetPair 1 j (scaleField c u) (Train.advection (scaleField c u)) =
      c ^ 8 * c ^ (2 * j) * jetPair c j u (Train.advection u) := by
  unfold jetPair
  let G : Plane → ℝ := fun z =>
    ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w u k z * wordComp w (Train.advection u) k z
  have hpt : (fun z : Plane => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      wordComp w (scaleField c u) k z * wordComp w (Train.advection (scaleField c u)) k z) =
      fun z : Plane => (c ^ 3 * c ^ j) * (c ^ 7 * c ^ j) * G (B0155.dil c z) := by
    funext z
    dsimp only [G]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wordComp_scaleField, wordComp_advection_scaleField, mem_wordsOfLength_length hw]
    ring
  rw [hpt, integral_const_mul, integral_cell_one_dil hc G]
  dsimp only [G]
  have hc0 : c ≠ 0 := hc.ne'
  rw [pow_mul]
  field_simp
  ring

/-! ### 2. Exact jet energy balance for `tr.v` at any `s > 0` and for `U` at any `T ≥ 0` -/

theorem trainTimeDerivJetLocalAllAges_proof : TrainTimeDerivJetLocalAllAges :=
  trainTimeDerivJetLocalAllAges_of
    (trainLapLocal_of_err trainErrJetLocalL2_proof)
    (trainAdvLocal_of trainErrJetLocalL2_proof trainErrSupLocal_proof)
    (trainPressureGradLocal_of
      (trainAdvLocal_of trainErrJetLocalL2_proof trainErrSupLocal_proof)
      trainStressDivLocal_proof)
    trainStressDivLocal_proof

theorem vc_lap_local_l2 {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) :
    LocalSmoothJetL2 c (fun r => ν • Train.vecLaplacian (Vc ν c r)) := by
  have hc0 : 0 < c := by linarith
  have hcomp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  refine ⟨fun r hr => ?_, fun s hs w k => ?_⟩
  · refine contDiff_euclidean.2 fun k => ?_
    have hVc := vcSmoothPosE_proof ν c hν hc0 r hr
    have key : ContDiff ℝ ∞ (fun z => ν * Train.lapS (fun y => Vc ν c r y k) z) :=
      contDiff_const.mul (lapLocal_lapS_contDiff (hcomp hVc k))
    have e : ∀ z : Plane, ((ν • Train.vecLaplacian (Vc ν c r)) z) k =
        ν * Train.lapS (fun y => Vc ν c r y k) z := fun z => by
      simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, lapLocal_vecLap_apply]
    simp only [e]
    exact key
  · obtain ⟨e1, he1, K1, h1⟩ := vcJetLocalL2_proof ν c hν hc s hs (true :: true :: w) k
    obtain ⟨e2, he2, K2, h2⟩ := vcJetLocalL2_proof ν c hν hc s hs (false :: false :: w) k
    refine ⟨min e1 e2, lt_min he1 he2, 2 * ν ^ 2 * (K1 + K2), fun r hr hrs => ?_⟩
    have hr1 : |r - s| < e1 := lt_of_lt_of_le hrs (min_le_left _ _)
    have hr2 : |r - s| < e2 := lt_of_lt_of_le hrs (min_le_right _ _)
    obtain ⟨m1, i1⟩ := h1 r hr hr1
    obtain ⟨m2, i2⟩ := h2 r hr hr2
    have hk : ContDiff ℝ ∞ (fun y => Vc ν c r y k) := hcomp (vcSmoothPosE_proof ν c hν hc0 r hr) k
    have eq : ∀ z : Plane, wordComp w (fun x => ν • Train.vecLaplacian (Vc ν c r) x) k z =
        ν * (wordComp (true :: true :: w) (Vc ν c r) k z +
          wordComp (false :: false :: w) (Vc ν c r) k z) := by
      intro z
      have e1' : (fun x => (ν • Train.vecLaplacian (Vc ν c r) x) k) =
          fun x => ν * Train.lapS (fun y => Vc ν c r y k) x := by
        funext x
        rw [PiLp.smul_apply, smul_eq_mul, lapLocal_vecLap_apply]
      calc wordComp w (fun x => ν • Train.vecLaplacian (Vc ν c r) x) k z
          = B0151.derivWord w (fun x => ν * Train.lapS (fun y => Vc ν c r y k) x) z := by
            unfold wordComp; rw [e1']
        _ = ν * B0151.derivWord w (fun x => Train.lapS (fun y => Vc ν c r y k) x) z :=
            lapLocal_dw_const_mul ν w _ z
        _ = ν * Train.lapS (B0151.derivWord w (fun y => Vc ν c r y k)) z := by
            rw [JetViscIBP.derivWord_lap w _ hk]
        _ = ν * (wordComp (true :: true :: w) (Vc ν c r) k z +
              wordComp (false :: false :: w) (Vc ν c r) k z) := by
            rw [lapLocal_lapS_dw]; rfl
    have hw : wordComp w (ν • Train.vecLaplacian (Vc ν c r)) k =
        fun z => ν * (wordComp (true :: true :: w) (Vc ν c r) k z +
          wordComp (false :: false :: w) (Vc ν c r) k z) := funext eq
    dsimp only
    rw [hw]
    exact lapLocal_l2_comb c ν _ _ K1 K2 m1 m2 i1 i2

theorem vel_timeDeriv_local_l2 {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s)
    (w : List Bool) (k : Fin 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (wordComp w (fun z => deriv (fun t => tr.v t z) r) k) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (wordComp w (fun z => deriv (fun t => tr.v t z) r) k z) ^ 2 ≤ K := by
  have hc0 : 0 < c := by linarith
  obtain ⟨e1, he1, K1, h1⟩ := trainTimeDerivJetLocalAllAges_proof ν c hν hc tr htr s hs w k
  obtain ⟨hVsm, hVloc⟩ := vc_lap_local_l2 hν hc
  obtain ⟨e2, he2, K2, h2⟩ := hVloc s hs w k
  refine ⟨min e1 e2, lt_min he1 he2, 2 * (K1 + K2), fun r hr hrs => ?_⟩
  have hr1 : |r - s| < e1 := lt_of_lt_of_le hrs (min_le_left _ _)
  have hr2 : |r - s| < e2 := lt_of_lt_of_le hrs (min_le_right _ _)
  obtain ⟨m1, i1⟩ := h1 r hr hr1
  obtain ⟨m2, i2⟩ := h2 r hr hr2
  have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hdv_sm : ContDiff ℝ ∞ (fun z => deriv (fun t => tr.v t z) r) :=
    ErrPressureLapAux.dt_contDiff hvU hr
  have hVc_sm : ContDiff ℝ ∞ (fun z => (ν • Train.vecLaplacian (Vc ν c r)) z) := hVsm r hr
  have hpt : ∀ z : Plane,
      deriv (fun t => trainErr tr t z) r =
        deriv (fun t => tr.v t z) r - (ν • Train.vecLaplacian (Vc ν c r)) z := by
    intro z
    have hVt := (TrainErrorEquation.differentiableAt_time tr hr z).hasDerivAt
    have hVc := Train.Vc_heat hν hc0.ne' hr.le z
    exact (hVt.sub hVc).deriv
  have hde_sm : ContDiff ℝ ∞ (fun z => deriv (fun t => trainErr tr t z) r) := by
    have heq : (fun z => deriv (fun t => trainErr tr t z) r) =
        fun z => deriv (fun t => tr.v t z) r - (ν • Train.vecLaplacian (Vc ν c r)) z :=
      funext hpt
    rw [heq]
    exact hdv_sm.sub hVc_sm
  have hsum_pt : (fun z => deriv (fun t => tr.v t z) r) =
      fun z => deriv (fun t => trainErr tr t z) r + (ν • Train.vecLaplacian (Vc ν c r)) z := by
    funext z
    rw [hpt z, sub_add_cancel]
  have hwc : wordComp w (fun z => deriv (fun t => tr.v t z) r) k =
      fun z => wordComp w (fun y => deriv (fun t => trainErr tr t y) r) k z +
        wordComp w (ν • Train.vecLaplacian (Vc ν c r)) k z := by
    rw [hsum_pt]
    exact pgl_wc_add hde_sm hVc_sm w k
  rw [hwc]
  refine ⟨m1.add m2, ?_⟩
  set f := wordComp w (fun y => deriv (fun t => trainErr tr t y) r) k
  set g := wordComp w (ν • Train.vecLaplacian (Vc ν c r)) k
  have hf : Integrable (fun z => f z ^ 2) (Cyl.cellμ c) := m1.integrable_sq
  have hg : Integrable (fun z => g z ^ 2) (Cyl.cellμ c) := m2.integrable_sq
  have hfg : Integrable (fun z => (f z + g z) ^ 2) (Cyl.cellμ c) := (m1.add m2).integrable_sq
  have hmono : ∫ z, (f z + g z) ^ 2 ∂(Cyl.cellμ c) ≤
      ∫ z, (2 * f z ^ 2 + 2 * g z ^ 2) ∂(Cyl.cellμ c) :=
    integral_mono hfg ((hf.const_mul 2).add (hg.const_mul 2))
      (fun z => by nlinarith [sq_nonneg (f z - g z)])
  rw [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  change ∫ z, (f z + g z) ^ 2 ∂(Cyl.cellμ c) ≤ _
  have i1' : ∫ z, f z ^ 2 ∂(Cyl.cellμ c) ≤ K1 := i1
  have i2' : ∫ z, g z ^ 2 ∂(Cyl.cellμ c) ≤ K2 := i2
  linarith

open UnforcedLeray.Short.PartI.TrainWordEnergyInstance in
theorem vel_wordEnergy_hasDerivAt {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s)
    (w : List Bool) (k : Fin 2) :
    (∀ᶠ r in 𝓝 s, MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c)) ∧
    MemLp (wordComp w (fun y => deriv (fun t => tr.v t y) s) k) 2 (Cyl.cellμ c) ∧
    HasDerivAt (fun r => ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2)
      (2 * ∫ z in Cyl.cell c, wordComp w (tr.v s) k z *
        wordComp w (fun y => deriv (fun t => tr.v t y) s) k z) s := by
  obtain ⟨ε0, hε0, K0, hK⟩ := vel_timeDeriv_local_l2 hν hc tr htr hs w k
  have hεpos : 0 < min ε0 (s / 4) := lt_min hε0 (by linarith)
  have hv_on : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ioi 0 ×ˢ univ) := by
    have hproj : ContDiff ℝ ∞ (fun y : Vec => (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) y) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff
    exact hproj.comp_contDiffOn (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl))
  have hw_smooth : ∀ z : Plane, ContDiffOn ℝ ∞ (fun τ => wordComp w (tr.v τ) k z) (Ioi 0) := by
    intro z
    have hW : ContDiffOn ℝ ∞ (swtcWord w (fun p : ℝ × Plane => tr.v p.1 p.2 k)) swtcO :=
      swtc_sm w _ hv_on
    have hline : ContDiffOn ℝ ∞ (fun τ : ℝ => (τ, z)) (Ioi 0) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have hmaps : MapsTo (fun τ : ℝ => (τ, z)) (Ioi 0) swtcO := fun τ hτ => ⟨hτ, mem_univ z⟩
    exact (hW.comp hline hmaps).congr (fun τ hτ => swtc_slice w _ hv_on τ hτ z)
  have hw_loc_deriv : ∀ {r : ℝ}, 3 * s / 4 < r → ∀ z : Plane,
      deriv (fun t => wordComp w (tr.v (loc s t)) k z) r =
        wordComp w (fun y => deriv (fun τ => tr.v τ y) r) k z := by
    intro r hr z
    have hev : (fun t => wordComp w (tr.v (loc s t)) k z) =ᶠ[𝓝 r]
        (fun t => wordComp w (tr.v t) k z) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      rw [loc_eq_id hs ht]
    rw [hev.deriv_eq]
    have hr0 : 0 < r := by linarith
    have key : deriv (fun τ => B0151.derivWord w (fun z' => tr.v τ z' k) z) r =
        B0151.derivWord w (fun z' => deriv (fun τ => tr.v τ z' k) r) z :=
      swtc_main (fun p : ℝ × Plane => tr.v p.1 p.2 k) hv_on w r z hr0
    have hfun : (fun z' => deriv (fun τ => tr.v τ z' k) r) =
        fun y => deriv (fun τ => tr.v τ y) r k := by
      funext y
      exact deriv_comp_proj (g := fun τ => tr.v τ y)
        (TrainErrorEquation.differentiableAt_time tr hr0 y) k
    rw [hfun] at key
    exact key
  have hC : ∀ z, ContDiff ℝ 1 (fun r => wordComp w (tr.v (loc s r)) k z) := fun z =>
    ContDiffOn.comp_contDiff ((hw_smooth z).of_le (by exact_mod_cast le_top))
      ((contDiff_loc s).of_le (by exact_mod_cast le_top)) (fun x => loc_pos hs x)
  have hF : MemLp (fun z => wordComp w (tr.v (loc s s)) k z) 2 (Cyl.cellμ c) := by
    rw [loc_self]
    obtain ⟨εv, hεv, Kv, hKv⟩ := velJetLocalL2_proof ν c hν hc tr htr s hs w k
    exact (hKv s hs (by simp [hεv])).1
  have hD : ∀ r, |r - s| < min ε0 (s / 4) →
      MemLp (fun z => deriv (fun t => wordComp w (tr.v (loc s t)) k z) r) 2 (Cyl.cellμ c) ∧
      ∫ z, (deriv (fun t => wordComp w (tr.v (loc s t)) k z) r) ^ 2 ∂(Cyl.cellμ c) ≤ K0 := by
    intro r hr
    have hr1 : |r - s| < ε0 := lt_of_lt_of_le hr (min_le_left _ _)
    have hr2 : |r - s| < s / 4 := lt_of_lt_of_le hr (min_le_right _ _)
    have hr34 : 3 * s / 4 < r := by have := (abs_lt.1 hr2).1; linarith
    obtain ⟨hm, hint⟩ := hK r (by linarith) hr1
    simp only [hw_loc_deriv hr34]
    exact ⟨hm, hint⟩
  obtain ⟨hev, hder⟩ := L2SqDeriv.l2Sq_hasDerivAt (μ := Cyl.cellμ c)
    (fun r z => wordComp w (tr.v (loc s r)) k z) s (min ε0 (s / 4)) K0 hεpos hC hF hD
  have hs34 : 3 * s / 4 < s := by linarith
  have hV : (2 * ∫ z, wordComp w (tr.v (loc s s)) k z *
      deriv (fun t => wordComp w (tr.v (loc s t)) k z) s ∂(Cyl.cellμ c)) =
      2 * ∫ z in Cyl.cell c, wordComp w (tr.v s) k z *
        wordComp w (fun y => deriv (fun t => tr.v t y) s) k z := by
    congr 2
    funext z
    rw [loc_self, hw_loc_deriv hs34 z]
  refine ⟨?_, (hK s hs (by simp [hε0])).1, ?_⟩
  · filter_upwards [hev, Ioi_mem_nhds hs34] with r hr hr2
    rw [loc_eq_id hs hr2] at hr
    exact hr
  · have hfuneq : (fun r => ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2) =ᶠ[𝓝 s]
        (fun r => ∫ z in Cyl.cell c, (wordComp w (tr.v (loc s r)) k z) ^ 2) := by
      filter_upwards [Ioi_mem_nhds hs34] with r hr
      rw [loc_eq_id hs hr]
    rw [← hV]
    exact hder.congr_of_eventuallyEq hfuneq

theorem vel_jetEnergy_timeDeriv {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    HasDerivAt (fun r => jetEnergy c j (tr.v r))
      (2 * jetPair c j (tr.v s) (fun y => deriv (fun t => tr.v t y) s)) s := by
  have H := fun (w : List Bool) (k : Fin 2) => vel_wordEnergy_hasDerivAt hν hc tr htr hs w k
  set d : Plane → Vec := fun y => deriv (fun t => tr.v t y) s
  have hev : ∀ᶠ r in 𝓝 s, ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c) := by
    rw [Filter.eventually_all_finset]
    intro w _
    rw [Filter.eventually_all]
    exact fun k => (H w k).1
  have hs0 : ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      MemLp (wordComp w (tr.v s) k) 2 (Cyl.cellμ c) :=
    fun w _ k => (H w k).1.self_of_nhds
  have hder : HasDerivAt (fun r => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2)
      (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, 2 * ∫ z in Cyl.cell c,
        wordComp w (tr.v s) k z * wordComp w d k z) s :=
    HasDerivAt.fun_sum fun w _ => HasDerivAt.fun_sum fun k _ => (H w k).2.2
  have hint : ∀ r, (∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c)) →
      jetEnergy c j (tr.v r) = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2 := by
    intro r hr
    unfold jetEnergy jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun w hw' => ?_
      rw [integral_finsetSum]
      · simp [sq]
      · exact fun k _ => (hr w hw' k).integrable_mul (hr w hw' k)
    · exact fun w hw' => integrable_finsetSum _ fun k _ => (hr w hw' k).integrable_mul (hr w hw' k)
  have hpair : jetPair c j (tr.v s) d = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell c, wordComp w (tr.v s) k z * wordComp w d k z := by
    unfold jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun w hw' => ?_
      rw [integral_finsetSum]
      exact fun k _ => (hs0 w hw' k).integrable_mul (H w k).2.1
    · exact fun w hw' => integrable_finsetSum _ fun k _ => (hs0 w hw' k).integrable_mul (H w k).2.1
  have hsum : (2 * jetPair c j (tr.v s) d) = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      2 * ∫ z in Cyl.cell c, wordComp w (tr.v s) k z * wordComp w d k z := by
    rw [hpair, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
  rw [hsum]
  exact hder.congr_of_eventuallyEq (by filter_upwards [hev] with r hr using hint r hr)

theorem vel_cellSmoothL2 {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) :
    CellSmoothL2 c (tr.v s) := by
  refine ⟨TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs.le,
    tr.isTrain.periodic_v s hs.le, fun w k => ?_⟩
  obtain ⟨ε, hε, K, hK⟩ := velJetLocalL2_proof ν c hν hc tr htr s hs w k
  exact (hK s hs (by simp [hε])).1

theorem vel_advection_smoothJetL2 {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) :
    SmoothJetL2 c (Train.advection (tr.v s)) := by
  open AdvLeib in
  have hcs := vel_cellSmoothL2 hν hc tr htr hs
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have Bv : ∀ k : Fin 2, AdvLeib.BW (fun x => tr.v s x k) := by
    intro k
    refine ⟨comp hcs.1 k, fun w => ?_⟩
    obtain ⟨M, hM⟩ := vjl_wordBoundedOn htr hs.le w k
    exact ⟨M, fun z => hM s ⟨hs.le, le_rfl⟩ z⟩
  have Lv : ∀ k : Fin 2, AdvLeib.LW c (fun x => tr.v s x k) := fun k =>
    ⟨comp hcs.1 k, fun w => hcs.2.2 w k⟩
  have key : ∀ (k : Fin 2) (z : Plane), Train.advection (tr.v s) z k =
      tr.v s z 0 * B0151.derivWord [true] (fun x => tr.v s x k) z +
      tr.v s z 1 * B0151.derivWord [false] (fun x => tr.v s x k) z := by
    intro k z
    fin_cases k <;> rfl
  have hLW : ∀ k : Fin 2, AdvLeib.LW c (fun x => Train.advection (tr.v s) x k) := by
    intro k
    have hG : AdvLeib.Gp c (fun z => Train.advection (tr.v s) z k) := by
      have g := AdvLeib.Gp.add
        (AdvLeib.Gp.prod (Bv 0) ((Lv k).deriv true))
        (AdvLeib.Gp.prod (Bv 1) ((Lv k).deriv false))
      convert g using 1
      funext z
      exact key k z
    exact hG.lw
  exact ⟨contDiff_euclidean.2 fun k => (hLW k).1, fun w k => (hLW k).2 w⟩

theorem vel_jetEnergy_balance {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    HasDerivAt (fun r => jetEnergy c j (tr.v r))
      (2 * (-ν * jetEnergy c (j + 1) (tr.v s) -
        jetPair c j (tr.v s) (Train.advection (tr.v s)))) s := by
  have hc0 : 0 < c := by linarith
  have hder := vel_jetEnergy_timeDeriv hν hc tr htr hs j
  have hcs := vel_cellSmoothL2 hν hc tr htr hs
  have hcomp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have hLap : SmoothJetL2 c (fun y => ν • Train.vecLaplacian (tr.v s) y) := by
    refine ⟨?_, fun w k => ?_⟩
    · refine contDiff_euclidean.2 fun k => ?_
      have key : ContDiff ℝ ∞ (fun z => ν * Train.lapS (fun y => tr.v s y k) z) :=
        contDiff_const.mul (lapLocal_lapS_contDiff (hcomp hcs.1 k))
      have e : ∀ z : Plane, ((ν • Train.vecLaplacian (tr.v s) z) k) =
          ν * Train.lapS (fun y => tr.v s y k) z := fun z => by
        simp only [PiLp.smul_apply, smul_eq_mul, lapLocal_vecLap_apply]
      simp only [e]
      exact key
    · have hk : ContDiff ℝ ∞ (fun y => tr.v s y k) := hcomp hcs.1 k
      have eq : wordComp w (fun x => ν • Train.vecLaplacian (tr.v s) x) k =
          fun z => ν * (wordComp (true :: true :: w) (tr.v s) k z +
            wordComp (false :: false :: w) (tr.v s) k z) := by
        funext z
        have e1' : (fun x => (ν • Train.vecLaplacian (tr.v s) x) k) =
            fun x => ν * Train.lapS (fun y => tr.v s y k) x := by
          funext x
          rw [PiLp.smul_apply, smul_eq_mul, lapLocal_vecLap_apply]
        calc wordComp w (fun x => ν • Train.vecLaplacian (tr.v s) x) k z
            = B0151.derivWord w (fun x => ν * Train.lapS (fun y => tr.v s y k) x) z := by
              unfold wordComp; rw [e1']
          _ = ν * B0151.derivWord w (fun x => Train.lapS (fun y => tr.v s y k) x) z :=
              lapLocal_dw_const_mul ν w _ z
          _ = ν * Train.lapS (B0151.derivWord w (fun y => tr.v s y k)) z := by
              rw [JetViscIBP.derivWord_lap w _ hk]
          _ = ν * (wordComp (true :: true :: w) (tr.v s) k z +
                wordComp (false :: false :: w) (tr.v s) k z) := by
              rw [lapLocal_lapS_dw]; rfl
      rw [eq]
      exact ((hcs.2.2 (true :: true :: w) k).add (hcs.2.2 (false :: false :: w) k)).const_mul ν
  have hAdv : SmoothJetL2 c (Train.advection (tr.v s)) :=
    vel_advection_smoothJetL2 hν hc tr htr hs
  have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hDt : SmoothJetL2 c (fun y => deriv (fun t => tr.v t y) s) :=
    ⟨ErrPressureLapAux.dt_contDiff hvU hs,
      fun w k => (vel_wordEnergy_hasDerivAt hν hc tr htr hs w k).2.1⟩
  have hGradP_eq : Train.gradS (tr.p s) =
      fun y => ((fun z => ν • Train.vecLaplacian (tr.v s) z) y -
        (fun z => deriv (fun t => tr.v t z) s) y) - Train.advection (tr.v s) y := by
    funext y
    have hmom := tr.isTrain.momentum s hs y
    unfold Train.momentumResidual at hmom
    linear_combination (norm := module) hmom
  have hGradP : SmoothJetL2 c (Train.gradS (tr.p s)) := by
    rw [hGradP_eq]
    exact pairSplit_smoothJetL2_sub (pairSplit_smoothJetL2_sub hLap hDt) hAdv
  have hDt_eq : (fun y => deriv (fun t => tr.v t y) s) =
      fun y => ((fun z => ν • Train.vecLaplacian (tr.v s) z) y - Train.advection (tr.v s) y) -
        Train.gradS (tr.p s) y := by
    funext y
    have hmom := tr.isTrain.momentum s hs y
    unfold Train.momentumResidual at hmom
    linear_combination (norm := module) hmom
  have hsplit : jetPair c j (tr.v s) (fun y => deriv (fun t => tr.v t y) s) =
      -ν * jetEnergy c (j + 1) (tr.v s) - jetPair c j (tr.v s) (Train.advection (tr.v s)) := by
    rw [hDt_eq,
      pairSplit_jetPair_sub j hcs.2.2 (pairSplit_smoothJetL2_sub hLap hAdv) hGradP,
      pairSplit_jetPair_sub j hcs.2.2 hLap hAdv,
      pairSplit_jetPair_smul,
      jetViscousIBP_proof c hc0 (tr.v s) hcs j]
    have hps : ContDiff ℝ ∞ (tr.p s) :=
      TrainErrorEquation.contDiff_slice tr.isTrain.smooth_p hs.le
    have hp_bd : ∃ M : ℝ, ∀ z : Plane, |tr.p s z| ≤ M :=
      periodicDecayBounded_proof c hc0 (tr.p s) hps.continuous
        (tr.isTrain.periodic_p s hs.le) (tr.isTrain.pressure_decay s hs.le)
    have horth := jetPressureOrth_proof c hc0 (tr.v s) hcs (tr.isTrain.solenoidal s hs.le)
      (tr.p s) hps (tr.isTrain.periodic_p s hs.le) hp_bd hGradP.2 j
    rw [horth]
    ring
  rw [hsplit] at hder
  exact hder

/-- **Exact jet energy balance for the overlap-rescaled velocity `U = overlapField ν c tr.v`**
on the unit cylinder for all `T ≥ 0` (source lines 379-387). -/
theorem overlap_jetEnergy_balance {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    let U := overlapField ν c tr.v
    HasDerivAt (fun t => jetEnergy 1 j (U t))
      (2 * (-jetEnergy 1 (j + 1) (U T) -
        eC ν c * jetPair 1 j (U T) (Train.advection (U T)))) T := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hc1 : 1 ≤ c := hc.le
  set s : ℝ := B0155.ageOf ν c T with hs_def
  have hs0 : 0 < B0146.overlapAge ν c := by
    unfold B0146.overlapAge
    exact div_pos (by nlinarith) hν
  have hs : 0 < s := by
    rw [hs_def, B0155.ageOf, ← overlapAge_eq_age]
    have : 0 ≤ c ^ 2 / ν * T := mul_nonneg (div_nonneg (sq_nonneg c) hν.le) hT
    linarith
  have hU_scale : ∀ t : ℝ, overlapField ν c tr.v t = scaleField c (tr.v (B0155.ageOf ν c t)) := by
    intro t
    funext y
    simp only [overlapField, scaleField, B0155.ageOf, overlapAge_eq_age]
    congr 2
    ring
  have hfun : (fun t => jetEnergy 1 j (overlapField ν c tr.v t)) =
      fun t => c ^ 4 * c ^ (2 * j) * jetEnergy c j (tr.v (B0155.ageOf ν c t)) := by
    funext t
    rw [hU_scale t, jetEnergy_scaleField hc0 j]
  have hage_deriv : HasDerivAt (B0155.ageOf ν c) (c ^ 2 / ν) T := by
    unfold B0155.ageOf
    simpa using (hasDerivAt_id T).const_mul (c ^ 2 / ν) |>.const_add (B0155.age ν c)
  have hcomp_deriv : HasDerivAt (fun t => c ^ 4 * c ^ (2 * j) * jetEnergy c j (tr.v (B0155.ageOf ν c t)))
      (c ^ 4 * c ^ (2 * j) *
        (2 * (-ν * jetEnergy c (j + 1) (tr.v s) -
          jetPair c j (tr.v s) (Train.advection (tr.v s))) * (c ^ 2 / ν))) T :=
    ((vel_jetEnergy_balance hν hc1 tr htr hs j).comp T hage_deriv).const_mul (c ^ 4 * c ^ (2 * j))
  rw [← hfun] at hcomp_deriv
  refine hcomp_deriv.congr_deriv ?_
  rw [hU_scale T, jetEnergy_scaleField hc0 (j + 1) (tr.v s),
    jetPair_advection_scaleField hc0 j (tr.v s)]
  unfold eC
  have hν0 : ν ≠ 0 := hν.ne'
  have hc0' : c ≠ 0 := hc0.ne'
  rw [Nat.mul_add, pow_add]
  field_simp
  ring

/-! ### 3. Tame higher-order inequality and high-norm energy inequality on the unit cylinder -/

theorem overlapField_eq_scaleField (ν c : ℝ) (v : ℝ → Plane → Vec) (t : ℝ) :
    overlapField ν c v t = scaleField c (v (B0155.ageOf ν c t)) := by
  funext y
  simp only [overlapField, scaleField, B0155.ageOf, overlapAge_eq_age]
  congr 2
  ring

theorem overlapAgeOf_pos {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c) {T : ℝ} (hT : 0 ≤ T) :
    0 < B0155.ageOf ν c T := by
  rw [B0155.ageOf, ← overlapAge_eq_age]
  have hs0 : 0 < B0146.overlapAge ν c := by
    unfold B0146.overlapAge
    exact div_pos (by nlinarith) hν
  have hT0 : 0 ≤ c ^ 2 / ν * T := mul_nonneg (div_nonneg (sq_nonneg c) hν.le) hT
  linarith

theorem overlapField_cellSmoothL2 {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) :
    CellSmoothL2 1 (overlapField ν c tr.v T) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hs : 0 < B0155.ageOf ν c T := overlapAgeOf_pos hν hc hT
  have hcs := vel_cellSmoothL2 hν hc.le tr htr hs
  have hsm : ContDiff ℝ ∞ (overlapField ν c tr.v T) := by
    rw [overlapField_eq_scaleField]
    unfold scaleField
    exact (hcs.1.comp (contDiff_id.const_smul c)).const_smul (c ^ 3)
  refine ⟨hsm, (overlap_equation_of_trainSol hν hc tr).1.periodic_U T hT, fun w k => ?_⟩
  have hwk_sm : ContDiff ℝ ∞ (wordComp w (overlapField ν c tr.v T) k) :=
    contDiff_wordComp hsm w k
  rw [memLp_two_iff_integrable_sq hwk_sm.continuous.aestronglyMeasurable]
  have hsq : (fun Z : Plane => (wordComp w (overlapField ν c tr.v T) k Z) ^ 2) =
      fun Z : Plane => (c ^ 3 * c ^ w.length) ^ 2 *
        (wordComp w (tr.v (B0155.ageOf ν c T)) k (B0155.dil c Z)) ^ 2 := by
    funext Z
    rw [overlapField_eq_scaleField, wordComp_scaleField]
    ring
  rw [hsq]
  exact B0155.integrableOn_cell_one_dil hc0 (hcs.2.2 w k).integrable_sq ((c ^ 3 * c ^ w.length) ^ 2)

theorem overlapField_jthyp {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) {G : ℝ}
    (hG : ∀ (β : Bool) (k : Fin 2) (z : Plane),
      |wordComp [β] (overlapField ν c tr.v T) k z| ≤ G) :
    JTHyp 1 (fun _ => 0) (overlapField ν c tr.v T) G (fun _ => 0) := by
  have hs : 0 < B0155.ageOf ν c T := overlapAgeOf_pos hν hc hT
  refine ⟨le_rfl, contDiff_const, fun _ => rfl, ?_,
    overlapField_cellSmoothL2 hν hc tr htr hT,
    (overlap_equation_of_trainSol hν hc tr).1.solenoidal T hT, ?_, hG, ?_⟩
  · intro z
    simp [Cyl.divergence, Cyl.partialQ, Cyl.partialEta]
  · intro w k
    obtain ⟨M, hM⟩ := vjl_wordBoundedOn htr hs.le w k
    refine ⟨|c ^ 3 * c ^ w.length| * M, fun z => ?_⟩
    rw [overlapField_eq_scaleField, wordComp_scaleField, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (hM (B0155.ageOf ν c T) ⟨hs.le, le_rfl⟩ (B0155.dil c z)) (abs_nonneg _)
  · intro w k z
    have h0 : wordComp w (fun _ : Plane => (0 : Vec)) k z = 0 := by
      have hfun : (fun x : Plane => (0 : Vec) k) = fun x => 0 * (0 : ℝ) := by
        funext x; simp
      unfold wordComp
      rw [hfun, lapLocal_dw_const_mul 0 w (fun _ => (0 : ℝ)) z, zero_mul]
    rw [h0, abs_zero]

theorem jetPair_zero_advection {f : Plane → Vec} {G : ℝ}
    (H : JTHyp 1 (fun _ => 0) f G (fun _ => 0)) :
    jetPair 1 0 f (Train.advection f) = 0 := by
  have hf := H.2.2.2.2.1
  have hfb := H.2.2.2.2.2.2.1
  rw [advection_eq_advB, jtExpand_proof 0 1 f f f hf.1 hf.1 hf (Or.inl hf) hfb hfb]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hw0 : w = [] := List.eq_nil_of_length_eq_zero (mem_wordsOfLength_length hw)
  subst hw0
  simp only [wacSplits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact jtQTop_proof 1 (fun _ => 0) f G (fun _ => 0) H []

theorem sum_abs_jetPair_advection_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : Plane → Vec} {G : ℝ},
      JTHyp 1 (fun _ => 0) f G (fun _ => 0) →
      ∑ j ∈ Finset.range (k + 1), |jetPair 1 j f (Train.advection f)| ≤
        C * G * cylDissipationSq k f ∧
      ∑ j ∈ Finset.range (k + 1), |jetPair 1 j f (Train.advection f)| ≤
        C * G * cylSobolevSq k f := by
  choose A hA hQ using jtQuad_proof
  refine ⟨1 + ∑ j ∈ Finset.range (k + 1), A j,
    by have : 0 ≤ ∑ j ∈ Finset.range (k + 1), A j := Finset.sum_nonneg fun j _ => hA j; linarith,
    fun {f G} H => ?_⟩
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (H.2.2.2.2.2.2.2.1 true 0 (0, 0))
  have hC_ge : ∑ j ∈ Finset.range (k + 1), A j ≤ 1 + ∑ j ∈ Finset.range (k + 1), A j := by linarith
  have hterm_diss : ∀ j ∈ Finset.range (k + 1),
      |jetPair 1 j f (Train.advection f)| ≤ A j * (G * cylDissipationSq k f) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj_pos
    · rw [jetPair_zero_advection H, abs_zero]
      exact mul_nonneg (hA 0) (mul_nonneg hG0 (cylDissipationSq_nonneg k f))
    · have hj_le : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have h1 := (hQ j 1 (fun _ => 0) f G (fun _ => 0) H).2.2
      have h2 : jetEnergy 1 j f ≤ cylDissipationSq k f :=
        jetEnergy_le_cylDissipationSq hj_pos hj_le f
      exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hG0) (hA j))
  have hterm_sob : ∀ j ∈ Finset.range (k + 1),
      |jetPair 1 j f (Train.advection f)| ≤ A j * (G * cylSobolevSq k f) := by
    intro j hj
    have hj_le : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 := (hQ j 1 (fun _ => 0) f G (fun _ => 0) H).2.2
    have h2 : jetEnergy 1 j f ≤ cylSobolevSq k f :=
      jetEnergy_le_cylSobolevSq hj_le f
    exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hG0) (hA j))
  constructor
  · calc ∑ j ∈ Finset.range (k + 1), |jetPair 1 j f (Train.advection f)|
        ≤ ∑ j ∈ Finset.range (k + 1), A j * (G * cylDissipationSq k f) :=
          Finset.sum_le_sum hterm_diss
      _ = (∑ j ∈ Finset.range (k + 1), A j) * (G * cylDissipationSq k f) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + ∑ j ∈ Finset.range (k + 1), A j) * (G * cylDissipationSq k f) :=
          mul_le_mul_of_nonneg_right hC_ge (mul_nonneg hG0 (cylDissipationSq_nonneg k f))
      _ = (1 + ∑ j ∈ Finset.range (k + 1), A j) * G * cylDissipationSq k f := by ring
  · calc ∑ j ∈ Finset.range (k + 1), |jetPair 1 j f (Train.advection f)|
        ≤ ∑ j ∈ Finset.range (k + 1), A j * (G * cylSobolevSq k f) :=
          Finset.sum_le_sum hterm_sob
      _ = (∑ j ∈ Finset.range (k + 1), A j) * (G * cylSobolevSq k f) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + ∑ j ∈ Finset.range (k + 1), A j) * (G * cylSobolevSq k f) :=
          mul_le_mul_of_nonneg_right hC_ge (mul_nonneg hG0 (cylSobolevSq_nonneg k f))
      _ = (1 + ∑ j ∈ Finset.range (k + 1), A j) * G * cylSobolevSq k f := by ring

/-- **Tame higher-order overlap energy inequality** (source lines 350-358 and 385-389):
for every `k : ℕ`, there is `C_k > 0` such that whenever `|∂_β U_m(T)| ≤ G` on the unit cylinder,
`(1/2) d/dT ‖U‖_{H^k}² + ‖∇U‖_{H^k}² ≤ C_k e_c G ‖∇U‖_{H^k}²` and
`(1/2) d/dT ‖U‖_{H^k}² + ‖∇U‖_{H^k}² ≤ C_k e_c G ‖U‖_{H^k}²`. -/
theorem overlap_tame_energy_inequality (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ν c : ℝ}, 0 < ν → 1 < c →
        ∀ (tr : B0140.TrainSol ν c), IsBUCTrain tr →
          ∀ {T G : ℝ}, 0 ≤ T →
            (∀ (β : Bool) (m : Fin 2) (z : Plane),
              |wordComp [β] (overlapField ν c tr.v T) m z| ≤ G) →
            ∃ D : ℝ,
              HasDerivAt (fun t => cylSobolevSq k (overlapField ν c tr.v t)) D T ∧
              (1 / 2) * D + cylDissipationSq k (overlapField ν c tr.v T) ≤
                C * eC ν c * G * cylDissipationSq k (overlapField ν c tr.v T) ∧
              (1 / 2) * D + cylDissipationSq k (overlapField ν c tr.v T) ≤
                C * eC ν c * G * cylSobolevSq k (overlapField ν c tr.v T) := by
  obtain ⟨C, hC, hbound⟩ := sum_abs_jetPair_advection_le k
  refine ⟨C, hC, fun {ν c} hν hc tr htr {T G} hT hG => ?_⟩
  set U := overlapField ν c tr.v
  have H := overlapField_jthyp hν hc tr htr hT hG
  obtain ⟨hb_diss, hb_sob⟩ := hbound H
  have hder : HasDerivAt (fun t => cylSobolevSq k (U t))
      (∑ j ∈ Finset.range (k + 1),
        2 * (-jetEnergy 1 (j + 1) (U T) -
          eC ν c * jetPair 1 j (U T) (Train.advection (U T)))) T := by
    unfold cylSobolevSq
    exact HasDerivAt.fun_sum fun j _ => overlap_jetEnergy_balance hν hc tr htr hT j
  refine ⟨_, hder, ?_, ?_⟩
  · have hD_eq : (1 / 2) * (∑ j ∈ Finset.range (k + 1),
        2 * (-jetEnergy 1 (j + 1) (U T) -
          eC ν c * jetPair 1 j (U T) (Train.advection (U T)))) +
        cylDissipationSq k (U T) =
        -eC ν c * ∑ j ∈ Finset.range (k + 1), jetPair 1 j (U T) (Train.advection (U T)) := by
      unfold cylDissipationSq
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      have : (∑ x ∈ Finset.range (k + 1),
          (1 / 2 * (2 * (-jetEnergy 1 (x + 1) (U T) -
            eC ν c * jetPair 1 x (U T) (Train.advection (U T)))) +
            jetEnergy 1 (x + 1) (U T))) =
          ∑ x ∈ Finset.range (k + 1), (-eC ν c * jetPair 1 x (U T) (Train.advection (U T))) :=
        Finset.sum_congr rfl fun x _ => by ring
      rw [this, ← Finset.mul_sum]
    rw [hD_eq]
    have heC_pos : 0 ≤ eC ν c := by
      unfold eC
      have hc0 : 0 < c := zero_lt_one.trans hc
      positivity
    have hle1 : -eC ν c * ∑ j ∈ Finset.range (k + 1), jetPair 1 j (U T) (Train.advection (U T)) ≤
        eC ν c * ∑ j ∈ Finset.range (k + 1), |jetPair 1 j (U T) (Train.advection (U T))| := by
      have hsum_le : -(∑ j ∈ Finset.range (k + 1), jetPair 1 j (U T) (Train.advection (U T))) ≤
          ∑ j ∈ Finset.range (k + 1), |jetPair 1 j (U T) (Train.advection (U T))| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun j _ => neg_le_abs _
      nlinarith
    have hle2 := mul_le_mul_of_nonneg_left hb_diss heC_pos
    linarith
  · have hD_eq : (1 / 2) * (∑ j ∈ Finset.range (k + 1),
        2 * (-jetEnergy 1 (j + 1) (U T) -
          eC ν c * jetPair 1 j (U T) (Train.advection (U T)))) +
        cylDissipationSq k (U T) =
        -eC ν c * ∑ j ∈ Finset.range (k + 1), jetPair 1 j (U T) (Train.advection (U T)) := by
      unfold cylDissipationSq
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      have : (∑ x ∈ Finset.range (k + 1),
          (1 / 2 * (2 * (-jetEnergy 1 (x + 1) (U T) -
            eC ν c * jetPair 1 x (U T) (Train.advection (U T)))) +
            jetEnergy 1 (x + 1) (U T))) =
          ∑ x ∈ Finset.range (k + 1), (-eC ν c * jetPair 1 x (U T) (Train.advection (U T))) :=
        Finset.sum_congr rfl fun x _ => by ring
      rw [this, ← Finset.mul_sum]
    rw [hD_eq]
    have heC_pos : 0 ≤ eC ν c := by
      unfold eC
      have hc0 : 0 < c := zero_lt_one.trans hc
      positivity
    have hle1 : -eC ν c * ∑ j ∈ Finset.range (k + 1), jetPair 1 j (U T) (Train.advection (U T)) ≤
        eC ν c * ∑ j ∈ Finset.range (k + 1), |jetPair 1 j (U T) (Train.advection (U T))| := by
      have hsum_le : -(∑ j ∈ Finset.range (k + 1), jetPair 1 j (U T) (Train.advection (U T))) ≤
          ∑ j ∈ Finset.range (k + 1), |jetPair 1 j (U T) (Train.advection (U T))| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun j _ => neg_le_abs _
      nlinarith
    have hle2 := mul_le_mul_of_nonneg_left hb_sob heC_pos
    linarith

theorem supRhs_one_le_sqrt {C J0 J1 J2 E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (h0 : J0 ≤ E) (h1 : J1 ≤ E) (h2 : J2 ≤ E) :
    supRhs C 1 J0 J1 J2 ≤ 2 * C * Real.sqrt E := by
  unfold supRhs
  rw [Real.one_rpow, one_mul]
  have hs0 : Real.sqrt J0 ≤ Real.sqrt E := Real.sqrt_le_sqrt h0
  have hs1 : Real.sqrt J1 ≤ Real.sqrt E := Real.sqrt_le_sqrt h1
  have hs2 : Real.sqrt J2 ≤ Real.sqrt E := Real.sqrt_le_sqrt h2
  have hsq : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE
  have hp1 : (Real.sqrt J0 * Real.sqrt J2) ^ (1 / 2 : ℝ) ≤ Real.sqrt E := by
    rw [Real.sqrt_eq_rpow E]
    exact Real.rpow_le_rpow (by positivity)
      ((mul_le_mul hs0 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq hsq) (by positivity)
  have hp2 : (Real.sqrt J0 * Real.sqrt J1) ^ (1 / 2 : ℝ) ≤ Real.sqrt E := by
    rw [Real.sqrt_eq_rpow E]
    exact Real.rpow_le_rpow (by positivity)
      ((mul_le_mul hs0 hs1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq hsq) (by positivity)
  nlinarith

/-- **High-norm overlap energy inequality** (source lines 385-388):
for `N ≥ 3`, there is `C_N > 0` such that for `U = overlapField ν c tr.v` on the unit cylinder,
`(1/2) d/dT ‖U‖_{H^N}² + (1 - C_N e_c ‖U‖_{H^N}) ‖∇U‖_{H^N}² ≤ 0`. -/
theorem overlap_highnorm_energy_inequality (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ν c : ℝ}, 0 < ν → 1 < c →
        ∀ (tr : B0140.TrainSol ν c), IsBUCTrain tr →
          ∀ {T : ℝ}, 0 ≤ T →
            let U := overlapField ν c tr.v
            ∃ D : ℝ,
              HasDerivAt (fun t => cylSobolevSq N (U t)) D T ∧
              (1 / 2) * D +
                (1 - C * eC ν c * Real.sqrt (cylSobolevSq N (U T))) *
                  cylDissipationSq N (U T) ≤ 0 := by
  obtain ⟨Ct, hCt, htame⟩ := overlap_tame_energy_inequality N
  obtain ⟨Cb, hCb, hbridge⟩ := jetSupBridge_proof 1
  refine ⟨Ct * (2 * (Cb + 1)), by positivity, fun {ν c} hν hc tr htr {T} hT => ?_⟩
  set U := overlapField ν c tr.v
  have hcs := overlapField_cellSmoothL2 hν hc tr htr hT
  have hG : ∀ (β : Bool) (m : Fin 2) (z : Plane),
      |wordComp [β] (U T) m z| ≤ 2 * (Cb + 1) * Real.sqrt (cylSobolevSq N (U T)) := by
    intro β m z
    have h1 := (hbridge 1 le_rfl (U T) hcs).1 [β] rfl m z
    have h2 : supRhs Cb 1 (jetEnergy 1 1 (U T)) (jetEnergy 1 2 (U T)) (jetEnergy 1 3 (U T)) ≤
        supRhs (Cb + 1) 1 (jetEnergy 1 1 (U T)) (jetEnergy 1 2 (U T)) (jetEnergy 1 3 (U T)) := by
      unfold supRhs
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : supRhs (Cb + 1) 1 (jetEnergy 1 1 (U T)) (jetEnergy 1 2 (U T)) (jetEnergy 1 3 (U T)) ≤
        2 * (Cb + 1) * Real.sqrt (cylSobolevSq N (U T)) :=
      supRhs_one_le_sqrt (by linarith) (cylSobolevSq_nonneg N (U T))
        (jetEnergy_le_cylSobolevSq (by omega) (U T))
        (jetEnergy_le_cylSobolevSq (by omega) (U T))
        (jetEnergy_le_cylSobolevSq hN (U T))
    exact (h1.trans h2).trans h3
  obtain ⟨D, hder, hdiss, _⟩ := htame hν hc tr htr hT hG
  refine ⟨D, hder, ?_⟩
  linarith

/-! ### 4. Initial datum bound, bootstrap continuity, and uniform high-norm bound (`PartI:T12`) -/

theorem jetEnergy_le_of_cellL2_le {f : Plane → Vec} (hf : CellSmoothL2 1 f) (j : ℕ)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hL2 : cellL2 1 (jet j f) ≤ ENNReal.ofReal C₀) :
    jetEnergy 1 j f ≤ 2 * 2 ^ j * C₀ ^ 2 := by
  have hproj : ∀ k : Fin 2, ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    fun k => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x k)
  have hpt : ∀ w ∈ wordsOfLength j, ∀ (k : Fin 2) (z : Plane),
      |wordComp w f k z| ≤ ‖jet j f z‖ := by
    intro w hw k z
    have hlen : w.length = j := mem_wordsOfLength_length hw
    have hg : ContDiff ℝ ∞ (fun x => f x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hf.1
    have hw_le := (cylJetWord_proof (fun x => f x k) hg j z).1 w hlen
    have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (f := f) (x := z) (n := j) hf.1.contDiffAt (by exact_mod_cast le_top)
    have h1 : ‖iteratedFDeriv ℝ j (fun x => f x k) z‖ ≤ ‖iteratedFDeriv ℝ j f z‖ := by
      calc ‖iteratedFDeriv ℝ j (fun x => f x k) z‖
          ≤ ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
              ‖iteratedFDeriv ℝ j f z‖ := hcomp
        _ ≤ 1 * ‖iteratedFDeriv ℝ j f z‖ :=
            mul_le_mul_of_nonneg_right (hproj k) (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ j f z‖ := one_mul _
    exact hw_le.trans h1
  have hword_int : ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      ∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2 ≤ C₀ ^ 2 := by
    intro w hw k
    have hmono : eLpNorm (fun z => |wordComp w f k z|) 2 (Cyl.cellμ 1) ≤ cellL2 1 (jet j f) := by
      unfold cellL2
      apply eLpNorm_mono
      intro z
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      exact hpt w hw k z
    have heq := jl2_abs_eLpNorm (Cyl.cellμ 1) (wordComp w f k) (hf.2.2 w k)
    have hle : ENNReal.ofReal (Real.sqrt (∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2)) ≤
        ENNReal.ofReal C₀ :=
      heq ▸ (hmono.trans hL2)
    have hsqrt : Real.sqrt (∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2) ≤ C₀ :=
      (ENNReal.ofReal_le_ofReal_iff hC₀).1 hle
    have hint_nn : 0 ≤ ∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    calc ∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2
        = (Real.sqrt (∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2)) ^ 2 :=
          (Real.sq_sqrt hint_nn).symm
      _ ≤ C₀ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  have hJ : jetEnergy 1 j f = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2 := by
    unfold jetEnergy jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [integral_finsetSum]
      · simp [sq]
      · exact fun k _ => (hf.2.2 w k).integrable_mul (hf.2.2 w k)
    · exact fun w _ => integrable_finsetSum _ fun k _ => (hf.2.2 w k).integrable_mul (hf.2.2 w k)
  rw [hJ]
  calc ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∫ z in Cyl.cell 1, (wordComp w f k z) ^ 2
      ≤ ∑ _w ∈ wordsOfLength j, ∑ _k : Fin 2, C₀ ^ 2 :=
        Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun k _ => hword_int w hw k
    _ = ((wordsOfLength j).card : ℝ) * (2 * C₀ ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
    _ ≤ (2 ^ j : ℝ) * (2 * C₀ ^ 2) := by
        have hcard : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by
          exact_mod_cast card_wordsOfLength_le j
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * 2 ^ j * C₀ ^ 2 := by ring

/-- Uniform bound on the unit-cylinder Sobolev squared norm `cylSobolevSq N' (U T)` for all `T ≥ 0`
by bootstrap continuity from `T = 0` (`PartI:T11`). -/
theorem overlap_sobolevSq_uniform (ρ : ℝ) (hρ : 1 / 2 < ρ) (N' : ℕ) (hN' : 3 ≤ N') :
    ∃ E₀ ν₀ : ℝ, 0 < E₀ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ T : ℝ, 0 ≤ T →
            cylSobolevSq N' (overlapField ν (trainPeriod ρ ν) tr.v T) ≤ E₀ := by
  obtain ⟨C₀, ν₀, hC₀, hν₀, hdatum⟩ := overlap_rescaled_equation_and_datum ρ hρ N'
  obtain ⟨C₁, hC₁, henergy⟩ := overlap_highnorm_energy_inequality N' hN'
  set E₀ : ℝ := ∑ j ∈ Finset.range (N' + 1), 2 * 2 ^ j * C₀ ^ 2 with hE₀_def
  have hE₀ : 0 < E₀ := by
    have h0 : 0 < 2 * 2 ^ 0 * C₀ ^ 2 := by positivity
    have hle : 2 * 2 ^ 0 * C₀ ^ 2 ≤ E₀ :=
      Finset.single_le_sum (f := fun j : ℕ => 2 * 2 ^ j * C₀ ^ 2)
        (fun j _ => by positivity) (Finset.mem_range.2 (Nat.zero_lt_succ N'))
    linarith
  set R : ℝ := max 1 (C₁ * Real.sqrt (2 * E₀))
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨ν₁, hν₁, _, hperiod⟩ := trainPeriodAsymptotics_proof ρ hρ R hR
  refine ⟨E₀, min ν₀ (min ν₁ (1 / 2)), hE₀,
    lt_min hν₀ (lt_min hν₁ (by norm_num)), fun ν hν hν_le tr htr T hT => ?_⟩
  have hν_0 : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν_1 : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc_gt1 : 1 < c := by
    change 1 < trainPeriod ρ ν
    unfold trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans hc_gt1
  have hR_le : R ≤ ν * c ^ 2 := (hperiod ν hν hν_1).2
  let U := overlapField ν c tr.v
  -- Initial bound at `T = 0`
  have hU0_le : cylSobolevSq N' (U 0) ≤ E₀ := by
    have hcs0 := overlapField_cellSmoothL2 hν hc_gt1 tr htr le_rfl
    have hd0 := (hdatum ν hν hν_0 tr htr).2.2
    unfold cylSobolevSq
    rw [hE₀_def]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_le : j ≤ N' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact jetEnergy_le_of_cellL2_le hcs0 j hC₀.le (hd0 j hj_le).1
  -- Energy derivative at every `t ≥ 0`
  have hder_all : ∀ t : ℝ, 0 ≤ t →
      ∃ D : ℝ, HasDerivAt (fun τ => cylSobolevSq N' (U τ)) D t ∧
        (1 / 2) * D +
          (1 - C₁ * eC ν c * Real.sqrt (cylSobolevSq N' (U t))) *
            cylDissipationSq N' (U t) ≤ 0 :=
    fun t ht => henergy hν hc_gt1 tr htr ht
  choose D hD_deriv hD_ineq using hder_all
  have hg_cont : ContinuousOn (fun t => cylSobolevSq N' (U t)) (Icc 0 T) := by
    intro t ht
    exact (hD_deriv t ht.1).continuousAt.continuousWithinAt
  have hboot := bootstrapContinuity_proof T hT
    (fun t => cylSobolevSq N' (U t)) (fun _ => 2 * E₀)
    hg_cont continuousOn_const (fun _ _ => by linarith) (by linarith)
    (fun s hs hle_on => ?_) T ⟨hT, le_rfl⟩
  · change cylSobolevSq N' (U T) ≤ E₀
    linarith
  · have hanti : AntitoneOn (fun t => cylSobolevSq N' (U t)) (Icc 0 s) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 s)
        (f' := fun t => deriv (fun τ => cylSobolevSq N' (U τ)) t)
      · exact hg_cont.mono (Icc_subset_Icc_right hs.2)
      · intro t ht
        have htI : t ∈ Icc 0 s := interior_subset ht
        exact (hD_deriv t htI.1).differentiableAt.hasDerivAt.hasDerivWithinAt
      · intro t ht
        have htI : t ∈ Icc 0 s := interior_subset ht
        have ht0 : 0 ≤ t := htI.1
        rw [(hD_deriv t ht0).deriv]
        have hgt : cylSobolevSq N' (U t) ≤ 2 * E₀ := hle_on t htI
        have hsqrt_le : Real.sqrt (cylSobolevSq N' (U t)) ≤ Real.sqrt (2 * E₀) :=
          Real.sqrt_le_sqrt hgt
        have heC_pos : 0 ≤ eC ν c := by unfold eC; positivity
        have hprod_le : C₁ * eC ν c * Real.sqrt (cylSobolevSq N' (U t)) ≤ 1 := by
          have h1 : C₁ * eC ν c * Real.sqrt (cylSobolevSq N' (U t)) ≤
              C₁ * eC ν c * Real.sqrt (2 * E₀) :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
          have h2 : C₁ * eC ν c * Real.sqrt (2 * E₀) ≤ 1 := by
            unfold eC
            have hvc_pos : 0 < ν * c ^ 2 := by positivity
            have hCR : C₁ * Real.sqrt (2 * E₀) ≤ ν * c ^ 2 :=
              (le_max_right 1 _).trans hR_le
            calc C₁ * (ν * c ^ 2)⁻¹ * Real.sqrt (2 * E₀)
                = (C₁ * Real.sqrt (2 * E₀)) / (ν * c ^ 2) := by ring
              _ ≤ 1 := (div_le_one hvc_pos).2 hCR
          exact h1.trans h2
        have hdiss_nonneg : 0 ≤ (1 - C₁ * eC ν c * Real.sqrt (cylSobolevSq N' (U t))) *
            cylDissipationSq N' (U t) :=
          mul_nonneg (by linarith) (cylDissipationSq_nonneg N' (U t))
        have hineq := hD_ineq t ht0
        linarith
    have hs_le : cylSobolevSq N' (U s) ≤ cylSobolevSq N' (U 0) :=
      hanti ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
    linarith

/-- Single-order uniform overlap bound for order `j : ℕ`. -/
theorem overlap_highnorm_bound_j (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ T : ℝ, 0 ≤ T →
            let U := overlapField ν (trainPeriod ρ ν) tr.v T
            cellL2 1 (jet j U) ≤ ENNReal.ofReal C ∧
            B0277.supNormD j U ≤ ENNReal.ofReal C := by
  set N' : ℕ := max (j + 2) 3
  obtain ⟨E₀, ν₀, hE₀, hν₀, hsob⟩ := overlap_sobolevSq_uniform ρ hρ N' (le_max_right _ _)
  obtain ⟨Cl2, hCl2, hbridge_l2⟩ := jetL2Bridge_proof j
  obtain ⟨Csup, hCsup, hbridge_sup⟩ := jetSupBridge_proof j
  set C : ℝ := (Cl2 + 2 * Csup + 1) * Real.sqrt E₀
  have hC : 0 < C := by positivity
  refine ⟨C, min ν₀ (1 / 2), hC, lt_min hν₀ (by norm_num),
    fun ν hν hν_le tr htr T hT => ?_⟩
  have hν_0 : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc_gt1 : 1 < c := by
    change 1 < trainPeriod ρ ν
    unfold trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  let U := overlapField ν c tr.v T
  have hcs := overlapField_cellSmoothL2 hν hc_gt1 tr htr hT
  have hE := hsob ν hν hν_0 tr htr T hT
  have hj0 : j ≤ N' := by omega
  have hj1 : j + 1 ≤ N' := by omega
  have hj2 : j + 2 ≤ N' := le_max_left _ _
  have hJ0 : jetEnergy 1 j U ≤ E₀ := (jetEnergy_le_cylSobolevSq hj0 U).trans hE
  have hJ1 : jetEnergy 1 (j + 1) U ≤ E₀ := (jetEnergy_le_cylSobolevSq hj1 U).trans hE
  have hJ2 : jetEnergy 1 (j + 2) U ≤ E₀ := (jetEnergy_le_cylSobolevSq hj2 U).trans hE
  refine ⟨?_, ?_⟩
  · calc cellL2 1 (jet j U)
        ≤ ENNReal.ofReal (Cl2 * Real.sqrt (jetEnergy 1 j U)) := hbridge_l2 1 le_rfl U hcs
      _ ≤ ENNReal.ofReal C := by
          apply ENNReal.ofReal_le_ofReal
          have hs0 : Real.sqrt (jetEnergy 1 j U) ≤ Real.sqrt E₀ := Real.sqrt_le_sqrt hJ0
          have h1 : Cl2 * Real.sqrt (jetEnergy 1 j U) ≤ Cl2 * Real.sqrt E₀ :=
            mul_le_mul_of_nonneg_left hs0 hCl2
          have h2 : Cl2 * Real.sqrt E₀ ≤ C :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
          exact h1.trans h2
  · calc B0277.supNormD j U
        ≤ ENNReal.ofReal (supRhs Csup 1 (jetEnergy 1 j U)
            (jetEnergy 1 (j + 1) U) (jetEnergy 1 (j + 2) U)) :=
          (hbridge_sup 1 le_rfl U hcs).2
      _ ≤ ENNReal.ofReal C := by
          apply ENNReal.ofReal_le_ofReal
          have h1 := supRhs_one_le_sqrt hCsup hE₀.le hJ0 hJ1 hJ2
          have h2 : 2 * Csup * Real.sqrt E₀ ≤ C :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
          exact h1.trans h2

/-- **`PartI:T12` (`overlap_highnorm_uniform`)** (source lines 350-358 and 379-389):
for every `ρ > 1/2` and derivative budget `N : ℕ`, there exist `C > 0` and `ν₀ > 0` such that
for all `0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, every overlap time
`T ≥ 0`, and every `j ≤ N`, the overlap-rescaled velocity `U(T) = overlapField ν c tr.v T` on the
unit cylinder satisfies `cellL2 1 (jet j (U T)) ≤ ofReal C` and `supNormD j (U T) ≤ ofReal C`. -/
theorem overlap_highnorm_uniform : OverlapHighNormUniform := by
  intro ρ hρ N
  induction N with
  | zero =>
    obtain ⟨C₀, ν₀, hC₀, hν₀, h0⟩ := overlap_highnorm_bound_j ρ hρ 0
    refine ⟨C₀, ν₀, hC₀, hν₀, fun ν hν hν_le tr htr T hT j hj => ?_⟩
    have hj0 : j = 0 := Nat.le_zero.1 hj
    subst hj0
    exact h0 ν hν hν_le tr htr T hT
  | succ N ih =>
    obtain ⟨CN, νN, hCN, hνN, hN⟩ := ih
    obtain ⟨C1, ν1, hC1, hν1, h1⟩ := overlap_highnorm_bound_j ρ hρ (N + 1)
    refine ⟨max CN C1, min νN ν1, lt_max_of_lt_left hCN, lt_min hνN hν1,
      fun ν hν hν_le tr htr T hT j hj => ?_⟩
    have hν_N : ν ≤ νN := hν_le.trans (min_le_left _ _)
    have hν_1 : ν ≤ ν1 := hν_le.trans (min_le_right _ _)
    rcases Nat.of_le_succ hj with hjN | rfl
    · obtain ⟨hL, hS⟩ := hN ν hν hν_N tr htr T hT j hjN
      exact ⟨hL.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
        hS.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    · obtain ⟨hL, hS⟩ := h1 ν hν hν_1 tr htr T hT
      exact ⟨hL.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)),
        hS.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩

/-- Alias matching the `OverlapAndTailsDesign` naming convention. -/
theorem overlapHighNormUniform_proof : OverlapHighNormUniform :=
  overlap_highnorm_uniform

end UnforcedLeray.Short.PartI
