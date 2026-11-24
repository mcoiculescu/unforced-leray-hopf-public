import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.SliceDef
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8
import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction.FreeInteraction

/-!
# `PartII-b:F8/2` helper: assembly of `FlatKInteractionFromH2` from the slice Sobolev embedding

Source of record: `the November 2 reference manuscript` (SP), lines 2311-2314:
"Since `s‖v(s)‖_∞ + s‖Dv(s)‖_∞ ≤ 𝒫_ν` for `s ≥ 1`, these estimates bound `sB_vz` in `H_p`".

The train amplitude bounds are `FreeInteractionAux.trainVel_band_bound` (ages `(0, H]`) and
`FreeInteractionAux.trainVel_tail_bound` (ages `≥ 1`); the slice Sobolev embedding
`H¹(C_c) ⊂ L^{11/4}(C_c)` enters as `SliceSobolev`.  On `(0, H]` the factor `s` of `sB_vz` turns the
weight `s^{-9/8}` of `H_p` into `s^{13/8}`; on `(H, ∞)` it is absorbed by the decay of the train.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.FlatKH2

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- `flatK` is `AEStronglyMeasurable` for `hMeas c bgp` when its profile data are. -/
theorem aesm_flatK {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) (b0 b0q b0η : CProf)
    (hb0 : AEStronglyMeasurable b0 (hMeas c bgp)) (hq : AEStronglyMeasurable b0q (hMeas c bgp))
    (hη : AEStronglyMeasurable b0η (hMeas c bgp)) :
    AEStronglyMeasurable (flatK tr b0 b0q b0η) (hMeas c bgp) := by
  set U : Set Coord := {x : Coord | 0 < x.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hv_cd : ContDiffOn ℝ ∞ (fun m : Coord => tr.v m.1 m.2) U :=
    tr.isTrain.smooth_v.mono fun x (hx : 0 < x.1) => ⟨hx.le, trivial⟩
  have hdQ_cd : ContDiffOn ℝ ∞ (Axi.dQ (fun m : Coord => tr.v m.1 m.2)) U :=
    (hv_cd.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hdE_cd : ContDiffOn ℝ ∞ (Axi.dEta (fun m : Coord => tr.v m.1 m.2)) U :=
    (hv_cd.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hind_ae : ∀ {E : Type} [Zero E] (f : Coord → E),
      U.indicator f =ᵐ[hMeas c bgp] f := fun f => by
    filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
    exact Set.indicator_of_mem (show x ∈ U from hx.1) f
  have hv0_cont : ContinuousOn (fun x : Coord => (tr.v x.1 x.2 0 : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv_cd.continuousOn)
  have hv1_cont : ContinuousOn (fun x : Coord => (tr.v x.1 x.2 1 : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv_cd.continuousOn)
  have hdQ_cont : ContinuousOn
      (fun x : Coord => liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)) U :=
    FreeInteractionAux.continuous_liftM.comp_continuousOn hdQ_cd.continuousOn
  have hdE_cont : ContinuousOn
      (fun x : Coord => liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)) U :=
    FreeInteractionAux.continuous_liftM.comp_continuousOn hdE_cd.continuousOn
  have hv0_m : AEStronglyMeasurable (fun x : Coord => (tr.v x.1 x.2 0 : ℂ)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hv0_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hv1_m : AEStronglyMeasurable (fun x : Coord => (tr.v x.1 x.2 1 : ℂ)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hv1_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hdQ_m : AEStronglyMeasurable
      (fun x : Coord => liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hdQ_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hdE_m : AEStronglyMeasurable
      (fun x : Coord => liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hdE_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hb0_0_m : AEStronglyMeasurable (fun x : Coord => b0 x 0) (hMeas c bgp) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).comp_aestronglyMeasurable hb0
  have hb0_1_m : AEStronglyMeasurable (fun x : Coord => b0 x 1) (hMeas c bgp) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).comp_aestronglyMeasurable hb0
  have hs_m : AEStronglyMeasurable (fun x : Coord => x.1) (hMeas c bgp) :=
    continuous_fst.aestronglyMeasurable
  have hrhs_m : AEStronglyMeasurable
      (fun x : Coord => x.1 • ((tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
        b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
        b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)))
      (hMeas c bgp) :=
    hs_m.smul
      ((((hv0_m.smul hq).add (hv1_m.smul hη)).add
        (hb0_0_m.smul hdQ_m)).add (hb0_1_m.smul hdE_m))
  refine hrhs_m.congr ?_
  filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
  exact (FreeInteractionAux.flatK_eq_on_pos tr b0 b0q b0η hx.1).symm

/-- Pointwise bound of `flatK` by the velocity and gradient amplitudes, without `sqrtS`. -/
theorem flatK_pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0q b0η : CProf) {x : Coord}
    (hx : 0 < x.1) {V D : ℝ} (hV0 : 0 ≤ V) (hD0 : 0 ≤ D) (hV : ‖tr.v x.1 x.2‖ ≤ V)
    (hQ : ‖Axi.dQ (fun m : Coord => tr.v m.1 m.2) x‖ ≤ D)
    (hE : ‖Axi.dEta (fun m : Coord => tr.v m.1 m.2) x‖ ≤ D) :
    ‖flatK tr b0 b0q b0η x‖ ≤ x.1 * (V * (‖b0q x‖ + ‖b0η x‖) + 2 * D * ‖b0 x‖) := by
  have h := FreeInteractionAux.norm_flatK_le_of_vel_grad tr b0 b0q b0η hx hV0 hD0 hV hQ hE
  rw [FreeInteractionAux.norm_sqrtS_of_nonneg b0q hx.le,
    FreeInteractionAux.norm_sqrtS_of_nonneg b0η hx.le] at h
  have hs : Real.sqrt x.1 * Real.sqrt x.1 = x.1 := Real.mul_self_sqrt hx.le
  refine h.trans (le_of_eq ?_)
  linear_combination (V * ‖b0q x‖ + V * ‖b0η x‖) * hs

/-- The normalized cell measure is dominated by Lebesgue measure on the cell when `c ≥ 1`. -/
theorem avgμ_le_cell {c : ℝ} (hc : 1 ≤ c) :
    UnforcedLeray.Cyl.avgμ c ≤ volume.restrict (B0579.cell c) := by
  have hcell : UnforcedLeray.Cyl.cell c = B0579.cell c := by
    simp only [UnforcedLeray.Cyl.cell, B0579.cell, neg_div]
  rw [Measure.le_iff']
  intro S
  simp only [UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, hcell, Measure.smul_apply,
    smul_eq_mul]
  refine mul_le_of_le_one_left bot_le ?_
  rw [ENNReal.ofReal_le_one]
  exact inv_le_one_of_one_le₀ hc

/-- The `L^{11/4}(dq/c dη)` slice norm of a profile dominated pointwise by
`A (‖zq‖ + ‖zη‖ + 2‖z‖)`. -/
theorem slice_eLpNorm_le {c : ℝ} (hc : 1 ≤ c) (F z zq zη : CProf) (s A : ℝ) (hA : 0 ≤ A)
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    (hpt : ∀ x : ℝ × ℝ, ‖F (s, x)‖ ≤ A * (‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖)) :
    eLpNorm (fun x => F (s, x)) (ENNReal.ofReal bgp) (UnforcedLeray.Cyl.avgμ c) ≤
      ENNReal.ofReal A *
        (eLpNorm (fun x => zq (s, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => zη (s, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c)) +
          2 * eLpNorm (fun x => z (s, x)) (ENNReal.ofReal bgp)
            (volume.restrict (B0579.cell c))) := by
  set p : ℝ≥0∞ := ENNReal.ofReal bgp
  set μ := UnforcedLeray.Cyl.avgμ c
  have hp1 : 1 ≤ p := by
    simp only [p]
    rw [ENNReal.one_le_ofReal]
    norm_num [bgp]
  have hms : Measurable (fun x : ℝ × ℝ => ((s, x) : Coord)) := measurable_prodMk_left
  have mz : AEStronglyMeasurable (fun x => ‖z (s, x)‖) μ :=
    (hz.comp_measurable hms).norm.aestronglyMeasurable
  have mq : AEStronglyMeasurable (fun x => ‖zq (s, x)‖) μ :=
    (hzq.comp_measurable hms).norm.aestronglyMeasurable
  have mη : AEStronglyMeasurable (fun x => ‖zη (s, x)‖) μ :=
    (hzη.comp_measurable hms).norm.aestronglyMeasurable
  have hle := avgμ_le_cell hc
  have h2 : eLpNorm (fun x => 2 * ‖z (s, x)‖) p μ = 2 * eLpNorm (fun x => ‖z (s, x)‖) p μ := by
    rw [show (fun x => 2 * ‖z (s, x)‖) = (2 : ℝ) • (fun x => ‖z (s, x)‖) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsum : eLpNorm (fun x => ‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖) p μ ≤
      eLpNorm (fun x => ‖zq (s, x)‖) p μ + eLpNorm (fun x => ‖zη (s, x)‖) p μ +
        2 * eLpNorm (fun x => ‖z (s, x)‖) p μ := by
    rw [← h2]
    calc eLpNorm (fun x => ‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖) p μ
        ≤ eLpNorm (fun x => ‖zq (s, x)‖ + ‖zη (s, x)‖) p μ +
            eLpNorm (fun x => 2 * ‖z (s, x)‖) p μ :=
          eLpNorm_add_le (mq.add mη) (mz.const_mul 2) hp1
      _ ≤ eLpNorm (fun x => ‖zq (s, x)‖) p μ + eLpNorm (fun x => ‖zη (s, x)‖) p μ +
            eLpNorm (fun x => 2 * ‖z (s, x)‖) p μ := by
          gcongr
          exact eLpNorm_add_le mq mη hp1
  calc eLpNorm (fun x => F (s, x)) p μ
      ≤ eLpNorm (fun x => A * (‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖)) p μ :=
        eLpNorm_mono_real hpt
    _ = ENNReal.ofReal A *
          eLpNorm (fun x => ‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖) p μ := by
        rw [show (fun x => A * (‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖)) =
            A • (fun x => ‖zq (s, x)‖ + ‖zη (s, x)‖ + 2 * ‖z (s, x)‖) from rfl,
          eLpNorm_const_smul, Real.enorm_eq_ofReal hA]
    _ ≤ ENNReal.ofReal A * (eLpNorm (fun x => ‖zq (s, x)‖) p μ +
          eLpNorm (fun x => ‖zη (s, x)‖) p μ + 2 * eLpNorm (fun x => ‖z (s, x)‖) p μ) := by
        gcongr
    _ ≤ _ := by
        simp only [eLpNorm_norm]
        gcongr

/-- `QPeriodic` passes to `sqrtS`. -/
theorem qPeriodic_sqrtS {c : ℝ} {g : CProf} (hg : QPeriodic c g) : QPeriodic c (sqrtS g) := by
  unfold QPeriodic at hg ⊢
  filter_upwards [hg] with x hx
  show ((Real.sqrt (qShift c x).1 : ℝ) : ℂ) • g (qShift c x) = ((Real.sqrt x.1 : ℝ) : ℂ) • g x
  rw [hx]
  rfl

/-- `hMeas c bgp` is the product of `s^{-9/8} ds` and the normalized cell measure. -/
theorem hMeas_eq_prod (c : ℝ) :
    hMeas c bgp = (sMeas (-9 / 8)).prod (UnforcedLeray.Cyl.avgμ c) := by
  have h : (bgp / 2 - 5 / 2 : ℝ) = -9 / 8 := by norm_num [bgp]
  simp only [hMeas, Axi.ageμ, sMeas, h]

/-- The measure `s^b ds` lives on `(0, ∞)`. -/
theorem sMeas_restrict_Ioi (b : ℝ) : (sMeas b).restrict (Ioi 0) = sMeas b := by
  unfold sMeas
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_self]

/-- **Conditional assembly of `FlatKInteractionFromH2`** (SP 2311-2314) from the slice Sobolev
embedding. -/
theorem flatKInteractionFromH2_of (hS : SliceSobolev) : FlatKInteractionFromH2 := by
  obtain ⟨K, hKtop, hK⟩ := hS
  intro Sig hSig dm dp hdm
  obtain ⟨C_b, k_b, ν_b, hC_b, hν_b, hband⟩ :=
    FreeInteractionAux.trainVel_band_bound Sig hSig dm dp hdm
  obtain ⟨C_t, k_t, ν_t, hC_t, hν_t, htail⟩ := FreeInteractionAux.trainVel_tail_bound
  have hKr : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  refine ⟨4 * K.toReal * (C_b + C_t) + 1, k_b + k_t,
    min (min ν_b ν_t) (min Sig (1 / 2)), by positivity,
    lt_min (lt_min hν_b hν_t) (lt_min hSig (by norm_num)), ?_⟩
  intro p d hreg hν hAge z zq zη D2z hpz hpq hpη hmz hmq hmη hmD w1 w2 w3 w4 w5 w6 hf1 hf2
  have hν0 : 0 < p.ν := p.ν_pos
  have hνb : p.ν ≤ ν_b := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνt : p.ν ≤ ν_t := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνS : p.ν ≤ Sig := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνh : p.ν ≤ 1 / 2 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hνh.trans (by norm_num)
  have hc0 : 0 < p.c := p.c_pos
  have hc4 : 4 ≤ p.c := by
    rw [hreg.c_eq]
    have h2p : 0 < p.ν ^ 2 := by positivity
    have h2 : p.ν ^ 2 ≤ 1 / 4 := by nlinarith
    rw [le_inv_comm₀ (by norm_num) h2p]
    linarith
  have hc1 : 1 ≤ p.c := by linarith
  have hH : p.H = Sig / p.ν := by
    change p.ageCut / p.ν = Sig / p.ν
    rw [hAge]
  have hH1 : 1 ≤ p.H := by
    rw [hH, le_div_iff₀ hν0]
    linarith
  have hH0 : 0 ≤ p.H := by linarith
  -- the amplitude `M = (C_b + C_t) ν^{-k}`
  set M : ℝ := (C_b + C_t) * (p.ν ^ (k_b + k_t))⁻¹ with hM_def
  have hM0 : 0 ≤ M := by positivity
  have hpow : ∀ j : ℕ, j ≤ k_b + k_t → (p.ν ^ j)⁻¹ ≤ (p.ν ^ (k_b + k_t))⁻¹ := fun j hj =>
    inv_anti₀ (pow_pos hν0 _) (pow_le_pow_of_le_one hν0.le hν1 hj)
  have hCbM : C_b * (p.ν ^ k_b)⁻¹ ≤ M :=
    mul_le_mul (by linarith) (hpow k_b (Nat.le_add_right _ _)) (by positivity) (by positivity)
  have hCtM : C_t * (p.ν ^ k_t)⁻¹ ≤ M :=
    mul_le_mul (by linarith) (hpow k_t (Nat.le_add_left _ _)) (by positivity) (by positivity)
  -- the age weight: `s` on `(0, H]`, `1` after
  set W : ℝ → ℝ := fun s => if s ≤ p.H then s else 1 with hW_def
  have hpt : ∀ x : Coord, 0 < x.1 →
      ‖flatK p.train z zq zη x‖ ≤ (M * W x.1) * (‖zq x‖ + ‖zη x‖ + 2 * ‖z x‖) := by
    intro x hx
    by_cases hxH : x.1 ≤ p.H
    · obtain ⟨hV, hQ, hE⟩ := hband p d hreg hνb hAge x hx hxH
      have h := flatK_pt p.train z zq zη hx hM0 hM0 (hV.trans hCbM) (hQ.trans hCbM)
        (hE.trans hCbM)
      have hWx : W x.1 = x.1 := if_pos hxH
      rw [hWx]
      refine h.trans (le_of_eq ?_)
      ring
    · have hx1 : 1 ≤ x.1 := le_trans hH1 (le_of_lt (not_le.mp hxH))
      obtain ⟨hV, hQ, hE⟩ := htail p d dm dp hreg hνt x hx1
      have hWx : W x.1 = 1 := if_neg hxH
      have hV0 : 0 ≤ M / x.1 := div_nonneg hM0 hx.le
      have hr1 : x.1 ^ (-1 : ℝ) = 1 / x.1 := by rw [Real.rpow_neg_one, one_div]
      have hr32 : x.1 ^ (-(3 / 2 : ℝ)) ≤ x.1 ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have hCt0 : 0 ≤ C_t * (p.ν ^ k_t)⁻¹ := by positivity
      have key : C_t * (p.ν ^ k_t)⁻¹ * x.1 ^ (-1 : ℝ) ≤ M / x.1 := by
        rw [hr1, mul_one_div]
        exact div_le_div_of_nonneg_right hCtM hx.le
      have hV' : ‖p.train.v x.1 x.2‖ ≤ M / x.1 := hV.trans key
      have hQ' : ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ ≤ M / x.1 :=
        hQ.trans ((mul_le_mul_of_nonneg_left hr32 hCt0).trans key)
      have hE' : ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ ≤ M / x.1 :=
        hE.trans ((mul_le_mul_of_nonneg_left hr32 hCt0).trans key)
      have h := flatK_pt p.train z zq zη hx hV0 hV0 hV' hQ' hE'
      rw [hWx]
      refine h.trans (le_of_eq ?_)
      field_simp
  -- the three slice Sobolev bounds
  set N : ℝ → ℝ≥0∞ := sliceH2Norm p.c z zq zη D2z with hN_def
  have hA := hK p.c hc4 z zq zη hpz hmz hmq hmη w1 w2
  have hB := hK p.c hc4 zq (D2z 0 0) (D2z 0 1) hpq hmq (hmD 0 0) (hmD 0 1) w3 w4
  have hC := hK p.c hc4 zη (D2z 1 0) (D2z 1 1) hpη hmη (hmD 1 0) (hmD 1 1) w5 w6
  have hN1 : ∀ s, sliceH1Norm p.c z zq zη s ≤ N s := fun s => by
    simp only [hN_def, sliceH2Norm]
    exact le_self_add
  have hN2 : ∀ s, sliceH1Norm p.c zq (D2z 0 0) (D2z 0 1) s ≤ N s := fun s => by
    simp only [hN_def, sliceH2Norm, sliceH1Norm, Fin.sum_univ_two]
    rw [add_assoc (eLpNorm (fun z_1 => zq (s, z_1)) 2 (volume.restrict (B0579.cell p.c)))]
    exact add_le_add (le_add_self.trans le_self_add) le_self_add
  have hN3 : ∀ s, sliceH1Norm p.c zη (D2z 1 0) (D2z 1 1) s ≤ N s := fun s => by
    simp only [hN_def, sliceH2Norm, sliceH1Norm, Fin.sum_univ_two]
    rw [add_assoc (eLpNorm (fun z_1 => zη (s, z_1)) 2 (volume.restrict (B0579.cell p.c)))]
    exact add_le_add le_add_self le_add_self
  have hslice : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      eLpNorm (fun x => flatK p.train z zq zη (s, x)) (ENNReal.ofReal bgp)
          (UnforcedLeray.Cyl.avgμ p.c) ≤
        ENNReal.ofReal (M * W s) * (4 * K * N s) := by
    filter_upwards [hA, hB, hC, ae_restrict_mem measurableSet_Ioi] with s hsA hsB hsC hs
    have hs0 : (0 : ℝ) < s := hs
    have hW0 : 0 ≤ W s := by
      simp only [hW_def]
      split_ifs <;> linarith
    have h1 := slice_eLpNorm_le hc1 (flatK p.train z zq zη) z zq zη s (M * W s)
      (mul_nonneg hM0 hW0) hmz hmq hmη (fun x => hpt (s, x) hs0)
    refine h1.trans ?_
    gcongr
    calc eLpNorm (fun x => zq (s, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell p.c)) +
          eLpNorm (fun x => zη (s, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell p.c)) +
          2 * eLpNorm (fun x => z (s, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell p.c))
        ≤ K * N s + K * N s + 2 * (K * N s) := by
          gcongr
          · exact hsB.trans (by gcongr; exact hN2 s)
          · exact hsC.trans (by gcongr; exact hN3 s)
          · exact hsA.trans (by gcongr; exact hN1 s)
      _ = 4 * K * N s := by ring
  -- integration
  have hmeasF : AEStronglyMeasurable (flatK p.train z zq zη) (hMeas p.c bgp) :=
    aesm_flatK hc0 p.train z zq zη hmz.aestronglyMeasurable hmq.aestronglyMeasurable
      hmη.aestronglyMeasurable
  have hbgp0 : (0 : ℝ) < bgp := by norm_num [bgp]
  have hp0 : ENNReal.ofReal bgp ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hbgp0
  have hpr : (ENNReal.ofReal bgp).toReal = bgp := ENNReal.toReal_ofReal hbgp0.le
  have hinv : (1 / bgp : ℝ) = 4 / 11 := by norm_num [bgp]
  have hNm : Measurable N := measurable_sliceH2Norm p.c hmz hmq hmη hmD
  set KK : ℝ≥0∞ := ENNReal.ofReal M * (4 * K) with hKK_def
  have hKKtop : KK ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by norm_num) hKtop)
  set I₁ : ℝ≥0∞ := ∫⁻ s in Ioc 0 p.H, N s ^ bgp ∂sMeas (13 / 8) with hI₁
  set I₂ : ℝ≥0∞ := ∫⁻ s in Ioi p.H, N s ^ bgp ∂sMeas (-9 / 8) with hI₂
  -- the `bgp`-th power of the norm
  have hmain : ∫⁻ q, ‖flatK p.train z zq zη q‖ₑ ^ bgp ∂(hMeas p.c bgp) ≤ KK ^ bgp * (I₁ + I₂) := by
    rw [hMeas_eq_prod p.c]
    have hAEM : AEMeasurable (fun q : Coord => ‖flatK p.train z zq zη q‖ₑ ^ bgp)
        ((sMeas (-9 / 8)).prod (UnforcedLeray.Cyl.avgμ p.c)) := by
      rw [← hMeas_eq_prod p.c]
      exact hmeasF.enorm.pow_const bgp
    rw [lintegral_prod _ hAEM]
    have hfib : ∀ s : ℝ, ∫⁻ x, ‖flatK p.train z zq zη (s, x)‖ₑ ^ bgp
        ∂(UnforcedLeray.Cyl.avgμ p.c) =
        eLpNorm (fun x => flatK p.train z zq zη (s, x)) (ENNReal.ofReal bgp)
          (UnforcedLeray.Cyl.avgμ p.c) ^ bgp := by
      intro s
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top, hpr,
        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hbgp0.ne', ENNReal.rpow_one]
    simp_rw [hfib]
    have hae : ∀ᵐ s ∂(sMeas (-9 / 8)),
        eLpNorm (fun x => flatK p.train z zq zη (s, x)) (ENNReal.ofReal bgp)
            (UnforcedLeray.Cyl.avgμ p.c) ^ bgp ≤
          KK ^ bgp * (ENNReal.ofReal (W s) ^ bgp * N s ^ bgp) := by
      have hac : sMeas (-9 / 8) ≪ volume.restrict (Ioi (0 : ℝ)) :=
        withDensity_absolutelyContinuous _ _
      filter_upwards [hac.ae_le hslice, hac.ae_le (ae_restrict_mem measurableSet_Ioi)]
        with s hs hs0
      have hs0' : (0 : ℝ) < s := hs0
      have hW0 : 0 ≤ W s := by
        simp only [hW_def]
        split_ifs <;> linarith
      have heq : ENNReal.ofReal (M * W s) * (4 * K * N s) = KK * (ENNReal.ofReal (W s) * N s) := by
        rw [ENNReal.ofReal_mul hM0, hKK_def]
        ring
      calc _ ≤ (ENNReal.ofReal (M * W s) * (4 * K * N s)) ^ bgp :=
            ENNReal.rpow_le_rpow hs hbgp0.le
        _ = KK ^ bgp * (ENNReal.ofReal (W s) ^ bgp * N s ^ bgp) := by
            rw [heq, ENNReal.mul_rpow_of_nonneg KK _ hbgp0.le,
              ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (W s)) (N s) hbgp0.le]
    refine (lintegral_mono_ae hae).trans ?_
    have hWm : Measurable W := by
      simp only [hW_def]
      exact Measurable.ite measurableSet_Iic measurable_id measurable_const
    have hgm : Measurable (fun s => ENNReal.ofReal (W s) ^ bgp * N s ^ bgp) :=
      ((ENNReal.measurable_ofReal.comp hWm).pow_const bgp).mul (hNm.pow_const bgp)
    rw [lintegral_const_mul _ hgm]
    gcongr
    rw [← sMeas_restrict_Ioi, ← Set.Ioc_union_Ioi_eq_Ioi hH0,
      lintegral_union measurableSet_Ioi
        (Set.disjoint_left.2 (fun x hx hx' => (not_lt.2 hx.2) hx'))]
    gcongr
    · -- on `(0, H]`: `W s = s`
      rw [hI₁, hardySing_sMeas_Ioc _ _ _ hgm,
        hardySing_sMeas_Ioc _ _ _ (hNm.pow_const bgp)]
      refine le_of_eq (setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_))
      have hs0 : (0 : ℝ) < s := hs.1
      have hWs : W s = s := if_pos hs.2
      simp only [hWs]
      rw [ENNReal.ofReal_rpow_of_nonneg hs0.le hbgp0.le, mul_comm (ENNReal.ofReal (s ^ bgp)),
        mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), ← Real.rpow_add hs0]
      norm_num [bgp]
    · -- on `(H, ∞)`: `W s = 1`
      rw [hI₂]
      refine le_of_eq (setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_))
      have hWs : W s = 1 := if_neg (not_le.2 hs)
      simp only [hWs, ENNReal.ofReal_one, ENNReal.one_rpow, one_mul]
  -- the norm itself
  have hnorm : hNorm p.c bgp (flatK p.train z zq zη) ≤ KK * (I₁ ^ (4 / 11 : ℝ) + I₂ ^ (4 / 11 : ℝ)) := by
    unfold hNorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top, hpr, hinv]
    calc (∫⁻ q, ‖flatK p.train z zq zη q‖ₑ ^ bgp ∂(hMeas p.c bgp)) ^ (4 / 11 : ℝ)
        ≤ (KK ^ bgp * (I₁ + I₂)) ^ (4 / 11 : ℝ) :=
          ENNReal.rpow_le_rpow hmain (by norm_num)
      _ = KK * (I₁ + I₂) ^ (4 / 11 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
          norm_num [bgp]
      _ ≤ KK * (I₁ ^ (4 / 11 : ℝ) + I₂ ^ (4 / 11 : ℝ)) := by
          gcongr
          exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
  have hKK : KK ≤ ENNReal.ofReal ((4 * K.toReal * (C_b + C_t) + 1) * (p.ν ^ (k_b + k_t))⁻¹) := by
    have hK4 : (4 : ℝ≥0∞) * K = ENNReal.ofReal (4 * K.toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hKtop]
      norm_num
    rw [hKK_def, hK4, ← ENNReal.ofReal_mul hM0]
    apply ENNReal.ofReal_le_ofReal
    have hνk : 0 ≤ (p.ν ^ (k_b + k_t))⁻¹ := by positivity
    have he : M * (4 * K.toReal) = 4 * K.toReal * (C_b + C_t) * (p.ν ^ (k_b + k_t))⁻¹ := by
      rw [hM_def]
      ring
    rw [he, add_mul, one_mul]
    linarith
  have hbound : hNorm p.c bgp (flatK p.train z zq zη) ≤
      ENNReal.ofReal ((4 * K.toReal * (C_b + C_t) + 1) * (p.ν ^ (k_b + k_t))⁻¹) *
        (sLpNorm (13 / 8) p.H (sliceH2Norm p.c z zq zη D2z) +
          tailLpNorm (-9 / 8) p.H (sliceH2Norm p.c z zq zη D2z)) :=
    hnorm.trans (mul_le_mul' hKK le_rfl)
  refine ⟨⟨?_, ?_, ?_⟩, hbound⟩
  · exact FreeInteractionAux.qPeriodic_flatK p.train z zq zη hpz (qPeriodic_sqrtS hpq)
      (qPeriodic_sqrtS hpη)
  · exact hmeasF
  · refine hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    exact ENNReal.add_lt_top.2 ⟨hf1, hf2⟩

end UnforcedLeray.Short.IIb.FlatKH2
