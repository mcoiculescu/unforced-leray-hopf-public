import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1
import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity

/-!
# Part I, task `PartI:T04/5/1/2/2`: `APEnergyMomentumIdentity` (single-solution momentum identity)

Source of record: `the November 2 reference manuscript`, lines 278-286.

Route. Write `φ = etaCutoff R`. The momentum residual gives pointwise
`∂_s v = -(v·∇)v + ν Δv - ∇p`, so `φ·2⟨v,∂_s v⟩ = -2φ⟨v,(v·∇)v⟩ + 2νφ⟨v,Δv⟩ - 2φ⟨v,∇p⟩`.
* transport: `tp_core` with `w = v` gives `-2∫φ⟨v,(v·∇)v⟩ = ∫|v|² v_η φ'`;
* viscous: `vi_scalar` on each component, as in `viscousIdentity`;
* pressure: cell integration by parts for `G₁ = pφv₁`, `G₂ = pφv₂` (`CellDerivZero`) with
  `div v = 0` gives `∫φ⟨v,∇p⟩ = -∫φ' p v_η`.
Integrability of every piece is from `CellIntegrableOfSupport` and continuity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem apM_toVec : Continuous (Train.toVec) :=
  Train.toVecL.continuous

theorem apM_partials {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialQ f) ∧ Continuous (Cyl.partialEta f) :=
  Cyl.C1_partial_of_contDiff (hf.of_le (by simp))

/-- **Task `PartI:T04/5/1/2/2`**: the single-solution momentum identity for the cutoff energy. -/
theorem apEnergyMomentumIdentity : APEnergyMomentumIdentity := by
  intro ν c T v p hν hc hcls R hR s hs
  have hc0 : 0 < c := by linarith
  have hR0 : 0 < R := by linarith
  have hsI : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
  have hv : ContDiff ℝ ∞ (v s) := hcls.classical.contDiff_slice hsI
  have hpS : ContDiff ℝ ∞ (p s) := by
    have h := hcls.classical.smooth_p.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun z _ => (⟨hsI, mem_univ z⟩ : (s, z) ∈ Icc 0 T ×ˢ univ))
    exact contDiffOn_univ.1 h
  obtain ⟨C₀, -, hcut⟩ := etaCutoffFacts
  obtain ⟨hsm, -, -, hzero, hder⟩ := hcut R hR
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h := hder η
    rw [hzero η hη, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  have hI : CellIntegrableOfSupport := cellIntegrable_of_support
  have hZ : CellDerivZero := cellDerivZero_of_periodic
  have hvp : Cyl.IsPeriodic c (v s) := hcls.classical.periodic_v s hsI
  have hpp : Cyl.IsPeriodic c (p s) := hcls.classical.periodic_p s hsI
  have hdiv : ∀ z : Plane, Cyl.divergence (v s) z = 0 := fun z => hcls.classical.solenoidal s hsI z
  have hvC : Continuous (v s) := hv.continuous
  have hpd : Differentiable ℝ (p s) := hpS.differentiable (by simp)
  have hvd : Differentiable ℝ (v s) := hv.differentiable (by simp)
  have hφs : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) := hsm.comp contDiff_snd
  have hφd : Differentiable ℝ (fun z : Plane => etaCutoff R z.2) := hφs.differentiable (by simp)
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) := hφs.continuous
  have hφdc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hsm.continuous_deriv (by simp)).comp continuous_snd
  have hf0 : ContDiff ℝ ∞ (fun z : Plane => v s z 0) := tp_comp_contDiff (v s) 0 hv
  have hf1 : ContDiff ℝ ∞ (fun z : Plane => v s z 1) := tp_comp_contDiff (v s) 1 hv
  have hf0d : Differentiable ℝ (fun z : Plane => v s z 0) := hf0.differentiable (by simp)
  have hf1d : Differentiable ℝ (fun z : Plane => v s z 1) := hf1.differentiable (by simp)
  have hF1d : Differentiable ℝ (fun y : Plane => p s y * etaCutoff R y.2) := hpd.mul hφd
  -- the momentum equation, solved for the time derivative
  have hder' : ∀ z : Plane, deriv (fun t => v t z) s =
      -Train.advection (v s) z + ν • Train.vecLaplacian (v s) z - Train.gradS (p s) z := by
    intro z
    have h := hcls.classical.momentum s hs z
    unfold Train.momentumResidual at h
    calc deriv (fun t => v t z) s
        = (deriv (fun t => v t z) s + Train.advection (v s) z - ν • Train.vecLaplacian (v s) z
            + Train.gradS (p s) z) + (-Train.advection (v s) z + ν • Train.vecLaplacian (v s) z
            - Train.gradS (p s) z) := by abel
      _ = -Train.advection (v s) z + ν • Train.vecLaplacian (v s) z - Train.gradS (p s) z := by
          rw [h, zero_add]
  have hint : ∀ z : Plane,
      etaCutoff R z.2 * (2 * inner ℝ (v s z) (deriv (fun t => v t z) s)) =
        -(2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
          + 2 * ν * (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z))
          - 2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) := by
    intro z
    rw [hder' z]
    simp only [inner_add_right, inner_sub_right, inner_neg_right, real_inner_smul_right]
    ring
  have hLHS : (∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * inner ℝ (v s z) (deriv (fun t => v t z) s)))
      = ∫ z in Cyl.cell c,
        (-(2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
          + 2 * ν * (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z))
          - 2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z))) := by
    congr 1
    funext z
    exact hint z
  -- continuity of the pieces
  have hpc : ∀ f : Plane → ℝ, ContDiff ℝ ∞ f →
      Continuous (Cyl.partialQ f) ∧ Continuous (Cyl.partialEta f) := fun f hf => apM_partials hf
  have hadvC : Continuous (fun z : Plane => Train.advection (v s) z) := by
    have h0 : Continuous (fun z : Plane => v s z 0 * Cyl.partialQ (fun w => v s w 0) z +
        v s z 1 * Cyl.partialEta (fun w => v s w 0) z) :=
      ((hf0.continuous).mul (hpc _ hf0).1).add ((hf1.continuous).mul (hpc _ hf0).2)
    have h1 : Continuous (fun z : Plane => v s z 0 * Cyl.partialQ (fun w => v s w 1) z +
        v s z 1 * Cyl.partialEta (fun w => v s w 1) z) :=
      ((hf0.continuous).mul (hpc _ hf1).1).add ((hf1.continuous).mul (hpc _ hf1).2)
    unfold Train.advection
    exact apM_toVec.comp (h0.prodMk h1)
  have hlapC : Continuous (fun z : Plane => Train.vecLaplacian (v s) z) := by
    have h0 : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialQ (fun w => v s w 0)) z +
        Cyl.partialEta (Cyl.partialEta (fun w => v s w 0)) z) :=
      (hpc _ (vi_partialQ_contDiff hf0)).1.add (hpc _ (vi_partialEta_contDiff hf0)).2
    have h1 : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialQ (fun w => v s w 1)) z +
        Cyl.partialEta (Cyl.partialEta (fun w => v s w 1)) z) :=
      (hpc _ (vi_partialQ_contDiff hf1)).1.add (hpc _ (vi_partialEta_contDiff hf1)).2
    unfold Train.vecLaplacian Train.lapS
    exact apM_toVec.comp (h0.prodMk h1)
  have hgradC : Continuous (fun z : Plane => Train.gradS (p s) z) := by
    unfold Train.gradS
    exact apM_toVec.comp ((hpc _ hpS).1.prodMk (hpc _ hpS).2)
  have hAc : Continuous (fun z : Plane => etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)) :=
    hφc.mul (hvC.inner hadvC)
  have hBc : Continuous (fun z : Plane => etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) :=
    hφc.mul (hvC.inner hlapC)
  have hCc : Continuous (fun z : Plane => etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) :=
    hφc.mul (hvC.inner hgradC)
  have hAi : IntegrableOn (fun z : Plane => etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z))
      (Cyl.cell c) := hI c R hc0 hR0 _ hAc (fun z hz => by simp [hzero z.2 hz])
  have hBi : IntegrableOn (fun z : Plane => etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z))
      (Cyl.cell c) := hI c R hc0 hR0 _ hBc (fun z hz => by simp [hzero z.2 hz])
  have hCi : IntegrableOn (fun z : Plane => etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z))
      (Cyl.cell c) := hI c R hc0 hR0 _ hCc (fun z hz => by simp [hzero z.2 hz])
  have hDi : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * p s z * v s z 1) (Cyl.cell c) :=
    hI c R hc0 hR0 _ ((hφdc.mul hpS.continuous).mul hf1.continuous)
      (fun z hz => by simp [hdzero z.2 hz])
  -- transport identity (`tp_core` with `w = v`)
  have htp : -2 * ∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z) =
      ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2 :=
    tp_core c R hc0 hR0 (etaCutoff R) hsm hzero hdzero (v s) (v s) hv hv hvp hvp hdiv hI hZ
  -- viscous identity (`vi_scalar` on both components)
  have hvisc : ∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z) =
      -(∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (v s) z) -
        ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z) := by
    have hper0 : Cyl.IsPeriodic c (fun z : Plane => v s z 0) := fun z => by
      show v s (z.1 + c, z.2) 0 = v s z 0
      rw [hvp z]
    have hper1 : Cyl.IsPeriodic c (fun z : Plane => v s z 1) := fun z => by
      show v s (z.1 + c, z.2) 1 = v s z 1
      rw [hvp z]
    obtain ⟨hA0, hB0, hC0, hE0⟩ := vi_scalar hc0 hR0 hI hZ hsm hzero hdzero
      (fun z : Plane => v s z 0) hf0 hper0
    obtain ⟨hA1, hB1, hC1, hE1⟩ := vi_scalar hc0 hR0 hI hZ hsm hzero hdzero
      (fun z : Plane => v s z 1) hf1 hper1
    have hinnerL : ∀ z : Plane,
        inner ℝ (v s z) (Train.vecLaplacian (v s) z) =
          v s z 0 * (Cyl.partialQ (Cyl.partialQ (fun w : Plane => v s w 0)) z +
              Cyl.partialEta (Cyl.partialEta (fun w : Plane => v s w 0)) z) +
          v s z 1 * (Cyl.partialQ (Cyl.partialQ (fun w : Plane => v s w 1)) z +
              Cyl.partialEta (Cyl.partialEta (fun w : Plane => v s w 1)) z) := by
      intro z
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        Train.vecLaplacian, Train.lapS, Train.toVec_zero, Train.toVec_one]
      ring
    have hinnerE : ∀ z : Plane,
        inner ℝ (v s z) (Cyl.partialEta (v s) z) =
          v s z 0 * Cyl.partialEta (fun w : Plane => v s w 0) z +
          v s z 1 * Cyl.partialEta (fun w : Plane => v s w 1) z := by
      intro z
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        vi_partialEta_comp hvd 0 z, vi_partialEta_comp hvd 1 z]
      ring
    have hgradP : ∀ z : Plane, etaCutoff R z.2 * gradNormSq (v s) z =
        etaCutoff R z.2 * (Cyl.partialQ (fun w => v s w 0) z ^ 2 +
            Cyl.partialEta (fun w => v s w 0) z ^ 2) +
        etaCutoff R z.2 * (Cyl.partialQ (fun w => v s w 1) z ^ 2 +
            Cyl.partialEta (fun w => v s w 1) z ^ 2) := by
      intro z
      unfold gradNormSq
      ring
    have hV : ∀ z : Plane, etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z) =
        etaCutoff R z.2 * (v s z 0 * (Cyl.partialQ (Cyl.partialQ (fun w => v s w 0)) z +
            Cyl.partialEta (Cyl.partialEta (fun w => v s w 0)) z)) +
        etaCutoff R z.2 * (v s z 1 * (Cyl.partialQ (Cyl.partialQ (fun w => v s w 1)) z +
            Cyl.partialEta (Cyl.partialEta (fun w => v s w 1)) z)) := by
      intro z
      rw [hinnerL z]
      ring
    have hJ : ∀ z : Plane, deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z) =
        deriv (etaCutoff R) z.2 * (v s z 0 * Cyl.partialEta (fun w => v s w 0) z) +
        deriv (etaCutoff R) z.2 * (v s z 1 * Cyl.partialEta (fun w => v s w 1) z) := by
      intro z
      rw [hinnerE z]
      ring
    simp only [hV, hgradP, hJ]
    rw [integral_add hA0 hA1, integral_add hB0 hB1, integral_add hC0 hC1]
    linear_combination hE0 + hE1
  -- pressure identity (`CellDerivZero` for `G₁ = p φ v₁`, `G₂ = p φ v₂`, and `div v = 0`)
  have hG1s : ContDiff ℝ ∞ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) :=
    (hpS.mul hφs).mul hf0
  have hG2s : ContDiff ℝ ∞ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) :=
    (hpS.mul hφs).mul hf1
  have hG1p : Cyl.IsPeriodic c (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) := fun z => by
    show p s (z.1 + c, z.2) * etaCutoff R z.2 * v s (z.1 + c, z.2) 0 =
      p s z * etaCutoff R z.2 * v s z 0
    rw [hpp z, hvp z]
  have hG2p : Cyl.IsPeriodic c (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) := fun z => by
    show p s (z.1 + c, z.2) * etaCutoff R z.2 * v s (z.1 + c, z.2) 1 =
      p s z * etaCutoff R z.2 * v s z 1
    rw [hpp z, hvp z]
  have hpQ : ∀ z : Plane, Cyl.partialQ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) z =
      Cyl.partialQ (p s) z * etaCutoff R z.2 * v s z 0 +
        p s z * etaCutoff R z.2 * Cyl.partialQ (fun w => v s w 0) z := by
    intro z
    rw [tp_partialQ_mul _ _ hF1d hf0d z, tp_partialQ_mul _ _ hpd hφd z,
      tp_partialQ_snd (etaCutoff R) z]
    ring
  have hpE : ∀ z : Plane, Cyl.partialEta (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) z =
      Cyl.partialEta (p s) z * etaCutoff R z.2 * v s z 1 +
        p s z * deriv (etaCutoff R) z.2 * v s z 1 +
        p s z * etaCutoff R z.2 * Cyl.partialEta (fun w => v s w 1) z := by
    intro z
    rw [tp_partialEta_mul _ _ hF1d hf1d z, tp_partialEta_mul _ _ hpd hφd z,
      tp_partialEta_snd (etaCutoff R) z]
    ring
  have hG1z : ∀ z : Plane, 2 * R ≤ |z.2| →
      p s z * etaCutoff R z.2 * v s z 0 = 0 := fun z hz => by simp [hzero z.2 hz]
  have hG2z : ∀ z : Plane, 2 * R ≤ |z.2| →
      p s z * etaCutoff R z.2 * v s z 1 = 0 := fun z hz => by simp [hzero z.2 hz]
  obtain ⟨hQ1, -⟩ := hZ c R hc0 hR0 _ (hG1s.of_le (by simp)) hG1p hG1z
  obtain ⟨-, hE2⟩ := hZ c R hc0 hR0 _ (hG2s.of_le (by simp)) hG2p hG2z
  have hQi : IntegrableOn (fun z : Plane => Cyl.partialQ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) z)
      (Cyl.cell c) := hI c R hc0 hR0 _ (hpc _ hG1s).1
      (fun z hz => by rw [hpQ z]; simp [hzero z.2 hz])
  have hEi : IntegrableOn (fun z : Plane => Cyl.partialEta (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) z)
      (Cyl.cell c) := hI c R hc0 hR0 _ (hpc _ hG2s).2
      (fun z hz => by rw [hpE z]; simp [hzero z.2 hz, hdzero z.2 hz])
  have hsum : ∫ z in Cyl.cell c, (Cyl.partialQ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) z +
      Cyl.partialEta (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) z) = 0 := by
    rw [integral_add hQi hEi, hQ1, hE2, add_zero]
  have hpt : ∀ z : Plane,
      Cyl.partialQ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) z +
        Cyl.partialEta (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) z =
      etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) +
        deriv (etaCutoff R) z.2 * p s z * v s z 1 + p s z * etaCutoff R z.2 * Cyl.divergence (v s) z := by
    intro z
    rw [hpQ z, hpE z]
    have hin : inner ℝ (v s z) (Train.gradS (p s) z) =
        v s z 0 * Cyl.partialQ (p s) z + v s z 1 * Cyl.partialEta (p s) z := by
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        Train.gradS, Train.toVec_zero, Train.toVec_one]
      ring
    have hdv : Cyl.divergence (v s) z =
        Cyl.partialQ (fun w => v s w 0) z + Cyl.partialEta (fun w => v s w 1) z := rfl
    rw [hin, hdv]
    ring
  have hsplit : ∫ z in Cyl.cell c, (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) +
      deriv (etaCutoff R) z.2 * p s z * v s z 1) = 0 := by
    have hcongr : (∫ z in Cyl.cell c, (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) +
        deriv (etaCutoff R) z.2 * p s z * v s z 1)) =
        ∫ z in Cyl.cell c, (Cyl.partialQ (fun y : Plane => p s y * etaCutoff R y.2 * v s y 0) z +
          Cyl.partialEta (fun y : Plane => p s y * etaCutoff R y.2 * v s y 1) z) := by
      congr 1
      funext z
      rw [hpt z, hdiv z]
      ring
    rw [hcongr, hsum]
  have hpres : ∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) =
      -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1) := by
    have h := hsplit
    rw [integral_add hCi hDi] at h
    linarith
  -- assemble
  have hL : ∫ z in Cyl.cell c,
      (-(2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
        + 2 * ν * (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z))
        - 2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)))
      = -(2 * (∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
        + 2 * ν * (∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z))
        - 2 * (∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) := by
    have hA2 : Integrable (fun z : Plane => 2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
        (volume.restrict (Cyl.cell c)) := Integrable.const_mul hAi 2
    have hB2 : Integrable (fun z : Plane => 2 * ν * (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)))
        (volume.restrict (Cyl.cell c)) := Integrable.const_mul hBi (2 * ν)
    have hC2 : Integrable (fun z : Plane => 2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)))
        (volume.restrict (Cyl.cell c)) := Integrable.const_mul hCi 2
    have hN : Integrable (fun z : Plane => -(2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z))))
        (volume.restrict (Cyl.cell c)) := hA2.neg
    have hS1 : Integrable (fun z : Plane =>
        -(2 * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z))) +
          2 * ν * (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)))
        (volume.restrict (Cyl.cell c)) := hN.add hB2
    rw [integral_sub hS1 hC2, integral_add hN hB2, integral_neg, integral_const_mul,
      integral_const_mul, integral_const_mul]
  rw [hLHS, hL]
  unfold apEnergyRhs
  linear_combination htp + (2 * ν) * hvisc - 2 * hpres

end UnforcedLeray.Short.PartI
