import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP

/-!
# `PartIII-a:T21/c2/2/5/3`, leaf 2: the transport identity (`FmrTransGenId`)

Source: `the November 2 reference manuscript`, lines 2950-2954.  Weight-generic copy of
`PartII-b` `TransportIBP.transport_identity`, `tendsto_Lf`, `core`: the weight `jb^m` is replaced by an
admissible weight `w` (`TransWt`).  The seam symmetry and `C¹` regularity of `w` and the bound
`|w| ≤ K₀ jb^m` are the only properties of the weight used.  Integrability of the two integrands is
a hypothesis of the target.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Transport integrand `g (v·∇g) w`. -/
def fmrGw (v : B0579.Plane → UnforcedLeray.Cyl.Vec2) (g w : B0579.Plane → ℝ) (z : B0579.Plane) : ℝ :=
  g z * (v z 0 * B0579.pd 0 g z + v z 1 * B0579.pd 1 g z) * w z

/-- Right integrand `g² (v·∇w)`. -/
def fmrHw (v : B0579.Plane → UnforcedLeray.Cyl.Vec2) (g w : B0579.Plane → ℝ) (z : B0579.Plane) : ℝ :=
  g z ^ 2 * (v z 0 * B0579.pd 0 w z + v z 1 * B0579.pd 1 w z)

/-- Cut-off remainder `χ χ' g² w v₁`. -/
def fmrLw (v : B0579.Plane → UnforcedLeray.Cyl.Vec2) (g w : B0579.Plane → ℝ) (R : ℝ)
    (z : B0579.Plane) : ℝ :=
  TransportIBP.cutF R z.2 * TransportIBP.cutD R z.2 * (g z ^ 2 * w z * v z 1)

theorem fmr_cont_v {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} (hv : ContDiff ℝ 1 v) (j : Fin 2) :
    Continuous fun z => v z j :=
  ((EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous

theorem fmr_continuous_Gw {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g w : B0579.Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hg : ContDiff ℝ 1 g) (hw : ContDiff ℝ 1 w) :
    Continuous (fmrGw v g w) := by
  unfold fmrGw
  exact (hg.continuous.mul (((fmr_cont_v hv 0).mul (TransportIBP.continuous_pd hg 0)).add
    ((fmr_cont_v hv 1).mul (TransportIBP.continuous_pd hg 1)))).mul hw.continuous

theorem fmr_continuous_Hw {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g w : B0579.Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hg : ContDiff ℝ 1 g) (hw : ContDiff ℝ 1 w) :
    Continuous (fmrHw v g w) := by
  unfold fmrHw
  exact (hg.continuous.pow 2).mul (((fmr_cont_v hv 0).mul (TransportIBP.continuous_pd hw 0)).add
    ((fmr_cont_v hv 1).mul (TransportIBP.continuous_pd hw 1)))

theorem fmr_continuous_Lw {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g w : B0579.Plane → ℝ} {R : ℝ}
    (hv : ContDiff ℝ 1 v) (hg : ContDiff ℝ 1 g) (hw : ContDiff ℝ 1 w) :
    Continuous (fmrLw v g w R) := by
  unfold fmrLw
  have hF : Continuous fun z : B0579.Plane => TransportIBP.cutF R z.2 :=
    (TransportIBP.cutF_contDiff R).continuous.comp continuous_snd
  have hD : Continuous fun z : B0579.Plane => TransportIBP.cutD R z.2 :=
    (TransportIBP.continuous_cutD R).comp continuous_snd
  exact (hF.mul hD).mul (((hg.continuous.pow 2).mul hw.continuous).mul (fmr_cont_v hv 1))

theorem fmr_norm_Lw_le {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g w : B0579.Plane → ℝ}
    {m K M K0 R : ℝ} (hK : 0 ≤ K) (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hK0 : 0 ≤ K0)
    (hwb : ∀ x : B0579.Plane, |w x| ≤ K0 * B0579.jb x ^ m) (hR : 0 < R)
    (hD : ∀ η : ℝ, |TransportIBP.cutD R η| ≤ K * (1 / R)) (z : B0579.Plane) :
    ‖fmrLw v g w R z‖ ≤ (K * M * (1 / R) * K0) * (g z ^ 2 * B0579.jb z ^ m) := by
  have hJm : 0 ≤ B0579.jb z ^ m := Real.rpow_nonneg (B0579.jb_pos z).le m
  have hg2 : 0 ≤ g z ^ 2 := sq_nonneg _
  have hχ : |TransportIBP.cutF R z.2| ≤ 1 := by
    rw [abs_of_nonneg (TransportIBP.cutF_nonneg R z.2)]
    exact TransportIBP.cutF_le_one R z.2
  have hv1 : |v z 1| ≤ M := by linarith [abs_nonneg (v z 0), hM z]
  have hwz := hwb z
  have hD' := hD z.2
  have e : |TransportIBP.cutF R z.2 * TransportIBP.cutD R z.2 * (g z ^ 2 * w z * v z 1)|
      = |TransportIBP.cutF R z.2| * |TransportIBP.cutD R z.2| * (g z ^ 2 * |w z| * |v z 1|) := by
    simp only [abs_mul, abs_of_nonneg hg2]
  have h12 : |TransportIBP.cutF R z.2| * |TransportIBP.cutD R z.2| ≤ 1 * (K * (1 / R)) :=
    mul_le_mul hχ hD' (abs_nonneg _) zero_le_one
  have h3 : g z ^ 2 * |w z| * |v z 1| ≤ g z ^ 2 * (K0 * B0579.jb z ^ m) * M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hwz hg2) hv1 (abs_nonneg _)
      (mul_nonneg hg2 (mul_nonneg hK0 hJm))
  unfold fmrLw
  rw [Real.norm_eq_abs, e]
  calc |TransportIBP.cutF R z.2| * |TransportIBP.cutD R z.2| * (g z ^ 2 * |w z| * |v z 1|)
      ≤ 1 * (K * (1 / R)) * (g z ^ 2 * (K0 * B0579.jb z ^ m) * M) :=
        mul_le_mul h12 h3 (mul_nonneg (mul_nonneg hg2 (abs_nonneg _)) (abs_nonneg _))
          (mul_nonneg zero_le_one (mul_nonneg hK (one_div_nonneg.2 hR.le)))
    _ = (K * M * (1 / R) * K0) * (g z ^ 2 * B0579.jb z ^ m) := by ring

theorem fmr_integrableOn_Lw {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g w : B0579.Plane → ℝ}
    {c m K M K0 R : ℝ} (hv : ContDiff ℝ 1 v) (hg1 : ContDiff ℝ 1 g) (hw : ContDiff ℝ 1 w)
    (hK : 0 ≤ K) (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hK0 : 0 ≤ K0)
    (hwb : ∀ x : B0579.Plane, |w x| ≤ K0 * B0579.jb x ^ m) (hR : 0 < R)
    (hD : ∀ η : ℝ, |TransportIBP.cutD R η| ≤ K * (1 / R)) (hg : CylSmoothDecay c g) :
    IntegrableOn (fmrLw v g w R) (UnforcedLeray.Cyl.cell c) :=
  TransportIBP.integrableOn_cell_of_bound
    (Q := fun z => (K * M * (1 / R) * K0) * (g z ^ 2 * B0579.jb z ^ m))
    (Integrable.const_mul (TransportIBP.integrableOn_g2rho hg m) (K * M * (1 / R) * K0))
    (fmr_continuous_Lw hv hg1 hw)
    (fun z _ => fmr_norm_Lw_le hK hM0 hM hK0 hwb hR hD z)

theorem fmr_tendsto_Lw {c K M K0 m : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    {g w : B0579.Plane → ℝ} (hK : 0 ≤ K) (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M)
    (hK0 : 0 ≤ K0) (hwb : ∀ x : B0579.Plane, |w x| ≤ K0 * B0579.jb x ^ m)
    (hD : ∀ R η : ℝ, 0 < R → |TransportIBP.cutD R η| ≤ K * (1 / R)) (hg : CylSmoothDecay c g) :
    Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c, fmrLw v g w ((n : ℝ) + 1) z)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => K * M * (1 / ((n : ℝ) + 1)) * K0 *
      ∫ z in UnforcedLeray.Cyl.cell c, g z ^ 2 * B0579.jb z ^ m) atTop (𝓝 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K * M)).mul_const K0).mul_const
      (∫ z in UnforcedLeray.Cyl.cell c, g z ^ 2 * B0579.jb z ^ m)
    simpa using this
  refine squeeze_zero_norm (fun n : ℕ => ?_) hlim
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hint := norm_integral_le_of_norm_le
    (Integrable.const_mul (TransportIBP.integrableOn_g2rho hg m) (K * M * (1 / ((n : ℝ) + 1)) * K0))
    (ae_of_all _ fun z => fmr_norm_Lw_le hK hM0 hM hK0 hwb hR (fun η => hD _ η hR) z)
  rw [integral_const_mul] at hint
  exact hint

theorem fmr_transport_identity {c m K M K0 R : ℝ} (hc : 0 < c)
    {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} (hv : ContDiff ℝ 1 v)
    (hvp : UnforcedLeray.Cyl.IsPeriodic c v) (hdiv : ∀ z, UnforcedLeray.Cyl.divergence v z = 0)
    {g w : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (hw : ContDiff ℝ 1 w)
    (hwseam : ∀ η : ℝ, w (-c / 2, η) = w (c / 2, η))
    (hK : 0 ≤ K) (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hK0 : 0 ≤ K0)
    (hwb : ∀ x : B0579.Plane, |w x| ≤ K0 * B0579.jb x ^ m) (hR : 0 < R)
    (hD : ∀ η : ℝ, |TransportIBP.cutD R η| ≤ K * (1 / R))
    (hI1 : IntegrableOn (fmrGw v g w) (UnforcedLeray.Cyl.cell c)) :
    (∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.cutF R z.2 ^ 2 * fmrGw v g w z) +
        ∫ z in UnforcedLeray.Cyl.cell c, fmrLw v g w R z
      = -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.cutF R z.2 ^ 2 * fmrHw v g w z := by
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have hgd : Differentiable ℝ g := hg1.differentiable (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hcut1 : ContDiff ℝ 1 (fun z : B0579.Plane => TransportIBP.cutF R z.2) :=
    TransportIBP.contDiff_one_of_top ((TransportIBP.cutF_contDiff R).comp contDiff_snd)
  have hw1 : ContDiff ℝ 1 (fun z : B0579.Plane => g z * TransportIBP.cutF R z.2) :=
    hg1.mul hcut1
  have hwp : UnforcedLeray.Cyl.IsPeriodic c
      (fun z : B0579.Plane => g z * TransportIBP.cutF R z.2) := by
    intro z
    show g (z.1 + c, z.2) * TransportIBP.cutF R z.2 = g z * TransportIBP.cutF R z.2
    rw [hg.periodic z]
  have hwv : UnforcedLeray.Cyl.VanishesOutside (2 * R)
      (fun z : B0579.Plane => g z * TransportIBP.cutF R z.2) := by
    intro z hz
    show g z * TransportIBP.cutF R z.2 = 0
    rw [TransportIBP.cutF_eq_zero hR hz.le, mul_zero]
  have T : ∫ z in UnforcedLeray.Cyl.cell c,
        (v z 0 * UnforcedLeray.Cyl.partialQ (fun y : B0579.Plane => g y * TransportIBP.cutF R y.2) z +
          v z 1 * UnforcedLeray.Cyl.partialEta (fun y : B0579.Plane => g y * TransportIBP.cutF R y.2) z) *
          (g z * TransportIBP.cutF R z.2) * w z
      = -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c, (g z * TransportIBP.cutF R z.2) ^ 2 *
          (v z 0 * UnforcedLeray.Cyl.partialQ w z + v z 1 * UnforcedLeray.Cyl.partialEta w z) :=
    UnforcedLeray.Cyl.transport_antisymm (R := 2 * R) hc hv hw1 hw hvp hwp hwseam hdiv hwv
  have eL : ∀ z : B0579.Plane,
      (v z 0 * UnforcedLeray.Cyl.partialQ (fun y : B0579.Plane => g y * TransportIBP.cutF R y.2) z +
          v z 1 * UnforcedLeray.Cyl.partialEta (fun y : B0579.Plane => g y * TransportIBP.cutF R y.2) z) *
          (g z * TransportIBP.cutF R z.2) * w z
        = TransportIBP.cutF R z.2 ^ 2 * fmrGw v g w z + fmrLw v g w R z := by
    intro z
    rw [TransportIBP.partialQ_cut hgd, TransportIBP.partialEta_cut hgd]
    unfold fmrGw fmrLw
    ring
  have eR : ∀ z : B0579.Plane,
      (g z * TransportIBP.cutF R z.2) ^ 2 *
          (v z 0 * UnforcedLeray.Cyl.partialQ w z + v z 1 * UnforcedLeray.Cyl.partialEta w z)
        = TransportIBP.cutF R z.2 ^ 2 * fmrHw v g w z := by
    intro z
    rw [← TransportIBP.pd0_eq_partialQ hwd z, ← TransportIBP.pd1_eq_partialEta hwd z]
    unfold fmrHw
    ring
  simp only [eL, eR] at T
  have int1 : IntegrableOn (fun z : B0579.Plane => TransportIBP.cutF R z.2 ^ 2 * fmrGw v g w z)
      (UnforcedLeray.Cyl.cell c) :=
    TransportIBP.integrable_cut_mul (fmr_continuous_Gw hv hg1 hw) hI1
  have int2 : IntegrableOn (fun z : B0579.Plane => fmrLw v g w R z) (UnforcedLeray.Cyl.cell c) :=
    fmr_integrableOn_Lw hv hg1 hw hK hM0 hM hK0 hwb hR hD hg
  rw [integral_add int1 int2] at T
  exact T

/-- **Leaf 2** (SP 2950-2954): the transport identity for an admissible weight `w`, for the
integrability hypotheses of the target. -/
theorem fmrTransGenId : FmrTransGenId := by
  intro ν c tr σ hσ hc hν hM m w hw g hg hI1 hI2
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  rw [hcell] at hI1 hI2 ⊢
  obtain ⟨M, hM⟩ := hM
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM 0)
  have hv : ContDiff ℝ 1 (tr.v σ) :=
    TransportIBP.contDiff_one_of_top (TransportIBP.contDiff_slice tr hσ)
  have hvp : UnforcedLeray.Cyl.IsPeriodic c (tr.v σ) := tr.isTrain.periodic_v σ hσ
  have hdiv : ∀ z, UnforcedLeray.Cyl.divergence (tr.v σ) z = 0 := tr.isTrain.solenoidal σ hσ
  obtain ⟨K0, hK0, hK0le⟩ : ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ x : B0579.Plane,
      |w x| + |B0579.pd 0 w x| + |B0579.pd 1 w x| ≤ K0 * B0579.jb x ^ m := by
    obtain ⟨K, hK⟩ := hw.bound
    refine ⟨max K 0, le_max_right _ _, fun x => (hK x).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (B0579.jb_pos x).le m)
  have hwb : ∀ x : B0579.Plane, |w x| ≤ K0 * B0579.jb x ^ m := fun x => by
    have := hK0le x
    linarith [abs_nonneg (B0579.pd 0 w x), abs_nonneg (B0579.pd 1 w x)]
  have hw1 : ContDiff ℝ 1 w := hw.smooth
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  obtain ⟨K, hKnn, hK⟩ := TransportIBP.exists_cutD_bound
  have hI1' : IntegrableOn (fmrGw (tr.v σ) g w) (UnforcedLeray.Cyl.cell c) := hI1
  have hI2' : IntegrableOn (fmrHw (tr.v σ) g w) (UnforcedLeray.Cyl.cell c) := hI2
  have tA := TransportIBP.tendsto_cut_integral (fmr_continuous_Gw hv hg1 hw1) hI1'
  have tH := TransportIBP.tendsto_cut_integral (fmr_continuous_Hw hv hg1 hw1) hI2'
  have tL := fmr_tendsto_Lw (c := c) hKnn hM0 hM hK0 hwb hK hg
  have hid : ∀ n : ℕ,
      (∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.cutF ((n : ℝ) + 1) z.2 ^ 2 * fmrGw (tr.v σ) g w z) +
          ∫ z in UnforcedLeray.Cyl.cell c, fmrLw (tr.v σ) g w ((n : ℝ) + 1) z
        = -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c,
            TransportIBP.cutF ((n : ℝ) + 1) z.2 ^ 2 * fmrHw (tr.v σ) g w z :=
    fun n => fmr_transport_identity hc hv hvp hdiv hg hw1 hw.seam hKnn hM0 hM hK0 hwb (by positivity)
      (fun η => hK ((n : ℝ) + 1) η (by positivity)) hI1'
  have h1 := tA.add tL
  have h2 := tH.const_mul (-(1 / 2 : ℝ))
  have h3 := tendsto_nhds_unique (h1.congr hid) h2
  rw [add_zero] at h3
  show -(2 * ∫ z in UnforcedLeray.Cyl.cell c, fmrGw (tr.v σ) g w z)
      = ∫ z in UnforcedLeray.Cyl.cell c, fmrHw (tr.v σ) g w z
  linarith

end UnforcedLeray.Short.IIIa
