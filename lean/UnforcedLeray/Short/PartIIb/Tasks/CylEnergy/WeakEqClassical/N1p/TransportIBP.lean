import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common

/-!
# Part II-b, task `PartII-b:T22/2/2/4`: the transport integration by parts (`RtdTransportIBP`)

Source of record: `the November 2 reference manuscript`, lines 2092-2093 and
2097-2101. The weight-`m = 0` transport identity `TransportIBP.core` (SP 2092-2101) is applied to
`g + s h` for `s = ±1`. Its right-hand side `Hf` vanishes at weight `0`, so `∫ Gf (g + s h) = 0`
for both signs; the two identities give `∫ (v·∇g) h + ∫ g (v·∇h) = 0`, and integrability of the
two cross terms comes from the decay bounds on the cell strip.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

namespace RtdTransportAux

/-- Linearity of `∂_j` in the direction of a sum with a scalar multiple. -/
theorem pd_lin {g h : B0579.Plane → ℝ} (s : ℝ) (hg : Differentiable ℝ g)
    (hh : Differentiable ℝ h) (j : Fin 2) (z : B0579.Plane) :
    B0579.pd j (fun x => g x + s * h x) z = B0579.pd j g z + s * B0579.pd j h z := by
  have hd : HasFDerivAt (fun x => g x + s * h x)
      (fderiv ℝ g z + s • fderiv ℝ h z) z :=
    (hg z).hasFDerivAt.add ((hh z).hasFDerivAt.const_mul s)
  unfold B0579.pd
  rw [hd.fderiv]
  simp

/-- `lapP` is linear in the same sense. -/
theorem lapP_lin {g h : B0579.Plane → ℝ} (s : ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (z : B0579.Plane) :
    lapP (fun x => g x + s * h x) z = lapP g z + s * lapP h z := by
  have gd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have dg0 : Differentiable ℝ (B0579.pd 0 g) := (DbCommon.pd_contDiff_one hg 0).differentiable (by norm_num)
  have dg1 : Differentiable ℝ (B0579.pd 1 g) := (DbCommon.pd_contDiff_one hg 1).differentiable (by norm_num)
  have dh0 : Differentiable ℝ (B0579.pd 0 h) := (DbCommon.pd_contDiff_one hh 0).differentiable (by norm_num)
  have dh1 : Differentiable ℝ (B0579.pd 1 h) := (DbCommon.pd_contDiff_one hh 1).differentiable (by norm_num)
  have e0 : B0579.pd 0 (fun x => g x + s * h x) = fun x => B0579.pd 0 g x + s * B0579.pd 0 h x :=
    funext (pd_lin s gd hd 0)
  have e1 : B0579.pd 1 (fun x => g x + s * h x) = fun x => B0579.pd 1 g x + s * B0579.pd 1 h x :=
    funext (pd_lin s gd hd 1)
  unfold lapP
  rw [e0, e1, pd_lin s dg0 dh0 0 z, pd_lin s dg1 dh1 1 z]
  ring

theorem abs_add_smul_le (a b s : ℝ) : |a + s * b| ≤ |a| + |s| * |b| := by
  calc |a + s * b| ≤ |a| + |s * b| := abs_add_le _ _
    _ = |a| + |s| * |b| := by rw [abs_mul]

/-- A linear combination `g + s h` of two `CylSmoothDecay` functions is `CylSmoothDecay`. -/
theorem cylSmoothDecay_lin {c : ℝ} {g h : B0579.Plane → ℝ} (s : ℝ) (hg : CylSmoothDecay c g)
    (hh : CylSmoothDecay c h) : CylSmoothDecay c (fun x => g x + s * h x) := by
  have gd : Differentiable ℝ g := hg.smooth.differentiable (by norm_num)
  have hd : Differentiable ℝ h := hh.smooth.differentiable (by norm_num)
  refine ⟨hg.smooth.add (contDiff_const.mul hh.smooth), fun x => ?_, fun N => ?_⟩
  · show g (x.1 + c, x.2) + s * h (x.1 + c, x.2) = g x + s * h x
    rw [hg.periodic x, hh.periodic x]
  · obtain ⟨Cg, hCg⟩ := hg.decay N
    obtain ⟨Ch, hCh⟩ := hh.decay N
    refine ⟨Cg + |s| * Ch, fun x => ?_⟩
    have hw : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have k0 := abs_add_smul_le (g x) (h x) s
    have k1 := abs_add_smul_le (B0579.pd 0 g x) (B0579.pd 0 h x) s
    have k2 := abs_add_smul_le (B0579.pd 1 g x) (B0579.pd 1 h x) s
    have k3 := abs_add_smul_le (lapP g x) (lapP h x) s
    have hsum : |g x + s * h x| + |B0579.pd 0 (fun x => g x + s * h x) x|
        + |B0579.pd 1 (fun x => g x + s * h x) x| + |lapP (fun x => g x + s * h x) x|
        ≤ (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|)
          + (|s| * |h x| + |s| * |B0579.pd 0 h x| + |s| * |B0579.pd 1 h x| + |s| * |lapP h x|) := by
      rw [pd_lin s gd hd 0 x, pd_lin s gd hd 1 x, lapP_lin s hg.smooth hh.smooth x]
      linarith [k0, k1, k2, k3]
    calc (|g x + s * h x| + |B0579.pd 0 (fun x => g x + s * h x) x|
          + |B0579.pd 1 (fun x => g x + s * h x) x| + |lapP (fun x => g x + s * h x) x|)
          * (1 + x.2 ^ 2) ^ N
        ≤ ((|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|)
          + (|s| * |h x| + |s| * |B0579.pd 0 h x| + |s| * |B0579.pd 1 h x| + |s| * |lapP h x|))
          * (1 + x.2 ^ 2) ^ N := mul_le_mul_of_nonneg_right hsum hw
      _ = (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * (1 + x.2 ^ 2) ^ N
          + |s| * ((|h x| + |B0579.pd 0 h x| + |B0579.pd 1 h x| + |lapP h x|)
            * (1 + x.2 ^ 2) ^ N) := by ring
      _ ≤ Cg + |s| * Ch :=
          add_le_add (hCg x) (mul_le_mul_of_nonneg_left (hCh x) (abs_nonneg s))

/-- The weight-zero integrand `H` vanishes identically (`∂ jb⁰ = 0`). -/
theorem hf_zero {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} (u : B0579.Plane → ℝ)
    (z : B0579.Plane) : TransportIBP.Hf v u 0 z = 0 := by
  simp only [TransportIBP.Hf]
  rw [B0579.pd_zero_jb_rpow, B0579.pd_one_jb_rpow]
  ring

theorem hf_integral_zero {c : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} (u : B0579.Plane → ℝ) :
    ∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.Hf v u 0 z = 0 := by
  simp [hf_zero]

/-- Pointwise expansion of the weight-zero transport integrand along `g + s h`. -/
theorem gf_lin {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g h : B0579.Plane → ℝ} (s : ℝ)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (z : B0579.Plane) :
    TransportIBP.Gf v (fun x => g x + s * h x) 0 z =
      TransportIBP.Gf v g 0 z + s * ((v z 0 * B0579.pd 0 g z + v z 1 * B0579.pd 1 g z) * h z
        + g z * (v z 0 * B0579.pd 0 h z + v z 1 * B0579.pd 1 h z))
        + s ^ 2 * TransportIBP.Gf v h 0 z := by
  have gd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  simp only [TransportIBP.Gf, Real.rpow_zero, mul_one]
  rw [pd_lin s gd hd 0 z, pd_lin s gd hd 1 z]
  ring

theorem abs_mul_le_of_decay {a b C D J : ℝ} (hJ : 0 < J) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (ha : |a| * J ^ (2 : ℝ) ≤ C) (hb : |b| * J ^ (2 : ℝ) ≤ D) :
    |a| * |b| ≤ C * D * J ^ (-4 : ℝ) := by
  have key : J ^ (2 : ℝ) * J ^ (2 : ℝ) * J ^ (-4 : ℝ) = 1 := by
    rw [← Real.rpow_add hJ, ← Real.rpow_add hJ]
    norm_num
  have hprod : (|a| * J ^ (2 : ℝ)) * (|b| * J ^ (2 : ℝ)) ≤ C * D :=
    mul_le_mul ha hb (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hJ.le _)) hC0
  have hJ4 : 0 ≤ J ^ (-4 : ℝ) := Real.rpow_nonneg hJ.le _
  calc |a| * |b| = (|a| * J ^ (2 : ℝ)) * (|b| * J ^ (2 : ℝ)) * J ^ (-4 : ℝ) := by
        linear_combination (-(|a| * |b|)) * key
    _ ≤ C * D * J ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right hprod hJ4

/-- Integrability of the cross term `(v·∇g) h` on the cell. -/
theorem integrable_cross {c M : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    (hv : ContDiff ℝ 1 v) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) {g h : B0579.Plane → ℝ}
    (hg : CylSmoothDecay c g) (hh : CylSmoothDecay c h) :
    IntegrableOn (fun x => (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) * h x)
      (UnforcedLeray.Cyl.cell c) := by
  obtain ⟨C, hC0, hC⟩ := TransportIBP.decay_bound hg 2
  obtain ⟨D, hD0, hD⟩ := TransportIBP.decay_bound hh 2
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have hv0 : Continuous fun z => v z 0 :=
    ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hv1 : Continuous fun z => v z 1 :=
    ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hcont : Continuous fun x => (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) * h x :=
    ((hv0.mul (TransportIBP.continuous_pd hg1 0)).add
      (hv1.mul (TransportIBP.continuous_pd hg1 1))).mul hh.smooth.continuous
  refine TransportIBP.integrableOn_cell_of_bound
    (Q := fun x => M * (C * D) * B0579.jb x ^ (-4 : ℝ))
    (TransportIBP.integrable_jb_neg4.const_mul (M * (C * D))).integrableOn hcont
    (fun x hx => ?_)
  obtain ⟨a0, a1, a2⟩ := hC x hx
  obtain ⟨b0, b1, b2⟩ := hD x hx
  have hab : |B0579.pd 0 g x| * |h x| ≤ C * D * B0579.jb x ^ (-4 : ℝ) :=
    abs_mul_le_of_decay (B0579.jb_pos x) hC0 hD0 a1 b0
  have hbb : |B0579.pd 1 g x| * |h x| ≤ C * D * B0579.jb x ^ (-4 : ℝ) :=
    abs_mul_le_of_decay (B0579.jb_pos x) hC0 hD0 a2 b0
  have hK0 : 0 ≤ C * D * B0579.jb x ^ (-4 : ℝ) :=
    mul_nonneg (mul_nonneg hC0 hD0) (Real.rpow_nonneg (B0579.jb_pos x).le _)
  have habs : |v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x|
      ≤ |v x 0| * |B0579.pd 0 g x| + |v x 1| * |B0579.pd 1 g x| := by
    calc |v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x|
        ≤ |v x 0 * B0579.pd 0 g x| + |v x 1 * B0579.pd 1 g x| := abs_add_le _ _
      _ = |v x 0| * |B0579.pd 0 g x| + |v x 1| * |B0579.pd 1 g x| := by rw [abs_mul, abs_mul]
  show ‖(v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) * h x‖
      ≤ M * (C * D) * B0579.jb x ^ (-4 : ℝ)
  rw [Real.norm_eq_abs, abs_mul]
  calc |v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x| * |h x|
      ≤ (|v x 0| * |B0579.pd 0 g x| + |v x 1| * |B0579.pd 1 g x|) * |h x| :=
        mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    _ = |v x 0| * (|B0579.pd 0 g x| * |h x|) + |v x 1| * (|B0579.pd 1 g x| * |h x|) := by ring
    _ ≤ |v x 0| * (C * D * B0579.jb x ^ (-4 : ℝ))
          + |v x 1| * (C * D * B0579.jb x ^ (-4 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hab (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hbb (abs_nonneg _))
    _ = (|v x 0| + |v x 1|) * (C * D * B0579.jb x ^ (-4 : ℝ)) := by ring
    _ ≤ M * (C * D * B0579.jb x ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (hM x) hK0
    _ = M * (C * D) * B0579.jb x ^ (-4 : ℝ) := by ring

end RtdTransportAux

/-- **Leaf 4: integration by parts of the transport term on the cell** (SP 2092-2093,
2097-2101). -/
theorem rtdTransportIBP : UnforcedLeray.Short.IIb.RtdTransportIBP := by
  intro ν c tr r hr hc hM g h hg hh
  obtain ⟨M, hM⟩ := hM
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hv : ContDiff ℝ 1 (tr.v r) :=
    TransportIBP.contDiff_one_of_top (TransportIBP.contDiff_slice tr hr)
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM 0)
  have hvp := tr.isTrain.periodic_v r hr
  have hdiv := tr.isTrain.solenoidal r hr
  have hg2 : ContDiff ℝ 2 g := hg.smooth
  have hh2 : ContDiff ℝ 2 h := hh.smooth
  rw [hcell]
  have iA := RtdTransportAux.integrable_cross hv hM hg hh
  have iB : IntegrableOn (fun x => g x * (tr.v r x 0 * B0579.pd 0 h x + tr.v r x 1 * B0579.pd 1 h x))
      (UnforcedLeray.Cyl.cell c) := by
    convert RtdTransportAux.integrable_cross hv hM hh hg using 1
    funext x
    ring
  have iP := (TransportIBP.core hc hv hvp hdiv hM0 hM hg 0).1
  have iQ := (TransportIBP.core hc hv hvp hdiv hM0 hM hh 0).1
  have hint : ∀ s : ℝ,
      ∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.Gf (tr.v r) (fun x => g x + s * h x) 0 z
        = (∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.Gf (tr.v r) g 0 z)
          + s * ((∫ z in UnforcedLeray.Cyl.cell c,
                (tr.v r z 0 * B0579.pd 0 g z + tr.v r z 1 * B0579.pd 1 g z) * h z)
              + ∫ z in UnforcedLeray.Cyl.cell c,
                g z * (tr.v r z 0 * B0579.pd 0 h z + tr.v r z 1 * B0579.pd 1 h z))
          + s ^ 2 * ∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.Gf (tr.v r) h 0 z := by
    intro s
    have e : ∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.Gf (tr.v r) (fun x => g x + s * h x) 0 z
        = ∫ z in UnforcedLeray.Cyl.cell c, (TransportIBP.Gf (tr.v r) g 0 z
            + s * ((tr.v r z 0 * B0579.pd 0 g z + tr.v r z 1 * B0579.pd 1 g z) * h z
              + g z * (tr.v r z 0 * B0579.pd 0 h z + tr.v r z 1 * B0579.pd 1 h z))
            + s ^ 2 * TransportIBP.Gf (tr.v r) h 0 z) :=
      integral_congr_ae (ae_of_all _ fun z => RtdTransportAux.gf_lin (v := tr.v r) s hg2 hh2 z)
    have iAB : IntegrableOn (fun z => (tr.v r z 0 * B0579.pd 0 g z + tr.v r z 1 * B0579.pd 1 g z)
        * h z + g z * (tr.v r z 0 * B0579.pd 0 h z + tr.v r z 1 * B0579.pd 1 h z))
        (UnforcedLeray.Cyl.cell c) := iA.add iB
    have iS : IntegrableOn (fun z => s * ((tr.v r z 0 * B0579.pd 0 g z + tr.v r z 1 * B0579.pd 1 g z)
        * h z + g z * (tr.v r z 0 * B0579.pd 0 h z + tr.v r z 1 * B0579.pd 1 h z)))
        (UnforcedLeray.Cyl.cell c) := iAB.const_mul s
    have iT : IntegrableOn (fun z => TransportIBP.Gf (tr.v r) g 0 z + s * ((tr.v r z 0 * B0579.pd 0 g z
        + tr.v r z 1 * B0579.pd 1 g z) * h z + g z * (tr.v r z 0 * B0579.pd 0 h z
        + tr.v r z 1 * B0579.pd 1 h z)))
        (UnforcedLeray.Cyl.cell c) := iP.add iS
    have iU : IntegrableOn (fun z => s ^ 2 * TransportIBP.Gf (tr.v r) h 0 z)
        (UnforcedLeray.Cyl.cell c) := iQ.const_mul (s ^ 2)
    rw [e, integral_add iT iU, integral_add iP iS, integral_const_mul s,
      integral_add iA iB, integral_const_mul (s ^ 2)]
  have hz : ∀ s : ℝ,
      ∫ z in UnforcedLeray.Cyl.cell c, TransportIBP.Gf (tr.v r) (fun x => g x + s * h x) 0 z = 0 := by
    intro s
    obtain ⟨-, -, eq⟩ := TransportIBP.core hc hv hvp hdiv hM0 hM
      (RtdTransportAux.cylSmoothDecay_lin s hg hh) 0
    rw [eq, RtdTransportAux.hf_integral_zero, mul_zero]
  have k1 := hz 1
  have k2 := hz (-1)
  rw [hint 1] at k1
  rw [hint (-1)] at k2
  norm_num at k1 k2
  refine ⟨iA, iB, ?_⟩
  linarith

end UnforcedLeray.Short.IIb
