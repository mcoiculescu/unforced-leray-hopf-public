import UnforcedLeray.Short.PartIIb.Sub.G1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Sub.R1_5
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!


Source of record: `the November 2 reference manuscript`, lines 2355-2383 and
1214-ff (`eq:m3-ring-lift`).

Off the axis, `p.raw τ` is the similarity profile `e^{τ/2} u(e^τ, e^{τ/2} y)` of the B0185 lift
velocity `u = streamLift (merStream R ψ t)` of the decaying train stream, hence divergence free
(`Axi.div_streamLift_eq_zero` and the dilation chain rule; `offAxis_divFree`).  On the axis the
divergence of the `C¹` field `p.raw τ` (`RawContDiff`) is continuous and vanishes on the dense set
`axisᶜ` (`rawDivFree_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0184 UnforcedLeray.B0185

/-- The `ContDiffOn 2` of the train stream on the age domain, from the joint smoothness in
`BgRegime`. -/
theorem trainStream_contDiffOn {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp) :
    ContDiffOn ℝ 2 (trainStream p) ageDomain := by
  have h := (hb.train_stream_smooth).of_le (m := 2) (by simp)
  have hc : ContDiffOn ℝ 2
      ((fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ x.1 x.2) ∘
        fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))) ageDomain := by
    refine h.comp (by fun_prop : ContDiff ℝ 2 fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))).contDiffOn ?_
    intro x hx
    exact ⟨hx, trivial⟩
  exact hc

/-- **Off-axis solenoidality of `U_raw`** (the ring lift of the train stream). -/
theorem offAxis_divFree {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp) (τ : ℝ)
    {y : Space} (hy : y ∉ Axi.axis) :
    ∑ k : Fin 3, fderiv ℝ (p.raw τ) y (EuclideanSpace.single k 1) k = 0 := by
  set l : ℝ := Real.exp (τ / 2) with hl
  have hlpos : 0 < l := Real.exp_pos _
  set t : ℝ := Real.exp τ with ht
  have htpos : 0 < t := Real.exp_pos _
  have hR : p.R ≠ 0 := p.R_pos.ne'
  have hψ := trainStream_contDiffOn hb
  have hψd : DifferentiableOn ℝ (trainStream p) ageDomain := hψ.differentiableOn (by norm_num)
  set Ψ : ℝ × ℝ → ℝ := merStream p.R (trainStream p) t with hΨ
  have hΨ2 : ContDiffOn ℝ 2 Ψ (Ioi 0 ×ˢ univ) := contDiffOn_merStream p.R t hR htpos hψ
  have hu : ∀ z : Space, liftVelocity p.R (trainStream p) t z = Axi.streamLift Ψ z := by
    intro z
    exact congrFun (liftVelocity_eq_streamLift p.R t hR htpos hψd) z
  have hly : l • y ∉ Axi.axis := by
    rw [Axi.mem_axis_iff]
    have : Axi.ϱ (l • y) = l * Axi.ϱ y := by
      rw [UnforcedLeray.B0190.ϱ_dilate hlpos y]
    rw [this]
    exact mul_ne_zero hlpos.ne' (Axi.ϱ_ne_zero hy)
  have hSd : DifferentiableAt ℝ (Axi.streamLift Ψ) (l • y) := by
    have hp : 0 < (Axi.mer (l • y)).1 := Axi.ϱ_pos hly
    have hnh : Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ 𝓝 (Axi.mer (l • y)) :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp, trivial⟩
    have hP : DifferentiableAt ℝ (Axi.streamProfile Ψ) (Axi.mer (l • y)) :=
      ((Axi.contDiffOn_streamProfile hΨ2).contDiffAt hnh).differentiableAt (by norm_num)
    exact (Axi.hasFDerivAt_liftMer hly hP).differentiableAt
  -- the field near `y`
  have hev : p.raw τ =ᶠ[𝓝 y] fun z => l • Axi.streamLift Ψ (l • z) := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds (Set.mem_compl hy)] with z hz
    have hz' : Axi.ϱ z ≠ 0 := Axi.ϱ_ne_zero hz
    rw [rawIsRingLift_of UnforcedLeray.Short.PartI.trainStreamSmooth p hb.train_buc τ z hz']
    simp only [UnforcedLeray.B0190.simProfile, pow_one]
    exact congrArg (fun w => l • w) (hu _)
  have hdiv0 : Axi.divergence (Axi.streamLift Ψ) (l • y) = 0 :=
    Axi.div_streamLift_eq_zero hΨ2 hly
  have h1 : HasFDerivAt (fun z : Space => l • z) (l • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul l
  have h2 := (hSd.hasFDerivAt.comp y h1).const_smul l
  have hfd : fderiv ℝ (p.raw τ) y = l • ((fderiv ℝ (Axi.streamLift Ψ) (l • y)).comp
      (l • ContinuousLinearMap.id ℝ Space)) := by
    rw [hev.fderiv_eq]
    exact h2.fderiv
  rw [hfd]
  unfold Axi.divergence at hdiv0
  have : ∀ k : Fin 3, (l • ((fderiv ℝ (Axi.streamLift Ψ) (l • y)).comp
      (l • ContinuousLinearMap.id ℝ Space))) (EuclideanSpace.single k 1) k =
      (l * l) * fderiv ℝ (Axi.streamLift Ψ) (l • y) (coordinateVector k) k := by
    intro k
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_apply, map_smul, PiLp.smul_apply, smul_eq_mul]
    simp only [coordinateVector]
    ring
  rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.mul_sum, hdiv0, mul_zero]

/-- **`RawDivFree`, from the slice smoothness `RawContDiff`**: off the axis by `offAxis_divFree`;
on the axis the divergence of the `C¹` field `p.raw τ` is continuous and vanishes on the dense set
`axisᶜ`. -/
theorem rawDivFree_of (h : RawContDiff) : RawDivFree := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν _ _ i τ y
  have hC : ContDiff ℝ 1 (p.raw τ) := (H p d hreg hν τ).of_le (by simp)
  have hcont : Continuous fun z : Space =>
      ∑ k : Fin 3, fderiv ℝ (p.raw τ) z (EuclideanSpace.single k 1) k := by
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun z : Space => fderiv ℝ (p.raw τ) z (EuclideanSpace.single k 1) :=
      (hC.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp h1
  have hext := Continuous.ext_on UnforcedLeray.Cons.C03.dense_compl_axis hcont continuous_const
    (fun z hz => by simpa using offAxis_divFree hreg τ hz)
  simpa using congrFun hext y

end UnforcedLeray.Short.IIb
