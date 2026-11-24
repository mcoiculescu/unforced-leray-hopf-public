import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_1

/-!
# Part I, task `PartI:T02/1/4/6/4/5/2`: decomposition of `AdvectionLipLeaf`

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1, mild solution and spatial representative).

`AdvectionLipLeaf` is reduced to four analytic `Prop`s about the smooth periodic representative
`w` of the mild `H³` train `u` (all are consequences of `IsSpatialRepOn` and the continuity of
`u` on the compact interval `[0,T]`):

* `AdvLipSupDiff`: `‖w r z - w s z‖ ≤ C ‖u r - u s‖_{H³}` (`smooth_cyl_sup_le_h2norm` plus the
  `H³ → H²` forgetful map and `represents` at order zero);
* `AdvLipSupW`: `‖w r z‖ ≤ M` uniformly (`IsSpatialRepOn.bounded`);
* `AdvLipGradBound`: `‖∂_q w r‖_{L²}, ‖∂_η w r‖_{L²} ≤ K` uniformly (`represents` at order one,
  `vecH3CellDerivCLM` bounded, `u` bounded on `[0,T]`);
* `AdvLipGradDiff`: `‖∂(w r - w s)‖_{L²} ≤ K ‖u r - u s‖_{H³}` (`vecH3CellDerivCLM` is linear and
  continuous).

The algebra `(a·∇)a - (b·∇)b = (d·∇)a + (b·∇)d`, `d = a - b`, is done here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- Sup bound of the difference of representatives by the `H³` distance (source 261-288). -/
def AdvLipSupDiff : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r (hr : r ∈ Icc (0 : ℝ) T) s (hs : s ∈ Icc (0 : ℝ) T) (z : Plane),
      ‖w r z - w s z‖ ≤ C * ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖

/-- Uniform sup bound of the representative on `[0,T]` (from `IsSpatialRepOn.bounded`). -/
def AdvLipSupW : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ z : Plane, ‖w r z‖ ≤ M

/-- Uniform `L²(cell)` bound of the two first partials of the representative on `[0,T]`. -/
def AdvLipGradBound : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Icc (0 : ℝ) T,
      eLpNorm (Cyl.partialQ (w r)) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal K ∧
      eLpNorm (Cyl.partialEta (w r)) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal K

/-- `L²(cell)` bound of the first partials of the difference by the `H³` distance. -/
def AdvLipGradDiff : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r (hr : r ∈ Icc (0 : ℝ) T) s (hs : s ∈ Icc (0 : ℝ) T),
      eLpNorm (fun z => Cyl.partialQ (w r) z - Cyl.partialQ (w s) z) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖ ∧
      eLpNorm (fun z => Cyl.partialEta (w r) z - Cyl.partialEta (w s) z) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖

/-- Vector form of the advection for a differentiable field. -/
theorem advLip_advection_eq {f : Plane → Vec} (hd : Differentiable ℝ f) (z : Plane) :
    Train.advection f z = f z 0 • Cyl.partialQ f z + f z 1 • Cyl.partialEta f z := by
  have hq0 : Cyl.partialQ (fun w => f w 0) z = Cyl.partialQ f z 0 := advLeaf_partialQ_proj hd 0 z
  have hq1 : Cyl.partialQ (fun w => f w 1) z = Cyl.partialQ f z 1 := advLeaf_partialQ_proj hd 1 z
  have he0 : Cyl.partialEta (fun w => f w 0) z = Cyl.partialEta f z 0 :=
    advLeaf_partialEta_proj hd 0 z
  have he1 : Cyl.partialEta (fun w => f w 1) z = Cyl.partialEta f z 1 :=
    advLeaf_partialEta_proj hd 1 z
  ext l
  fin_cases l
  · simp [Train.advection, hq0, he0]
  · simp [Train.advection, hq1, he1]

/-- The scalar-times-vector `L²` bound. -/
theorem advLip_smul_bound {c : ℝ} {φ : Plane → ℝ} {P : Plane → Vec} {A : ℝ}
    (hφ : ∀ z, |φ z| ≤ A) :
    eLpNorm (fun z => φ z • P z) 2 (Cyl.cellμ c) ≤
      ENNReal.ofReal A * eLpNorm P 2 (Cyl.cellμ c) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφ z) (norm_nonneg _)

theorem advLip_comp_abs_le (v : Vec) (j : Fin 2) : |v j| ≤ ‖v‖ := by
  have h1 : ‖v j‖ ≤ ‖v‖ := PiLp.norm_apply_le v j
  rwa [Real.norm_eq_abs] at h1

/-- Assembly: `AdvectionLipLeaf` from the four analytic leaves. -/
theorem advectionLipLeaf_of (hD : AdvLipSupDiff) (hW : AdvLipSupW) (hG : AdvLipGradBound)
    (hGD : AdvLipGradDiff) : AdvectionLipLeaf := by
  intro ν c T hν hc hc1 hT u hu w hw
  obtain ⟨C, hC0, hC⟩ := hD ν c T hν hc hc1 hT u hu w hw
  obtain ⟨M, hM0, hM⟩ := hW ν c T hν hc hc1 hT u hu w hw
  obtain ⟨K3, hK30, hK3⟩ := hG ν c T hν hc hc1 hT u hu w hw
  obtain ⟨K4, hK40, hK4⟩ := hGD ν c T hν hc hc1 hT u hu w hw
  refine ⟨2 * C * K3 + 2 * M * K4, by positivity, ?_⟩
  intro r hr s hs
  set δ : ℝ := ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  set μ := Cyl.cellμ c with hμ
  have hda : Differentiable ℝ (w r) := (hw.smooth r hr).differentiable (by simp)
  have hdb : Differentiable ℝ (w s) := (hw.smooth s hs).differentiable (by simp)
  have hca : Continuous (w r) := hda.continuous
  have hcb : Continuous (w s) := hdb.continuous
  have hPaQ := advLeaf_partialQ_memLp hw hr
  have hPaE := advLeaf_partialEta_memLp hw hr
  have hPbQ := advLeaf_partialQ_memLp hw hs
  have hPbE := advLeaf_partialEta_memLp hw hs
  -- the four terms
  let T1 : Plane → Vec := fun z => (w r z - w s z) 0 • Cyl.partialQ (w r) z
  let T2 : Plane → Vec := fun z => (w r z - w s z) 1 • Cyl.partialEta (w r) z
  let T3 : Plane → Vec := fun z => w s z 0 • (Cyl.partialQ (w r) z - Cyl.partialQ (w s) z)
  let T4 : Plane → Vec := fun z => w s z 1 • (Cyl.partialEta (w r) z - Cyl.partialEta (w s) z)
  have hid : (fun z => Train.advection (w r) z - Train.advection (w s) z) =
      fun z => T1 z + T2 z + T3 z + T4 z := by
    funext z
    rw [advLip_advection_eq hda, advLip_advection_eq hdb]
    simp only [T1, T2, T3, T4, PiLp.sub_apply, sub_smul, smul_sub]
    abel
  have hcomp : ∀ (a : Plane → Vec), Continuous a → ∀ j : Fin 2, Continuous fun z => a z j :=
    fun a ha j => (advLeafProj j).continuous.comp ha
  have hdc : ∀ j : Fin 2, Continuous fun z => (w r z - w s z) j := fun j =>
    hcomp (fun z => w r z - w s z) (hca.sub hcb) j
  have hbc : ∀ j : Fin 2, Continuous fun z => w s z j := fun j => hcomp _ hcb j
  have m1 : AEStronglyMeasurable T1 μ := (hdc 0).aestronglyMeasurable.smul hPaQ.aestronglyMeasurable
  have m2 : AEStronglyMeasurable T2 μ := (hdc 1).aestronglyMeasurable.smul hPaE.aestronglyMeasurable
  have m3 : AEStronglyMeasurable T3 μ :=
    (hbc 0).aestronglyMeasurable.smul (hPaQ.aestronglyMeasurable.sub hPbQ.aestronglyMeasurable)
  have m4 : AEStronglyMeasurable T4 μ :=
    (hbc 1).aestronglyMeasurable.smul (hPaE.aestronglyMeasurable.sub hPbE.aestronglyMeasurable)
  obtain ⟨hq3, he3⟩ := hK3 r hr
  obtain ⟨hq4, he4⟩ := hK4 r hr s hs
  have hd0 : ∀ (j : Fin 2) z, |(w r z - w s z) j| ≤ C * δ := fun j z =>
    (advLip_comp_abs_le _ j).trans (hC r hr s hs z)
  have hb0 : ∀ (j : Fin 2) z, |w s z j| ≤ M := fun j z =>
    (advLip_comp_abs_le _ j).trans (hM s hs z)
  have b1 : eLpNorm T1 2 μ ≤ ENNReal.ofReal (C * δ * K3) := by
    refine (advLip_smul_bound (hd0 0)).trans ?_
    rw [ENNReal.ofReal_mul (p := C * δ) (by positivity)]
    gcongr
  have b2 : eLpNorm T2 2 μ ≤ ENNReal.ofReal (C * δ * K3) := by
    refine (advLip_smul_bound (hd0 1)).trans ?_
    rw [ENNReal.ofReal_mul (p := C * δ) (by positivity)]
    gcongr
  have b3 : eLpNorm T3 2 μ ≤ ENNReal.ofReal (M * K4 * δ) := by
    refine (advLip_smul_bound (hb0 0)).trans ?_
    have e : ENNReal.ofReal (M * K4 * δ) =
        ENNReal.ofReal M * (ENNReal.ofReal K4 * ENNReal.ofReal δ) := by
      rw [mul_assoc, ENNReal.ofReal_mul hM0, ENNReal.ofReal_mul hK40]
    rw [e]
    gcongr
  have b4 : eLpNorm T4 2 μ ≤ ENNReal.ofReal (M * K4 * δ) := by
    refine (advLip_smul_bound (hb0 1)).trans ?_
    have e : ENNReal.ofReal (M * K4 * δ) =
        ENNReal.ofReal M * (ENNReal.ofReal K4 * ENNReal.ofReal δ) := by
      rw [mul_assoc, ENNReal.ofReal_mul hM0, ENNReal.ofReal_mul hK40]
    rw [e]
    gcongr
  rw [hid]
  have hsum : eLpNorm (fun z => T1 z + T2 z + T3 z + T4 z) 2 μ ≤
      eLpNorm T1 2 μ + eLpNorm T2 2 μ + eLpNorm T3 2 μ + eLpNorm T4 2 μ := by
    have e1 : eLpNorm (fun z => T1 z + T2 z + T3 z + T4 z) 2 μ ≤
        eLpNorm (fun z => T1 z + T2 z + T3 z) 2 μ + eLpNorm T4 2 μ :=
      eLpNorm_add_le ((m1.add m2).add m3) m4 (by norm_num)
    have e2 : eLpNorm (fun z => T1 z + T2 z + T3 z) 2 μ ≤
        eLpNorm (fun z => T1 z + T2 z) 2 μ + eLpNorm T3 2 μ :=
      eLpNorm_add_le (m1.add m2) m3 (by norm_num)
    have e3 : eLpNorm (fun z => T1 z + T2 z) 2 μ ≤ eLpNorm T1 2 μ + eLpNorm T2 2 μ :=
      eLpNorm_add_le m1 m2 (by norm_num)
    calc _ ≤ _ := e1
      _ ≤ _ := by gcongr; exact e2.trans (by gcongr)
  refine hsum.trans ?_
  have hfin : ENNReal.ofReal (C * δ * K3) + ENNReal.ofReal (C * δ * K3) +
      ENNReal.ofReal (M * K4 * δ) + ENNReal.ofReal (M * K4 * δ) =
      ENNReal.ofReal (2 * C * K3 + 2 * M * K4) * ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [← hfin]
  gcongr

end UnforcedLeray.Short.PartI
