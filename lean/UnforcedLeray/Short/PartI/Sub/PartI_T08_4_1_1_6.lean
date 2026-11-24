import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.ErrPressureGradJetL2

/-!
# Part I, task `PartI:T08/4/1/1/6` (`TrainPressureGradLocal`): decomposition

Source: `the November 2 reference manuscript` lines 266-270, 326-329.

`Δπ + div F = 0` (`F = A + div Q_c`) at every age `r > 0`.  The qualitative result
`pressureGradJetL2OfDivForm_proof` gives `∂_w ∇π(r) ∈ L²(cell)`.  Local uniformity in `r` needs the
quantitative a priori estimate `PressureGradJetL2Quant` (constants depending only on the word, not
on `π, F, c`): `‖∂_w ∇π‖² ≤ C_w ∑_{u ∈ L_w} ‖∂_u F‖²` (true with `C_w = 1`-type constants by
periodic integration by parts / cutoff exhaustion).  Here the target is reduced to it and to
`TrainAdvLocal`, `TrainStressDivLocal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Quantitative pressure-gradient estimate** (lines 266-270, 326-329).  For each word `w` there
is a finite set `L` of words and `C ≥ 0` (independent of `c, π, F`) such that for every smooth
periodic bounded `π` and smooth periodic `F` with `L²` jets and `Δπ + div F = 0`,
`∫_cell ∑_k (∂_w ∂_k π)² ≤ C ∑_{u∈L} ∑_m ∫_cell (∂_u F_m)²`. -/
def PressureGradJetL2Quant : Prop :=
  ∀ w : List Bool, ∃ L : Finset (List Bool), ∃ C : ℝ, 0 ≤ C ∧
    ∀ c : ℝ, 0 < c → ∀ (π : Plane → ℝ) (F : Plane → Vec),
      ContDiff ℝ ∞ π → Cyl.IsPeriodic c π → (∃ M : ℝ, ∀ z, |π z| ≤ M) →
      SmoothJetL2 c F → Cyl.IsPeriodic c F →
      (∀ z, Train.lapS π z +
        (Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z) = 0) →
      ∫ z in Cyl.cell c, ∑ k : Fin 2, (wordComp w (Train.gradS π) k z) ^ 2 ≤
        C * ∑ u ∈ L, ∑ m : Fin 2, ∫ z in Cyl.cell c, (wordComp u F m z) ^ 2

theorem pgl_wc_add {A M : Plane → Vec} (hA : ContDiff ℝ ∞ A) (hM : ContDiff ℝ ∞ M)
    (w : List Bool) (k : Fin 2) :
    wordComp w (fun z => A z + M z) k = fun z => wordComp w A k z + wordComp w M k z := by
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  unfold wordComp
  exact ForcingIBP.derivWord_add_smooth w (fun x => A x k) (fun x => M x k) (comp hA k) (comp hM k)

/-- Per-age hypotheses of the quantitative lemma, from `TrainAdvLocal`, `TrainStressDivLocal`. -/
theorem pgl_fact {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (hA : LocalSmoothJetL2 c (fun r => advDiff tr r))
    (hM : LocalSmoothJetL2 c (fun r => Train.matDiv (Qc ν c r))) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (errPressure tr r) ∧ Cyl.IsPeriodic c (errPressure tr r) ∧
    (∃ M : ℝ, ∀ z, |errPressure tr r z| ≤ M) ∧
    SmoothJetL2 c (fun z => advDiff tr r z + Train.matDiv (Qc ν c r) z) ∧
    Cyl.IsPeriodic c (fun z => advDiff tr r z + Train.matDiv (Qc ν c r) z) ∧
    (∀ z, Train.lapS (errPressure tr r) z +
      (Cyl.partialQ (fun w => (advDiff tr r w + Train.matDiv (Qc ν c r) w) 0) z +
        Cyl.partialEta (fun w => (advDiff tr r w + Train.matDiv (Qc ν c r) w) 1) z) = 0) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hpcs, hpcd⟩ := pcSmoothDecay_proof ν c r hν hc hr.le
  have hps : ContDiff ℝ ∞ (tr.p r) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_p hr.le
  have hπs : ContDiff ℝ ∞ (errPressure tr r) := hps.sub hpcs
  have hπp : Cyl.IsPeriodic c (errPressure tr r) := by
    intro z
    show tr.p r (z.1 + c, z.2) - pc ν c r (z.1 + c, z.2) = tr.p r z - pc ν c r z
    rw [tr.isTrain.periodic_p r hr.le z, Train.pc_periodic ν c r z]
  have hdec : Tendsto (errPressure tr r) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have := (tr.isTrain.pressure_decay r hr.le).sub hpcd
    rw [sub_zero] at this
    exact this
  have hbd : ∃ M : ℝ, ∀ z : Plane, |errPressure tr r z| ≤ M :=
    periodicDecayBounded_proof c hc0 _ hπs.continuous hπp hdec
  have hAc := hA.1 r hr
  have hMc := hM.1 r hr
  have hAj : ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (advDiff tr r) k) 2 (Cyl.cellμ c) := by
    intro w k
    obtain ⟨ε, hε, K, h⟩ := hA.2 r hr w k
    exact (h r hr (by simpa using hε)).1
  have hMj : ∀ (w : List Bool) (k : Fin 2),
      MemLp (wordComp w (Train.matDiv (Qc ν c r)) k) 2 (Cyl.cellμ c) := by
    intro w k
    obtain ⟨ε, hε, K, h⟩ := hM.2 r hr w k
    exact (h r hr (by simpa using hε)).1
  have hvper : Cyl.IsPeriodic c (tr.v r) := tr.isTrain.periodic_v r hr.le
  have hVper : Cyl.IsPeriodic c (Vc ν c r) := Train.Vc_periodic ν c r
  have hadv : Cyl.IsPeriodic c (advDiff tr r) := by
    intro z
    show Train.advection (tr.v r) (z.1 + c, z.2) - Train.advection (Vc ν c r) (z.1 + c, z.2) =
      Train.advection (tr.v r) z - Train.advection (Vc ν c r) z
    rw [errGradAdvPeriodic hvper z, errGradAdvPeriodic hVper z]
  have hmat : Cyl.IsPeriodic c (Train.matDiv (Qc ν c r)) :=
    errGradMatDivPeriodic (fun k l => qcPeriodic_proof ν c r k l)
  refine ⟨hπs, hπp, hbd, ⟨hAc.add hMc, fun w k => ?_⟩, ?_, fun z => ?_⟩
  · rw [pgl_wc_add hAc hMc]
    exact (hAj w k).add (hMj w k)
  · intro z
    show advDiff tr r (z.1 + c, z.2) + Train.matDiv (Qc ν c r) (z.1 + c, z.2) =
      advDiff tr r z + Train.matDiv (Qc ν c r) z
    rw [hadv z, hmat z]
  · exact errPressureLap_proof ν c hν hc tr r hr z

theorem trainPressureGradLocal_of_quant (hQ : PressureGradJetL2Quant)
    (h1 : TrainAdvLocal) (h2 : TrainStressDivLocal) : TrainPressureGradLocal := by
  intro ν c hν hc tr htr
  have hc0 : 0 < c := by linarith
  have sA := h1 ν c hν hc tr htr
  have sM := h2 ν c hν hc tr htr
  have F := fun r (hr : 0 < r) => pgl_fact hν hc tr sA sM hr
  have hmem : ∀ r : ℝ, 0 < r → ∀ (w : List Bool) (k : Fin 2),
      MemLp (wordComp w (Train.gradS (errPressure tr r)) k) 2 (Cyl.cellμ c) := fun r hr =>
    pressureGradJetL2OfDivForm_proof c hc0 (errPressure tr r)
      (fun z => advDiff tr r z + Train.matDiv (Qc ν c r) z) (F r hr).1 (F r hr).2.1
      (F r hr).2.2.1 (F r hr).2.2.2.1 (F r hr).2.2.2.2.1 (F r hr).2.2.2.2.2
  refine ⟨fun r hr => ErrPressureLapAux.gradS_contDiff (F r hr).1, fun s hs w k => ?_⟩
  obtain ⟨L, C, hC, hbound⟩ := hQ w
  have hA' : ∀ (u : List Bool) (m : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ,
      ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp u (advDiff tr r) m) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp u (advDiff tr r) m z) ^ 2 ≤ K :=
    fun u m => sA.2 s hs u m
  have hM' : ∀ (u : List Bool) (m : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ,
      ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp u (Train.matDiv (Qc ν c r)) m) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2 ≤ K :=
    fun u m => sM.2 s hs u m
  choose εA hεA KA hKA using hA'
  choose εM hεM KM hKM using hM'
  have ev : ∀ᶠ r in 𝓝 s, ∀ u ∈ L, ∀ m : Fin 2, |r - s| < εA u m ∧ |r - s| < εM u m := by
    rw [Filter.eventually_all_finset]
    intro u _
    rw [Filter.eventually_all]
    intro m
    have : ∀ᶠ r in 𝓝 s, dist r s < min (εA u m) (εM u m) :=
      Metric.eventually_nhds_iff.2 ⟨min (εA u m) (εM u m), lt_min (hεA u m) (hεM u m),
        fun y hy => hy⟩
    filter_upwards [this] with r hr
    rw [Real.dist_eq] at hr
    exact ⟨lt_of_lt_of_le hr (min_le_left _ _), lt_of_lt_of_le hr (min_le_right _ _)⟩
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 ev
  refine ⟨ε, hε, C * ∑ u ∈ L, ∑ m : Fin 2, 2 * (KA u m + KM u m), fun r hr hrs => ?_⟩
  refine ⟨hmem r hr w k, ?_⟩
  have hrs' : ∀ u ∈ L, ∀ m : Fin 2, |r - s| < εA u m ∧ |r - s| < εM u m :=
    hP (by rw [Real.dist_eq]; exact hrs)
  obtain ⟨hπs, hπp, hbd, hFs, hFp, hlap⟩ := F r hr
  have step1 : ∫ z in Cyl.cell c, (wordComp w (Train.gradS (errPressure tr r)) k z) ^ 2 ≤
      ∫ z in Cyl.cell c, ∑ k' : Fin 2, (wordComp w (Train.gradS (errPressure tr r)) k' z) ^ 2 := by
    refine integral_mono ?_ ?_ fun z => ?_
    · exact (hmem r hr w k).integrable_sq
    · exact integrable_finset_sum _ fun k' _ => (hmem r hr w k').integrable_sq
    · exact Finset.single_le_sum (f := fun k' : Fin 2 =>
        (wordComp w (Train.gradS (errPressure tr r)) k' z) ^ 2)
        (fun k' _ => sq_nonneg _) (Finset.mem_univ k)
  have step2 := hbound c hc0 (errPressure tr r)
    (fun z => advDiff tr r z + Train.matDiv (Qc ν c r) z) hπs hπp hbd hFs hFp hlap
  refine step1.trans (step2.trans ?_)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => Finset.sum_le_sum
    fun m _ => ?_) hC
  obtain ⟨hmA, hiA⟩ := hKA u m r hr (hrs' u hu m).1
  obtain ⟨hmM, hiM⟩ := hKM u m r hr (hrs' u hu m).2
  have hAc := sA.1 r hr
  have hMc := sM.1 r hr
  rw [pgl_wc_add hAc hMc]
  have iA : IntegrableOn (fun z => (wordComp u (advDiff tr r) m z) ^ 2) (Cyl.cell c) :=
    hmA.integrable_sq
  have iM : IntegrableOn (fun z => (wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2)
      (Cyl.cell c) := hmM.integrable_sq
  have iS : IntegrableOn (fun z => 2 * (wordComp u (advDiff tr r) m z) ^ 2 +
      2 * (wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2) (Cyl.cell c) :=
    (iA.const_mul 2).add (iM.const_mul 2)
  have iT : IntegrableOn (fun z => (wordComp u (advDiff tr r) m z +
      wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2) (Cyl.cell c) :=
    (hmA.add hmM).integrable_sq
  calc ∫ z in Cyl.cell c, (wordComp u (advDiff tr r) m z +
        wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2
      ≤ ∫ z in Cyl.cell c, (2 * (wordComp u (advDiff tr r) m z) ^ 2 +
        2 * (wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2) := by
        refine integral_mono iT iS fun z => ?_
        nlinarith [sq_nonneg (wordComp u (advDiff tr r) m z -
          wordComp u (Train.matDiv (Qc ν c r)) m z)]
    _ = 2 * (∫ z in Cyl.cell c, (wordComp u (advDiff tr r) m z) ^ 2) +
        2 * (∫ z in Cyl.cell c, (wordComp u (Train.matDiv (Qc ν c r)) m z) ^ 2) := by
        rw [integral_add (iA.const_mul 2) (iM.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * (KA u m + KM u m) := by linarith

/-- **Leaf Q0 (order 0, lines 266-270, 326-329).**  Under the Poisson hypotheses,
`∫_cell |∇π|² ≤ 4 ∫_cell |F|²` (cutoff `φ_R(η)`: `∫φ²|∇π|² = -∫φ²πΔπ - 2∫φπ∇φ·∇π`,
`-∫φ²πΔπ = ∫φ²π div F`, Cauchy-Schwarz, strip terms `O(M² R^{-1/2})`, let `R → ∞`). -/
def PressureGradOrder0Quant : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (π : Plane → ℝ) (F : Plane → Vec),
    ContDiff ℝ ∞ π → Cyl.IsPeriodic c π → (∃ M : ℝ, ∀ z, |π z| ≤ M) →
    SmoothJetL2 c F → Cyl.IsPeriodic c F →
    (∀ z, Train.lapS π z +
      (Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z) = 0) →
    ∫ z in Cyl.cell c, ∑ k : Fin 2, (Train.gradS π z k) ^ 2 ≤
      4 * ∑ m : Fin 2, ∫ z in Cyl.cell c, (F z m) ^ 2

/-- **Leaf Q1 (gradient from `h, Δh ∈ L²`, quantitative).**  For smooth periodic `h` with
`h, Δh ∈ L²(cell)`: `∫ (∂_q h)² + (∂_η h)² ≤ 2 (∫ h² + ∫ (Δh)²)` (cutoff IBP
`∫φ²|∇h|² ≤ ‖h‖‖Δh‖ + ½∫φ²|∇h|² + 2∫h²|∇φ|²`, let `R → ∞`). -/
def GradL2QuantP : Prop :=
  ∀ (c : ℝ) (h : Plane → ℝ), 0 < c → ContDiff ℝ ∞ h → Cyl.IsPeriodic c h →
    MemLp h 2 (Cyl.cellμ c) → MemLp (Train.lapS h) 2 (Cyl.cellμ c) →
    ∫ z in Cyl.cell c, ((Cyl.partialQ h z) ^ 2 + (Cyl.partialEta h z) ^ 2) ≤
      2 * ((∫ z in Cyl.cell c, (h z) ^ 2) + ∫ z in Cyl.cell c, (Train.lapS h z) ^ 2)

/-- **Leaf Q2 (pointwise Laplacian identity for word jets of `∇π`).**  For each word `w` and
component `k` there are words `u0, u1` such that, whenever `Δπ + div F = 0` with `π, F` smooth,
`Δ ∂_w (∇π)_k = -(∂_{u0} F_0 + ∂_{u1} F_1)` (word derivatives commute with `Δ`, `∂_k`; apply
`∂_w ∂_k` to the Poisson identity). -/
def PressureGradWordLapId : Prop :=
  ∀ (w : List Bool) (k : Fin 2), ∃ u0 u1 : List Bool,
    ∀ (π : Plane → ℝ) (F : Plane → Vec), ContDiff ℝ ∞ π → ContDiff ℝ ∞ F →
    (∀ z, Train.lapS π z +
      (Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z) = 0) →
    ∀ z, Train.lapS (wordComp w (Train.gradS π) k) z =
      -(wordComp u0 F 0 z + wordComp u1 F 1 z)

end UnforcedLeray.Short.PartI
