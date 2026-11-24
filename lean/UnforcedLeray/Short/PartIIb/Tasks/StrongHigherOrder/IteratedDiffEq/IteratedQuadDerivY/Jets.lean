import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedQuadDerivY.Words
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedQuadDerivY.Inlet

/-!
# Word derivatives of `u = e + w` at a parameter point (`PartII-b:S2/1/4`, helper)

Source of record: `the November 2 reference manuscript`,
lines 2552-2559 ("all factors through order `k` are bounded and derivatives through order `k + 2`
are in `Y_p`"), 2543-2551 (inlet decay), 1515-1531 (`D_p ⊂ L^∞`), 2531 (`Dw ∈ L^{2q₀}`).

`uWord p z a = D^a e + D^a w` (`e = E_εα` classically, `w` distributionally along the word `a`).
* Inlet: every word derivative of `e` is bounded by `B (1+|y|)^{-1}` off the axis
  (`IterQuadInlet.inletDecayAll`), hence lies in `L^∞ ∩ L^{2q₀}` of the cell.
* Correction: with a gradient tower of height `k + 1` (orders `≤ k + 2`) and orders `≤ k` in `D_p`,
  orders `1, …, k + 1` lie in `L^{2q₀}` (`gradL2pIBP`) and all orders in `L^{q₀}`.
* `uWord_weak`, `uWord_loc2`, `uWord_locq`: the hypotheses of `ibp_lb`;
  `uWord_prod`: every Leibniz product of total order `k + 2` lies in `L^{q₀}` of the cell.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

namespace IterQuadSub

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Cons.C03.Concrete (Params phaseInt phaseCell pairF advT rep rep_add_period
  stronglyMeasurable_rep)
open scoped ContDiff ENNReal

/-- `D^a u = D^a e + D^a w` along the word `a`. -/
def uWord (p : Params) (z : p.Z) (a : List (Fin 3)) (x : ℝ × UnforcedLeray.Space) : CVec3 :=
  eWord a (p.eFun (p.coord z)) x + rep (dWord a (p.wOf z)) x.1 x.2

theorem uWord_nil (p : Params) (z : p.Z) : uWord p z [] = p.uOf z := rfl

theorem uWord_apply (p : Params) (z : p.Z) (a : List (Fin 3)) (x : ℝ × UnforcedLeray.Space)
    (c : Fin 3) :
    uWord p z a x c = eWord a (p.eFun (p.coord z)) x c + rep (dWord a (p.wOf z)) x.1 x.2 c := by
  simp [uWord]

/-- The local cell measure is below the cell measure. -/
theorem loc_le_cell (P R : ℝ) :
    ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤ cellMeasure P :=
  Measure.prod_mono le_rfl Measure.restrict_le_self

theorem cproj_contDiff {f : ℝ × UnforcedLeray.Space → CVec3} (hf : ContDiff ℝ ∞ f) (c : Fin 3) :
    ContDiff ℝ ∞ (fun x => f x c) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) c : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf

theorem eFun_slice_eq (p : Params) (α : Fin 2 → ℝ) (τ : ℝ) :
    (fun w => p.eFun α (τ, w)) = realCL ∘ (fun w => ∑ i : Fin 2, α i • p.inlet i τ w) := by
  funext w
  rw [Function.comp_apply, realCL_apply]
  unfold Params.eFun
  rfl

theorem norm_iteratedFDeriv_eFun_slice_le (p : Params) (α : Fin 2 → ℝ) (τ : ℝ)
    (hinlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ)) (n : ℕ) (y : UnforcedLeray.Space) :
    ‖iteratedFDeriv ℝ n (fun w => p.eFun α (τ, w)) y‖ ≤
      |α 0| * ‖iteratedFDeriv ℝ n (p.inlet 0 τ) y‖ +
        |α 1| * ‖iteratedFDeriv ℝ n (p.inlet 1 τ) y‖ := by
  have hF : ContDiff ℝ ∞ (fun w => ∑ i : Fin 2, α i • p.inlet i τ w) :=
    ContDiff.sum fun i _ => (hinlet i).const_smul (α i)
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [eFun_slice_eq]
  have h2 := realCL.norm_iteratedFDeriv_comp_left (x := y) hF.contDiffAt hn
  have h3 : iteratedFDeriv ℝ n (fun w => ∑ i : Fin 2, α i • p.inlet i τ w) y =
      ∑ i : Fin 2, α i • iteratedFDeriv ℝ n (p.inlet i τ) y := by
    rw [iteratedFDeriv_sum (fun i _ => ((hinlet i).const_smul (α i)).of_le hn),
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact iteratedFDeriv_const_smul_apply (a := α i) ((hinlet i).contDiffAt.of_le hn)
  have h4 : ‖iteratedFDeriv ℝ n (fun w => ∑ i : Fin 2, α i • p.inlet i τ w) y‖ ≤
      |α 0| * ‖iteratedFDeriv ℝ n (p.inlet 0 τ) y‖ +
        |α 1| * ‖iteratedFDeriv ℝ n (p.inlet 1 τ) y‖ := by
    rw [h3, Fin.sum_univ_two]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h2.trans ((mul_le_of_le_one_left (norm_nonneg _) norm_realCL_le).trans h4)

/-! ### The inlet part -/

section Inlet

variable {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
  (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
  (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (z : p.Z)
include hq hreg hν1 hmode

theorem e_word_bound (l : List (Fin 3)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), y ∉ UnforcedLeray.Axi.axis →
      ‖eWord l (p.eFun (p.coord z)) (τ, y)‖ * (1 + ‖y‖) ≤ B := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  obtain ⟨B, hB0, hB⟩ := IterQuadInlet.inletDecayAll lam q hq l.length p hmode hc1 hR1
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  refine ⟨(|p.coord z 0| + |p.coord z 1|) * B, by positivity, fun τ y hy => ?_⟩
  have hinlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ) := by
    intro i
    have h := (inlet_contDiff_joint lam q hq hreg hν1 hmode i).comp
      ((contDiff_const (c := τ)).prodMk (contDiff_id (𝕜 := ℝ) (E := UnforcedLeray.Space)))
    show ContDiff ℝ ∞ (fun w => p.inlet i τ w)
    exact h
  have h5 : ‖eWord l (p.eFun (p.coord z)) (τ, y)‖ ≤
      |p.coord z 0| * ‖iteratedFDeriv ℝ l.length (p.inlet 0 τ) y‖ +
        |p.coord z 1| * ‖iteratedFDeriv ℝ l.length (p.inlet 1 τ) y‖ :=
    (norm_eWord_le_slice he l τ y).trans
      (norm_iteratedFDeriv_eFun_slice_le p (p.coord z) τ hinlet l.length y)
  have hy0 : 0 ≤ 1 + ‖y‖ := by positivity
  have hb0 := hB 0 τ y hy
  have hb1 := hB 1 τ y hy
  calc ‖eWord l (p.eFun (p.coord z)) (τ, y)‖ * (1 + ‖y‖)
      ≤ (|p.coord z 0| * ‖iteratedFDeriv ℝ l.length (p.inlet 0 τ) y‖ +
          |p.coord z 1| * ‖iteratedFDeriv ℝ l.length (p.inlet 1 τ) y‖) * (1 + ‖y‖) :=
        mul_le_mul_of_nonneg_right h5 hy0
    _ = |p.coord z 0| * ((1 + ‖y‖) * ‖iteratedFDeriv ℝ l.length (p.inlet 0 τ) y‖) +
          |p.coord z 1| * ((1 + ‖y‖) * ‖iteratedFDeriv ℝ l.length (p.inlet 1 τ) y‖) := by ring
    _ ≤ |p.coord z 0| * B + |p.coord z 1| * B := by
        gcongr
    _ = (|p.coord z 0| + |p.coord z 1|) * B := by ring

theorem e_word_memLp2 (l : List (Fin 3)) :
    MemLp (eWord l (p.eFun (p.coord z))) (2 * UnforcedLeray.B0412.q0E) (cellMeasure p.period) := by
  obtain ⟨B, hB0, hB⟩ := e_word_bound hq hreg hν1 hmode z l
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  exact memLp_cell_of_inv_bound (contDiff_eWord l he).continuous.aestronglyMeasurable B hB0 hB

theorem e_word_memLpTop (l : List (Fin 3)) :
    MemLp (eWord l (p.eFun (p.coord z))) ∞ (cellMeasure p.period) := by
  obtain ⟨B, hB0, hB⟩ := e_word_bound hq hreg hν1 hmode z l
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  exact memLp_top_cell_of_inv_bound (contDiff_eWord l he).continuous.aestronglyMeasurable B hB0 hB

end Inlet

/-! ### The correction part -/

section Corr

variable {p : Params} (hP1 : p.period ≤ 1) (z : p.Z) (k : ℕ)
  (hT : HasPhaseGradTower p.period UnforcedLeray.B0412.q0E (k + 1) (p.wOf z))
  (hD : ∀ a : List (Fin 3), a.length ≤ k →
    dWord a (p.wOf z) ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E)

include hT in
theorem w_hasPhaseOp (a : List (Fin 3)) (ha : a.length ≤ k + 1) (j : Fin 3) :
    HasPhaseOp (fun Φ => -dy j Φ) (dWord a (p.wOf z)) (dWord (a ++ [j]) (p.wOf z)) :=
  tower_hasPhaseOp a (k + 1) (p.wOf z) hT ha j

include hP1 hT hD in
theorem w_memLp_2q0 (a : List (Fin 3)) (ha0 : a ≠ []) (ha : a.length ≤ k + 1) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep (dWord a (p.wOf z)) x.1 x.2)
      (2 * UnforcedLeray.B0412.q0E) (phaseμ p.period) := by
  obtain ⟨a', j, rfl⟩ : ∃ a' j, a = a' ++ [j] :=
    ⟨a.dropLast, a.getLast ha0, (List.dropLast_append_getLast ha0).symm⟩
  have ha' : a'.length ≤ k := by simp only [List.length_append, List.length_singleton] at ha; omega
  obtain ⟨M, hM0, hM⟩ := Quad2IbpSub.rep_ae_bound_of_mem_D hP1 (hD a' ha')
  exact (gradL2pIBP p.period (dWord a' (p.wOf z)) (fun j => dWord (a' ++ [j]) (p.wOf z))
    (fun j m => dWord (a' ++ [j] ++ [m]) (p.wOf z)) M hM0 hM
    (fun j => w_hasPhaseOp z k hT a' (by omega) j)
    (fun j m => w_hasPhaseOp z k hT (a' ++ [j]) (by simp; omega) m) j).1

theorem w_memLp_q0 (a : List (Fin 3)) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep (dWord a (p.wOf z)) x.1 x.2)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) := by
  have hm : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
      (Ioc (0 : ℝ) p.period ×ˢ (univ : Set UnforcedLeray.Space)) = cellMeasure p.period := by
    simpa only [cellMeasure, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure UnforcedLeray.Space)) (Ioc (0 : ℝ) p.period)).symm
  have hL := UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell (P := p.period)
    (q := UnforcedLeray.B0412.q0E) UnforcedLeray.B0412.q0E_ne_top (dWord a (p.wOf z))
  rw [hm] at hL
  exact hL

include hP1 hD in
theorem w_bound (a : List (Fin 3)) (ha : a.length ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂(cellMeasure p.period),
      ‖rep (dWord a (p.wOf z)) x.1 x.2‖ ≤ M :=
  Quad2IbpSub.rep_ae_bound_of_mem_D hP1 (hD a ha)

end Corr

/-! ### `D^a u` -/

section U

variable {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
  (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
  (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (hP1 : p.period ≤ 1)
  (z : p.Z) (k : ℕ)
  (hT : HasPhaseGradTower p.period UnforcedLeray.B0412.q0E (k + 1) (p.wOf z))
  (hD : ∀ a : List (Fin 3), a.length ≤ k →
    dWord a (p.wOf z) ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E)

theorem uWord_fun (a : List (Fin 3)) (c : Fin 3) :
    (fun x => uWord p z a x c) =
      fun x => eWord a (p.eFun (p.coord z)) x c + rep (dWord a (p.wOf z)) x.1 x.2 c :=
  funext fun x => uWord_apply p z a x c

include hq hreg hν1 hmode hT in
theorem uWord_weak (a : List (Fin 3)) (ha : a.length ≤ k + 1) (j c : Fin 3) :
    WeakDyS p.period j (fun x => uWord p z a x c) (fun x => uWord p z (a ++ [j]) x c) := by
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  have hea := contDiff_eWord a he
  have hs : ContDiff ℝ ∞ (fun x => eWord a (p.eFun (p.coord z)) x c) := cproj_contDiff hea c
  have hcomm : (fun x => eWord (a ++ [j]) (p.eFun (p.coord z)) x c) =
      dy j (fun x => eWord a (p.eFun (p.coord z)) x c) := by
    funext x
    rw [eWord_append]
    exact (dy_comp_coord hea j c x).symm
  have hwe : WeakDyS p.period j (fun x => eWord a (p.eFun (p.coord z)) x c)
      (fun x => eWord (a ++ [j]) (p.eFun (p.coord z)) x c) := by
    rw [hcomm]
    exact weakDyS_of_smooth p.period j hs
  obtain ⟨hw, hm, hm'⟩ := gEQRepWeak p.period j (dWord a (p.wOf z)) (dWord (a ++ [j]) (p.wOf z))
    (w_hasPhaseOp z k hT a ha j) c
  have he_loc : MemLpLoc p.period (fun x => eWord a (p.eFun (p.coord z)) x c) 2 :=
    fun R => memLp_ddu_loc p.period R hs.continuous 2
  have he'_loc : MemLpLoc p.period (fun x => eWord (a ++ [j]) (p.eFun (p.coord z)) x c) 2 :=
    fun R => memLp_ddu_loc p.period R (cproj_contDiff (contDiff_eWord (a ++ [j]) he) c).continuous 2
  have hr_loc : MemLpLoc p.period (fun x => rep (dWord a (p.wOf z)) x.1 x.2 c) 2 :=
    memLpLoc_mono (fun R => hm.mono_measure (loc_le_cell p.period R)) q0E_two_le
  have hr'_loc : MemLpLoc p.period (fun x => rep (dWord (a ++ [j]) (p.wOf z)) x.1 x.2 c) 2 :=
    memLpLoc_mono (fun R => hm'.mono_measure (loc_le_cell p.period R)) q0E_two_le
  rw [uWord_fun, uWord_fun]
  exact Quad2IbpSub.weakDyS_add_loc2 j he_loc he'_loc hr_loc hr'_loc hwe hw

include hq hreg hν1 hmode hP1 hT hD in
theorem uWord_loc2 (a : List (Fin 3)) (ha : a.length ≤ k + 1) (c : Fin 3) :
    MemLpLoc p.period (fun x => uWord p z a x c) (2 * UnforcedLeray.B0412.q0E) := by
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  intro R
  rw [uWord_fun]
  have hA := memLp_ddu_loc p.period R (cproj_contDiff (contDiff_eWord a he) c).continuous
    (2 * UnforcedLeray.B0412.q0E)
  refine hA.add ?_
  by_cases ha0 : a = []
  · subst ha0
    obtain ⟨M, hM0, hM⟩ := w_bound hP1 z k hD [] (by simp)
    have hC := memLp_ddu_loc p.period R (f := fun _ => (M : ℂ)) continuous_const
      (2 * UnforcedLeray.B0412.q0E)
    refine hC.of_le ?_ ?_
    · exact ((measurable_coord' (stronglyMeasurable_rep _).measurable c).aestronglyMeasurable)
    · refine ae_mono (loc_le_cell p.period R) ?_
      filter_upwards [hM] with x hx
      have h1 : ‖rep (dWord [] (p.wOf z)) x.1 x.2 c‖ ≤ ‖rep (dWord [] (p.wOf z)) x.1 x.2‖ :=
        PiLp.norm_apply_le _ c
      rw [Complex.norm_real, Real.norm_of_nonneg hM0]
      exact h1.trans hx
  · have h2 := w_memLp_2q0 hP1 z k hT hD a ha0 ha
    exact (memLp_coord' h2 c).mono_measure (loc_le_cell p.period R)

include hq hreg hν1 hmode in
theorem uWord_locq (a : List (Fin 3)) (c : Fin 3) :
    MemLpLoc p.period (fun x => uWord p z a x c) UnforcedLeray.B0412.q0E := by
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  intro R
  rw [uWord_fun]
  exact (memLp_ddu_loc p.period R (cproj_contDiff (contDiff_eWord a he) c).continuous _).add
    ((memLp_coord' (w_memLp_q0 z a) c).mono_measure (loc_le_cell p.period R))

include hq hreg hν1 hmode in
theorem uWord_measurable (a : List (Fin 3)) : StronglyMeasurable (uWord p z a) := by
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := Quad2IbpSub.eFun_contDiff hq hreg hν1 hmode z
  exact (contDiff_eWord a he).continuous.stronglyMeasurable.add (stronglyMeasurable_rep _)

theorem uWord_periodic (a : List (Fin 3)) (x : ℝ × UnforcedLeray.Space) :
    uWord p z a (x.1 + p.period, x.2) = uWord p z a x := by
  show eWord a (p.eFun (p.coord z)) (x.1 + p.period, x.2) +
      rep (dWord a (p.wOf z)) (x.1 + p.period) x.2 =
    eWord a (p.eFun (p.coord z)) x + rep (dWord a (p.wOf z)) x.1 x.2
  rw [eWord_periodic a (fun y => eFun_period' p (p.coord z) y) x, rep_add_period]

/-- The product of an `L^{2q₀} ∩ L^∞ + L^{q₀}` factor and an `L^{2q₀} + L^{q₀}` factor that is
also bounded lies in `L^{q₀}`. -/
theorem memLp_prod_split {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ea ra eb rb : X → ℂ}
    (hea2 : MemLp ea (2 * UnforcedLeray.B0412.q0E) μ) (heaT : MemLp ea ∞ μ)
    (hra : MemLp ra UnforcedLeray.B0412.q0E μ)
    (heb2 : MemLp eb (2 * UnforcedLeray.B0412.q0E) μ) (hrb : MemLp rb UnforcedLeray.B0412.q0E μ)
    (hubT : MemLp (fun x => eb x + rb x) ∞ μ) :
    MemLp (fun x => (ea x + ra x) * (eb x + rb x)) UnforcedLeray.B0412.q0E μ := by
  have t1 : MemLp (fun x => ea x * eb x) UnforcedLeray.B0412.q0E μ := heb2.mul hea2
  have t2 : MemLp (fun x => ea x * rb x) UnforcedLeray.B0412.q0E μ := hrb.mul heaT
  have t3 : MemLp (fun x => ra x * (eb x + rb x)) UnforcedLeray.B0412.q0E μ := hubT.mul hra
  have h := (t1.add t2).add t3
  convert h using 1
  funext x
  simp only [Pi.add_apply]
  ring

include hq hreg hν1 hmode hP1 hT hD in
theorem uWord_prod (a b : List (Fin 3)) (hab : a.length + b.length = k + 2) (m i : Fin 3) :
    MemLp (fun x => uWord p z a x m * uWord p z b x i) UnforcedLeray.B0412.q0E
      (cellMeasure p.period) := by
  have E2 : ∀ (l : List (Fin 3)) (c : Fin 3),
      MemLp (fun x => eWord l (p.eFun (p.coord z)) x c) (2 * UnforcedLeray.B0412.q0E)
        (cellMeasure p.period) := fun l c =>
    memLp_coord' (e_word_memLp2 hq hreg hν1 hmode z l) c
  have ET : ∀ (l : List (Fin 3)) (c : Fin 3),
      MemLp (fun x => eWord l (p.eFun (p.coord z)) x c) ∞ (cellMeasure p.period) := fun l c =>
    memLp_coord' (e_word_memLpTop hq hreg hν1 hmode z l) c
  have WQ : ∀ (l : List (Fin 3)) (c : Fin 3),
      MemLp (fun x => rep (dWord l (p.wOf z)) x.1 x.2 c) UnforcedLeray.B0412.q0E
        (cellMeasure p.period) := fun l c => memLp_coord' (w_memLp_q0 z l) c
  have UT : ∀ c : Fin 3, MemLp (fun x => eWord [] (p.eFun (p.coord z)) x c +
      rep (dWord [] (p.wOf z)) x.1 x.2 c) ∞ (cellMeasure p.period) := by
    intro c
    obtain ⟨M, hM0, hM⟩ := w_bound hP1 z k hD [] (by simp)
    refine (ET [] c).add (memLp_top_of_bound
      ((measurable_coord' (stronglyMeasurable_rep _).measurable c).aestronglyMeasurable) M ?_)
    filter_upwards [hM] with x hx
    exact (PiLp.norm_apply_le _ c).trans hx
  have U2 : ∀ (l : List (Fin 3)), l ≠ [] → l.length ≤ k + 1 → ∀ c : Fin 3,
      MemLp (fun x => uWord p z l x c) (2 * UnforcedLeray.B0412.q0E) (cellMeasure p.period) := by
    intro l hl0 hl c
    rw [uWord_fun]
    exact (E2 l c).add (memLp_coord' (w_memLp_2q0 hP1 z k hT hD l hl0 hl) c)
  simp only [uWord_apply]
  by_cases ha : a = []
  · subst ha
    have h := memLp_prod_split (E2 b i) (ET b i) (WQ b i) (E2 [] m) (WQ [] m) (UT m)
    convert h using 1
    funext x
    ring
  by_cases hb : b = []
  · subst hb
    exact memLp_prod_split (E2 a m) (ET a m) (WQ a m) (E2 [] i) (WQ [] i) (UT i)
  have ha1 : 1 ≤ a.length := List.length_pos_iff.2 ha
  have hb1 : 1 ≤ b.length := List.length_pos_iff.2 hb
  have hA := U2 a ha (by omega) m
  have hB := U2 b hb (by omega) i
  rw [uWord_fun] at hA hB
  exact hB.mul hA

end U

end IterQuadSub

end UnforcedLeray.Short.IIb
