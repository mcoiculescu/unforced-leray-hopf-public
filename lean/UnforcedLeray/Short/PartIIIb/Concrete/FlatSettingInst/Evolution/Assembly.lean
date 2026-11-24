import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves

/-!
# Conditional assembly of `TrainEvolutionExists` (source 2819-2836, 4349-4352)

Source of record: `the November 2 reference manuscript` (73 pages).

For `m > 8`, `0 < ν ≤ min ν₁ 1` (`ν₁` from `TrainBoundsSmall`), `c = ν⁻²` and a BUC train `tr`:

1. the horizon flux paths `Pn n` (`FluxPathExistsAll`, finite-horizon train bounds) and a rescaled
   heat family `H` with the reflection laws (`ReflHeatSupplierExists`) give the real Volterra
   evolution `E = Exist.horizonEvolution hm Pn H` on the actual zero-circulation state space
   (source 2819-2836); its orbits are weak flows on unit strips (`stripWeakAssemblyOnFromParts`,
   `horizonEvolution_eq`), it is a cocycle (`horizonEvolution_comp`), commutes with the reflection
   (`VolterraReflect`, `FluxBOnRefl`: the train is odd, source 287-288), is bounded on bounded age
   strips (`VolterraData.norm_evolution_le`) and jointly strongly continuous (`VolterraJointCont`);
2. `U(s,t) = cx (E s t)` for `0 ≤ t ≤ s` (the complexification keeps `X_{m,c}`, source 4349-4352),
   `U(s,t) = I` otherwise;
3. the fields of `TrainEvolution`: `flow` by `FlowOfRealFamily`, `cocycle` by `cx_comp_eq`, `real` by
   `conjX_cx`, `locBdd` by `norm_cx_le`, `jointCont` by `norm_cx_sub_cx_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Infra.VolterraEvolution (VolterraData)
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.Short.IIIa.Exist

/-- **`TrainEvolutionExists` from its leaves** (source 2819-2836, 4349-4352, 287-288). -/
theorem trainEvolutionExists_of
    (hTB : TrainBoundsSmall) (hFP : FluxPathExistsAll) (hHeat : ReflHeatSupplierExists)
    (hBS : BiotSavartFieldAll) (hFI : FluxIdentityOnAll) (hMI : MildIntegratedOnAll)
    (hSC : StripContinuityOnAll) (hLoc : HorizonLocality) (hCongr : FlowCongrAE)
    (hFlow : FlowOfRealFamily) (hRefl : VolterraReflect) (hJC : VolterraJointCont)
    (hB : FluxBOnRefl) : TrainEvolutionExists := by
  intro m hm8
  obtain ⟨ν₁, hν₁, hTBm⟩ := hTB m hm8
  refine ⟨min ν₁ 1, lt_min hν₁ one_pos, ?_⟩
  intro ν hν c hc hm1fact tr htr
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hνν₁ : ν ≤ ν₁ := hν.2.trans (min_le_left _ _)
  have hc2 : c = ν ^ (-2 : ℝ) := by
    rw [hc, cOf, Real.rpow_neg hν0.le, Real.rpow_two]
  subst hc2
  have hR : Regime ν (ν ^ (-2 : ℝ)) m := ⟨hν0, hν1, rfl, hm8⟩
  haveI hcpos : Fact (0 < ν ^ (-2 : ℝ)) := ⟨hR.pos_c⟩
  have hm1 : 1 ≤ m := hR.one_le_m
  have hBnd : FiniteHorizonTrainBounds tr m := hTBm ν hν0 hνν₁ tr htr
  obtain ⟨H, hH, hH0, hHS⟩ := hHeat ν (ν ^ (-2 : ℝ)) m hR.one_le_c hm1 hν0 hν1
  have hP : ∀ n : ℕ, Nonempty (ActualTrainFluxPathOn (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr
      (Nat.cast_nonneg n)) := fun n => hFP ν _ m hm1 tr hR hBnd n (Nat.cast_nonneg n)
  let Pn : ∀ n : ℕ, ActualTrainFluxPathOn (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr
      (Nat.cast_nonneg n) := fun n => Classical.choice (hP n)
  have hStrip : ∀ n : ℕ, StripWeakLpOn hm1 tr (Pn n) H := fun n =>
    stripWeakAssemblyOnFromParts hBS hFI hMI hSC ν _ m hm1 tr n (Nat.cast_nonneg n) (Pn n) H hR hH
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ → ActualVorticity (c := ν ^ (-2 : ℝ)) (m := m) hm1 →L[ℝ]
      ActualVorticity (c := ν ^ (-2 : ℝ)) (m := m) hm1, E = horizonEvolution hm1 Pn H :=
    ⟨_, rfl⟩
  -- the real Volterra evolution
  have hEeq : ∀ (n : ℕ) (s τ : ℝ), 0 ≤ s → s ≤ τ → τ ≤ n →
      E τ s = (horizonData hm1 (Pn n) H).evolution τ s := by
    intro n s τ hs hsτ hτn
    rw [hE]
    exact horizonEvolution_eq hm1 hLoc Pn H hs hsτ hτn
  have hcoc : ∀ s r τ : ℝ, 0 ≤ s → s ≤ r → r ≤ τ → ∀ w, E τ r (E r s w) = E τ s w := by
    intro s r τ hs hsr hrτ w
    rw [hE]
    exact horizonEvolution_comp hm1 hLoc Pn H hs hsr hrτ w
  have hstripE : ∀ a : ℝ, 0 ≤ a → ∀ w, IsLinFlowOn ν (ν ^ (-2 : ℝ)) m tr a (a + 1)
      (cplx (vortFn hm1 w)) (fun r => cplx (vortFn hm1 (E r a w)))
      (fun r => stripVel hm1 (E r a w)) := by
    intro a ha w
    have hn : a + 1 ≤ ((⌈a + 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    refine hCongr ν _ m tr a (a + 1) _ _ _ _ _ _ (by linarith) (hStrip ⌈a + 1⌉₊ a ha hn w)
      Filter.EventuallyEq.rfl (fun s hs => Filter.EventuallyEq.of_eq ?_)
      (fun s hs => Filter.EventuallyEq.of_eq ?_)
    · beta_reduce
      rw [hEeq ⌈a + 1⌉₊ a s ha hs.1 (hs.2.trans hn)]
    · beta_reduce
      rw [hEeq ⌈a + 1⌉₊ a s ha hs.1 (hs.2.trans hn)]
  have hpar : ∀ τ s : ℝ, s ≤ τ → ∀ w, E τ s (reflV hm1 w) = reflV hm1 (E τ s w) := by
    intro τ s hsτ w
    rw [hE]
    exact hRefl _ _ (horizonData hm1 (Pn ⌈τ⌉₊) H) (horizonData_compatible hm1 (Pn ⌈τ⌉₊) H)
      (reflV hm1) reflF (reflV_reflV hm1) hH0 hHS
      (fun t x => hB ν _ m hm1 tr _ _ (Pn ⌈τ⌉₊) t x) s τ hsτ w
  have hJE : ∀ w, ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 w)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} := by
    intro w p hp
    have hpn : p.1 < ((⌈p.1⌉₊ + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil p.1
      push_cast
      linarith
    have hD := hJC _ _ (horizonData hm1 (Pn (⌈p.1⌉₊ + 1)) H)
      (horizonData_compatible hm1 (Pn (⌈p.1⌉₊ + 1)) H) H.S₀_zero w
    have hcont : ContinuousWithinAt
        (fun q : ℝ × ℝ => (horizonData hm1 (Pn (⌈p.1⌉₊ + 1)) H).evolution q.1 q.2 w)
        {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1} p :=
      (hD p hp.2).mono (fun q hq => hq.2)
    refine hcont.congr_of_eventuallyEq ?_ ?_
    · have hopen : {q : ℝ × ℝ | q.1 < ((⌈p.1⌉₊ + 1 : ℕ) : ℝ)} ∈ 𝓝 p :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hpn
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hopen] with q hq1 hq2
      exact congrArg (fun L => L w) (hEeq _ q.2 q.1 hq1.1 hq1.2 (le_of_lt hq2))
    · exact congrArg (fun L => L w) (hEeq _ p.2 p.1 hp.1 hp.2 hpn.le)
  have hBdE : ∀ T : ℝ, ∃ C : ℝ, ∀ s t : ℝ, 0 ≤ t → t ≤ s → s ≤ T → ‖E s t‖ ≤ C := by
    intro T
    refine ⟨(horizonData hm1 (Pn ⌈T⌉₊) H).evolutionBound *
      Real.exp (Real.log (horizonData hm1 (Pn ⌈T⌉₊) H).evolutionBound * |T|),
      fun s t ht hts hsT => ?_⟩
    rw [hEeq ⌈T⌉₊ t s ht hts (hsT.trans (Nat.le_ceil T))]
    refine ((horizonData hm1 (Pn ⌈T⌉₊) H).norm_evolution_le hts).trans ?_
    have hM := (horizonData hm1 (Pn ⌈T⌉₊) H).one_le_evolutionBound
    have hlog : 0 ≤ Real.log (horizonData hm1 (Pn ⌈T⌉₊) H).evolutionBound := Real.log_nonneg hM
    have hst : s - t ≤ |T| := by
      have := le_abs_self T
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hst hlog))
      (by linarith)
  -- the complexified operator family
  classical
  let U : ℝ → ℝ → Xmc (ν ^ (-2 : ℝ)) m →L[ℂ] Xmc (ν ^ (-2 : ℝ)) m := fun s t =>
    if h : 0 ≤ t ∧ t ≤ s then cx (E s t) (hpar s t h.2) else ContinuousLinearMap.id ℂ _
  have hU : ∀ s t (h : 0 ≤ t ∧ t ≤ s), U s t = cx (E s t) (hpar s t h.2) :=
    fun s t h => dif_pos h
  have hU' : ∀ s t, ¬(0 ≤ t ∧ t ≤ s) → U s t = ContinuousLinearMap.id ℂ _ :=
    fun s t h => dif_neg h
  refine ⟨{
    U := U
    off := hU'
    flow := ?_
    cocycle := ?_
    real := ?_
    locBdd := ?_
    jointCont := ?_ }⟩
  · intro t ht x
    refine ⟨fun s x' j => stripVel hm1 (E s t (reV x)) x' j +
      Complex.I * stripVel hm1 (E s t (imV x)) x' j, ?_⟩
    refine hFlow ν _ m hm1 tr E hcoc hstripE t ht (reV x) (imV x) (xFn x)
      (fun s => xFn (U s t x)) (xFn_eq_reV_imV x) (fun s hts => ?_)
    show xFn (U s t x) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] _
    rw [hU s t ⟨ht, hts⟩]
    exact xFn_cx _ _ x
  · intro s r t ht htr hrs
    rw [hU s r ⟨ht.trans htr, hrs⟩, hU r t ⟨ht, htr⟩, hU s t ⟨ht, htr.trans hrs⟩]
    exact cx_comp_eq _ _ _ _ _ _ (fun w => hcoc t r s ht htr hrs w)
  · intro s t x
    by_cases h : 0 ≤ t ∧ t ≤ s
    · rw [hU s t h]
      exact conjX_cx _ _ x
    · rw [hU' s t h]
      rfl
  · intro T
    obtain ⟨C, hC⟩ := hBdE T
    refine ⟨2 * C, fun s t ht hts hsT => ?_⟩
    rw [hU s t ⟨ht, hts⟩]
    exact (norm_cx_le _ _).trans (by linarith [hC s t ht hts hsT])
  · intro x
    rw [Metric.continuousOn_iff]
    intro p hp ε hε
    obtain ⟨δa, hδa, ha⟩ := Metric.continuousOn_iff.1 (hJE (reV x)) p hp (ε / 2) (by linarith)
    obtain ⟨δb, hδb, hb⟩ := Metric.continuousOn_iff.1 (hJE (imV x)) p hp (ε / 2) (by linarith)
    refine ⟨min δa δb, lt_min hδa hδb, fun q hq hqp => ?_⟩
    have h1 := ha q hq (lt_of_lt_of_le hqp (min_le_left _ _))
    have h2 := hb q hq (lt_of_lt_of_le hqp (min_le_right _ _))
    rw [dist_eq_norm] at h1 h2 ⊢
    show ‖U q.1 q.2 x - U p.1 p.2 x‖ < ε
    rw [hU q.1 q.2 hq, hU p.1 p.2 hp]
    exact (norm_cx_sub_cx_le _ _ _ _ x).trans_lt (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
