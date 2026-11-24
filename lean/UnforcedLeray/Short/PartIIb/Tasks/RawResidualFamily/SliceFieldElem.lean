import UnforcedLeray.Short.PartIIb.Sub.R1

/-!


Proves `UnforcedLeray.Short.IIb.SliceFieldElem` (`Sub/R1.lean`), the statement that a
`P`-periodic, `L^{q₀}`-continuous field `F` with axisymmetric slices defines an element `f` of
`Y_{q₀}` with the phase pairings `⟪Φ, f⟫ = P⁻¹∫₀ᴾ∫ Φ·F`, the bound `‖f‖ ≤ sup_τ ‖F(τ)‖`,
realness and `𝒪`-invariance.

Source of record: `the November 2 reference manuscript`, lines 2042-2046, and
`paper/main.tex` line 5200. The witness is `f := testElem P q₀ (realC ∘ F)`.
Nothing here changes the target statement or adds hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## Real fields seen in `ℂ³` -/

theorem sfContDiff_realC : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : Space => (realC x).ofLp i) =
      fun x : Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply (p := 2) (i := i))

theorem sfRealC_zero : realC (0 : Space) = 0 := by
  ext i
  simp [realC_apply]

theorem sfRealC_sub (a b : Space) : realC (a - b) = realC a - realC b := by
  ext i
  simp [realC_apply]

theorem sfNorm_realC (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realC_apply, Complex.norm_real]

/-- A real-valued phase test, complexified, is a phase test. -/
theorem sfIsPhaseTest_realC {P : ℝ} {φ : ℝ × Space → Space} (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (fun x => realC (φ x)) := by
  obtain ⟨R, hR⟩ := hφ.bounded_support
  exact
    { smooth := sfContDiff_realC.comp hφ.smooth
      periodic := fun τ y => congrArg realC (hφ.periodic τ y)
      bounded_support := ⟨R, fun τ y hy => by
        show realC (φ (τ, y)) = 0
        rw [hR τ y hy, sfRealC_zero]⟩ }

/-! ## The slice field `(τ, y) ↦ realC (F τ y)` -/

theorem sfIsSliceTest {P : ℝ} {F : ℝ → SpatialField}
    (hper : ∀ τ, F (τ + P) = F τ)
    (hmem : ∀ τ, MemLp (F τ) q0E volume)
    (hcont : ∀ τ₀, Tendsto (fun τ => (eLpNorm (F τ - F τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) :
    IsSliceTest P q0E (fun x => realC (F x.1 x.2)) := by
  have hmR : ∀ τ, MemLp (fun y => realC (F τ y)) q0E volume := fun τ =>
    MemLp.of_le (hmem τ)
      (sfContDiff_realC.continuous.comp_aestronglyMeasurable (hmem τ).aestronglyMeasurable)
      (Eventually.of_forall fun y => (sfNorm_realC (F τ y)).le)
  have hnorm : ∀ τ τ₀, eLpNorm ((fun y => realC (F τ y)) - fun y => realC (F τ₀ y)) q0E volume =
      eLpNorm (F τ - F τ₀) q0E volume := fun τ τ₀ =>
    eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
      simp only [Pi.sub_apply]
      rw [← sfRealC_sub, sfNorm_realC])
  have hcontR : Continuous fun τ => MemLp.toLp (fun y => realC (F τ y)) (hmR τ) := by
    refine continuous_iff_continuousAt.2 fun τ₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine (hcont τ₀).congr fun τ => ?_
    show (eLpNorm (F τ - F τ₀) q0E volume).toReal =
      ‖MemLp.toLp (fun y => realC (F τ y)) (hmR τ) -
        MemLp.toLp (fun y => realC (F τ₀ y)) (hmR τ₀)‖
    rw [← MemLp.toLp_sub, Lp.norm_toLp, hnorm]
  refine ⟨fun τ y => ?_, hmR, hcontR⟩
  show realC (F (τ + P) y) = realC (F τ y)
  rw [hper τ]

/-- The `L^{q₀}` norm of a slice of the complexified field is the norm of the slice. -/
theorem sfNorm_sliceMap {P : ℝ} {F : ℝ → SpatialField}
    (hS : IsSliceTest P q0E (fun x => realC (F x.1 x.2))) (t : ℝ) :
    ‖sliceMap hS.2 t‖ = (eLpNorm (F t) q0E volume).toReal := by
  unfold sliceMap
  rw [Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun y => sfNorm_realC (F t y))

/-- For a slice-test element, `testElem` agrees a.e. on the circle with the slice map. -/
theorem sfTestElem_ae {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) :
    ⇑(testElem P r Φ) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑(circleSlice hΦ) := by
  rw [testElem_of hΦ]
  exact ContinuousMap.coeFn_toLp _ _

/-! ## The pairing with the slice element -/

/-- **Pairing identity.** For a phase test `Φ`, the pairing of `Φ` with the slice element of
`realC ∘ F` is the period integral `P⁻¹∫₀ᴾ∫ Φ·F`. -/
theorem sfPhasePair_eq {P : ℝ} [Fact (0 < P)] {F : ℝ → SpatialField}
    (hper : ∀ τ, F (τ + P) = F τ)
    (hmem : ∀ τ, MemLp (F τ) q0E volume)
    (hcont : ∀ τ₀, Tendsto (fun τ => (eLpNorm (F τ - F τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0))
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q0E Φ (testElem P q0E (fun x => realC (F x.1 x.2))) =
      pairF P Φ (fun x => realC (F x.1 x.2)) := by
  have hS : IsSliceTest P q0E (fun x => realC (F x.1 x.2)) := sfIsSliceTest hper hmem hcont
  have hT : IsSliceTest P (conjExp q0E) Φ := hΦ.isSliceTest (conjExp q0E)
  have hkey : (fun x : AddCircle P => innerPair q0E (testElem P (conjExp q0E) Φ x)
      (testElem P q0E (fun x => realC (F x.1 x.2)) x)) =ᵐ[AddCircle.haarAddCircle (T := P)]
      (fun x => innerPair q0E (circleSlice hT x) (circleSlice hS x)) := by
    filter_upwards [sfTestElem_ae hT, sfTestElem_ae hS] with x h1 h2
    simp only [h1, h2]
  unfold phasePair
  rw [phasePairing_apply, integral_congr_ae hkey, AddCircle.integral_haarAddCircle]
  have hI := AddCircle.integral_preimage P 0
    (fun x : AddCircle P => innerPair q0E (circleSlice hT x) (circleSlice hS x))
  rw [zero_add] at hI
  rw [← hI]
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  dsimp only
  rw [circleSlice_coe, circleSlice_coe, innerPair_apply]
  refine integral_congr_ae ?_
  have e1 : ⇑(sliceMap hT.2 a) =ᵐ[volume] fun y => Φ (a, y) :=
    MemLp.coeFn_toLp (hT.2.memLp a)
  have e2 : ⇑(sliceMap hS.2 a) =ᵐ[volume] fun y => realC (F a y) :=
    MemLp.coeFn_toLp (hS.2.memLp a)
  filter_upwards [e1, e2] with y h1 h2
  rw [h1, h2]

/-- The pairing of a real phase test with a real field is real. -/
theorem sfPairF_realC_im (P : ℝ) (φ g : ℝ × Space → Space) :
    (pairF P (fun x => realC (φ x)) (fun x => realC (g x))).im = 0 := by
  have hre : ∀ x : ℝ × Space, dotL (realC (φ x)) (realC (g x)) =
      ((∑ i : Fin 3, φ x i * g x i : ℝ) : ℂ) := by
    intro x
    simp [dotL_apply, realC_apply]
  have hval : pairF P (fun x => realC (φ x)) (fun x => realC (g x)) =
      P⁻¹ • (((∫ t in Ioc (0 : ℝ) P, ∫ y, ∑ i : Fin 3, φ (t, y) i * g (t, y) i : ℝ)) : ℂ) := by
    unfold pairF phaseInt
    simp only [hre, integral_complex_ofReal]
  rw [hval]
  simp

/-! ## The statement -/

theorem sliceFieldElem_proof : UnforcedLeray.Short.IIb.SliceFieldElem := by
  unfold SliceFieldElem
  intro p F hper hmem hcont
  have hS : IsSliceTest p.period q0E (fun x => realC (F x.1 x.2)) :=
    sfIsSliceTest hper hmem hcont
  refine ⟨testElem p.period q0E (fun x => realC (F x.1 x.2)),
    fun Φ hΦ => sfPhasePair_eq hper hmem hcont hΦ, ?_, ?_, ?_⟩
  · -- the norm bound
    intro B hB
    have hC : 0 ≤ B := le_trans ENNReal.toReal_nonneg (hB 0)
    have hbd : ∀ x : AddCircle p.period, ‖circleSlice hS x‖ ≤ B := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H t =>
        rw [circleSlice_coe, sfNorm_sliceMap hS t]
        exact hB t
    have hae : ∀ᵐ x ∂(AddCircle.haarAddCircle (T := p.period)),
        ‖testElem p.period q0E (fun x => realC (F x.1 x.2)) x‖ ≤ B := by
      filter_upwards [sfTestElem_ae hS] with x hx
      rw [hx]
      exact hbd x
    have h := Lp.norm_le_of_ae_bound hC hae
    simpa [measureUnivNNReal] using h
  · -- realness
    refine (mem_realSub _ _).2 fun φ hφ => ?_
    rw [sfPhasePair_eq hper hmem hcont (sfIsPhaseTest_realC hφ)]
    exact sfPairF_realC_im _ φ (fun x => F x.1 x.2)
  · -- 𝒪-invariance
    intro hax
    refine mem_Osym.2 ((isOInvariant_iff _).2 fun g hg => ?_)
    have hall : ∀ x : AddCircle p.period, ∀ᵐ y ∂(volume : Measure Space),
        gC g (circleSlice hS x (g.symm y)) = circleSlice hS x y := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H t =>
        rw [circleSlice_coe]
        have hm : ∀ᵐ z ∂(volume : Measure Space), sliceMap hS.2 t z = realC (F t z) :=
          MemLp.coeFn_toLp (hS.2.memLp t)
        have hm' : ∀ᵐ y ∂(volume : Measure Space),
            sliceMap hS.2 t (g.symm y) = realC (F t (g.symm y)) :=
          g.symm.measurePreserving.quasiMeasurePreserving.ae hm
        filter_upwards [hm', hm, hax t g hg] with y h1 h2 h3
        have h3' : g (F t (g.symm y)) = F t y := h3
        rw [h1, h2, gC_realC, h3']
    filter_upwards [sfTestElem_ae hS] with x hx
    rw [hx]
    exact hall x
