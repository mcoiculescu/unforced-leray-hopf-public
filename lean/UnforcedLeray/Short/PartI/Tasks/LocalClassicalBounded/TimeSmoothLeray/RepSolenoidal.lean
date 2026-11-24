import UnforcedLeray.Short.PartI.Sub.T02_1_4

/-!
# Part I, task `PartI:T02/1/4/3`: the spatial representative of the mild solution is solenoidal

Source of record: `the November 2 reference manuscript`, lines 261-288
(the mild solution is divergence free for every positive and zero time).

Target: `repSolenoidal : RepSolenoidal` (leaf 3 of `Sub/T02_1_4.lean`).

Route.
* The mild train satisfies `P₀H³ u s = u s` (second conjunct of `IsMildTrain`), so the value
  `vecH3CellDerivCLM 0 (u s)` lies in `Cyl.divFree c` (`P0H3CLM_value_mem_divFree`).
* `IsSpatialRepOn.represents` at `α = 0` identifies that value a.e. on the cell with the smooth
  field `w s`; hence `∫_cell ⟨w s, ∇φ⟩ = 0` for every cylinder test `φ`.
* Integration by parts on the cell (`Cyl.integral_cell_partialQ_mul`,
  `Cyl.integral_cell_partialEta_mul`) turns this into `∫_cell φ · div (w s) = 0`.
* The fundamental lemma of `Sob.cylinder c` (`ae_zero`) gives `div (w s) = 0` a.e. on the cell.
* `div (w s)` is continuous and `c`-periodic, so the a.e. zero set is everything: it vanishes on
  the open strip, hence on its closure, and every point is a periodic shift of a point of that
  closed strip.
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

/-! ### Elementary facts about components, derivatives and periodicity -/

private theorem rsol_comp_isPeriodic {c : ℝ} {f : Plane → Vec} (h : Cyl.IsPeriodic c f)
    (i : Fin 2) : Cyl.IsPeriodic c (fun z => f z i) :=
  fun z => congrArg (fun v : Vec => v i) (h z)

private theorem rsol_continuous_partialQ {w : Plane → Vec} (hsm : ContDiff ℝ ∞ w) (i : Fin 2) :
    Continuous (Cyl.partialQ fun z => w z i) := by
  have h1 : ContDiff ℝ 1 w := hsm.of_le (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z => w z i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp h1
  exact (Cyl.contDiff_partialQ (n := 0) (h := fun z => w z i) (by simpa using h2)).continuous

private theorem rsol_continuous_partialEta {w : Plane → Vec} (hsm : ContDiff ℝ ∞ w)
    (i : Fin 2) : Continuous (Cyl.partialEta fun z => w z i) := by
  have h1 : ContDiff ℝ 1 w := hsm.of_le (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z => w z i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp h1
  exact (Cyl.contDiff_partialEta (n := 0) (h := fun z => w z i) (by simpa using h2)).continuous

private theorem rsol_partialQ_isPeriodic {c : ℝ} {f : Plane → ℝ} (hf : Cyl.IsPeriodic c f) :
    Cyl.IsPeriodic c (Cyl.partialQ f) := by
  intro z
  have hfun : (fun q : ℝ => f (q + c, z.2)) = fun q : ℝ => f (q, z.2) :=
    funext fun q => hf (q, z.2)
  have key := deriv_comp_add_const (f := fun q : ℝ => f (q, z.2)) (a := c) (x := z.1)
  rw [hfun] at key
  exact key.symm

private theorem rsol_partialEta_isPeriodic {c : ℝ} {f : Plane → ℝ} (hf : Cyl.IsPeriodic c f) :
    Cyl.IsPeriodic c (Cyl.partialEta f) := by
  intro z
  have hfun : (fun η : ℝ => f (z.1 + c, η)) = fun η : ℝ => f (z.1, η) :=
    funext fun η => hf (z.1, η)
  show deriv (fun η : ℝ => f (z.1 + c, η)) z.2 = deriv (fun η : ℝ => f (z.1, η)) z.2
  rw [hfun]

private theorem rsol_divergence_isPeriodic {c : ℝ} {u : Plane → Vec}
    (hu : Cyl.IsPeriodic c u) : Cyl.IsPeriodic c (Cyl.divergence u) := by
  intro z
  have h0 := rsol_partialQ_isPeriodic (rsol_comp_isPeriodic hu 0) z
  have h1 := rsol_partialEta_isPeriodic (rsol_comp_isPeriodic hu 1) z
  show Cyl.partialQ (fun y => u y 0) (z.1 + c, z.2) + Cyl.partialEta (fun y => u y 1) (z.1 + c, z.2)
    = Cyl.partialQ (fun y => u y 0) z + Cyl.partialEta (fun y => u y 1) z
  rw [h0, h1]

private theorem rsol_continuous_divergence {w : Plane → Vec} (hsm : ContDiff ℝ ∞ w) :
    Continuous (Cyl.divergence w) :=
  (rsol_continuous_partialQ hsm 0).add (rsol_continuous_partialEta hsm 1)

/-! ### Integration by parts against cylinder tests -/

/-- The `L²(cell)` pairing of a cylinder-test gradient with an `L²` field equals the cell integral
of the pointwise pairing, once the field is a.e. equal to a function `w`. -/
private theorem rsol_inner_L2_gradT_eq {c : ℝ} {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ)
    {v : Cyl.L2v c} {w : Plane → Vec} (hvw : (v : Plane → Vec) =ᵐ[Cyl.cellμ c] w) :
    ⟪v, Cyl.gradL hφ⟫_ℝ = ∫ z in Cyl.cell c, ⟪w z, Cyl.gradT φ z⟫_ℝ := by
  rw [Cyl.gradL, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (Cyl.memLp_gradT hφ), hvw] with z h1 h2
  rw [h1, h2]

/-- If a smooth periodic field pairs to zero with the gradient of every cylinder test, then its
divergence integrates to zero against every cylinder test. -/
private theorem rsol_integral_test_divergence {c : ℝ} (hc : 0 < c) {w : Plane → Vec}
    (hsm : ContDiff ℝ ∞ w) (hper : Cyl.IsPeriodic c w)
    {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ)
    (hint : ∫ z in Cyl.cell c, ⟪w z, Cyl.gradT φ z⟫_ℝ = 0) :
    ∫ z in Cyl.cell c, φ z * Cyl.divergence w z = 0 := by
  have hd : Differentiable ℝ w := hsm.differentiable (by simp)
  have hd0 : Differentiable ℝ (fun z => w z 0) := Cyl.differentiable_component hd 0
  have hd1 : Differentiable ℝ (fun z => w z 1) := Cyl.differentiable_component hd 1
  have hp0 : Cyl.IsPeriodic c (fun z => w z 0) := rsol_comp_isPeriodic hper 0
  have hp1 : Cyl.IsPeriodic c (fun z => w z 1) := rsol_comp_isPeriodic hper 1
  have hc0 : Continuous (fun z => w z 0) := hd0.continuous
  have hc1 : Continuous (fun z => w z 1) := hd1.continuous
  have hq0 : Continuous (Cyl.partialQ fun z => w z 0) := rsol_continuous_partialQ hsm 0
  have he1 : Continuous (Cyl.partialEta fun z => w z 1) := rsol_continuous_partialEta hsm 1
  have i1 : IntegrableOn (fun z => Cyl.partialQ φ z * w z 0) (Cyl.cell c) :=
    (Cyl.isCylTest_partialQ hφ).integrableOn_mul hc0
  have i2 : IntegrableOn (fun z => φ z * Cyl.partialQ (fun y => w y 0) z) (Cyl.cell c) :=
    hφ.integrableOn_mul hq0
  have i3 : IntegrableOn (fun z => Cyl.partialEta φ z * w z 1) (Cyl.cell c) :=
    (Cyl.isCylTest_partialEta hφ).integrableOn_mul hc1
  have i4 : IntegrableOn (fun z => φ z * Cyl.partialEta (fun y => w y 1) z) (Cyl.cell c) :=
    hφ.integrableOn_mul he1
  have i0e : IntegrableOn (fun z => φ z * w z 1) (Cyl.cell c) := hφ.integrableOn_mul hc1
  have hqp := Cyl.integral_cell_partialQ_mul hc hφ.differentiable hd0 hφ.isPeriodic hp0 i1 i2
  have hep := Cyl.integral_cell_partialEta_mul hφ.differentiable hd1 i0e i3 i4
  have hsum : (∫ z in Cyl.cell c, Cyl.partialQ φ z * w z 0) +
      ∫ z in Cyl.cell c, Cyl.partialEta φ z * w z 1 = 0 := by
    have hpt : (fun z => ⟪w z, Cyl.gradT φ z⟫_ℝ) =
        fun z => Cyl.partialQ φ z * w z 0 + Cyl.partialEta φ z * w z 1 := by
      funext z
      rw [Cyl.gradT, Cyl.inner_vec]
      ring
    have h := hint
    rw [hpt, integral_add i1 i3] at h
    exact h
  have hsplit : (fun z => φ z * Cyl.divergence w z) =
      fun z => φ z * Cyl.partialQ (fun y => w y 0) z
        + φ z * Cyl.partialEta (fun y => w y 1) z := by
    funext z
    simp only [Cyl.divergence, mul_add]
  rw [hsplit, integral_add i2 i4]
  linarith

/-! ### The fundamental lemma on the cell, upgraded by continuity and periodicity -/

/-- A continuous `c`-periodic function vanishing a.e. on the cylinder cell vanishes everywhere. -/
private theorem rsol_eq_zero_of_ae_cell {c : ℝ} (hc : 0 < c) {g : Plane → ℝ} (hg : Continuous g)
    (hper : Cyl.IsPeriodic c g) (hae : g =ᵐ[(Sob.cylinder c).μ] 0) : ∀ z, g z = 0 := by
  have hae' : ∀ᵐ z ∂(volume.restrict (Sob.cylCell c)), g z = 0 := hae
  have hUsub : Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) ⊆ Sob.cylCell c := fun z hz =>
    ⟨Ioo_subset_Ico_self hz.1, mem_univ _⟩
  have hU0 : ∀ z ∈ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ), g z = 0 := by
    intro z0 hz0
    by_contra hne
    have hopen : IsOpen {z : Plane | g z ≠ 0} := isOpen_ne_fun hg continuous_const
    have hUopen : IsOpen (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) :=
      isOpen_Ioo.prod isOpen_univ
    obtain ⟨r, hr, hball⟩ :=
      Metric.isOpen_iff.mp (hopen.inter hUopen) z0 ⟨hne, hz0⟩
    have hsub : Metric.ball z0 r ⊆ Sob.cylCell c := fun z hz => hUsub (hball hz).2
    have hbad := ae_iff.mp hae'
    have hmono : volume.restrict (Sob.cylCell c) (Metric.ball z0 r) ≤
        volume.restrict (Sob.cylCell c) {z : Plane | ¬ g z = 0} :=
      measure_mono fun z hz => (hball hz).1
    rw [Measure.restrict_eq_self _ hsub, hbad] at hmono
    have hpos : 0 < volume (Metric.ball z0 r) := Metric.measure_ball_pos volume z0 hr
    exact lt_irrefl _ (lt_of_lt_of_le hpos hmono)
  intro z
  have hclosed : IsClosed {z : Plane | g z = 0} := isClosed_eq hg continuous_const
  have hcl : closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) ⊆ {z : Plane | g z = 0} :=
    closure_minimal (fun z hz => hU0 z hz) hclosed
  have hclos : closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) =
      Icc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_Ioo (ne_of_lt (by linarith)), closure_univ]
  have hperF : Function.Periodic (fun q : ℝ => g (q, z.2)) c := fun q => hper (q, z.2)
  obtain ⟨y, hy, hgy⟩ := hperF.exists_mem_Ico hc z.1 (-(c / 2))
  have hyc : y ∈ Icc (-(c / 2)) (c / 2) := ⟨hy.1, by linarith [hy.2]⟩
  have hmem : (y, z.2) ∈ closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := by
    rw [hclos]
    exact ⟨hyc, mem_univ _⟩
  have h0 : g (y, z.2) = 0 := hcl hmem
  have hgz : g z = g (y, z.2) := hgy
  rw [hgz]
  exact h0

/-! ### The theorem -/

/-- **Leaf 3** (solenoidality), `repSolenoidal`: the spatial representative of the mild solution
is divergence free at every time `s ∈ [0,T]`. -/
theorem repSolenoidal : RepSolenoidal := by
  intro ν c T hν hc hc1 hT u hu w hw s hs z
  have hfix : P0H3CLM hc (u ⟨s, hs⟩) = u ⟨s, hs⟩ := hu.2.1 ⟨s, hs⟩
  have hmem : vecH3CellDerivCLM (c := c) Sob.Idx.zero (u ⟨s, hs⟩) ∈ Cyl.divFree c := by
    have h := P0H3CLM_value_mem_divFree hc (u ⟨s, hs⟩)
    rwa [hfix] at h
  have hrep := hw.represents ⟨s, hs⟩ Sob.Idx.zero
  simp only [Sob.TestDomain.word_zero, Sob.iterD_nil] at hrep
  have hsm : ContDiff ℝ ∞ (w s) := hw.smooth s hs
  have hper : Cyl.IsPeriodic c (w s) := hw.periodic s hs
  have hweak : ∀ φ : Plane → ℝ, Sob.IsCylTest c φ →
      ∫ y in Cyl.cell c, φ y * Cyl.divergence (w s) y = 0 := by
    intro φ hφ
    apply rsol_integral_test_divergence hc hsm hper hφ
    have h0 := Cyl.mem_divFree.mp hmem φ hφ
    rw [real_inner_comm, rsol_inner_L2_gradT_eq hφ hrep] at h0
    exact h0
  have hae : Cyl.divergence (w s) =ᵐ[(Sob.cylinder c).μ] 0 := by
    refine (Sob.cylinder c).ae_zero (Cyl.divergence (w s)) ?_ ?_
    · show LocallyIntegrable (Cyl.divergence (w s)) (volume.restrict (Sob.cylCell c))
      exact (rsol_continuous_divergence hsm).locallyIntegrable
    · intro φ hφ
      have h := hweak φ hφ
      rw [Sob.cyl_cell_eq c] at h
      exact h
  exact rsol_eq_zero_of_ae_cell hc (rsol_continuous_divergence hsm)
    (rsol_divergence_isPeriodic hper) hae z

end UnforcedLeray.Short.PartI
