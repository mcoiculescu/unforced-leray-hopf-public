import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F7
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.LinearBodySource
import UnforcedLeray.Units.B0278

/-!
# Linear gluing and `F`-free PDE leaf interfaces for `PartII-b:F7/2` (`SP 2289–2295`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2054–2057 (`short-bg:train-late`), lines 2213–2217 (`short-bg:body-eq`), and lines
2289–2295 (`short-bg:global-energy`).

This file:
1. Defines the single-profile (`F`-free) cylinder `H¹_σ(C_c)` slice and tail meridional PDE
   predicates (`cylSliceL2`, `cylSliceH1`, `IsCylSolenoidalSlice`, `IsCylH1Slice`,
   `IsCylSourceH1`, `IsTailMeridionalSolution`, `glueAtHorizon`) and the three `F`-free PDE leaves:
   - `(a)` `MeridionalTailExistence`: existence of a `C([T, ∞); H¹_σ(C_c))` tail solution on
     `(T, ∞)` from an `H¹_σ(C_c)` slice datum at `T` and an `L¹((T, ∞); H¹_σ(C_c))` source `g`;
   - `(b)` `MeridionalHorizonGluing`: extraction of a `C((0, T]; H¹_σ(C_c))` representative on
     `(0, T]` with a genuine `H¹_σ(C_c)` horizon trace at `s = T`, and weak PDE gluing across
     `s = T` with any matching `C([T, ∞); H¹(C_c))` tail solution;
   - `(c)` `MeridionalTailH1Gronwall`: differentiated `H¹(C_c)` velocity energy Gronwall bound on
     `(T, ∞)` controlled by `∫_T^∞ (‖Dv(s)‖_∞ + ‖D²v(s)‖_∞) ds` and `∫_T^∞ ‖g(t)‖_{H¹} dt`.
2. Proves unconditionally (`ContLinearGlueAux.linear_meridional_continuation`, zero `sorry`) via
   Hamel-basis `ℝ`-linear extension, `cylSliceH1` left-continuity transfer up to the horizon
   `s = p.H` (avoiding any degenerate single-slice ambiguity on `zOf_eb F`), and `L²(cell)` entrance
   vorticity transfer (`curl_transfer_Ioo`) that `(a) + (b) + (c)` produce `ℝ`-linear maps
   `zOf, zqOf, zηOf : HpR p.c →ₗ[ℝ] CProf` solving `IsGlobalMeridionalCorrection` with both early
   and late `H¹(C_c)` slice bounds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Cylinder `H¹_σ(C_c)` slice and tail meridional PDE predicates -/

/-- `L²` norm on the fundamental cylinder cell `B0579.cell c = [-c/2, c/2) × ℝ`. -/
def cylSliceL2 (c : ℝ) (u : B0579.Plane → CMerid) : ℝ≥0∞ :=
  eLpNorm u 2 (volume.restrict (B0579.cell c))

/-- Slice `H¹(C_c)` norm `‖u‖_{L²(cell)} + ‖u_q‖_{L²(cell)} + ‖u_η‖_{L²(cell)}` (`sliceH1Norm` on a
single slice triple `(u, u_q, u_η)`). -/
def cylSliceH1 (c : ℝ) (u uq uη : B0579.Plane → CMerid) : ℝ≥0∞ :=
  cylSliceL2 c u + cylSliceL2 c uq + cylSliceL2 c uη

/-- Weak divergence-free condition on `C_c = (ℝ/cℤ) × ℝ` against `c`-periodic cylinder test
functions (`B0579.IsCylTest c ψ`). -/
def IsCylSolenoidalSlice (c : ℝ) (u : B0579.Plane → CMerid) : Prop :=
  ∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun y => u y 0 * (B0579.pd 0 ψ y : ℂ) + u y 1 * (B0579.pd 1 ψ y : ℂ))
        (B0579.cell c) ∧
      ∫ y in B0579.cell c,
        (u y 0 * (B0579.pd 0 ψ y : ℂ) + u y 1 * (B0579.pd 1 ψ y : ℂ)) = 0

/-- An `H¹_σ(C_c)` slice datum `(u, u_q, u_η)`: strongly measurable fields in `L²(cell)` such that
`u_q, u_η` are the weak cylinder spatial derivatives of `u` and `u` is weakly divergence-free on
`C_c` (SP 2213–2217, 2289–2295). -/
structure IsCylH1Slice (c : ℝ) (u uq uη : B0579.Plane → CMerid) : Prop where
  sm_u : StronglyMeasurable u
  sm_uq : StronglyMeasurable uq
  sm_uη : StronglyMeasurable uη
  weak_q : ∀ k : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun y => u y k) (fun y => uq y k)
  weak_eta : ∀ k : Fin 2, IIIa.HasWeakCellDerivC c 1 (fun y => u y k) (fun y => uη y k)
  solenoidal : IsCylSolenoidalSlice c u
  memL2_u : MemLp u 2 (volume.restrict (B0579.cell c))
  memL2_uq : MemLp uq 2 (volume.restrict (B0579.cell c))
  memL2_uη : MemLp uη 2 (volume.restrict (B0579.cell c))

/-- Strongly measurable, `c`-periodic, weakly solenoidal `H¹` body-source triple `(g, g_q, g_η)` on
`(0, ∞) × ℝ²` (SP 2216). -/
structure IsCylSourceH1 (c : ℝ) (g gq gη : CProf) : Prop where
  sm_g : StronglyMeasurable g
  sm_gq : StronglyMeasurable gq
  sm_gη : StronglyMeasurable gη
  periodic_g : QPeriodic c g
  periodic_gq : QPeriodic c gq
  periodic_gη : QPeriodic c gη
  weak_q : HasWeakVec vQ0 dZero g gq
  weak_eta : HasWeakVec vEta dZero g gη
  solenoidal : ∀ φ, IsCoordTest φ →
    Integrable (fun x => g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) = 0

/-- Weak solution of the meridional body equation `z_s - ν Δ_{q,η} z + P_0(B_v z) = g`
(`short-bg:body-eq`, SP 2216) on the open tail half-space `(T, ∞) × ℝ²` (`Ioi T ×ˢ univ`). -/
structure IsTailMeridionalSolution (p : Params) (T : ℝ)
    (g z zq zη : CProf) : Prop where
  periodic : ∀ᵐ x : Coord, T < x.1 →
    z (qShift p.c x) = z x ∧ zq (qShift p.c x) = zq x ∧ zη (qShift p.c x) = zη x
  weak_q : ∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioi T ×ˢ univ →
    Integrable (fun x => z x i * (coordTranspose vQ0 dZero φ x : ℂ)) ∧
      Integrable (fun x => zq x i * (φ x : ℂ)) ∧
      ∫ x, zq x i * (φ x : ℂ) = ∫ x, z x i * (coordTranspose vQ0 dZero φ x : ℂ)
  weak_eta : ∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioi T ×ˢ univ →
    Integrable (fun x => z x i * (coordTranspose vEta dZero φ x : ℂ)) ∧
      Integrable (fun x => zη x i * (φ x : ℂ)) ∧
      ∫ x, zη x i * (φ x : ℂ) = ∫ x, z x i * (coordTranspose vEta dZero φ x : ℂ)
  solenoidal : ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioi T ×ˢ univ →
    Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0
  equation : ∀ Ψ, IsPlanarSolTest Ψ →
    (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioi T ×ˢ univ) →
    Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z zq zη) Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z zq zη) Ψ x) =
        ∫ x, cdot g Ψ x

/-- Piecewise horizon gluing at `s = T`: `z₁` on `s ≤ T` and `z₂` on `s > T`. -/
def glueAtHorizon (T : ℝ) (z₁ z₂ : CProf) : CProf :=
  fun x => if x.1 ≤ T then z₁ x else z₂ x

/-! ## 2. The three `F`-free PDE continuation leaves (`(a)`, `(b)`, `(c)`) -/

/-- **Leaf `(a)` (`MeridionalTailExistence`, SP 2213–2217, 2289–2295)**:
for every `BgRegime` parameter point, horizon `T > 0`, initial slice datum
`(u, uq, uη) ∈ H¹_σ(C_c)`, and body source `(g, gq, gη) ∈ L¹((T, ∞); H¹_σ(C_c))`, the linear
2D cylinder Oseen/Stokes equation `z_s - ν Δ z + P_0(B_v z) = g` on `(T, ∞)` admits a strongly
measurable tail solution `(z₂, zq₂, zη₂)` continuous in `H¹(C_c)` on `[T, ∞)` whose slice at `T`
agrees with `(u, uq, uη)` in `H¹(C_c)`. -/
def MeridionalTailExistence : Prop :=
  ∀ {p : Params} {d dm dp T : ℝ},
    BgRegime p d dm dp → 0 < T →
    ∀ {u uq uη : B0579.Plane → CMerid},
      IsCylH1Slice p.c u uq uη →
    ∀ {g gq gη : CProf},
      IsCylSourceH1 p.c g gq gη →
      (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤ →
      ∃ z₂ zq₂ zη₂ : CProf,
        StronglyMeasurable z₂ ∧ StronglyMeasurable zq₂ ∧ StronglyMeasurable zη₂ ∧
        cylSliceH1 p.c (fun y => z₂ (T, y) - u y)
          (fun y => zq₂ (T, y) - uq y) (fun y => zη₂ (T, y) - uη y) = 0 ∧
        IsTailMeridionalSolution p T g z₂ zq₂ zη₂ ∧
        ∀ s : ℝ, T ≤ s →
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => z₂ (s', y) - z₂ (s, y))
            (fun y => zq₂ (s', y) - zq₂ (s, y))
            (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)

/-- **Leaf `(b)` (`MeridionalHorizonGluing`, SP 2213–2217, 2289–2295)**:
any solution `(z_eb, zq_eb, zη_eb)` of `IsMeridionalCorrectionOn p T g` on `(0, T)` with a.e.
bounded `H¹(C_c)` norm on `(0, T]` and `g ∈ L¹((0, T]; H¹_σ(C_c))` admits a strongly measurable,
`c`-periodic `C((0, T]; H¹_σ(C_c))` representative `(z₁, zq₁, zη₁)` agreeing `volume`-a.e. on
`(0, T) × ℝ²` with `(z_eb, zq_eb, zη_eb)` whose horizon slice at `s = T` belongs to `H¹_σ(C_c)`;
moreover, gluing `(z₁, zq₁, zη₁)` across `s = T` with any `C([T, ∞); H¹(C_c))` tail solution
`(z₂, zq₂, zη₂)` matching `(z₁(T), zq₁(T), zη₁(T))` in `H¹(C_c)` (with `g ∈ L¹((T, ∞); H¹)`)
yields a global weak solution `IsGlobalMeridionalCorrection p g` on `(0, ∞)` (partition of unity
in `s` around `s = T` cancels the jump-free one-sided `L²` traces). -/
def MeridionalHorizonGluing : Prop :=
  ∀ {p : Params} {d dm dp T M : ℝ} {α : E2},
    BgRegime p d dm dp → 0 < T → 0 ≤ M →
    ∀ {g gq gη z_eb zq_eb zη_eb : CProf},
      IsCylSourceH1 p.c g gq gη →
      (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤ →
      IsMeridionalCorrectionOn p T g z_eb zq_eb zη_eb α →
      (∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z_eb zq_eb zη_eb s ≤ ENNReal.ofReal M) →
      ∃ z₁ zq₁ zη₁ : CProf,
        StronglyMeasurable z₁ ∧ StronglyMeasurable zq₁ ∧ StronglyMeasurable zη₁ ∧
        QPeriodic p.c z₁ ∧ QPeriodic p.c zq₁ ∧ QPeriodic p.c zη₁ ∧
        (∀ᵐ x : Coord, x.1 ∈ Ioo 0 T →
          z₁ x = z_eb x ∧ zq₁ x = zq_eb x ∧ zη₁ x = zη_eb x) ∧
        (∀ s ∈ Ioc 0 T,
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => z₁ (s', y) - z₁ (s, y))
            (fun y => zq₁ (s', y) - zq₁ (s, y))
            (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0)) ∧
        IsCylH1Slice p.c (fun y => z₁ (T, y)) (fun y => zq₁ (T, y)) (fun y => zη₁ (T, y)) ∧
        ∀ {z₂ zq₂ zη₂ : CProf},
          StronglyMeasurable z₂ → StronglyMeasurable zq₂ → StronglyMeasurable zη₂ →
          (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤ →
          cylSliceH1 p.c (fun y => z₂ (T, y) - z₁ (T, y))
            (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0 →
          IsTailMeridionalSolution p T g z₂ zq₂ zη₂ →
          (∀ s : ℝ, T ≤ s →
            Tendsto (fun s' => cylSliceH1 p.c
              (fun y => z₂ (s', y) - z₂ (s, y))
              (fun y => zq₂ (s', y) - zq₂ (s, y))
              (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)) →
          IsGlobalMeridionalCorrection p g
            (glueAtHorizon T z₁ z₂) (glueAtHorizon T zq₁ zq₂) (glueAtHorizon T zη₁ zη₂) α

/-- **Leaf `(c)` (`MeridionalTailH1Gronwall`, SP 2054–2057, 2289–2295)**:
differentiated `H¹(C_c)` velocity energy inequality on `(T, ∞)` (`T ≥ 1`): because `div v_c = 0`
and `P_0` is orthogonal on `L²(C_c)` and commutes with `(∂_q, ∂_η)`, the transport terms
`⟨z, v·∇z⟩` and `⟨∂_j z, v·∇(∂_j z)⟩` vanish, so the Hilbertian `H¹` energy growth rate is
bounded solely by `‖Dv(s)‖_∞ + ‖D²v(s)‖_∞`; Gronwall (`A_H1 ≥ 1` accounting for the `ℓ¹`/`ℓ²`
equivalence of `sliceH1Norm`) yields the uniform tail `H¹(C_c)` bound on `(T, ∞)`. -/
def MeridionalTailH1Gronwall : Prop :=
  ∃ A_H1 K_H1 : ℝ, 1 ≤ A_H1 ∧ 0 < K_H1 ∧
    ∀ {p : Params} {d dm dp T B_strain : ℝ},
      BgRegime p d dm dp → p.ν ≤ 1 → 1 ≤ T → 0 ≤ B_strain →
      ∫⁻ s in Ioi T,
          (B0277.supNormD 1 (p.train.v s) + B0277.supNormD 2 (p.train.v s)) ≤
        ENNReal.ofReal B_strain →
      ∀ {g gq gη z₂ zq₂ zη₂ : CProf},
        IsCylSourceH1 p.c g gq gη →
        (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤ →
        StronglyMeasurable z₂ → StronglyMeasurable zq₂ → StronglyMeasurable zη₂ →
        IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)) →
        IsTailMeridionalSolution p T g z₂ zq₂ zη₂ →
        (∀ s : ℝ, T ≤ s →
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => z₂ (s', y) - z₂ (s, y))
            (fun y => zq₂ (s', y) - zq₂ (s, y))
            (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)) →
        ∀ s : ℝ, T < s →
          sliceH1Norm p.c z₂ zq₂ zη₂ s ≤
            ENNReal.ofReal (A_H1 * Real.exp (K_H1 * B_strain)) *
              (sliceH1Norm p.c z₂ zq₂ zη₂ T +
                ENNReal.ofReal K_H1 * ∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t)

/-! ## 3. Hamel-basis `ℝ`-linear assembly of `(zOf, zqOf, zηOf)` from `(a) + (b) + (c)` -/

namespace ContLinearGlueAux

/-- Finite `ℝ`-linear combination of profiles. -/
private def comb {ι : Type*} (a : ι →₀ ℝ) (w : ι → CProf) : CProf :=
  fun x => ∑ i ∈ a.support, a i • w i x

/-- Finite `ℝ`-linear combination of cylinder slices. -/
private def combSlice {ι : Type*} (a : ι →₀ ℝ) (u : ι → B0579.Plane → CMerid) :
    B0579.Plane → CMerid :=
  fun y => ∑ i ∈ a.support, a i • u i y

private lemma constr_eq_comb {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : Module.Basis ι ℝ V) (f : ι → CProf) (F : V) :
    B.constr ℝ f F = comb (B.repr F) f := by
  funext x
  simp [Module.Basis.constr_apply, Finsupp.sum, comb, Finset.sum_apply]

private lemma comb_apply {ι : Type*} (a : ι →₀ ℝ) (w : ι → CProf) (x : Coord) (k : Fin 2) :
    comb a w x k = ∑ i ∈ a.support, a i • w i x k := by
  simp [comb]

private lemma combSlice_apply {ι : Type*} (a : ι →₀ ℝ) (u : ι → B0579.Plane → CMerid)
    (y : B0579.Plane) (k : Fin 2) :
    combSlice a u y k = ∑ i ∈ a.support, a i • u i y k := by
  simp [combSlice]

private lemma comb_slice_eq {ι : Type*} (a : ι →₀ ℝ) (w : ι → CProf) (s : ℝ) :
    (fun y => comb a w (s, y)) = combSlice a (fun i y => w i (s, y)) := by
  rfl

private lemma glueAtHorizon_comb {ι : Type*} (T : ℝ) (a : ι →₀ ℝ) (z₁ z₂ : ι → CProf) :
    comb a (fun i => glueAtHorizon T (z₁ i) (z₂ i)) =
      glueAtHorizon T (comb a z₁) (comb a z₂) := by
  funext x
  by_cases hx : x.1 ≤ T <;> simp [comb, glueAtHorizon, hx]

private lemma stronglyMeasurable_glueAtHorizon (T : ℝ) {z₁ z₂ : CProf}
    (hz₁ : StronglyMeasurable z₁) (hz₂ : StronglyMeasurable z₂) :
    StronglyMeasurable (glueAtHorizon T z₁ z₂) := by
  have heq : glueAtHorizon T z₁ z₂ = Set.piecewise {x : Coord | x.1 ≤ T} z₁ z₂ := by
    funext x; simp [glueAtHorizon, Set.piecewise]
  rw [heq]
  exact StronglyMeasurable.piecewise (measurableSet_le measurable_fst measurable_const) hz₁ hz₂

private lemma comb_meas {ι : Type*} (a : ι →₀ ℝ) {w : ι → CProf}
    (hw : ∀ i, StronglyMeasurable (w i)) :
    StronglyMeasurable (comb a w) := by
  convert Finset.stronglyMeasurable_sum a.support (fun i _ => (hw i).const_smul (a i)) using 1
  funext x; simp [comb, Finset.sum_apply]

private lemma combSlice_meas {ι : Type*} (a : ι →₀ ℝ) {u : ι → B0579.Plane → CMerid}
    (hu : ∀ i, StronglyMeasurable (u i)) :
    StronglyMeasurable (combSlice a u) := by
  convert Finset.stronglyMeasurable_sum a.support (fun i _ => (hu i).const_smul (a i)) using 1
  funext y; simp [combSlice, Finset.sum_apply]

private lemma sliceMeas {w : CProf} (hw : StronglyMeasurable w) (s : ℝ) :
    StronglyMeasurable (fun y : B0579.Plane => w (s, y)) :=
  hw.comp_measurable measurable_prodMk_left

private lemma compMeas {α : Type*} [MeasurableSpace α] {w : α → CMerid}
    (hw : StronglyMeasurable w) (i : Fin 2) :
    StronglyMeasurable (fun x => w x i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hw

private lemma qPeriodic_comb {ι : Type*} (c : ℝ) (a : ι →₀ ℝ) {w : ι → CProf}
    (hw : ∀ i, QPeriodic c (w i)) :
    QPeriodic c (comb a w) := by
  unfold QPeriodic at hw ⊢
  have hall := (Filter.eventually_all_finset a.support).2 (fun i _ => hw i)
  filter_upwards [hall] with x hx
  simp only [comb]
  exact Finset.sum_congr rfl fun i hi => by rw [hx i hi]

/-! ### `L²(cell)` / `cylSliceH1` triangle inequalities and finite combinations -/

private def dd (c : ℝ) (w : CProf) (s s' : ℝ) : ℝ≥0∞ :=
  cylSliceL2 c (fun y => w (s', y) - w (s, y))

private lemma cylSliceL2_le (c : ℝ) {w : CProf} (hw : StronglyMeasurable w) (s s' : ℝ) :
    cylSliceL2 c (fun y => w (s, y)) ≤ cylSliceL2 c (fun y => w (s', y)) + dd c w s s' := by
  have e : (fun y => w (s, y)) = (fun y => w (s', y)) - (fun y => w (s', y) - w (s, y)) := by
    funext y; simp
  unfold cylSliceL2 dd
  rw [e]
  exact eLpNorm_sub_le (sliceMeas hw s').aestronglyMeasurable
    ((sliceMeas hw s').sub (sliceMeas hw s)).aestronglyMeasurable (by norm_num)

private lemma sliceH1Norm_eq_cylSliceH1 (c : ℝ) (z zq zη : CProf) (s : ℝ) :
    sliceH1Norm c z zq zη s =
      cylSliceH1 c (fun y => z (s, y)) (fun y => zq (s, y)) (fun y => zη (s, y)) :=
  rfl

private lemma sliceH1_le_add_dd (c : ℝ) {Z Zq Zη : CProf}
    (hZ : StronglyMeasurable Z) (hZq : StronglyMeasurable Zq) (hZη : StronglyMeasurable Zη)
    (s s' : ℝ) :
    sliceH1Norm c Z Zq Zη s ≤
      sliceH1Norm c Z Zq Zη s' +
        cylSliceH1 c (fun y => Z (s', y) - Z (s, y))
          (fun y => Zq (s', y) - Zq (s, y)) (fun y => Zη (s', y) - Zη (s, y)) := by
  have h1 := cylSliceL2_le c hZ s s'
  have h2 := cylSliceL2_le c hZq s s'
  have h3 := cylSliceL2_le c hZη s s'
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  unfold sliceH1Norm cylSliceH1 cylSliceL2 dd
  ac_rfl

private lemma cylSliceL2_comb_diff_le {ι : Type*} (c : ℝ) (a : ι →₀ ℝ)
    {u v : ι → B0579.Plane → CMerid}
    (hu : ∀ i, StronglyMeasurable (u i)) (hv : ∀ i, StronglyMeasurable (v i)) :
    cylSliceL2 c (fun y => combSlice a u y - combSlice a v y) ≤
      ∑ i ∈ a.support, ENNReal.ofReal |a i| * cylSliceL2 c (fun y => u i y - v i y) := by
  have e : (fun y => combSlice a u y - combSlice a v y) =
      ∑ i ∈ a.support, a i • (fun y => u i y - v i y) := by
    funext y
    simp [combSlice, Finset.sum_sub_distrib, smul_sub, Finset.sum_apply]
  unfold cylSliceL2
  rw [e]
  refine (eLpNorm_sum_le (fun i _ =>
    (((hu i).sub (hv i)).const_smul (a i)).aestronglyMeasurable) (by norm_num)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine eLpNorm_const_smul_le.trans ?_
  rw [Real.enorm_eq_ofReal_abs]
  exact le_rfl

private lemma cylSliceH1_comb_diff_le {ι : Type*} (c : ℝ) (a : ι →₀ ℝ)
    {u uq uη v vq vη : ι → B0579.Plane → CMerid}
    (hu : ∀ i, StronglyMeasurable (u i)) (huq : ∀ i, StronglyMeasurable (uq i))
    (huη : ∀ i, StronglyMeasurable (uη i))
    (hv : ∀ i, StronglyMeasurable (v i)) (hvq : ∀ i, StronglyMeasurable (vq i))
    (hvη : ∀ i, StronglyMeasurable (vη i)) :
    cylSliceH1 c (fun y => combSlice a u y - combSlice a v y)
        (fun y => combSlice a uq y - combSlice a vq y)
        (fun y => combSlice a uη y - combSlice a vη y) ≤
      ∑ i ∈ a.support, ENNReal.ofReal |a i| *
        cylSliceH1 c (fun y => u i y - v i y)
          (fun y => uq i y - vq i y) (fun y => uη i y - vη i y) := by
  have h1 := cylSliceL2_comb_diff_le c a hu hv
  have h2 := cylSliceL2_comb_diff_le c a huq hvq
  have h3 := cylSliceL2_comb_diff_le c a huη hvη
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cylSliceH1
  rw [mul_add, mul_add]

private lemma cylSliceH1_comb_tendsto {ι : Type*} (c : ℝ) (a : ι →₀ ℝ)
    {z zq zη : ι → CProf}
    (hz : ∀ i, StronglyMeasurable (z i)) (hzq : ∀ i, StronglyMeasurable (zq i))
    (hzη : ∀ i, StronglyMeasurable (zη i))
    {s : ℝ} {l : Filter ℝ}
    (h : ∀ i, Tendsto (fun s' => cylSliceH1 c
      (fun y => z i (s', y) - z i (s, y))
      (fun y => zq i (s', y) - zq i (s, y))
      (fun y => zη i (s', y) - zη i (s, y))) l (𝓝 0)) :
    Tendsto (fun s' => cylSliceH1 c
      (fun y => comb a z (s', y) - comb a z (s, y))
      (fun y => comb a zq (s', y) - comb a zq (s, y))
      (fun y => comb a zη (s', y) - comb a zη (s, y))) l (𝓝 0) := by
  have hsum : Tendsto (fun s' => ∑ i ∈ a.support, ENNReal.ofReal |a i| *
      cylSliceH1 c (fun y => z i (s', y) - z i (s, y))
        (fun y => zq i (s', y) - zq i (s, y))
        (fun y => zη i (s', y) - zη i (s, y))) l (𝓝 0) := by
    have := tendsto_finsetSum a.support (fun i _ =>
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |a i|) (h i)
        (Or.inr ENNReal.ofReal_ne_top))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun s' => ?_)
  exact cylSliceH1_comb_diff_le c a
    (fun i => sliceMeas (hz i) s') (fun i => sliceMeas (hzq i) s')
    (fun i => sliceMeas (hzη i) s')
    (fun i => sliceMeas (hz i) s) (fun i => sliceMeas (hzq i) s)
    (fun i => sliceMeas (hzη i) s)

private lemma dd_tendsto_of_cylSliceH1 {c : ℝ} {z zq zη : CProf} {s : ℝ} {l : Filter ℝ}
    (h : Tendsto (fun s' => cylSliceH1 c
      (fun y => z (s', y) - z (s, y))
      (fun y => zq (s', y) - zq (s, y))
      (fun y => zη (s', y) - zη (s, y))) l (𝓝 0)) :
    Tendsto (dd c z s) l (𝓝 0) ∧ Tendsto (dd c zq s) l (𝓝 0) ∧
      Tendsto (dd c zη s) l (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (fun s' => ?_)
  · unfold dd cylSliceH1; exact le_self_add.trans le_self_add
  · unfold dd cylSliceH1; exact le_add_self.trans le_self_add
  · unfold dd cylSliceH1; exact le_add_self

/-! ### Finite `ℝ`-linear closure of `IsCylH1Slice` and zero-distance congruence -/

private lemma memLp_combSlice {ι : Type*} (c : ℝ) (a : ι →₀ ℝ)
    {u : ι → B0579.Plane → CMerid}
    (hu : ∀ i, MemLp (u i) 2 (volume.restrict (B0579.cell c))) :
    MemLp (combSlice a u) 2 (volume.restrict (B0579.cell c)) := by
  classical
  have hsum : ∀ s : Finset ι,
      MemLp (fun y => ∑ i ∈ s, a i • u i y) 2 (volume.restrict (B0579.cell c)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have heq : (fun y => ∑ j ∈ insert i s, a j • u j y) =
          (a i • u i) + (fun y => ∑ j ∈ s, a j • u j y) := by
        funext y; simp [Finset.sum_insert hi]
      rw [heq]
      exact ((hu i).const_smul (a i)).add ih
  exact hsum a.support

private lemma hasWeakCellDerivC_comb {ι : Type*} (c : ℝ) (j : Fin 2) (a : ι →₀ ℝ)
    {u g : ι → B0579.Plane → ℂ}
    (h : ∀ i, IIIa.HasWeakCellDerivC c j (u i) (g i)) :
    IIIa.HasWeakCellDerivC c j (fun y => ∑ i ∈ a.support, a i • u i y)
      (fun y => ∑ i ∈ a.support, a i • g i y) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · simp only [Finset.sum_mul, smul_mul_assoc]
    exact integrable_finsetSum _ (fun i _ => ((h i).1 ψ hψ).1.smul (a i))
  · simp only [Finset.sum_mul, smul_mul_assoc]
    exact integrable_finsetSum _ (fun i _ => ((h i).1 ψ hψ).2.smul (a i))
  · simp only [Finset.sum_mul, smul_mul_assoc]
    have a1 : ∀ i ∈ a.support,
        IntegrableOn (fun y => a i • (u i y * (B0579.pd j ψ y : ℂ))) (B0579.cell c) :=
      fun i _ => ((h i).1 ψ hψ).1.smul (a i)
    have a2 : ∀ i ∈ a.support,
        IntegrableOn (fun y => a i • (g i y * (ψ y : ℂ))) (B0579.cell c) :=
      fun i _ => ((h i).1 ψ hψ).2.smul (a i)
    rw [integral_finsetSum a.support a1, integral_finsetSum a.support a2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul, integral_smul, (h i).2 ψ hψ, smul_neg]

private lemma isCylSolenoidalSlice_comb {ι : Type*} (c : ℝ) (a : ι →₀ ℝ)
    {u : ι → B0579.Plane → CMerid}
    (h : ∀ i, IsCylSolenoidalSlice c (u i)) :
    IsCylSolenoidalSlice c (combSlice a u) := by
  intro ψ hψ
  have heq : (fun y => combSlice a u y 0 * (B0579.pd 0 ψ y : ℂ) +
        combSlice a u y 1 * (B0579.pd 1 ψ y : ℂ)) =
      fun y => ∑ i ∈ a.support, a i •
        (u i y 0 * (B0579.pd 0 ψ y : ℂ) + u i y 1 * (B0579.pd 1 ψ y : ℂ)) := by
    funext y
    simp only [combSlice_apply, Finset.sum_mul, smul_mul_assoc, ← Finset.sum_add_distrib,
      smul_add]
  rw [heq]
  have hint : ∀ i ∈ a.support, IntegrableOn
      (fun y => a i • (u i y 0 * (B0579.pd 0 ψ y : ℂ) + u i y 1 * (B0579.pd 1 ψ y : ℂ)))
      (B0579.cell c) :=
    fun i _ => ((h i ψ hψ).1).smul (a i)
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum a.support hint]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_smul, (h i ψ hψ).2, smul_zero]

private lemma isCylH1Slice_comb {ι : Type*} (c : ℝ) (a : ι →₀ ℝ)
    {u uq uη : ι → B0579.Plane → CMerid}
    (h : ∀ i, IsCylH1Slice c (u i) (uq i) (uη i)) :
    IsCylH1Slice c (combSlice a u) (combSlice a uq) (combSlice a uη) where
  sm_u := combSlice_meas a (fun i => (h i).sm_u)
  sm_uq := combSlice_meas a (fun i => (h i).sm_uq)
  sm_uη := combSlice_meas a (fun i => (h i).sm_uη)
  weak_q k := by
    simpa [combSlice_apply] using hasWeakCellDerivC_comb c 0 a (fun i => (h i).weak_q k)
  weak_eta k := by
    simpa [combSlice_apply] using hasWeakCellDerivC_comb c 1 a (fun i => (h i).weak_eta k)
  solenoidal := isCylSolenoidalSlice_comb c a (fun i => (h i).solenoidal)
  memL2_u := memLp_combSlice c a (fun i => (h i).memL2_u)
  memL2_uq := memLp_combSlice c a (fun i => (h i).memL2_uq)
  memL2_uη := memLp_combSlice c a (fun i => (h i).memL2_uη)

private lemma ae_cell_eq_of_cylSliceL2_sub_zero {c : ℝ} {v u : B0579.Plane → CMerid}
    (hv : StronglyMeasurable v) (hu : StronglyMeasurable u)
    (h0 : cylSliceL2 c (fun y => v y - u y) = 0) :
    u =ᵐ[volume.restrict (B0579.cell c)] v := by
  have hsub : (fun y => v y - u y) =ᵐ[volume.restrict (B0579.cell c)] 0 :=
    (eLpNorm_eq_zero_iff ((hv.sub hu).aestronglyMeasurable) (by norm_num)).1 h0
  filter_upwards [hsub] with y hy
  exact (sub_eq_zero.1 hy).symm

private lemma hasWeakCellDerivC_congr {c : ℝ} {j : Fin 2} {u v g h : B0579.Plane → ℂ}
    (hu : u =ᵐ[volume.restrict (B0579.cell c)] v)
    (hg : g =ᵐ[volume.restrict (B0579.cell c)] h)
    (hw : IIIa.HasWeakCellDerivC c j u g) :
    IIIa.HasWeakCellDerivC c j v h := by
  obtain ⟨hI, hE⟩ := hw
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have e1 : (fun x => u x * (B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => v x * (B0579.pd j ψ x : ℂ) := hu.mono fun x hx => by dsimp only; rw [hx]
    have e2 : (fun x => g x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => h x * (ψ x : ℂ) := hg.mono fun x hx => by dsimp only; rw [hx]
    exact ⟨(hI ψ hψ).1.congr e1, (hI ψ hψ).2.congr e2⟩
  · have e1 : (fun x => v x * (B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => u x * (B0579.pd j ψ x : ℂ) := hu.symm.mono fun x hx => by dsimp only; rw [hx]
    have e2 : (fun x => h x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => g x * (ψ x : ℂ) := hg.symm.mono fun x hx => by dsimp only; rw [hx]
    rw [integral_congr_ae e1, integral_congr_ae e2, hE ψ hψ]

private lemma isCylH1Slice_of_cylSliceH1_eq_zero {c : ℝ}
    {u uq uη v vq vη : B0579.Plane → CMerid}
    (hu : IsCylH1Slice c u uq uη)
    (hv : StronglyMeasurable v) (hvq : StronglyMeasurable vq) (hvη : StronglyMeasurable vη)
    (h0 : cylSliceH1 c (fun y => v y - u y) (fun y => vq y - uq y) (fun y => vη y - uη y) = 0) :
    IsCylH1Slice c v vq vη ∧
      cylSliceH1 c v vq vη = cylSliceH1 c u uq uη := by
  have h_u0 : cylSliceL2 c (fun y => v y - u y) = 0 :=
    le_antisymm ((le_self_add.trans le_self_add).trans h0.le) zero_le
  have h_q0 : cylSliceL2 c (fun y => vq y - uq y) = 0 :=
    le_antisymm ((le_add_self.trans le_self_add).trans h0.le) zero_le
  have h_η0 : cylSliceL2 c (fun y => vη y - uη y) = 0 :=
    le_antisymm (le_add_self.trans h0.le) zero_le
  have eu := ae_cell_eq_of_cylSliceL2_sub_zero hv hu.sm_u h_u0
  have eq := ae_cell_eq_of_cylSliceL2_sub_zero hvq hu.sm_uq h_q0
  have eη := ae_cell_eq_of_cylSliceL2_sub_zero hvη hu.sm_uη h_η0
  have hnorm : cylSliceH1 c v vq vη = cylSliceH1 c u uq uη := by
    unfold cylSliceH1 cylSliceL2
    rw [eLpNorm_congr_ae eu.symm, eLpNorm_congr_ae eq.symm, eLpNorm_congr_ae eη.symm]
  refine ⟨{
    sm_u := hv
    sm_uq := hvq
    sm_uη := hvη
    weak_q := fun k =>
      hasWeakCellDerivC_congr (eu.mono fun y hy => by rw [hy])
        (eq.mono fun y hy => by rw [hy]) (hu.weak_q k)
    weak_eta := fun k =>
      hasWeakCellDerivC_congr (eu.mono fun y hy => by rw [hy])
        (eη.mono fun y hy => by rw [hy]) (hu.weak_eta k)
    solenoidal := fun ψ hψ => by
      obtain ⟨hI, hE⟩ := hu.solenoidal ψ hψ
      have hae : (fun y => u y 0 * (B0579.pd 0 ψ y : ℂ) + u y 1 * (B0579.pd 1 ψ y : ℂ)) =ᵐ[
          volume.restrict (B0579.cell c)]
          fun y => v y 0 * (B0579.pd 0 ψ y : ℂ) + v y 1 * (B0579.pd 1 ψ y : ℂ) :=
        eu.mono fun y hy => by dsimp only; rw [hy]
      exact ⟨hI.congr hae, (integral_congr_ae hae.symm).trans hE⟩
    memL2_u := hu.memL2_u.ae_eq eu
    memL2_uq := hu.memL2_uq.ae_eq eq
    memL2_uη := hu.memL2_uη.ae_eq eη
  }, hnorm⟩

/-! ### Finite `ℝ`-linear closure of `flatBv`, `IsTailMeridionalSolution`, and global PDE -/

private lemma flatBv_comb {ν c : ℝ} (tr : B0140.TrainSol ν c) {ι : Type*}
    (a : ι →₀ ℝ) (z zq zη : ι → CProf) :
    flatBv tr (comb a z) (comb a zq) (comb a zη) =
      comb a (fun k => flatBv tr (z k) (zq k) (zη k)) := by
  funext x; ext i
  simp only [flatBv, comb_apply, Complex.real_smul, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma cdot_comb {ι : Type*} (a : ι →₀ ℝ) (g : ι → CProf)
    (Ψ : Coord → Fin 2 → ℝ) (x : Coord) :
    cdot (comb a g) Ψ x = ∑ k ∈ a.support, a k • cdot (g k) Ψ x := by
  simp only [cdot, comb_apply, Complex.real_smul, Fin.sum_univ_two, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma cdot_flatBv_comb {ν c : ℝ} (tr : B0140.TrainSol ν c) {ι : Type*}
    (a : ι →₀ ℝ) (z zq zη : ι → CProf) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) :
    cdot (flatBv tr (comb a z) (comb a zq) (comb a zη)) Ψ x =
      ∑ k ∈ a.support, a k • cdot (flatBv tr (z k) (zq k) (zη k)) Ψ x := by
  rw [flatBv_comb]
  exact cdot_comb a _ Ψ x

private lemma merid_pair_comb {ι : Type*} (ν : ℝ) (a : ι →₀ ℝ) (z : ι → CProf)
    (Ψ : Coord → Fin 2 → ℝ) (x : Coord) :
    (∑ i : Fin 2, comb a z x i * meridTranspose ν Ψ x i) =
      ∑ k ∈ a.support, a k • (∑ i : Fin 2, z k x i * meridTranspose ν Ψ x i) := by
  simp only [comb_apply, Complex.real_smul, Fin.sum_univ_two, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma isTailMeridionalSolution_comb {ι : Type*} (p : Params) (T : ℝ) (a : ι →₀ ℝ)
    {g z zq zη : ι → CProf}
    (h : ∀ k, IsTailMeridionalSolution p T (g k) (z k) (zq k) (zη k)) :
    IsTailMeridionalSolution p T (comb a g) (comb a z) (comb a zq) (comb a zη) where
  periodic := by
    have hall := (Filter.eventually_all_finset a.support).2 (fun k _ => (h k).periodic)
    filter_upwards [hall] with x hx hT
    refine ⟨?_, ?_, ?_⟩ <;> simp only [comb] <;> refine Finset.sum_congr rfl fun k hk => ?_
    · rw [(hx k hk hT).1]
    · rw [(hx k hk hT).2.1]
    · rw [(hx k hk hT).2.2]
  weak_q i φ hφ hsupp := by
    simp only [comb_apply, Finset.sum_mul, smul_mul_assoc]
    have a1 : ∀ k ∈ a.support,
        Integrable (fun x => a k • (z k x i * (coordTranspose vQ0 dZero φ x : ℂ))) :=
      fun k _ => ((h k).weak_q i φ hφ hsupp).1.smul (a k)
    have a2 : ∀ k ∈ a.support,
        Integrable (fun x => a k • (zq k x i * (φ x : ℂ))) :=
      fun k _ => ((h k).weak_q i φ hφ hsupp).2.1.smul (a k)
    refine ⟨integrable_finsetSum _ a1, integrable_finsetSum _ a2, ?_⟩
    rw [integral_finsetSum a.support a2, integral_finsetSum a.support a1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul, integral_smul, ((h k).weak_q i φ hφ hsupp).2.2]
  weak_eta i φ hφ hsupp := by
    simp only [comb_apply, Finset.sum_mul, smul_mul_assoc]
    have a1 : ∀ k ∈ a.support,
        Integrable (fun x => a k • (z k x i * (coordTranspose vEta dZero φ x : ℂ))) :=
      fun k _ => ((h k).weak_eta i φ hφ hsupp).1.smul (a k)
    have a2 : ∀ k ∈ a.support,
        Integrable (fun x => a k • (zη k x i * (φ x : ℂ))) :=
      fun k _ => ((h k).weak_eta i φ hφ hsupp).2.1.smul (a k)
    refine ⟨integrable_finsetSum _ a1, integrable_finsetSum _ a2, ?_⟩
    rw [integral_finsetSum a.support a2, integral_finsetSum a.support a1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul, integral_smul, ((h k).weak_eta i φ hφ hsupp).2.2]
  solenoidal φ hφ hsupp := by
    have heq : (fun x => comb a z x 0 * (cpd 1 φ x : ℂ) + comb a z x 1 * (cpd 2 φ x : ℂ)) =
        fun x => ∑ k ∈ a.support, a k •
          (z k x 0 * (cpd 1 φ x : ℂ) + z k x 1 * (cpd 2 φ x : ℂ)) := by
      funext x
      simp only [comb_apply, Finset.sum_mul, smul_mul_assoc, ← Finset.sum_add_distrib, smul_add]
    rw [heq]
    have hint : ∀ k ∈ a.support,
        Integrable (fun x => a k • (z k x 0 * (cpd 1 φ x : ℂ) + z k x 1 * (cpd 2 φ x : ℂ))) :=
      fun k _ => ((h k).solenoidal φ hφ hsupp).1.smul (a k)
    refine ⟨integrable_finsetSum _ hint, ?_⟩
    rw [integral_finsetSum a.support hint]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_smul, ((h k).solenoidal φ hφ hsupp).2, smul_zero]
  equation Ψ hΨ hsupp := by
    have ez : (fun x => ∑ i : Fin 2, comb a z x i * meridTranspose p.ν Ψ x i) =
        fun x => ∑ k ∈ a.support, a k • (∑ i : Fin 2, z k x i * meridTranspose p.ν Ψ x i) :=
      funext (merid_pair_comb p.ν a z Ψ)
    have eb : cdot (flatBv p.train (comb a z) (comb a zq) (comb a zη)) Ψ =
        fun x => ∑ k ∈ a.support, a k • cdot (flatBv p.train (z k) (zq k) (zη k)) Ψ x :=
      funext (cdot_flatBv_comb p.train a z zq zη Ψ)
    have eg : cdot (comb a g) Ψ = fun x => ∑ k ∈ a.support, a k • cdot (g k) Ψ x :=
      funext (cdot_comb a g Ψ)
    have iz : ∀ k ∈ a.support,
        Integrable (fun x => a k • (∑ i : Fin 2, z k x i * meridTranspose p.ν Ψ x i)) :=
      fun k _ => ((h k).equation Ψ hΨ hsupp).1.smul (a k)
    have ib : ∀ k ∈ a.support,
        Integrable (fun x => a k • cdot (flatBv p.train (z k) (zq k) (zη k)) Ψ x) :=
      fun k _ => ((h k).equation Ψ hΨ hsupp).2.1.smul (a k)
    have ig : ∀ k ∈ a.support, Integrable (fun x => a k • cdot (g k) Ψ x) :=
      fun k _ => ((h k).equation Ψ hΨ hsupp).2.2.1.smul (a k)
    have hIz : Integrable (fun x => ∑ i : Fin 2, comb a z x i * meridTranspose p.ν Ψ x i) := by
      rw [ez]; exact integrable_finsetSum _ iz
    have hIb : Integrable (cdot (flatBv p.train (comb a z) (comb a zq) (comb a zη)) Ψ) := by
      rw [eb]; exact integrable_finsetSum _ ib
    have hIg : Integrable (cdot (comb a g) Ψ) := by
      rw [eg]; exact integrable_finsetSum _ ig
    refine ⟨hIz, hIb, hIg, ?_⟩
    rw [integral_add hIz hIb]
    rw [ez, eb, eg, integral_finsetSum a.support iz, integral_finsetSum a.support ib,
      integral_finsetSum a.support ig, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk_eq := ((h k).equation Ψ hΨ hsupp).2.2.2
    have hkz := ((h k).equation Ψ hΨ hsupp).1
    have hkb := ((h k).equation Ψ hΨ hsupp).2.1
    rw [integral_smul, integral_smul, integral_smul, ← smul_add,
      ← integral_add hkz hkb, hk_eq]

private lemma hasWeakVec_comb (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {ι : Type*}
    (a : ι →₀ ℝ) {w g : ι → CProf} (h : ∀ k, HasWeakVec v d (w k) (g k)) :
    HasWeakVec v d (comb a w) (comb a g) := fun i => by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · simp only [comb_apply, Finset.sum_mul, smul_mul_assoc]
    exact integrable_finsetSum _ (fun k _ => ((h k i).1 φ hφ).1.smul (a k))
  · simp only [comb_apply, Finset.sum_mul, smul_mul_assoc]
    exact integrable_finsetSum _ (fun k _ => ((h k i).1 φ hφ).2.smul (a k))
  · simp only [comb_apply, Finset.sum_mul, smul_mul_assoc]
    have a1 : ∀ k ∈ a.support,
        Integrable (fun x => a k • (g k x i * (φ x : ℂ))) :=
      fun k _ => ((h k i).1 φ hφ).2.smul (a k)
    have a2 : ∀ k ∈ a.support,
        Integrable (fun x => a k • (w k x i * (coordTranspose v d φ x : ℂ))) :=
      fun k _ => ((h k i).1 φ hφ).1.smul (a k)
    rw [integral_finsetSum a.support a1, integral_finsetSum a.support a2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul, integral_smul, (h k i).2 φ hφ]

/-! ### Horizon `Ioc 0 T` density transfer and `L²(cell)` entrance curl transfer on `Ioo 0 T` -/

/-- A slice quantity `G` bounded at almost every `s ∈ Ioo 0 T` and upper-semicontinuous along
`𝓝[Ioc 0 T] s` at every `s ∈ Ioc 0 T` is bounded at EVERY `s ∈ Ioc 0 T` (including `s = T`). -/
private lemma ae_Ioc_le_of_ae_Ioo_and_cont {T : ℝ} {G : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    (hgood : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 T → G s ≤ B)
    (hcont : ∀ s ∈ Ioc 0 T, ∀ ε : ℝ≥0∞, ε ≠ 0 → ∀ᶠ s' in 𝓝[Ioc 0 T] s, G s ≤ G s' + ε) :
    ∀ s ∈ Ioc 0 T, G s ≤ B := by
  intro s hs
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have h1 := hcont s hs ε (by simpa using hε.ne')
  obtain ⟨U, hU_nhds, hU_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU_nhds
  set a₀ : ℝ := max 0 (s - δ)
  have ha₀_lt : a₀ < s := max_lt hs.1 (by linarith)
  set V : Set ℝ := Ioo a₀ s
  have hV_open : IsOpen V := isOpen_Ioo
  have hmid : (a₀ + s) / 2 ∈ V := ⟨by linarith, by linarith⟩
  have hV_pos : 0 < volume V := hV_open.measure_pos volume ⟨(a₀ + s) / 2, hmid⟩
  have hN : volume {s' : ℝ | ¬(s' ∈ Ioo 0 T → G s' ≤ B)} = 0 := ae_iff.1 hgood
  obtain ⟨s', hs'V, hs'N⟩ : ∃ s' ∈ V, s' ∉ {s' : ℝ | ¬(s' ∈ Ioo 0 T → G s' ≤ B)} := by
    by_contra hcon
    have hsub : V ⊆ {s' : ℝ | ¬(s' ∈ Ioo 0 T → G s' ≤ B)} := fun x hxV => by
      by_contra hx
      exact hcon ⟨x, hxV, hx⟩
    exact hV_pos.ne' (measure_mono_null hsub hN)
  have hs'_pos : 0 < s' := (le_max_left 0 (s - δ)).trans_lt hs'V.1
  have hs'_ltT : s' < T := hs'V.2.trans_le hs.2
  have hs'_Ioo : s' ∈ Ioo 0 T := ⟨hs'_pos, hs'_ltT⟩
  have hs'_Ioc : s' ∈ Ioc 0 T := ⟨hs'_pos, hs'_ltT.le⟩
  have hs'_ball : s' ∈ Metric.ball s δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hle : s - δ ≤ a₀ := le_max_right 0 (s - δ)
    exact ⟨by linarith [hs'V.1], by linarith [hs'V.2]⟩
  have hG_s' : G s' ≤ B := by
    by_contra hh
    exact hs'N (fun h' => hh (h' hs'_Ioo))
  have hstep : G s ≤ G s' + ε := hU_sub ⟨hball hs'_ball, hs'_Ioc⟩
  exact hstep.trans (add_le_add_left hG_s' _)

private lemma comb_ae_Ioo {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : Module.Basis ι ℝ V) (T : ℝ) (L : V →ₗ[ℝ] CProf) (w : ι → CProf)
    (h : ∀ i, ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → w i x = L (B i) x) (F : V) :
    ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → comb (B.repr F) w x = L F x := by
  have hL : L = B.constr ℝ (fun i => L (B i)) := B.ext (fun i => by simp)
  have e : L F = comb (B.repr F) (fun i => L (B i)) := by
    rw [← constr_eq_comb B (fun i => L (B i)) F, ← hL]
  have hall := (Filter.eventually_all_finset (B.repr F).support).2 (fun i _ => h i)
  filter_upwards [hall] with x hx hxT
  rw [e]
  exact Finset.sum_congr rfl fun i hi => by rw [hx i hi hxT]

private lemma slice_ae_Ioo {c T : ℝ} {u v : CProf}
    (h : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → u x = v x) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 T →
      (fun y => u (s, y)) =ᵐ[volume.restrict (B0579.cell c)] (fun y => v (s, y)) := by
  have hprod : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure B0579.Plane),
      (s, y).1 ∈ Ioo 0 T → u (s, y) = v (s, y) :=
    Measure.ae_ae_of_ae_prod h
  filter_upwards [hprod] with s hs hsT
  exact ae_restrict_of_ae (hs.mono fun y hy => hy hsT)

private lemma cellMeasure_zero (c : ℝ) :
    B0579.cellMeasure c 0 = volume.restrict (B0579.cell c) := by
  unfold B0579.cellMeasure
  have : (fun x => (B0579.density 0 x : ℝ≥0∞)) = fun _ => 1 := by
    funext x; simp [B0579.density]
  rw [this]; exact withDensity_one

/-- `L²` triangle inequality `‖m - e‖₂ ≤ ‖m' - e‖₂ + ‖m - m'‖₂` without requiring measurability
of `e` (used for `entranceVorticityComb`). -/
private lemma eLpNorm_two_sub_le {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {m m' e : X → E}
    (hm : AEStronglyMeasurable m μ) (hm' : AEStronglyMeasurable m' μ) :
    eLpNorm (m - e) 2 μ ≤ eLpNorm (m' - e) 2 μ + eLpNorm (m - m') 2 μ := by
  have two : (2 : ℝ≥0∞).toReal = 2 := rfl
  have key : ∀ f : X → E, eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro f
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), two]
  rw [key, key, key]
  obtain ⟨g, hg, hgle, hint⟩ := exists_measurable_le_lintegral_eq μ (fun x => ‖(m - e) x‖ₑ ^ (2 : ℝ))
  set d : X → ℝ≥0∞ := fun x => ‖(m - m') x‖ₑ
  have hdm : AEMeasurable d μ := (hm.sub hm').enorm
  let k : X → ℝ≥0∞ := fun x => g x ^ (1 / (2 : ℝ))
  have hk : Measurable k := hg.pow_const _
  have hk2 : ∀ x, k x ^ (2 : ℝ) = g x := by
    intro x; simp only [k]; rw [← ENNReal.rpow_mul]; norm_num
  have hkle : ∀ x, k x ≤ ‖(m - e) x‖ₑ := by
    intro x
    have := ENNReal.rpow_le_rpow (hgle x) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    refine this.trans (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]; norm_num
  have hk' : ∀ x, k x - d x ≤ ‖(m' - e) x‖ₑ := by
    intro x
    rw [tsub_le_iff_right]
    refine (hkle x).trans ?_
    have : (m - e) x = (m' - e) x + (m - m') x := by simp
    rw [this]; exact enorm_add_le _ _
  have hkd : AEMeasurable (k - d) μ := hk.aemeasurable.sub hdm
  rw [hint]
  calc (∫⁻ a, g a ∂μ) ^ (1 / (2 : ℝ)) = (∫⁻ a, k a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        simp_rw [hk2]
    _ ≤ (∫⁻ a, ((k - d) + d) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun a => ?_) (by norm_num)
        exact ENNReal.rpow_le_rpow (by simpa using (le_tsub_add : k a ≤ k a - d a + d a))
          (by norm_num)
    _ ≤ (∫⁻ a, (k - d) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) +
          (∫⁻ a, d a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_Lp_add_le hkd hdm (by norm_num)
    _ ≤ _ := by
        gcongr with a
        exact hk' a

private lemma curl_le (c : ℝ) {Zq Zη : CProf}
    (hq : StronglyMeasurable Zq) (hη : StronglyMeasurable Zη)
    (ent : B0579.Plane → ℝ) (s s' : ℝ) :
    eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0) ≤
      eLpNorm (fun x => profCurl Zq Zη (s', x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0) +
        (dd c Zq s s' + dd c Zη s s') := by
  rw [cellMeasure_zero]
  set μ : Measure B0579.Plane := volume.restrict (B0579.cell c)
  let m : B0579.Plane → ℂ := fun x => profCurl Zq Zη (s, x)
  let m' : B0579.Plane → ℂ := fun x => profCurl Zq Zη (s', x)
  let e : B0579.Plane → ℂ := fun x => ((ent x : ℝ) : ℂ)
  have hm : StronglyMeasurable m :=
    (compMeas (sliceMeas hq s) 1).sub (compMeas (sliceMeas hη s) 0)
  have hm' : StronglyMeasurable m' :=
    (compMeas (sliceMeas hq s') 1).sub (compMeas (sliceMeas hη s') 0)
  have h1 := eLpNorm_two_sub_le (μ := μ) (e := e) hm.aestronglyMeasurable hm'.aestronglyMeasurable
  refine h1.trans (add_le_add_right ?_ _)
  let Dq : B0579.Plane → CMerid := fun y => Zq (s', y) - Zq (s, y)
  let Dη : B0579.Plane → CMerid := fun y => Zη (s', y) - Zη (s, y)
  have hDq : StronglyMeasurable Dq := (sliceMeas hq s').sub (sliceMeas hq s)
  have hDη : StronglyMeasurable Dη := (sliceMeas hη s').sub (sliceMeas hη s)
  have hb : ∀ x, ‖(m - m') x‖ ≤ ‖‖Dq x‖ + ‖Dη x‖‖ := by
    intro x
    have e1 : (m - m') x = -(Dq x 1) + Dη x 0 := by
      simp [m, m', Dq, Dη, profCurl]; ring
    rw [e1, Real.norm_of_nonneg (by positivity)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    exact add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
  calc eLpNorm (m - m') 2 μ ≤ eLpNorm (fun x => ‖Dq x‖ + ‖Dη x‖) 2 μ := eLpNorm_mono hb
    _ ≤ eLpNorm (fun x => ‖Dq x‖) 2 μ + eLpNorm (fun x => ‖Dη x‖) 2 μ :=
        eLpNorm_add_le hDq.norm.aestronglyMeasurable hDη.norm.aestronglyMeasurable (by norm_num)
    _ = dd c Zq s s' + dd c Zη s s' := by
        simp only [dd, cylSliceL2, eLpNorm_norm]
        rfl

private lemma curl_transfer_Ioo {c T : ℝ} (hT : 0 < T)
    {Zq Zη zq0 zη0 : CProf} (hq : StronglyMeasurable Zq) (hη : StronglyMeasurable Zη)
    (hdq : ∀ s ∈ Ioc 0 T, Tendsto (dd c Zq s) (𝓝[Ioc 0 T] s) (𝓝 0))
    (hdη : ∀ s ∈ Ioc 0 T, Tendsto (dd c Zη s) (𝓝[Ioc 0 T] s) (𝓝 0))
    (haq : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → Zq x = zq0 x)
    (haη : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → Zη x = zη0 x)
    (ent : B0579.Plane → ℝ)
    (h0 : Tendsto (fun s => eLpNorm (fun x => profCurl zq0 zη0 (s, x) - ((ent x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c 0)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun s => eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c 0)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h0 ⊢
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (h0 (ε / 2) (ENNReal.half_pos hε.ne'))
  set δ : ℝ := min T δ₀
  have hδ : 0 < δ := lt_min hT hδ₀
  set φ : ℝ → ℝ≥0∞ := fun s => eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2
    (B0579.cellMeasure c 0)
  have key : ∀ s ∈ Ioc 0 δ, φ s ≤ ε / 2 := by
    refine ae_Ioc_le_of_ae_Ioo_and_cont ?_ ?_
    · filter_upwards [slice_ae_Ioo (c := c) haq, slice_ae_Ioo (c := c) haη] with s e1 e2 hs
      have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
      have hsδ₀ : s ∈ Ioo 0 δ₀ := ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩
      have heq : φ s = eLpNorm (fun x => profCurl zq0 zη0 (s, x) - ((ent x : ℝ) : ℂ)) 2
          (B0579.cellMeasure c 0) := by
        dsimp [φ]
        rw [cellMeasure_zero]
        refine eLpNorm_congr_ae ?_
        filter_upwards [e1 hsT, e2 hsT] with x x1 x2
        simp [profCurl, x1, x2]
      rw [heq]
      exact hsub hsδ₀
    · intro s hs ε' hε'
      have hsT : s ∈ Ioc 0 T := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
      have hmono_nhds : 𝓝[Ioc 0 δ] s ≤ 𝓝[Ioc 0 T] s :=
        nhdsWithin_mono s (Ioc_subset_Ioc_right (min_le_left _ _))
      have hsum : Tendsto (fun s' => dd c Zq s s' + dd c Zη s s') (𝓝[Ioc 0 δ] s) (𝓝 0) := by
        simpa using ((hdq s hsT).mono_left hmono_nhds).add ((hdη s hsT).mono_left hmono_nhds)
      have hnear := (ENNReal.tendsto_nhds_zero.1 hsum) ε' (pos_iff_ne_zero.2 hε')
      filter_upwards [hnear] with s' hs'
      exact (curl_le c hq hη ent s s').trans (add_le_add_right hs' _)
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
  exact (key s ⟨hs.1, hs.2.le⟩).trans ENNReal.half_le_self

/-! ### Main linear continuation theorem -/

/-- **Unconditional `ℝ`-linear continuation assembly (`LinearGlue`)**:
given the three `F`-free PDE leaves `MeridionalTailExistence`, `MeridionalHorizonGluing`, and
`MeridionalTailH1Gronwall`, together with upgraded `ℝ`-linear body sources `(gOf, gqOf, gηOf)`
and early meridional corrections `(zOf_eb, zqOf_eb, zηOf_eb)` on `(0, p.H]`, produces `ℝ`-linear
maps `(zOf, zqOf, zηOf)` solving `IsGlobalMeridionalCorrection` on `(0, ∞)` with strongly
measurable profiles, preserved `Ioc 0 p.H` slice bounds (including at `s = p.H`), and the
differentiated `H¹(C_c)` Gronwall slice bound on `(p.H, ∞)`. -/
theorem linear_meridional_continuation
    (hEx : MeridionalTailExistence)
    (hGlue : MeridionalHorizonGluing)
    {A_H1 K_H1 : ℝ}
    (hGron : ∀ {p : Params} {d dm dp T B_strain : ℝ},
      BgRegime p d dm dp → p.ν ≤ 1 → 1 ≤ T → 0 ≤ B_strain →
      ∫⁻ s in Ioi T,
          (B0277.supNormD 1 (p.train.v s) + B0277.supNormD 2 (p.train.v s)) ≤
        ENNReal.ofReal B_strain →
      ∀ {g gq gη z₂ zq₂ zη₂ : CProf},
        IsCylSourceH1 p.c g gq gη →
        (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤ →
        StronglyMeasurable z₂ → StronglyMeasurable zq₂ → StronglyMeasurable zη₂ →
        IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)) →
        IsTailMeridionalSolution p T g z₂ zq₂ zη₂ →
        (∀ s : ℝ, T ≤ s →
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => z₂ (s', y) - z₂ (s, y))
            (fun y => zq₂ (s', y) - zq₂ (s, y))
            (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)) →
        ∀ s : ℝ, T < s →
          sliceH1Norm p.c z₂ zq₂ zη₂ s ≤
            ENNReal.ofReal (A_H1 * Real.exp (K_H1 * B_strain)) *
              (sliceH1Norm p.c z₂ zq₂ zη₂ T +
                ENNReal.ofReal K_H1 * ∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t))
    {p : Params} {d dm dp B_strain : ℝ} {M_eb : HpR p.c → ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hH1 : 1 ≤ p.H)
    (hB_nn : 0 ≤ B_strain) (hM_nn : ∀ F, 0 ≤ M_eb F)
    (hStrain : ∫⁻ s in Ioi p.H,
        (B0277.supNormD 1 (p.train.v s) + B0277.supNormD 2 (p.train.v s)) ≤
      ENNReal.ofReal B_strain)
    (αMap : HpR p.c →L[ℝ] E2)
    (gOf gqOf gηOf zOf_eb zqOf_eb zηOf_eb : HpR p.c →ₗ[ℝ] CProf)
    (hg_src : ∀ F : HpR p.c, IsCylSourceH1 p.c (gOf F) (gqOf F) (gηOf F))
    (hg_Ioc : ∀ F : HpR p.c, (∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) < ⊤)
    (hg_Ioi : ∀ F : HpR p.c, (∫⁻ s in Ioi p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) < ⊤)
    (hz_mc : ∀ F : HpR p.c,
      IsMeridionalCorrectionOn p p.H (gOf F) (zOf_eb F) (zqOf_eb F) (zηOf_eb F) (αMap F))
    (hz_early : ∀ F : HpR p.c, ∀ s ∈ Ioc 0 p.H,
      sliceH1Norm p.c (zOf_eb F) (zqOf_eb F) (zηOf_eb F) s + ENNReal.ofReal ‖αMap F‖ ≤
        ENNReal.ofReal (M_eb F)) :
    ∃ (zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf),
      ∀ F : HpR p.c,
        StronglyMeasurable (zOf F) ∧
        StronglyMeasurable (zqOf F) ∧
        StronglyMeasurable (zηOf F) ∧
        Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
        IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
        (∀ s ∈ Ioc 0 p.H,
          sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
            ENNReal.ofReal (M_eb F)) ∧
        (∀ s : ℝ, p.H < s →
          sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s ≤
            ENNReal.ofReal (A_H1 * Real.exp (K_H1 * B_strain)) *
              (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) p.H +
                ENNReal.ofReal K_H1 * ∫⁻ t in Ioi p.H,
                  sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) t)) := by
  classical
  have hH_pos : 0 < p.H := zero_lt_one.trans_le hH1
  -- Step 1: Construct glued early + tail solutions on each Hamel basis vector of HpR p.c
  let B := Module.Basis.ofVectorSpace ℝ (HpR p.c)
  have h_bas_ex : ∀ i,
      ∃ (z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf),
        StronglyMeasurable z₁ ∧ StronglyMeasurable zq₁ ∧ StronglyMeasurable zη₁ ∧
        QPeriodic p.c z₁ ∧ QPeriodic p.c zq₁ ∧ QPeriodic p.c zη₁ ∧
        (∀ᵐ x : Coord, x.1 ∈ Ioo 0 p.H →
          z₁ x = zOf_eb (B i) x ∧ zq₁ x = zqOf_eb (B i) x ∧ zη₁ x = zηOf_eb (B i) x) ∧
        (∀ s ∈ Ioc 0 p.H,
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => z₁ (s', y) - z₁ (s, y))
            (fun y => zq₁ (s', y) - zq₁ (s, y))
            (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 p.H] s) (𝓝 0)) ∧
        IsCylH1Slice p.c (fun y => z₁ (p.H, y)) (fun y => zq₁ (p.H, y)) (fun y => zη₁ (p.H, y)) ∧
        StronglyMeasurable z₂ ∧ StronglyMeasurable zq₂ ∧ StronglyMeasurable zη₂ ∧
        cylSliceH1 p.c (fun y => z₂ (p.H, y) - z₁ (p.H, y))
          (fun y => zq₂ (p.H, y) - zq₁ (p.H, y)) (fun y => zη₂ (p.H, y) - zη₁ (p.H, y)) = 0 ∧
        IsTailMeridionalSolution p p.H (gOf (B i)) z₂ zq₂ zη₂ ∧
        (∀ s : ℝ, p.H ≤ s →
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => z₂ (s', y) - z₂ (s, y))
            (fun y => zq₂ (s', y) - zq₂ (s, y))
            (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici p.H] s) (𝓝 0)) ∧
        IsGlobalMeridionalCorrection p (gOf (B i))
          (glueAtHorizon p.H z₁ z₂) (glueAtHorizon p.H zq₁ zq₂) (glueAtHorizon p.H zη₁ zη₂)
          (αMap (B i)) := by
    intro i
    have hz_ae_i : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
        sliceH1Norm p.c (zOf_eb (B i)) (zqOf_eb (B i)) (zηOf_eb (B i)) s ≤
          ENNReal.ofReal (M_eb (B i)) :=
      Eventually.of_forall fun s hs => le_self_add.trans (hz_early (B i) s hs)
    obtain ⟨z₁, zq₁, zη₁, hsm1, hsmq1, hsmη1, hper1, hperq1, hperη1,
        hae1, hcont1, hH1_1, hglue_i⟩ :=
      hGlue hreg hH_pos (hM_nn (B i)) (hg_src (B i)) (hg_Ioc (B i)) (hz_mc (B i)) hz_ae_i
    obtain ⟨z₂, zq₂, zη₂, hsm2, hsmq2, hsmη2, hmatch2, htail2, hcont2⟩ :=
      hEx hreg hH_pos hH1_1 (hg_src (B i)) (hg_Ioi (B i))
    have hglob_i := hglue_i hsm2 hsmq2 hsmη2 (hg_Ioi (B i)) hmatch2 htail2 hcont2
    exact ⟨z₁, zq₁, zη₁, z₂, zq₂, zη₂, hsm1, hsmq1, hsmη1, hper1, hperq1, hperη1,
      hae1, hcont1, hH1_1, hsm2, hsmq2, hsmη2, hmatch2, htail2, hcont2, hglob_i⟩
  choose z₁b zq₁b zη₁b z₂b zq₂b zη₂b
    hsm1b hsmq1b hsmη1b _hper1b _hperq1b _hperη1b
    hae1b hcont1b hH1_1b hsm2b hsmq2b hsmη2b hmatch2b htail2b hcont2b hglob_b
    using h_bas_ex
  let zb := fun i => glueAtHorizon p.H (z₁b i) (z₂b i)
  let zqb := fun i => glueAtHorizon p.H (zq₁b i) (zq₂b i)
  let zηb := fun i => glueAtHorizon p.H (zη₁b i) (zη₂b i)
  have hsm_zb : ∀ i, StronglyMeasurable (zb i) :=
    fun i => stronglyMeasurable_glueAtHorizon p.H (hsm1b i) (hsm2b i)
  have hsm_zqb : ∀ i, StronglyMeasurable (zqb i) :=
    fun i => stronglyMeasurable_glueAtHorizon p.H (hsmq1b i) (hsmq2b i)
  have hsm_zηb : ∀ i, StronglyMeasurable (zηb i) :=
    fun i => stronglyMeasurable_glueAtHorizon p.H (hsmη1b i) (hsmη2b i)
  -- Step 2: Extend linearly over HpR p.c via B.constr ℝ
  let zOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ zb
  let zqOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ zqb
  let zηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ zηb
  refine ⟨zOf, zqOf, zηOf, fun F => ?_⟩
  set a := B.repr F
  have hz_eq : zOf F = glueAtHorizon p.H (comb a z₁b) (comb a z₂b) := by
    change B.constr ℝ zb F = _
    rw [constr_eq_comb, glueAtHorizon_comb]
  have hzq_eq : zqOf F = glueAtHorizon p.H (comb a zq₁b) (comb a zq₂b) := by
    change B.constr ℝ zqb F = _
    rw [constr_eq_comb, glueAtHorizon_comb]
  have hzη_eq : zηOf F = glueAtHorizon p.H (comb a zη₁b) (comb a zη₂b) := by
    change B.constr ℝ zηb F = _
    rw [constr_eq_comb, glueAtHorizon_comb]
  have hg_comb : gOf F = comb a (fun i => gOf (B i)) := by
    have hL : gOf = B.constr ℝ (fun i => gOf (B i)) := B.ext (fun i => by simp)
    rw [← constr_eq_comb B (fun i => gOf (B i)) F, ← hL]
  -- Strong measurability and slice measurability
  have hsm_z1 : StronglyMeasurable (comb a z₁b) := comb_meas a hsm1b
  have hsm_zq1 : StronglyMeasurable (comb a zq₁b) := comb_meas a hsmq1b
  have hsm_zη1 : StronglyMeasurable (comb a zη₁b) := comb_meas a hsmη1b
  have hsm_z2 : StronglyMeasurable (comb a z₂b) := comb_meas a hsm2b
  have hsm_zq2 : StronglyMeasurable (comb a zq₂b) := comb_meas a hsmq2b
  have hsm_zη2 : StronglyMeasurable (comb a zη₂b) := comb_meas a hsmη2b
  have hsm_z : StronglyMeasurable (zOf F) := by
    rw [hz_eq]; exact stronglyMeasurable_glueAtHorizon p.H hsm_z1 hsm_z2
  have hsm_zq : StronglyMeasurable (zqOf F) := by
    rw [hzq_eq]; exact stronglyMeasurable_glueAtHorizon p.H hsm_zq1 hsm_zq2
  have hsm_zη : StronglyMeasurable (zηOf F) := by
    rw [hzη_eq]; exact stronglyMeasurable_glueAtHorizon p.H hsm_zη1 hsm_zη2
  have hm_z : Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hsm_z hsm_zq hsm_zη
  -- Early agreement on Ioo 0 p.H and cylSliceH1 continuity on Ioc 0 p.H
  have hae_z1 : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 p.H → comb a z₁b x = zOf_eb F x :=
    comb_ae_Ioo B p.H zOf_eb z₁b (fun i => (hae1b i).mono fun _ h hp => (h hp).1) F
  have hae_zq1 : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 p.H → comb a zq₁b x = zqOf_eb F x :=
    comb_ae_Ioo B p.H zqOf_eb zq₁b (fun i => (hae1b i).mono fun _ h hp => (h hp).2.1) F
  have hae_zη1 : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 p.H → comb a zη₁b x = zηOf_eb F x :=
    comb_ae_Ioo B p.H zηOf_eb zη₁b (fun i => (hae1b i).mono fun _ h hp => (h hp).2.2) F
  have hcont_z1 : ∀ s ∈ Ioc 0 p.H,
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => comb a z₁b (s', y) - comb a z₁b (s, y))
        (fun y => comb a zq₁b (s', y) - comb a zq₁b (s, y))
        (fun y => comb a zη₁b (s', y) - comb a zη₁b (s, y))) (𝓝[Ioc 0 p.H] s) (𝓝 0) :=
    fun s hs => cylSliceH1_comb_tendsto p.c a hsm1b hsmq1b hsmη1b (fun i => hcont1b i s hs)
  -- Early slice bound on ALL s ∈ Ioc 0 p.H (including s = p.H) via left-continuity transfer
  have hearly_z1 : ∀ s ∈ Ioc 0 p.H,
      sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s + ENNReal.ofReal ‖αMap F‖ ≤
        ENNReal.ofReal (M_eb F) := by
    refine ae_Ioc_le_of_ae_Ioo_and_cont ?_ ?_
    · filter_upwards [slice_ae_Ioo (c := p.c) hae_z1,
        slice_ae_Ioo (c := p.c) hae_zq1, slice_ae_Ioo (c := p.c) hae_zη1]
        with s ez eq eη hs
      have heq_sl : sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s =
          sliceH1Norm p.c (zOf_eb F) (zqOf_eb F) (zηOf_eb F) s := by
        unfold sliceH1Norm
        rw [eLpNorm_congr_ae (ez hs), eLpNorm_congr_ae (eq hs), eLpNorm_congr_ae (eη hs)]
      rw [heq_sl]
      exact hz_early F s ⟨hs.1, hs.2.le⟩
    · intro s hs ε hε
      have hnear := (ENNReal.tendsto_nhds_zero.1 (hcont_z1 s hs)) ε (pos_iff_ne_zero.2 hε)
      filter_upwards [hnear] with s' hs'
      calc sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s + ENNReal.ofReal ‖αMap F‖
          ≤ (sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s' + _) +
              ENNReal.ofReal ‖αMap F‖ :=
            add_le_add_left (sliceH1_le_add_dd p.c hsm_z1 hsm_zq1 hsm_zη1 s s') _
        _ ≤ (sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s' + ε) +
              ENNReal.ofReal ‖αMap F‖ :=
            add_le_add_left (add_le_add_right hs' _) _
        _ = (sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s' +
              ENNReal.ofReal ‖αMap F‖) + ε := by ac_rfl
  have hearly_out : ∀ s ∈ Ioc 0 p.H,
      sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
        ENNReal.ofReal (M_eb F) := by
    intro s hs
    have h1 : sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s =
        sliceH1Norm p.c (comb a z₁b) (comb a zq₁b) (comb a zη₁b) s := by
      rw [hz_eq, hzq_eq, hzη_eq]
      simp [sliceH1Norm, glueAtHorizon, hs.2]
    rw [h1]
    exact hearly_z1 s hs
  -- Step 3: Global PDE IsGlobalMeridionalCorrection on (zOf F, zqOf F, zηOf F)
  have hglob_out : IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) := by
    have hzc : zOf F = comb a zb := constr_eq_comb B zb F
    have hzqc : zqOf F = comb a zqb := constr_eq_comb B zqb F
    have hzηc : zηOf F = comb a zηb := constr_eq_comb B zηb F
    refine {
      periodic := by
        rw [hzc]; exact qPeriodic_comb p.c a (fun i => (hglob_b i).periodic)
      weak_q := by
        rw [hzc, hzqc]; exact hasWeakVec_comb vQ0 dZero a (fun i => (hglob_b i).weak_q)
      weak_eta := by
        rw [hzc, hzηc]; exact hasWeakVec_comb vEta dZero a (fun i => (hglob_b i).weak_eta)
      solenoidal := fun φ hφ => by
        rw [hzc]
        have heq : (fun x => comb a zb x 0 * (cpd 1 φ x : ℂ) + comb a zb x 1 * (cpd 2 φ x : ℂ)) =
            fun x => ∑ k ∈ a.support, a k •
              (zb k x 0 * (cpd 1 φ x : ℂ) + zb k x 1 * (cpd 2 φ x : ℂ)) := by
          funext x
          simp only [comb_apply, Finset.sum_mul, smul_mul_assoc, ← Finset.sum_add_distrib,
            smul_add]
        rw [heq]
        have hint : ∀ k ∈ a.support,
            Integrable (fun x => a k •
              (zb k x 0 * (cpd 1 φ x : ℂ) + zb k x 1 * (cpd 2 φ x : ℂ))) :=
          fun k _ => ((hglob_b k).solenoidal φ hφ).1.smul (a k)
        refine ⟨integrable_finsetSum _ hint, ?_⟩
        rw [integral_finsetSum a.support hint]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [integral_smul, ((hglob_b k).solenoidal φ hφ).2, smul_zero]
      equation := fun Ψ hΨ => by
        rw [hzc, hzqc, hzηc, hg_comb]
        have ez : (fun x => ∑ i : Fin 2, comb a zb x i * meridTranspose p.ν Ψ x i) =
            fun x => ∑ k ∈ a.support, a k • (∑ i : Fin 2, zb k x i * meridTranspose p.ν Ψ x i) :=
          funext (merid_pair_comb p.ν a zb Ψ)
        have eb : cdot (flatBv p.train (comb a zb) (comb a zqb) (comb a zηb)) Ψ =
            fun x => ∑ k ∈ a.support, a k • cdot (flatBv p.train (zb k) (zqb k) (zηb k)) Ψ x :=
          funext (cdot_flatBv_comb p.train a zb zqb zηb Ψ)
        have eg : cdot (comb a (fun i => gOf (B i))) Ψ =
            fun x => ∑ k ∈ a.support, a k • cdot (gOf (B k)) Ψ x :=
          funext (cdot_comb a (fun i => gOf (B i)) Ψ)
        have iz : ∀ k ∈ a.support,
            Integrable (fun x => a k • (∑ i : Fin 2, zb k x i * meridTranspose p.ν Ψ x i)) :=
          fun k _ => ((hglob_b k).equation Ψ hΨ).1.smul (a k)
        have ib : ∀ k ∈ a.support,
            Integrable (fun x => a k • cdot (flatBv p.train (zb k) (zqb k) (zηb k)) Ψ x) :=
          fun k _ => ((hglob_b k).equation Ψ hΨ).2.1.smul (a k)
        have ig : ∀ k ∈ a.support, Integrable (fun x => a k • cdot (gOf (B k)) Ψ x) :=
          fun k _ => ((hglob_b k).equation Ψ hΨ).2.2.1.smul (a k)
        have hIz : Integrable (fun x => ∑ i : Fin 2, comb a zb x i * meridTranspose p.ν Ψ x i) := by
          rw [ez]; exact integrable_finsetSum _ iz
        have hIb : Integrable (cdot (flatBv p.train (comb a zb) (comb a zqb) (comb a zηb)) Ψ) := by
          rw [eb]; exact integrable_finsetSum _ ib
        have hIg : Integrable (cdot (comb a (fun i => gOf (B i))) Ψ) := by
          rw [eg]; exact integrable_finsetSum _ ig
        refine ⟨hIz, hIb, hIg, ?_⟩
        rw [integral_add hIz hIb, ez, eb, eg, integral_finsetSum a.support iz,
          integral_finsetSum a.support ib, integral_finsetSum a.support ig,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk_eq := ((hglob_b k).equation Ψ hΨ).2.2.2
        have hkz := ((hglob_b k).equation Ψ hΨ).1
        have hkb := ((hglob_b k).equation Ψ hΨ).2.1
        rw [integral_smul, integral_smul, integral_smul, ← smul_add,
          ← integral_add hkz hkb, hk_eq]
      initial_curl := by
        have hdd_1 : ∀ s ∈ Ioc 0 p.H,
            Tendsto (dd p.c (comb a zq₁b) s) (𝓝[Ioc 0 p.H] s) (𝓝 0) ∧
              Tendsto (dd p.c (comb a zη₁b) s) (𝓝[Ioc 0 p.H] s) (𝓝 0) := by
          intro s hs
          have h := dd_tendsto_of_cylSliceH1 (hcont_z1 s hs)
          exact ⟨h.2.1, h.2.2⟩
        have hcurl_1 := curl_transfer_Ioo hH_pos hsm_zq1 hsm_zη1
          (fun s hs => (hdd_1 s hs).1) (fun s hs => (hdd_1 s hs).2)
          hae_zq1 hae_zη1 (entranceVorticityComb p (αMap F)) (hz_mc F).initial_curl
        refine hcurl_1.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hH_pos] with s hs
        rw [hzq_eq, hzη_eq]
        simp [profCurl, glueAtHorizon, hs.2.le]
    }
  -- Step 4: Tail Gronwall bound on s > p.H applied directly to (comb a z₂b, comb a zq₂b, comb a zη₂b)
  have hH1_z1H : IsCylH1Slice p.c (fun y => comb a z₁b (p.H, y))
      (fun y => comb a zq₁b (p.H, y)) (fun y => comb a zη₁b (p.H, y)) := by
    rw [comb_slice_eq, comb_slice_eq, comb_slice_eq]
    exact isCylH1Slice_comb p.c a hH1_1b
  have hmatch_z2H : cylSliceH1 p.c
      (fun y => comb a z₂b (p.H, y) - comb a z₁b (p.H, y))
      (fun y => comb a zq₂b (p.H, y) - comb a zq₁b (p.H, y))
      (fun y => comb a zη₂b (p.H, y) - comb a zη₁b (p.H, y)) = 0 := by
    refine le_antisymm ?_ zero_le
    refine (cylSliceH1_comb_diff_le p.c a
      (fun i => sliceMeas (hsm2b i) p.H) (fun i => sliceMeas (hsmq2b i) p.H)
      (fun i => sliceMeas (hsmη2b i) p.H)
      (fun i => sliceMeas (hsm1b i) p.H) (fun i => sliceMeas (hsmq1b i) p.H)
      (fun i => sliceMeas (hsmη1b i) p.H)).trans ?_
    simp [hmatch2b]
  obtain ⟨hH1_z2H, hnorm_H_eq⟩ := isCylH1Slice_of_cylSliceH1_eq_zero hH1_z1H
    (sliceMeas hsm_z2 p.H) (sliceMeas hsm_zq2 p.H) (sliceMeas hsm_zη2 p.H) hmatch_z2H
  have htail_z2 : IsTailMeridionalSolution p p.H (gOf F)
      (comb a z₂b) (comb a zq₂b) (comb a zη₂b) := by
    rw [hg_comb]
    exact isTailMeridionalSolution_comb p p.H a htail2b
  have hcont_z2 : ∀ s : ℝ, p.H ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => comb a z₂b (s', y) - comb a z₂b (s, y))
        (fun y => comb a zq₂b (s', y) - comb a zq₂b (s, y))
        (fun y => comb a zη₂b (s', y) - comb a zη₂b (s, y))) (𝓝[Ici p.H] s) (𝓝 0) :=
    fun s hs => cylSliceH1_comb_tendsto p.c a hsm2b hsmq2b hsmη2b (fun i => hcont2b i s hs)
  have hlate_out : ∀ s : ℝ, p.H < s →
      sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s ≤
        ENNReal.ofReal (A_H1 * Real.exp (K_H1 * B_strain)) *
          (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) p.H +
            ENNReal.ofReal K_H1 * ∫⁻ t in Ioi p.H,
              sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) t) := by
    intro s hs
    have h_s : sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s =
        sliceH1Norm p.c (comb a z₂b) (comb a zq₂b) (comb a zη₂b) s := by
      rw [hz_eq, hzq_eq, hzη_eq]
      simp [sliceH1Norm, glueAtHorizon, not_le.2 hs]
    have h_H : sliceH1Norm p.c (comb a z₂b) (comb a zq₂b) (comb a zη₂b) p.H =
        sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) p.H := by
      rw [hz_eq, hzq_eq, hzη_eq]
      simpa [sliceH1Norm, cylSliceH1, cylSliceL2, glueAtHorizon] using hnorm_H_eq
    rw [h_s, ← h_H]
    exact hGron hreg hν1 hH1 hB_nn hStrain (hg_src F) (hg_Ioi F)
      hsm_z2 hsm_zq2 hsm_zη2 hH1_z2H htail_z2 hcont_z2 s hs
  exact ⟨hsm_z, hsm_zq, hsm_zη, hm_z, hglob_out, hearly_out, hlate_out⟩

end ContLinearGlueAux

end UnforcedLeray.Short.IIb

end
